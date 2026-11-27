import PEqualNP.Defs

-- Run normalization and general certificate checker: Digger-Rockwell PR801, Apache-2.0.
-- Original source ea90309308dd46a22d4a469766e46dd63f4484d0.
-- The exact-one row projection and finite certificate below are specific to this claim.

namespace PEqualNP.Outside.L_meta_10409_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section Normalization
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

end Normalization

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lo (k : Nat) := 2 ^ k - 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mask (k : Nat) := lo (k + k)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def goal (k : Nat) := lo k <<< k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev fE : BFn 4 := fun x => decide ((List.ofFn x).count true = 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rowsE : List ℕ := [0, 0, 0, 0, 3, 3, 3, 3, 5, 5, 5, 5, 6, 6, 6, 6, 9, 9, 9, 9, 10, 10, 10, 10, 12, 12, 12, 12, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def xsE : List ℕ := [0x111111100f0ff0, 0x22222220f0f0f0, 0x4444444f00ff00, 0x8888888fff0000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowsE_len : rowsE.length = 56 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enc_inputsE :
    (List.ofFn fun (i : Fin 4) => (fun x : Fin 4 → Bool => x i)).map (fun a => encL a rowsE)
      = xsE := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enc_goalE : encL fE rowsE = goal 28 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskE : mask 28 = 2 ^ rowsE.length - 1 := by rw [rowsE_len]; simp [mask, lo]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem proper_failE : ∀ zs ∈ xsE.sublists, zs ≠ xsE →
    (cov 28 zs &&& lo 28) ≠ lo 28 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_subE (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 28) (goal 28) s xsE) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsE → NatRun (mask 28) (goal 28) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsE
  · subst e; exact noRunFull s hs h
  · exact proper_failE zs (List.mem_sublists.2 hz) e (required h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainE (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 28) (goal 28) s xsE) :
    ¬ HasCircuitSize 4 fE 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fE ⟨pt 4 0, pt 4 1, by decide⟩ 9 h
  have hr : NatRun (mask 28) (encL fE rowsE) s' (ws.map fun a => encL a rowsE) :=
    Run.map (fun a : BFn 4 => encL a rowsE)
      (fun a => by rw [maskE]; exact encL_inv a rowsE)
      (fun a b => encL_and a b rowsE) (fun a b => encL_or a b rowsE) hrun
  rw [enc_goalE] at hr
  refine no_subE noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsE]
  exact hsub.map _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
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
        grind
    · exact hw _ (by simp [ht])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
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
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩


-- The hint proposes a state in the next layer and a symmetry of the input rows.
-- The exact multiset comparison checks both proposals.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def matchesState (perm : Nat → Nat → Nat) (states : Nat → Nat → List Nat)
    (count : Nat → Nat) (lookup : Nat → List Nat → Nat) (s : Nat) (zs : List Nat) : Bool :=
  let entry := lookup s zs
  let i := entry / 32
  decide (i < count s) && (zs.map (perm (entry % 32))).isPerm (states s i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem matchesState_sound {perm states count lookup s zs}
    (hp : ∀ p {u ws}, NatRun (mask 28) (goal 28) u ws →
      NatRun (mask 28) (goal 28) u (ws.map (perm p)))
    (hm : matchesState perm states count lookup s zs = true)
    (hr : NatRun (mask 28) (goal 28) s zs) :
    ∃ i < count s, NatRun (mask 28) (goal 28) s (states s i) := by
  simp only [matchesState, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hm
  exact ⟨_, hm.1, Run.perm hm.2 (hp _ hr)⟩

-- Every legal next step must either fail separation or match a stored state.
-- At budget zero the only successful state is the single output wire.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def closedState (perm : Nat → Nat → Nat) (states : Nat → Nat → List Nat)
    (count : Nat → Nat) (lookup : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(states 0 i == [goal 28])
  | s + 1, i =>
    let ws := states (s + 1) i
    !(next (mask 28) (s + 2 - ws.length) ws fun zs =>
      covers 28 s zs && !(matchesState perm states count lookup s zs))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closedState_sound {perm states count lookup}
    (hp : ∀ p {u ws}, NatRun (mask 28) (goal 28) u ws →
      NatRun (mask 28) (goal 28) u (ws.map (perm p)))
    (hc : ∀ s ≤ 9, ∀ i < count s, closedState perm states count lookup s i = true) :
    ∀ s ≤ 9, ∀ i < count s, ¬ NatRun (mask 28) (goal 28) s (states s i) := by
  intro s
  induction s with
  | zero =>
    intro hs i hi h
    have hcheck := hc 0 hs i hi
    simp [closedState, zero_done h rfl] at hcheck
  | succ s ih =>
    intro hs i hi h
    let bad := fun zs => covers 28 s zs && !(matchesState perm states count lookup s zs)
    have hbad (zs) (hr : NatRun (mask 28) (goal 28) s zs) : bad zs = true := by
      have hn : matchesState perm states count lookup s zs = false := by
        cases he : matchesState perm states count lookup s zs with
        | false => rfl
        | true =>
          obtain ⟨j, hj, hrun⟩ := matchesState_sound hp he hr
          exact (ih (by omega) j hj hrun).elim
      simp [bad, covers_ok hr, hn]
    have het := next_complete h s rfl _ (List.Perm.refl _) bad hbad
    have hcheck := hc (s + 1) hs i hi
    change !(next _ _ _ bad) = true at hcheck
    rw [het] at hcheck
    contradiction


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def permChunks : List (List (Nat × Nat × Nat)) := [
  [(72057594037927935, 0, 0)],
  [(2392537310953472, 0, 9), (897201491607552, 0, 8), (1196268655476736, 0, 7), (36028833660403848, 0, 1), (13510812622651443, 0, 0), (18014416830201924, 1, 0), (9345848870912, 7, 0), (3504693326592, 8, 0), (4672924435456, 9, 0)],
  [(18014673454498816, 0, 5), (40533015272622336, 0, 4), (9007336727249408, 0, 3), (74767864709124, 0, 1), (168227695595529, 0, 0), (37383932354562, 1, 0), (1125917090906176, 3, 0), (2533313454538896, 4, 0), (562958545453088, 5, 0)],
  [(140737488879616, 0, 14), (17592186109952, 0, 12), (105553116659712, 0, 11), (2251799822073856, 0, 10), (281474977759232, 0, 8), (1688849866555392, 0, 7), (36028797153181696, 0, 6), (4503599644147712, 0, 4), (27021597864886272, 0, 3), (2147483656, 0, 2), (268435457, 0, 0), (1610612742, 1, 0), (34359738496, 2, 0), (4294967312, 4, 0), (25769803872, 5, 0), (549755815936, 6, 0), (68719476992, 8, 0), (412316861952, 9, 0), (8796093054976, 10, 0), (1099511631872, 12, 0), (6597069791232, 13, 0)],
  [(54043195729772544, 0, 13), (4503599644147712, 0, 12), (9007199288295424, 0, 10), (211106233319424, 0, 9), (17592186109952, 0, 8), (35184372219904, 0, 6), (824633723904, 0, 5), (68719476992, 0, 4), (137438953984, 0, 2), (3221225484, 0, 1), (268435457, 0, 0), (536870914, 2, 0), (3377699733110784, 3, 0), (281474977759232, 4, 0), (562949955518464, 6, 0), (13194139582464, 7, 0), (1099511631872, 8, 0), (2199023263744, 10, 0), (51539607744, 11, 0), (4294967312, 12, 0), (8589934624, 14, 0)],
  [(36169534642061312, 0, 14), (22605959151288320, 0, 12), (9042383660515328, 0, 10), (2252351725373448, 0, 2), (1407719828358405, 0, 0), (563087931343362, 2, 0), (8830452793472, 10, 0), (5519032995920, 12, 0), (2207613198368, 14, 0)],
  [(565148978782208, 0, 5), (3390893872693248, 0, 4), (282574489391104, 0, 3), (9007208415100962, 0, 1), (54043250490605772, 0, 0), (4503604207550481, 1, 0), (35321811173888, 3, 0), (211930867043328, 4, 0), (17660905586944, 5, 0)],
  [(2814749777592320, 0, 13), (1407374888796160, 0, 11), (175921861099520, 0, 5), (87960930549760, 0, 3), (45036042075504810, 0, 1), (22518021037752405, 1, 0), (10995116318720, 3, 0), (5497558159360, 5, 0), (687194769920, 11, 0), (343597384960, 13, 0)],
  [(18014398576590848, 0, 10), (36028797153181696, 0, 8), (13510798932443136, 0, 7), (4672924435456, 0, 6), (9345848870912, 0, 4), (3504693326592, 0, 3), (1073741828, 0, 2), (2147483656, 0, 0), (805306371, 1, 0), (1196268655476736, 2, 0), (2392537310953472, 4, 0), (897201491607552, 5, 0), (17179869248, 6, 0), (34359738496, 8, 0), (12884901936, 9, 0)],
  [(2392537310953472, 0, 15), (38122267300265984, 0, 11), (31525197509033984, 0, 7), (2147483656, 0, 3), (1879048199, 1, 0), (34359738496, 5, 0), (9375913642096, 9, 0), (8177617762048, 13, 0)],
  [(18014398576590848, 0, 18), (36028797153181696, 0, 17), (4503599644147712, 0, 15), (9007199288295424, 0, 14), (70643622347776, 0, 6), (141287244695552, 0, 5), (17660905586944, 0, 3), (35322884915716, 0, 2), (2147483656, 0, 1), (268435457, 1, 0), (1130298494435330, 2, 0), (2260595915128832, 3, 0), (282574489391104, 5, 0), (565148978782208, 6, 0), (17179869248, 14, 0), (34359738496, 15, 0), (4294967312, 17, 0), (8589934624, 18, 0)],
  [(36028797153181696, 0, 19), (18014398576590848, 0, 16), (4644337133027328, 0, 15), (9007199288295424, 0, 14), (70368744439808, 0, 12), (17592186109952, 0, 11), (35184372219904, 0, 10), (2251799822073856, 0, 7), (1125899911036928, 0, 4), (281477125242888, 0, 3), (562949955518464, 0, 2), (1073741828, 0, 0), (550024251393, 1, 0), (536870914, 2, 0), (274877907968, 4, 0), (68719476992, 5, 0), (137438953984, 6, 0), (8796093054976, 9, 0), (4398046527488, 12, 0), (1133871370368, 13, 0), (2199023263744, 14, 0), (17179869248, 16, 0), (4294967312, 17, 0), (8589934624, 18, 0)],
  [(6597069791232, 0, 9), (8796093054976, 0, 8), (1099511631872, 0, 6), (28710447731441664, 0, 5), (38280596975255552, 0, 4), (4785074621906944, 0, 2), (1610612742, 0, 1), (2147483656, 0, 0), (268435457, 2, 0), (438086665824, 3, 0), (584115554432, 4, 0), (73014444304, 6, 0), (105553116659712, 7, 0), (140737488879616, 8, 0), (17592186109952, 10, 0)],
  [(2251799822073856, 0, 18), (562949955518464, 0, 17), (1125899911036928, 0, 15), (281474977759232, 0, 14), (36169534642061312, 0, 6), (9042383660515328, 0, 5), (18084767321030656, 0, 3), (4521193977741320, 0, 2), (536870914, 0, 1), (1073741828, 1, 0), (8830721228929, 2, 0), (2207613198368, 3, 0), (4415226396736, 5, 0), (1103806599184, 6, 0), (549755815936, 14, 0), (137438953984, 15, 0), (274877907968, 17, 0), (68719476992, 18, 0)],
  [(18018796623118336, 0, 10), (45046991557795840, 0, 8), (4504699155779584, 0, 6), (1126175862686724, 0, 2), (2815439656716810, 0, 0), (281543965671681, 2, 0), (70385924309056, 6, 0), (175964810772640, 8, 0), (17596481077264, 10, 0)],
  [(2251799822073856, 0, 19), (562949955518464, 0, 16), (1125899911036928, 0, 15), (281474977759232, 0, 14), (36169534642061312, 0, 11), (9042383660515328, 0, 8), (18084767321030656, 0, 7), (4521191830257664, 0, 6), (2147483656, 0, 3), (536870914, 0, 0), (1073741828, 1, 0), (268435457, 2, 0), (8830452793472, 5, 0), (2207613198368, 8, 0), (4415226396736, 9, 0), (1103806599184, 10, 0), (549755815936, 13, 0), (137438953984, 16, 0), (274877907968, 17, 0), (68719476992, 18, 0)],
  [(54043195729772544, 0, 22), (13510798932443136, 0, 18), (211106233319424, 0, 6), (3431304146390028, 0, 2), (857826036597507, 2, 0), (3298534895616, 6, 0), (51539607744, 18, 0), (12884901936, 22, 0)],
  [(36028797153181696, 0, 23), (18014398576590848, 0, 21), (13510798932443136, 0, 18), (140737488879616, 0, 11), (70368744439808, 0, 9), (2251799822073856, 0, 7), (52776558329856, 0, 6), (1125899911036928, 0, 5), (2147483656, 0, 3), (844424933277696, 0, 2), (1073741828, 0, 1), (549755815936, 1, 0), (805306371, 2, 0), (274877907968, 3, 0), (8796093054976, 5, 0), (206158430976, 6, 0), (4398046527488, 7, 0), (3298534895616, 10, 0), (34359738496, 17, 0), (17179869248, 19, 0), (12884901936, 22, 0)],
  [(66991044706697216, 0, 13), (4800467784753152, 0, 9), (1099511631872, 0, 5), (3758096398, 0, 1), (268435457, 3, 0), (246290605539328, 7, 0), (18614388330208, 11, 0), (73014444304, 15, 0)],
  [(2251799822073856, 0, 18), (562949955518464, 0, 17), (1125899911036928, 0, 16), (36028797153181696, 0, 14), (9288674266054656, 0, 13), (18014398576590848, 0, 12), (4503599644147712, 0, 9), (8796093054976, 0, 6), (2199023263744, 0, 5), (4398046527488, 0, 4), (2147483656, 0, 2), (1100048502786, 0, 1), (1073741828, 0, 0), (140737488879616, 2, 0), (35184640655361, 3, 0), (70368744439808, 4, 0), (17592186109952, 7, 0), (34359738496, 10, 0), (8589934624, 11, 0), (17179869248, 12, 0), (549755815936, 14, 0), (141733921296, 15, 0), (274877907968, 16, 0), (68719476992, 19, 0)],
  [(18014398576590848, 0, 18), (36028797153181696, 0, 17), (9007199288295424, 0, 16), (4503599644147712, 0, 13), (1130297957564416, 0, 10), (2260595915128832, 0, 9), (565148978782208, 0, 8), (282574489391104, 0, 5), (1073741828, 0, 2), (2147483656, 0, 1), (536870914, 0, 0), (268435457, 3, 0), (70643622347776, 6, 0), (141287244695552, 7, 0), (35321811173888, 8, 0), (17660905586944, 11, 0), (17179869248, 14, 0), (34359738496, 15, 0), (8589934624, 16, 0), (4294967312, 19, 0)],
  [(38280596975255552, 0, 19), (28710447731441664, 0, 16), (4785074621906944, 0, 13), (149535729418248, 0, 3), (112151797063686, 0, 0), (18691966177281, 3, 0), (584115554432, 13, 0), (438086665824, 16, 0), (73014444304, 19, 0)],
  [(54043195729772544, 0, 22), (9007199288295424, 0, 19), (4503599644147712, 0, 17), (3377699733110784, 0, 10), (562949955518464, 0, 7), (13194139582464, 0, 6), (281474977759232, 0, 5), (2199023263744, 0, 3), (3221225484, 0, 2), (1099511631872, 0, 1), (536870914, 1, 0), (211106233319424, 2, 0), (268435457, 3, 0), (35184372219904, 5, 0), (824633723904, 6, 0), (17592186109952, 7, 0), (137438953984, 9, 0), (68719476992, 11, 0), (51539607744, 18, 0), (8589934624, 21, 0), (4294967312, 23, 0)],
  [(36028797153181696, 0, 23), (18014398576590848, 0, 21), (9007199288295424, 0, 19), (4503599644147712, 0, 17), (2251799822073856, 0, 15), (1125899911036928, 0, 13), (562949955518464, 0, 11), (281474977759232, 0, 9), (149535729418248, 0, 3), (74767864709124, 0, 1), (37383932354562, 1, 0), (18691966177281, 3, 0), (549755815936, 9, 0), (274877907968, 11, 0), (137438953984, 13, 0), (68719476992, 15, 0), (34359738496, 17, 0), (17179869248, 19, 0), (8589934624, 21, 0), (4294967312, 23, 0)]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def permPreimages : List (List Nat) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55],
  [0, 1, 3, 2, 4, 5, 7, 6, 16, 17, 19, 18, 20, 21, 23, 22, 8, 9, 11, 10, 12, 13, 15, 14, 24, 25, 27, 26, 28, 29, 31, 30, 32, 33, 35, 34, 44, 45, 47, 46, 48, 49, 51, 50, 36, 37, 39, 38, 40, 41, 43, 42, 52, 53, 55, 54],
  [0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15, 16, 18, 17, 19, 24, 26, 25, 27, 20, 22, 21, 23, 28, 30, 29, 31, 36, 38, 37, 39, 32, 34, 33, 35, 40, 42, 41, 43, 44, 46, 45, 47, 52, 54, 53, 55, 48, 50, 49, 51],
  [0, 3, 1, 2, 16, 19, 17, 18, 4, 7, 5, 6, 20, 23, 21, 22, 8, 11, 9, 10, 24, 27, 25, 26, 12, 15, 13, 14, 28, 31, 29, 30, 44, 47, 45, 46, 32, 35, 33, 34, 48, 51, 49, 50, 36, 39, 37, 38, 52, 55, 53, 54, 40, 43, 41, 42],
  [0, 2, 3, 1, 8, 10, 11, 9, 16, 18, 19, 17, 24, 26, 27, 25, 4, 6, 7, 5, 12, 14, 15, 13, 20, 22, 23, 21, 28, 30, 31, 29, 36, 38, 39, 37, 44, 46, 47, 45, 52, 54, 55, 53, 32, 34, 35, 33, 40, 42, 43, 41, 48, 50, 51, 49],
  [0, 3, 2, 1, 16, 19, 18, 17, 8, 11, 10, 9, 24, 27, 26, 25, 4, 7, 6, 5, 20, 23, 22, 21, 12, 15, 14, 13, 28, 31, 30, 29, 44, 47, 46, 45, 36, 39, 38, 37, 52, 55, 54, 53, 32, 35, 34, 33, 48, 51, 50, 49, 40, 43, 42, 41],
  [1, 0, 2, 3, 5, 4, 6, 7, 13, 12, 14, 15, 9, 8, 10, 11, 21, 20, 22, 23, 17, 16, 18, 19, 25, 24, 26, 27, 29, 28, 30, 31, 33, 32, 34, 35, 41, 40, 42, 43, 37, 36, 38, 39, 49, 48, 50, 51, 45, 44, 46, 47, 53, 52, 54, 55],
  [1, 0, 3, 2, 5, 4, 7, 6, 21, 20, 23, 22, 17, 16, 19, 18, 13, 12, 15, 14, 9, 8, 11, 10, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 49, 48, 51, 50, 45, 44, 47, 46, 41, 40, 43, 42, 37, 36, 39, 38, 53, 52, 55, 54],
  [2, 0, 1, 3, 10, 8, 9, 11, 14, 12, 13, 15, 6, 4, 5, 7, 26, 24, 25, 27, 18, 16, 17, 19, 22, 20, 21, 23, 30, 28, 29, 31, 38, 36, 37, 39, 42, 40, 41, 43, 34, 32, 33, 35, 54, 52, 53, 55, 46, 44, 45, 47, 50, 48, 49, 51],
  [3, 0, 1, 2, 19, 16, 17, 18, 23, 20, 21, 22, 7, 4, 5, 6, 27, 24, 25, 26, 11, 8, 9, 10, 15, 12, 13, 14, 31, 28, 29, 30, 47, 44, 45, 46, 51, 48, 49, 50, 35, 32, 33, 34, 55, 52, 53, 54, 39, 36, 37, 38, 43, 40, 41, 42],
  [2, 0, 3, 1, 10, 8, 11, 9, 26, 24, 27, 25, 18, 16, 19, 17, 14, 12, 15, 13, 6, 4, 7, 5, 22, 20, 23, 21, 30, 28, 31, 29, 38, 36, 39, 37, 54, 52, 55, 53, 46, 44, 47, 45, 42, 40, 43, 41, 34, 32, 35, 33, 50, 48, 51, 49],
  [3, 0, 2, 1, 19, 16, 18, 17, 27, 24, 26, 25, 11, 8, 10, 9, 23, 20, 22, 21, 7, 4, 6, 5, 15, 12, 14, 13, 31, 28, 30, 29, 47, 44, 46, 45, 55, 52, 54, 53, 39, 36, 38, 37, 51, 48, 50, 49, 35, 32, 34, 33, 43, 40, 42, 41],
  [1, 2, 0, 3, 13, 14, 12, 15, 5, 6, 4, 7, 9, 10, 8, 11, 21, 22, 20, 23, 25, 26, 24, 27, 17, 18, 16, 19, 29, 30, 28, 31, 41, 42, 40, 43, 33, 34, 32, 35, 37, 38, 36, 39, 49, 50, 48, 51, 53, 54, 52, 55, 45, 46, 44, 47],
  [1, 3, 0, 2, 21, 23, 20, 22, 5, 7, 4, 6, 17, 19, 16, 18, 13, 15, 12, 14, 25, 27, 24, 26, 9, 11, 8, 10, 29, 31, 28, 30, 49, 51, 48, 50, 33, 35, 32, 34, 45, 47, 44, 46, 41, 43, 40, 42, 53, 55, 52, 54, 37, 39, 36, 38],
  [2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11, 6, 5, 4, 7, 26, 25, 24, 27, 22, 21, 20, 23, 18, 17, 16, 19, 30, 29, 28, 31, 42, 41, 40, 43, 38, 37, 36, 39, 34, 33, 32, 35, 54, 53, 52, 55, 50, 49, 48, 51, 46, 45, 44, 47],
  [3, 1, 0, 2, 23, 21, 20, 22, 19, 17, 16, 18, 7, 5, 4, 6, 27, 25, 24, 26, 15, 13, 12, 14, 11, 9, 8, 10, 31, 29, 28, 30, 51, 49, 48, 50, 47, 45, 44, 46, 35, 33, 32, 34, 55, 53, 52, 54, 43, 41, 40, 42, 39, 37, 36, 38],
  [2, 3, 0, 1, 26, 27, 24, 25, 10, 11, 8, 9, 18, 19, 16, 17, 14, 15, 12, 13, 22, 23, 20, 21, 6, 7, 4, 5, 30, 31, 28, 29, 54, 55, 52, 53, 38, 39, 36, 37, 46, 47, 44, 45, 42, 43, 40, 41, 50, 51, 48, 49, 34, 35, 32, 33],
  [3, 2, 0, 1, 27, 26, 24, 25, 19, 18, 16, 17, 11, 10, 8, 9, 23, 22, 20, 21, 15, 14, 12, 13, 7, 6, 4, 5, 31, 30, 28, 29, 55, 54, 52, 53, 47, 46, 44, 45, 39, 38, 36, 37, 51, 50, 48, 49, 43, 42, 40, 41, 35, 34, 32, 33],
  [1, 2, 3, 0, 13, 14, 15, 12, 21, 22, 23, 20, 25, 26, 27, 24, 5, 6, 7, 4, 9, 10, 11, 8, 17, 18, 19, 16, 29, 30, 31, 28, 41, 42, 43, 40, 49, 50, 51, 48, 53, 54, 55, 52, 33, 34, 35, 32, 37, 38, 39, 36, 45, 46, 47, 44],
  [1, 3, 2, 0, 21, 23, 22, 20, 13, 15, 14, 12, 25, 27, 26, 24, 5, 7, 6, 4, 17, 19, 18, 16, 9, 11, 10, 8, 29, 31, 30, 28, 49, 51, 50, 48, 41, 43, 42, 40, 53, 55, 54, 52, 33, 35, 34, 32, 45, 47, 46, 44, 37, 39, 38, 36],
  [2, 1, 3, 0, 14, 13, 15, 12, 26, 25, 27, 24, 22, 21, 23, 20, 10, 9, 11, 8, 6, 5, 7, 4, 18, 17, 19, 16, 30, 29, 31, 28, 42, 41, 43, 40, 54, 53, 55, 52, 50, 49, 51, 48, 38, 37, 39, 36, 34, 33, 35, 32, 46, 45, 47, 44],
  [3, 1, 2, 0, 23, 21, 22, 20, 27, 25, 26, 24, 15, 13, 14, 12, 19, 17, 18, 16, 7, 5, 6, 4, 11, 9, 10, 8, 31, 29, 30, 28, 51, 49, 50, 48, 55, 53, 54, 52, 43, 41, 42, 40, 47, 45, 46, 44, 35, 33, 34, 32, 39, 37, 38, 36],
  [2, 3, 1, 0, 26, 27, 25, 24, 14, 15, 13, 12, 22, 23, 21, 20, 10, 11, 9, 8, 18, 19, 17, 16, 6, 7, 5, 4, 30, 31, 29, 28, 54, 55, 53, 52, 42, 43, 41, 40, 50, 51, 49, 48, 38, 39, 37, 36, 46, 47, 45, 44, 34, 35, 33, 32],
  [3, 2, 1, 0, 27, 26, 25, 24, 23, 22, 21, 20, 15, 14, 13, 12, 19, 18, 17, 16, 11, 10, 9, 8, 7, 6, 5, 4, 31, 30, 29, 28, 55, 54, 53, 52, 51, 50, 49, 48, 43, 42, 41, 40, 47, 46, 45, 44, 39, 38, 37, 36, 35, 34, 33, 32]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def moveChunks (x : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (m, l, r) :: cs => (((x &&& m) >>> r) <<< l) ||| moveChunks x cs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def readChunks (i : Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (m, l, r) :: cs =>
    if decide (l ≤ i) && m.testBit (r + (i-l)) then (r + (i-l)) :: readChunks i cs
    else readChunks i cs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chunks_bit (x i : Nat) (cs : List (Nat × Nat × Nat)) :
    (moveChunks x cs).testBit i = (readChunks i cs).any (fun j => x.testBit j) := by
  induction cs with
  | nil => simp [moveChunks, readChunks]
  | cons c cs ih =>
    rcases c with ⟨m,l,r⟩
    simp only [moveChunks, readChunks, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.testBit_and, ih]
    cases h : decide (l ≤ i) <;> cases hm : m.testBit (r + (i-l)) <;>
      cases hx : x.testBit (r + (i-l)) <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mapPerm (p x : Nat) : Nat :=
  if p < 24 then moveChunks x (permChunks.getD p []) &&& mask 28 else x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def permPreimage (p i : Nat) : Nat := (permPreimages.getD p []).getD i 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem readChunks_checked :
    ∀ (p : Fin 24) (i : Fin 56),
      readChunks i (permChunks.getD p []) = [permPreimage p i] ∧
      permPreimage p i < 56 ∧ (28 ≤ permPreimage p i ↔ 28 ≤ (i : Nat)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem mapPerm_bit {p i : Nat} (hp : p < 24) (hi : i < 56) (x : Nat) :
    (mapPerm p x).testBit i = x.testBit (permPreimage p i) := by
  have h := (readChunks_checked ⟨p,hp⟩ ⟨i,hi⟩).1
  simp only [mapPerm, ite_eq_left hp, Nat.testBit_and, chunks_bit, h,
    List.any_cons, List.any_nil, Bool.or_false, mask, lo, Nat.testBit_two_pow_sub_one]
  simp [hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem mapPerm_bit_high {p i : Nat} (hp : p < 24) (hi : ¬ i < 56) (x : Nat) :
    (mapPerm p x).testBit i = false := by
  have hm : (mask 28).testBit i = false := by
    change (2^56 - 1).testBit i = false
    rw [Nat.testBit_two_pow_sub_one, decide_eq_false hi]
  simp [mapPerm, hp, Nat.testBit_and, hm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mapPerm_and (p x y : Nat) :
    mapPerm p (x &&& y) = mapPerm p x &&& mapPerm p y := by
  by_cases hp : p < 24
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 56
    · simp [mapPerm_bit hp hi, Nat.testBit_and]
    · simp [mapPerm_bit_high hp hi, Nat.testBit_and]
  · simp [mapPerm, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mapPerm_or (p x y : Nat) :
    mapPerm p (x ||| y) = mapPerm p x ||| mapPerm p y := by
  by_cases hp : p < 24
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 56
    · simp [mapPerm_bit hp hi, Nat.testBit_or]
    · simp [mapPerm_bit_high hp hi, Nat.testBit_or]
  · simp [mapPerm, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mapPerm_xor (p x y : Nat) :
    mapPerm p (x ^^^ y) = mapPerm p x ^^^ mapPerm p y := by
  by_cases hp : p < 24
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 56
    · simp [mapPerm_bit hp hi, Nat.testBit_xor]
    · simp [mapPerm_bit_high hp hi, Nat.testBit_xor]
  · simp [mapPerm, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem mapPerm_constants :
    ∀ p : Fin 24, mapPerm p (mask 28) = mask 28 ∧ mapPerm p (goal 28) = goal 28 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mapPerm_mask (p : Nat) : mapPerm p (mask 28) = mask 28 := by
  by_cases hp : p < 24
  · exact (mapPerm_constants ⟨p,hp⟩).1
  · simp [mapPerm, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mapPerm_goal (p : Nat) : mapPerm p (goal 28) = goal 28 := by
  by_cases hp : p < 24
  · exact (mapPerm_constants ⟨p,hp⟩).2
  · simp [mapPerm, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem run_mapPerm (p : Nat) {s : Nat} {ws : List Nat}
    (h : NatRun (mask 28) (goal 28) s ws) :
    NatRun (mask 28) (goal 28) s (ws.map (mapPerm p)) := by
  have he (a : Nat) : mapPerm p (a ^^^ mask 28) = mapPerm p a ^^^ mask 28 := by
    rw [mapPerm_xor, mapPerm_mask]
  have h' := Run.map (mapPerm p) (inv' := (· ^^^ mask 28)) (meet' := (· &&& ·)) (join' := (· ||| ·)) he (mapPerm_and p) (mapPerm_or p) h
  rwa [mapPerm_goal] at h'



-- Finite certificate
-- There are 2,455 representative states. Each hash lookup supplies a proposed
-- permutation and state index. The checker verifies the resulting wire values.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certField (w width i : Nat) : Nat := (w >>> (width * i)) &&& (2 ^ width - 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def nStates : Nat → Nat
  | 2 => 13
  | 3 => 145
  | 4 => 699
  | 5 => 1017
  | 6 => 516
  | 7 => 59
  | 8 => 5
  | 9 => 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certStride : Nat → Nat
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | 8 => 5
  | 9 => 4
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certLength (s i : Nat) : Nat :=
  let b := i / 128
  let w := match s with
    | 2 => 0x2222222222222
    | 3 => (if b < 1 then 0x33333333333333333333333333333333333333333333333333333333333333323333333333333323333333333333333333333333333333333333333333333333 else 0x33333333333333333)
    | 4 => (if b < 3 then (if b < 2 then (if b < 1 then 0x44444344344444444444444444444444444444444444444444434444444444444434443444443444344444344344444444444444444444444444444444444444 else 0x44444444444444444444444444444444444444444444444444444443444444444444444444444444444444444444444444444444444444444344444444444444) else 0x44444444434444434444444444444434444434444444444443444444344444444344443444444444434444444434444444444444444444444444444444444444) else (if b < 5 then (if b < 4 then 0x44434444444444444344444444444444444444444443444444444444443444444444444444444444444444444444444444444444444444434444444444444444 else 0x44444444444443444344444444444444444444444444434444444444444444444444444444444444444444444444444444444444344444444444444444444444) else 0x44444444444444444444444444444444444444444444444444444444444))
    | 5 => (if b < 4 then (if b < 2 then (if b < 1 then 0x55555555555555555554555555555555554555555555555555555555555555545555555555455555555555555555455555555555455555555555555555545554 else 0x54555555555555555545554555555555455555555555555555555555555555555555555555545555454555555555555555545554555555545554435454555555) else (if b < 3 then 0x55555555555555555455555555555555555555555555555555555555545554555554554554555555555555555554555555555555555555555555555555455545 else 0x55555555545545555555555455545555555555455555555545555555555555555555555555455555555555555555555555555555555555555545555555555555)) else (if b < 6 then (if b < 5 then 0x55555545555555545555544355555555555545454545545455554555555545454544343444344445555544355455554554435555555555555555555545555555 else 0x54555555555555555555555555555555555455554555555555555555555455555455555555555454555455555454545455555455554555554554555455554555) else (if b < 7 then 0x55555555555555555554555555555555555555555555555545555555554555554555545554435545555555555554555545555555555555455455555554555555 else 0x4555555555555555555545555555555555455555555455555455555555555555555555555554555555455455555555555555455555555555555555555)))
    | 6 => (if b < 3 then (if b < 2 then (if b < 1 then 0x66665656565656566656665656655666565655466566666656655466565656665656565656566656565466565656565565565656565656665656665554555554 else 0x65666666666665666666566565666666666666566566665666565646666666666666665666566666666666665665665665666666566566656565665656666666) else 0x65666546566565546665665466666665566566666665666666656565665546656555555455443545466666656666666666666666666656655466666666666566) else (if b < 4 then 0x66666656656665666665656554545556665666566665665666666665665665666566666655465666566666666565656566666666665656566666666566666566 else 0x4656))
    | 7 => 0x46666554665656665656566565654665655655656565656566654555554
    | 8 => 0x45554
    | 9 => 0x4
    | _ => 0
  certField w 4 (i % 128)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certWire (s i : Nat) : Nat :=
  let b := i / 32
  let w := match s with
    | 2 => 0x4444444fffff00444444400000ff8888888fff00008888888000ffffeeeeeee00f0ff0111111100f0ff08888888ffff00088888880000fff1111111ffffff01111111000000f7777777ffffff07777777000000feeeeeee00ffff0111111100ffff0cccccccfffff00ccccccc00000ff3333333ffffff03333333000000fcccccccffffff03333333ffffff0eeeeeee0fffff011111110fffff0ccccccc0fffff033333330fffff0eeeeeeeffffff01111111ffffff0
    | 3 => (if b < 7 then (if b < 4 then (if b < 2 then (if b < 1 then 0x6666666ff0fff0111111100f0ff0999999900ff00f8888888fff0000111111100f0ff0333333300000ff2222222ff0f0f0111111100f0ff0ccccccc0ffff0022222220f0f0f0111111100f0ff07777777000ffff6666666ff00ff0111111100f0ff0999999900ff00f7777777000ffff111111100f0ff07777777000ffff6666666ff0fff0111111100ffff0eeeeeeeff0f00f999999900ff00f7777777000ffffeeeeeeeff0f00f77777770000fff6666666ff0fff0bbbbbbb0ff00ff7777777000ffff33333330ffff00ddddddd00f0f0f333333300000ff111111100f0ff0 else 0x11111110fffff0cccccccfffff002222222ff0fff0111111100f0ff0777777700000ff6666666ff0fff0111111100f0ff08888888ffff0006666666ff0fff0111111100ffff077777770ffffff4444444f00fff03333333000fff0777777700fffff6666666ff0fff01111111000fff07777777ffffff07777777000ffff0000000000fff0eeeeeeeff0f00fddddddd00f0f0f333333300000ff77777770000fff6666666ff0fff0111111100ffff0cccccccfffff002222222ff0f0f0111111100f0ff0dddddddf0f0f0f333333300000ff1111111f0f0ff077777770000fff) else (if b < 3 then 0x8888888fffff006666666ff0f0f0111111100f0ff0dddddddf0f0f0f333333300000ff1111111f0ffff0dddddddf0f0f0f777777700000ff5555555f0ffff0cccccccfffff002222222ffff0f011111110000ff0777777700fffff5555555f0ffff022222220fffff07777777000ffff4444444ffffff033333330fffff07777777000ffff6666666ffffff0111111100ffff0333333300000ff2222222ff0f0f01111111f0f0ff0333333300000ff2222222ff0fff0111111100f0ff07777777f00ffff66666660f0fff0111111100ffff07777777000ffff6666666ff0fff0 else 0xeeeeeeeffffff011111110fffff0ccccccc0fffff022222220f0f0f0111111100f0ff0ccccccc0ffff0033333330fffff0000000000000f0fffffff0ffffffcccccccffffff033333330fffff0bbbbbbbffffff04444444fffff00000000000000f08888888fff0ff06666666ff0fff0111111100ffff08888888ffffff06666666ff0fff0111111100ffff08888888fff00007777777ffffff00000000000fff08888888ffffff06666666ff0fff0111111100f0ff08888888ffff0007777777ffffff000000000000ff07777777000ffff4444444ff0fff0333333300ffff0)) else (if b < 6 then (if b < 5 then 0xf033333330fffff03333333000000f0000000f000000cccccccffffff03333333ffffff033333330fffff0cccccccffffff03333333ffffff0000000000000f000000000000000cccccccffffff03333333ffffff09999999fff0ff06666666ff0fff0000000000ff000cccccccffffff02222222ff0f0f0111111100f0ff0cccccccfffff003333333ffffff0000000000000f08888888ffff0006666666ff00ff0111111100ffff0ccccccc0ffff0022222220fffff0111111100f0ff08888888fff00007777777fff0ff000000000000ff0fffffff0ffffff else 0xfffffff00fffffeeeeeeeffffff0111111100ffff03333333000000f2222222ff0f0f0111111100f0ff077777770000fff6666666ffffff0111111100f0ff0eeeeeeeffffff0111111100f0ff00000000ff0fff09999999ffffff06666666ff0fff0000000000f0ff0eeeeeeeffffff0111111100ffff00000000ff0fff09999999ffffff06666666ff0fff0000000000ffff0eeeeeeeffffff0dddddddffffff03333333ffffff09999999ffffff06666666ffffff0111111100ffff0cccccccffffff03333333ffffff0111111100f0ff03333333ffffff0333333300000ff) else 0x6666666ff0fff0111111100f0ff0333333300000ff2222222ffffff0111111100f0ff0eeeeeeeffffff0111111100f0ff00000000ff0f0f0dddddddffffff02222222ff0f0f0000000000f0ff0bbbbbbbffffff04444444ffffff033333330fffff0dddddddffffff02222222ffffff0111111100f0ff07777777ffffff077777770000fff00000000000ff0111111100ffff01111111000000f0000000ff00000eeeeeeeffffff01111111ffffff0111111100ffff08888888ffffff07777777ffffff000000000000ff000000000000000eeeeeeeffffff01111111ffffff0)) else (if b < 11 then (if b < 9 then (if b < 8 then 0x111111100000f07777777000000f6666666ff0fff0111111100ffff0333333300000ff2222222ffffff01111111f0f0ff08888888ffffff07777777ffffff0111111100ffff0111111100f0ff01111111000000f0000000ff0f000eeeeeeeffffff01111111ffffff0111111100f0ff08888888ffffff07777777ffffff00000000000fff0fffffff00f0fffeeeeeeeffffff0111111100f0ff077777770000fff6666666ff0fff01111111ffffff07777777ff0ffff66666660000ff0111111100f0ff0777777700f0fff6666666ff0fff011111110000ff07777777000000f else 0x333333300000ff2222222ff0f0f011111110fffff077777770000fff6666666ff0fff01111111fff0ff0bbbbbbbffffff04444444ffffff0000000000000f0666666600ff00f4444444f0fff0022222220fff0f08888888ffff0006666666ffffff0111111100ffff09999999ffffff06666666ff0fff0000000000ff0008888888fff00f07777777ffffff00000000000fff0ddddddd00f0f0f333333300000ff1111111f0f0ff0eeeeeeeff0000f77777770000fff6666666ff0fff03333333f0f0fff22222220f0f0f0111111100000f0333333300f0fff2222222ff0f0f0) else (if b < 10 then 0x4444444f00ff00000000000000f08888888fff0ff07777777ffffff00000000000fff0999999900ff00f8888888fff0ff0111111100f0ff09999999fff000f888888800ff000111111100f0ff033333330fffff0333333300000ff0000000f0000f03333333f0000ff33333330fffff0000000000000f0eeeeeeeffffff01111111fff0ff0111111100ffff0eeeeeeeffffff0111111100ffff00000000ff00ff09999999fff0ff06666666ff0fff0000000000ffff09999999fff0ff06666666ffffff0111111100ffff0777777700000ff4444444f00fff033333330fffff0 else 0xff0f0cccccccfffff002222222ff0f0f0111111100ffff08888888ffff0f06666666ff0fff0111111100ffff0ccccccc0ffff0022222220f0fff0111111100f0ff0ccccccc00000ff8888888fff00004444444f00ff00fffffff0ffff0fcccccccfffff0033333330fffff08888888fff00008888888000ff0f000000000000f04444444f00ff00444444400000ff00000000ff00001111111fff0ff01111111000000f0000000000f0007777777ffffff0777777700000ff000000000000f0eeeeeeeffffff01111111ffffff011111110fffff0bbbbbbbf00fff0)) else (if b < 13 then (if b < 12 then 0x999999900ff00f8888888fff00f0111111100f0ff09999999fff0ff06666666ff0fff0000000000ff0f0333333300000ff2222222ff0f0f0111111100ffff077777770000fff6666666ff0fff011111110ff0ff077777770000fff5555555f0ffff022222220f0fff0777777700000ff6666666ff0fff0111111100ffff0333333300000ff2222222ff0fff01111111f0f0ff077777770000fff6666666ff0fff011111110fffff0cccccccfffff003333333ffffff000000000000ff08888888ffffff05555555f0ffff033333330fffff09999999ffffff06666666ff0fff0 else 0x333333300000ff111111100f0ff0ccccccc0f0ff0022222220f0f0f011111110000ff08888888ffff0f07777777ffffff000000000000ff0cccccccfffff002222222ff0fff0111111100ffff0cccccccffffff02222222ff0fff0111111100f0ff08888888fffff006666666ff0fff011111110fffff0cccccccfffff002222222ffff0f0111111100ffff0aaaaaaaffffff05555555f0ffff000000000ffff00fffffff00ff00fcccccccfffff0033333330fffff033333330fffff0333333300000ff0000000f0ff0f0aaaaaaaffff0f05555555f0ffff000000000ffff00) else 0xdddddddffffff02222222ff0fff0000000000f0ff0eeeeeeeffffff05555555ffffff03333333ffffff0aaaaaaaffff0f04444444ff0fff011111110fffff0dddddddffffff02222222ffff0f000000000000ff0aaaaaaaffff0f04444444f0ffff011111110fffff08888888ffffff06666666ff0fff011111110fffff0ddddddd0000f0f)))
    | 4 => (if b < 44 then (if b < 22 then (if b < 11 then (if b < 6 then (if b < 3 then (if b < 2 then (if b < 1 then 0xffffffffffff0fbbbbbbb0ff00ff7777777000ffff33333330fffff0bbbbbbb0ff00ff77777770000fff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff77777770000fff111111100f0ff0fffffff0ffffffdddddddf0f0f0f333333300000ff111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff777777700fffff11111110000ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff0 else 0xbbbbbbb0ff00ff8888888ff0000022222220f0f0f011111110000ff0bbbbbbb0ff00ff777777700fffff22222220f0f0f011111110000ff0dddddddf0fff0fbbbbbbb0fff0ff7777777000ffff111111100f0ff07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f77777770000fff4444444f00ff0022222220f0f0f07777777000ffff4444444f00ff0033333330fffff0000000000000f0cccccccf00000fbbbbbbb0ff00ff7777777000ffff000000000000f0bbbbbbb0ff00ff7777777000ffff33333330fffff0000000000000f0) else 0xdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100ffff0ffffffffff0fff7777777000ffff6666666ff0fff0111111100f0ff0bbbbbbb0ff00ff7777777000ffff2222222ff0f0f0111111100f0ff0cccccccf00000f8888888fff00004444444f00ff00000000000000f0fffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220f0fff0111111100f0ff0fffffff0ffffff333333300000ff22222220f0f0f0111111100f0ff0777777700fffff4444444f00ff0022222220f0f0f011111110000ff0) else (if b < 5 then (if b < 4 then 0xeeeeeeeff0f00fbbbbbbb0ff00ff77777770000fff22222220f0f0f0bbbbbbb0ff00ff7777777000ffff22222220fff0f011111110000ff0bbbbbbb0ff0fff7777777000ffff22222220f0fff0111111100f0ff0bbbbbbb0ff00ff7777777000ffff6666666ff0fff0111111100ffff0bbbbbbb0ff00ff7777777000ffff33333330fffff000000000000ff0eeeeeeeff0f00f7777777000ffff6666666ff0fff0111111100ffff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0cccccccf00000f7777777000ffff4444444f00ff00000000000000f0 else 0x7777777000ffff6666666ff0fff06666666ff00ff0111111100f0ff0000000000000007777777000ffff6666666ff00ff0111111100f0ff07777777000ffff6666666ff0fff06666666ff0fff0111111100ffff08888888ff000004444444f00ff0022222220f0f0f011111110000ff0bbbbbbbfff00ff7777777f00ffff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff000022222220fff0f011111110000ff07777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0) else 0x7777777000ffff6666666ff0fff0111111100ffff07777777000ff0f4444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330ffff00000000000000f0ffffffffff0fff7777777000ffff6666666ff0fff0111111100ffff0ffffffffff0fff77777770000fff6666666ff0fff0111111100f0ff07777777000ffff77777770000fff6666666ff0fff0111111100f0ff00000000000000077777770000fff6666666ff0fff0111111100f0ff0ffffffffff0fff7777777000ffff6666666ff00ff0111111100f0ff0)) else (if b < 9 then (if b < 8 then (if b < 7 then 0x777777700fffff7777777000ffff6666666ff0fff0111111100ffff07777777000ffff6666666ff0fff0111111100ffff00000000000fff07777777ffffff07777777000ffff6666666ff0fff0111111100ffff0eeeeeeeff0f00f8888888ffff00077777770000fff6666666ff0fff000000000000000eeeeeeeff0f00f77777770000fff6666666ff0fff08888888fff00004444444f00ff0033333330fffff0000000000000f07777777000ffff6666666ff0fff0111111100ffff0111111100f0ff07777777000ffff4444444f00fff033333330fffff0000000000000f0 else 0x7777777000ffff6666666ff0fff0111111100ffff0111111100ffff08888888fff00007777777000ffff6666666ff0fff0111111100ffff000000000000000cccccccfffff002222222ff0f0f0111111100f0ff07777777000ffff4444444f00fff033333330fffff03333333000fff07777777ff0ffff7777777000ffff6666666ff0fff0111111100ffff0dddddddf0f0f0fcccccccfffff00333333300000ff1111111f0f0ff000000000000000dddddddf0f0f0f333333300000ff1111111f0f0ff07777777000ffff6666666ff0fff0111111100ffff01111111000fff0) else 0x7777777000ffff6666666ff0fff0111111100f0ff00000000000fff0eeeeeeeff0f00f8888888fff000077777770000fff6666666ff0fff07777777000ffff6666666ff0fff0111111100ffff011111110000ff07777777000ffff6666666ff0fff0111111100ffff000000000000ff08888888fff00f04444444f00ff0033333330fffff0000000000000f0bbbbbbb0ff00ff7777777000ff0f33333330fffff0000000000000f0cccccccf00000f7777777000ffff4444444f00fff0000000000000f07777777000ffff7777777000ffff6666666ff0fff0111111100ffff0) else (if b < 10 then 0x999999900ff00f7777777000ffff6666666ff0fff0111111100f0ff0dddddddf0f0f0f3333333f0000ff333333300000ff111111100f0ff0cccccccf0000ff7777777000ffff4444444f00ff00000000000000f000000000000000999999900ff00f7777777000ffff111111100f0ff07777777000ffff6666666ff0fff0111111100ffff0000000000000008888888fff00006666666ff0fff0111111100ffff0111111100f0ff0dddddddf0f0f0f333333300000ff1111111f0f0ff0111111100f0ff07777777000ffff6666666ff0fff0111111100f0ff01111111000fff0 else 0x7777777000ffff6666666ff0fff033333330fffff0111111100ffff07777777000ffff5555555f0ffff022222220f0fff0111111100f0ff077777770000fff6666666ff0fff022222220f0f0f0111111100f0ff07777777000ffff5555555f0ff0f022222220f0f0f0111111100f0ff08888888ffff0007777777000ffff6666666ff0fff0111111100f0ff07777777f00ffff4444444000ff0033333330fffff0000000000000f077777770ffffff4444444f00ff003333333000fff0000000000000f07777777ffffff07777777000ffff0000000000ff00000000000000f0))) else (if b < 17 then (if b < 14 then (if b < 13 then (if b < 12 then 0x7777777000ffff5555555f0ffff022222220f0f0f000000000000ff07777777000ffff6666666ff0fff0111111100ffff0000000000000f09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f4444444f00ff00333333300000ff1111111f0f0ff0eeeeeeeff0f00f77777770000fff6666666ff0fff022222220f0f0f07777777000ffff5555555f0ffff022222220f0fff011111110000ff077777770f0ffff7777777000ffff6666666ff0fff0111111100ffff07777777000ffff5555555f0ffff022222220f0fff000000000000ff0 else 0x8888888fff00005555555f0ffff022222220f0f0f000000000000ff0dddddddf0f0f0f333333300000ff111111100f0ff00000000f000f00ffffffffff00ff7777777000ffff6666666ff0fff0111111100f0ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100f0ff07777777000ffff6666666ff0fff05555555f0ffff03333333000fff0dddddddf0f0f0f9999999fff0ff05555555f0ffff0333333300000ff7777777000ffff6666666ff0fff05555555f0ffff033333330fffff0999999900ff00f7777777000ffff22222220f0f0f0111111100f0ff0) else 0x7777777000ffff4444444fffff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff000033333330fffff000000000000ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00fff022222220f0fff0111111100f0ff0777777700000ff4444444f00ff0022222220f0f0f0111111100f0ff077777770ffffff4444444f00ff002222222000f0f011111110000ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff05555555f0ffff0333333300ffff0) else (if b < 16 then (if b < 15 then 0x999999900ff00f8888888fff0000111111100f0ff077777770f0ffff4444444f00ff00333333300ffff0000000000000f08888888fff00f04444444f00fff022222220f0f0f0111111100f0ff0777777700fffff4444444f00ff0022222220f0f0f01111111000fff07777777000ffff5555555f00fff022222220f0fff0111111100f0ff0777777700fffff4444444f00fff022222220f0f0f011111110000ff077777770000fff4444444f00ff0022222220f0f0f0111111100ffff0bbbbbbb0f000ff8888888fff000022222220f0f0f011111110000ff0 else 0x7777777000ffff55555550f00f0f4444444f00ff00111111100f0ff0ccccccc0ffff004444444f00ff0022222220f0f0f0111111100f0ff0666666600ff00f4444444f00ff0022222220f0f0f0111111100f0ff0ccccccc0ffff007777777f00ffff22222220f0f0f0111111100f0ff09999999ff00ff04444444f00ff0022222220f0f0f011111110000ff000000000000000ccccccc0ffff0022222220f0f0f0111111100f0ff0666666600ff00f4444444f00ff0022222220f0f0f011111110000ff0bbbbbbb0fff0ff999999900ff00f8888888fff0000111111100f0ff0) else 0x7777777000ffff4444444f0fff0022222220fff0f0111111100f0ff0cccccccfffff007777777000ffff2222222ff0f0f0111111100f0ff07777777000ffff4444444f0ffff022222220f0f0f0111111100f0ff08888888fff00004444444f0fff0022222220f0f0f011111110000ff07777777000ffff4444444f0fff0022222220f0f0f011111110000ff0bbbbbbbfff00ff7777777000ffff2222222ff0f0f0111111100f0ff0777777700fffff4444444f0fff0022222220f0f0f0111111100f0ff0ccccccc0ffff007777777000ffff22222220f0f0f0111111100f0ff0)) else (if b < 20 then (if b < 19 then (if b < 18 then 0x7777777000ffff333333300000ff2222222ff0f0f0111111100f0ff000000000000000333333300000ff2222222ff0f0f0111111100f0ff0fffffff0ffffffccccccc0ffff0022222220f0f0f0111111100f0ff0cccccccfffff00ccccccc0ffff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220fffff0111111100f0ff0333333300000ff22222220f0f0f0111111100f0ff00000000f000f00bbbbbbb0ff00ff7777777000ffff2222222ff0fff0111111100f0ff0aaaaaaaffff0f06666666ff0fff0333333300000ff111111100f0ff0 else 0x8888888fff000077777770000fff6666666ff0fff0111111100f0ff08888888fff00007777777000ffff6666666ff00ff0111111100f0ff04444444f00ff00333333300000ff2222222ff0f0f0111111100f0ff03333333f0000ff333333300000ff22222220f0f0f0111111100f0ff0cccccccf0000ff8888888fff00004444444f00ff00000000000000f0333333300000ff22222220f0f0f01111111f0f0ff0111111100f0ff0cccccccf00000f8888888fff00f04444444f00ff00000000000000f0dddddddf0f0f0f7777777000ffff4444444ff0ff0011111110ff0ff0) else 0x8888888fff00004444444f00fff033333330fffff03333333000fff0eeeeeeefffff0fcccccccfffff002222222ff0f0f0111111100f0ff0eeeeeeeff0f00f333333300000ff2222222ff0f0f0111111100f0ff0dddddddf0f0f0fcccccccfffff001111111f0f0ff0000000000000f09999999ffffff07777777000ffff6666666ff0fff0111111100ffff08888888fff00006666666ff0fff0111111100ffff01111111000fff0eeeeeeeff0f0ffcccccccfffff002222222ff0f0f0111111100f0ff0eeeeeeeff0f00f77777770000fff6666666ff0fff0111111100f0ff0) else (if b < 21 then 0x8888888fff00006666666ff0fff0111111100ffff011111110000ff08888888ffff0007777777000ffff6666666ff0fff0111111100ffff0cccccccfffff002222222ff0f0f0111111100f0ff000000000000000ffffffffffffffcccccccfffff002222222ff0f0f0111111100f0ff0ffffffffffffff7777777000ffff6666666ff0fff0111111100ffff0cccccccfffff002222222ff0f0f0111111100f0ff0111111100f0ff0eeeeeeeff0f00f8888888ffff0006666666ff0fff000000000000ff0eeeeeeeffffff07777777000ffff6666666ff0fff0111111100ffff0 else 0x8888888fff00f04444444f00ff0033333330fffff03333333000fff0dddddddfffff0fcccccccfffff002222222ff0f0f0111111100f0ff0dddddddf0f0f0f333333300000ff2222222ff0f0f0111111100f0ff08888888ffff0006666666ff0fff0111111100f0ff011111110000ff08888888ffff000777777700fffff6666666ff0fff0111111100f0ff09999999ffffff07777777000ffff6666666ff0fff0111111100f0ff08888888fff00006666666ff0fff0111111100f0ff01111111000fff09999999fff0ff07777777000ffff6666666ff0fff0111111100ffff0)))) else (if b < 33 then (if b < 28 then (if b < 25 then (if b < 24 then (if b < 23 then 0xaaaaaaaffff0f07777777000ffff6666666ff0fff0111111100ffff08888888fff00005555555f0ffff022222220f0fff011111110000ff0eeeeeeeff0ff0fcccccccfffff002222222ff0f0f0111111100f0ff07777777000ffff4444444f00ff003333333ffffff0000000000000f07777777000ffff6666666ff0fff0111111100f0ff0000000000ff0007777777000ffff4444444fffff0033333330fffff0000000000000f0999999900ff00f8888888fff00007777777000ffff111111100f0ff0bbbbbbb0ff00ff8888888fff000033333330fffff00000000000fff0 else 0xcccccccfffff00aaaaaaaffff0f06666666ff0f0f0111111100f0ff08888888ffff0f07777777000ffff6666666ff0fff0111111100f0ff0eeeeeeeffffff07777777000ffff5555555f0ffff033333330fffff08888888fff00006666666ff0fff05555555f0ffff03333333000fff07777777000ffff4444444f0fff0033333330fffff0000000000000f08888888fff0f005555555f0ffff022222220f0f0f011111110000ff08888888ffff00077777770f0ffff6666666ff0fff0111111100f0ff0dddddddf0f0f0f9999999fff0ff04444444f0fff00000000000000f0) else 0xfffffff0ff0fff7777777000ffff6666666ff0fff0111111100f0ff07777777000ffff4444444fffff0022222220f0f0f011111110000ff08888888fff00004444444fffff0022222220f0f0f011111110000ff08888888fff00005555555f0ffff022222220f0f00000000000000ff0777777700fffff4444444fffff0022222220f0f0f0111111100f0ff0bbbbbbb0ff0fff8888888fff000033333330fffff000000000000ff07777777000ffff5555555f0ffff022222220f0f0f0000000000f0ff07777777000ffff6666666ff0fff0111111100f0ff000000000ffff00) else (if b < 27 then (if b < 26 then 0x7777777000ffff4444444ff0fff033333330fffff0111111100f0ff0fffffff00fffffcccccccfffff0022222220f0f0f0111111100f0ff0cccccccfffff007777777000ffff6666666ff0fff011111110fffff07777777000ffff5555555f0ffff022222220fffff0111111100f0ff0dddddddf0f0f0f333333300000ff111111100f0ff00000000f00f0007777777000ffff6666666ff0fff011111110fffff0111111100f0ff0bbbbbbb0ff00ff8888888fff0ff033333330fffff000000000000ff0000000000000007777777000ffff6666666ff0fff011111110fffff0 else 0x9999999fff0f004444444f0fff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff777777700000ff22222220f0f0f0111111100f0ff07777777000ffff4444444fffff0022222220fff0f0111111100f0ff07777777000ffff4444444ff0ff002222222ff0f0f0111111100f0ff077777770ffffff4444444fffff0022222220f0f0f0111111100f0ff0cccccccfffff007777777000ffff2222222ffff0f0111111100f0ff08888888fff00007777777000ffff6666666ff0fff011111110fffff0dddddddfffff0faaaaaaaffff0f06666666ff0fff0111111100f0ff0) else 0x77777770ffffff4444444f00ff00222222200ff0f0111111100f0ff0777777700fffff4444444f0fff0022222220fff0f0111111100f0ff0bbbbbbb0fff0ff77777770000fff22222220f0f0f0111111100f0ff0aaaaaaaffff0f077777770f0ffff4444444ff0ff00111111100f0ff08888888fff00006666666ff0fff0111111100ff0f0111111100f0ff08888888fff0f005555555f00fff022222220f0f0f0111111100f0ff07777777000ffff4444444ff0ff0022222220f0fff0111111100f0ff07777777000ffff4444444f0fff0022222220f0fff0111111100f0ff0)) else (if b < 31 then (if b < 30 then (if b < 29 then 0x8888888fff00004444444f0fff0022222220fff0f011111110000ff09999999fff0ff04444444f0fff0022222220f0f0f011111110000ff08888888fff00005555555f0fff0022222220f0f0f000000000000ff0777777700fffff4444444ff0ff0022222220f0f0f011111110000ff077777770f0ffff4444444f00ff00222222200ff0f0111111100f0ff0cccccccfffff00777777700fffff2222222ff0f0f0111111100f0ff0cccccccfffff0077777770f0ffff2222222ff0f0f0111111100f0ff0777777700fffff4444444f0ffff022222220f0f0f0111111100f0ff0 else 0xdddddddffffff07777777000ffff2222222ff0fff0111111100f0ff07777777000ffff4444444f0ffff022222220f0f0f011111110000ff07777777000ffff4444444f0fff0022222220fff0f011111110000ff0bbbbbbb0f000ff7777777000ffff22222220f0f0f011111110000ff0bbbbbbb0ff00ff8888888fff000033333330fff0f000000000000ff0cccccccfffff002222222ff0f0f0111111100f0ff011111110000ff0cccccccfffff0022222220f0f0f01111111f0f0ff011111110000ff08888888fff00004444444f0ffff022222220f0f0f011111110000ff0) else 0x7777777000ffff4444444ff0ff0022222220fff0f0111111100f0ff0bbbbbbb0ff00ff77777770000fff22222220f0f0f0111111100ffff0cccccccfffff007777777000ffff2222222ff0fff0111111100f0ff0aaaaaaaffff0f07777777000ffff4444444ff0ff0011111110ff0ff0cccccccfffff007777777ff0ffff2222222ff0f0f0111111100f0ff0bbbbbbb0ff00ff77777770000fff6666666ff0fff0111111100f0ff0dddddddf0f0f0f777777700000ff4444444f00ff00111111100f0ff07777777000ffff4444444f0ffff022222220fff0f0111111100f0ff0) else (if b < 32 then 0x8888888ffff0006666666ff0fff06666666ff0fff0111111100ffff0cccccccfffff00333333300000ff2222222ff0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100ffff00000000000fff0eeeeeeeffffff0cccccccfffff002222222ff0f0f0111111100f0ff077777770000fff6666666ff0fff06666666ff0fff0111111100f0ff08888888ffff0006666666ff0fff0111111100f0ff000000000000ff0dddddddffffff0cccccccfffff002222222ff0f0f0111111100f0ff0cccccccfffff00cccccccfffff002222222ff0f0f0111111100f0ff0 else 0x8888888fffff006666666ff0fff033333330fffff0111111100f0ff0cccccccfffff00cccccccfffff002222222ff0fff0111111100f0ff0cccccccfffff006666666ff0fff02222222ff0f0f0111111100f0ff08888888fffff004444444f00ff0033333330fffff0000000000000f08888888fff00007777777ffffff00000000000ff00000000000000f0999999900ff00f8888888fff00006666666ff0fff0111111100f0ff08888888fff00006666666ff0fff0111111100f0ff00000000000fff08888888fff00006666666ff0fff0111111100ffff000000000000ff0))) else (if b < 39 then (if b < 36 then (if b < 35 then (if b < 34 then 0xddddddd0fffff0cccccccfffff0022222220f0f0f0111111100f0ff0dddddddffffff0ccccccc0ffff0022222220f0f0f0111111100f0ff0ffffffffff0fff8888888fff00007777777ffffff000000000000ff0ccccccc0ffff0022222220f0f0f0111111100f0ff0000000000000f0fffffff0ffffffcccccccffffff022222220f0f0f0111111100f0ff0ccccccc0ffff0033333330fffff022222220f0f0f0111111100f0ff0fffffff0ffffffcccccccfffff0033333330fffff0000000000000f0bbbbbbbffffff04444444fffff0022222220f0f0f0111111100f0ff0 else 0xccccccc0ffff00ccccccc0ffff0022222220f0f0f0111111100f0ff0999999900ff00f8888888fff00006666666ff00ff0111111100f0ff0ddddddd0fffff0ccccccc0ffff0022222220f0f0f0111111100f0ff0ffffffffffffffccccccc0ffff0022222220f0f0f0111111100f0ff0ccccccc0ffff00333333300000ff22222220f0f0f0111111100f0ff0ccccccc0ffff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00006666666ff00ff0111111100f0ff000000000000ff0fffffff0ffffffcccccccfffff0022222220fffff0111111100f0ff0) else 0x8888888fff00f04444444f00ff0033333330ffff00000000000000f0ffffffffff0fff8888888ffff0006666666ff0fff0111111100ffff0fffffff0ffffffccccccc0ffff002222222ff0f0f0111111100f0ff0cccccccfffff00ccccccc0ffff002222222ff0f0f0111111100f0ff0fffffff0ffffff333333300000ff2222222ff0f0f0111111100f0ff0fffffff0ffffffcccccccfffff002222222ff0f0f0111111100f0ff08888888fff00004444444f00ff0033333330ffff00000000000000f0ffffffffff0fff999999900ff00f8888888fff0000111111100f0ff0) else (if b < 38 then (if b < 37 then 0x8888888ffff0006666666ff0fff0111111100ffff0111111100f0ff08888888fff00f04444444f00fff033333330fffff0000000000000f0000000000000008888888ffff0006666666ff0fff0111111100ffff08888888ffff00077777770000fff6666666ff0fff0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff0000000000000f0cccccccfffff003333333ffffff02222222ff0f0f0111111100f0ff0ccccccc0ffff0022222220f0f0f0111111100f0ff0000000000000008888888fff00006666666ff00ff0111111100ffff0111111100f0ff0 else 0xcccccccfffff003333333ffffff0111111100f0ff0000000000000f000000000000000cccccccfffff003333333ffffff0000000000000f08888888fff00004444444f00ff003333333ffffff0000000000000f08888888fff00006666666ff0fff0111111100f0ff0000000000ff000cccccccfffff0033333330fffff00000000f000000000000000000f0cccccccfffff003333333ffffff022222220f0f0f0111111100f0ff0cccccccfffff0033333330fffff02222222ff0f0f0111111100f0ff0cccccccfffff002222222ff0f0f02222222ff0f0f0111111100f0ff0) else 0x3333333ffffff0333333300000ff2222222ff0f0f0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff00000000fffff00fffffffffffff0cccccccfffff002222222ff0f0f0111111100f0ff08888888fff00f04444444f00ff0033333330fffff03333333000000feeeeeeeffffff09999999ffffff06666666ff0fff0111111100f0ff09999999ffffff077777770000fff6666666ff0fff0111111100f0ff0eeeeeeeffffff09999999ffffff06666666ff0fff0111111100ffff0cccccccfffff003333333ffffff01111111f0f0ff0000000000000f0)) else (if b < 42 then (if b < 41 then (if b < 40 then 0x8888888ffff0007777777ffffff0111111100f0ff000000000000ff0000000000000008888888ffff0007777777ffffff000000000000ff0333333300000ff2222222ff0f0f0111111100f0ff0000000000000f0ddddddd00f0f0fcccccccfffff00111111100f0ff0000000000000f0cccccccffffff0cccccccfffff002222222ff0f0f0111111100f0ff0cccccccffffff02222222ff0f0f0111111100f0ff0000000000000f000000000000000cccccccffffff02222222ff0f0f0111111100f0ff0ffffffffffff0fcccccccfffff002222222ff0f0f0111111100f0ff0 else 0x8888888ffffff06666666ff0fff0111111100f0ff0fffffffff0f0ffcccccccfffff002222222ff0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100ffff01111111000000fdddddddffffff0333333300000ff2222222ff0f0f0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff00000000ff0f0f0eeeeeeeffffff0dddddddffffff02222222ff0f0f0111111100f0ff07777777ffffff077777770000fff6666666ff0fff0111111100f0ff08888888ffff0007777777ffffff06666666ff0fff000000000000ff0) else 0xddddddd00f0f0fcccccccfffff00333333300000ff111111100f0ff000000000000000ddddddd00f0f0f333333300000ff111111100f0ff077777770000fff6666666ff0fff0111111100f0ff011111110000ff0777777700f0fff77777770000fff6666666ff0fff0111111100f0ff077777770000fff6666666ff0fff0111111100f0ff000000000000ff0333333300000ff2222222ff0f0f0111111100f0ff0000000000f0f00cccccccfffff002222222ffffff02222222ff0f0f0111111100f0ff08888888ffffff06666666ff0fff0111111100f0ff000000000000ff0) else (if b < 43 then 0xffffffffffffff77777770000fff6666666ff0fff0111111100f0ff077777770000fff6666666ff0fff0111111100f0ff00000000ff0f000eeeeeeeffffff077777770000fff6666666ff0fff0111111100f0ff08888888ffff0006666666ff0fff066666660000ff0111111100f0ff0ddddddd00f0f0f333333300000ff2222222ff0f0f0111111100f0ff08888888ffff000777777700f0fff6666666ff0fff0111111100f0ff077777770000fff6666666ff0fff066666660000ff0111111100f0ff07777777ff0ffff77777770000fff6666666ff0fff0111111100f0ff0 else 0xcccccccfffff002222222ff0f0f0111111100f0ff01111111000000feeeeeeeffffff0333333300000ff2222222ff0f0f0111111100f0ff08888888fff00007777777ffffff033333330fffff00000000000fff08888888fff00007777777ffffff0111111100ffff00000000000fff0000000000000008888888fff00007777777ffffff00000000000fff0cccccccfffff002222222ff0f0f0111111100f0ff0000000000f0ff077777770000fff77777770000fff6666666ff0fff0111111100f0ff077777770000fff6666666ff0fff0111111100f0ff000000000000000))))) else (if b < 66 then (if b < 55 then (if b < 50 then (if b < 47 then (if b < 46 then (if b < 45 then 0x3333333ff0f0ff333333300000ff2222222ff0f0f0111111100f0ff0333333300000ff2222222ff0f0f0111111100f0ff0111111100000f0333333300f0fff333333300000ff2222222ff0f0f0111111100f0ff0333333300000ff2222222ff0f0f0111111100f0ff00000000ff0f000cccccccfffff002222222ff0f0f01111111ffffff0111111100f0ff08888888ffffff06666666ff0fff0111111100ffff00000000000fff0000000000000008888888ffffff06666666ff0fff0111111100ffff0fffffff00f0fffcccccccfffff002222222ff0f0f0111111100f0ff0 else 0x333333300000ff333333300000ff2222222ff0f0f0111111100f0ff0333333300000ff2222222ff0f0f0111111100f0ff000000000000000ffffffffffffff333333300000ff2222222ff0f0f0111111100f0ff0cccccccfffff0022222220f0f0f01111111f0f0ff0111111100000f0cccccccfffff003333333ff0f0ff2222222ff0f0f0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff0111111100000f0cccccccfffff00333333300f0fff2222222ff0f0f0111111100f0ff0333333300000ff22222220f0f0f01111111f0f0ff0111111100000f0) else 0xcccccccfffff00333333300000ff2222222ff0f0f01111111f0f0ff000000000000000333333300000ff2222222ff0f0f01111111f0f0ff08888888ffff0006666666ff0fff0111111100ffff0000000000ff0009999999ffffff08888888ffff0006666666ff0fff0111111100ffff08888888ffff0006666666ff0fff0111111100ffff00000000000fff08888888ffff0007777777ffffff06666666ff0fff0111111100ffff08888888ffff00077777770000fff6666666ff0fff0111111100ffff00000000000000077777770000fff6666666ff0fff0111111100ffff0) else (if b < 49 then (if b < 48 then 0x8888888ffff0006666666ff0fff0111111100f0ff0000000000ff0008888888ffff0006666666ff0fff0111111100f0ff00000000000fff08888888fff000077777770000fff6666666ff0fff0111111100ffff0cccccccfffff002222222ff0f0f01111111f0f0ff0000000000000f08888888ffff0006666666ff0fff0111111100ffff000000000000ff07777777000ff0f4444444f00fff033333330fffff0000000000000f0cccccccf00000f8888888fff00f04444444f00fff0000000000000f08888888ffff0006666666ff0fff0111111100ffff0111111100ffff0 else 0x999999900ff00f8888888ffff0006666666ff0fff0111111100f0ff0cccccccf00000f7777777000ff0f4444444f00ff00000000000000f03333333f0000ff333333300000ff2222222ff0f0f0111111100f0ff0cccccccf0000ff8888888fff00f04444444f00ff00000000000000f0333333300000ff2222222ff0f0f02222222ff0f0f0111111100f0ff08888888ffff0006666666ff0fff0111111100ffff00000000000000077777770000fff6666666ff0fff0111111100ffff0111111100f0ff0333333300000ff2222222ff0f0f01111111f0f0ff0111111100f0ff0) else 0xfffffff00fffff8888888ffff0006666666ff0fff0111111100f0ff08888888fff00007777777ffffff0111111100f0ff00000000000fff08888888fff00f04444444f00ff003333333ffffff0000000000000f0cccccccffffff033333330fffff00000000f000000000000000000f08888888ffffff04444444f00fff033333330fffff0000000000000f08888888fff00007777777ffffff00000000000fff0000000000000f08888888ffffff04444444f00ff0033333330fffff0000000000000f08888888fff00f07777777ffffff00000000000ff00000000000000f0)) else (if b < 53 then (if b < 52 then (if b < 51 then 0xeeeeeeeffffff09999999fff0ff06666666ff0fff0111111100ffff0cccccccfffff0033333330fffff01111111f0f0ff0000000000000f08888888fff0ff06666666ff0fff0111111100ffff0111111100f0ff0333333300000ff22222220f0f0f01111111f0f0ff0000000000f0f00eeeeeeeff0000f8888888fff00006666666ff0fff000000000000ff0cccccccfffff002222222ff0f0f011111110fffff0111111100f0ff08888888fff0ff06666666ff0fff0111111100ffff000000000000ff0000000000000008888888fff0ff06666666ff0fff0111111100ffff0 else 0x8888888fff00006666666ff0fff066666660000ff0111111100f0ff0ddddddd00f0f0f333333300000ff22222220f0f0f0111111100f0ff08888888fff0000777777700f0fff6666666ff0fff0111111100f0ff08888888fff00006666666ffffff0111111100ffff0111111100f0ff033333330fffff0333333300000ff2222222ff0f0f0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff000000000ffff008888888fff00f04444444f00ff0033333330fffff0333333300000ff9999999fff0ff077777770000fff6666666ff0fff0111111100f0ff0) else 0x3333333ffffff0333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff0022222220f0f0f0111111100f0ff00000000fffff008888888fff00004444444f00ff0033333330fffff03333333000000f8888888ffffff06666666ff0fff0111111100ffff0111111100f0ff0333333300000ff22222220f0f0f0111111100f0ff00000000f0f0f00cccccccfffff0022222220f0f0f01111111ffffff0111111100f0ff08888888ffffff06666666ff0fff0111111100f0ff00000000000fff0fffffff00f0fffcccccccfffff0022222220f0f0f0111111100f0ff0) else (if b < 54 then 0xcccccccfffff002222222ff0f0f022222220fffff0111111100f0ff08888888ffff0008888888fff00007777777ffffff000000000000ff08888888fff00006666666ff0fff0111111100f0ff0000000000ffff08888888fff00006666666ff0fff0111111100ffff0000000000f0ff0999999900fffff8888888fff00006666666ff0fff0111111100f0ff0cccccccfffff0033333330f0f0ff2222222ff0f0f0111111100f0ff03333333f0f0fff333333300000ff22222220f0f0f0111111100f0ff033333330f0f0ff333333300000ff2222222ff0f0f0111111100f0ff0 else 0x3333333f0000ff22222220f0f0f0111111100f0ff0111111100000f0999999900fffff999999900ff00f8888888fff0000111111100f0ff03333333f0000ff22222220f0f0f0111111100f0ff0000000000000f09999999fff0ff0999999900ff00f8888888fff0000111111100f0ff0999999900ff00f8888888fff0000111111100f0ff0000000000000008888888fffff004444444f00fff033333330fffff0000000000000f0999999900ff00f8888888fff0000111111100ffff0111111100f0ff09999999fff0ff08888888ffff0006666666ff0fff0111111100ffff0))) else (if b < 61 then (if b < 58 then (if b < 57 then (if b < 56 then 0x999999900ff00f8888888fff0000111111100f0ff000000000000ff0999999900ff00f8888888fff00007777777ffffff0111111100f0ff0333333300000ff22222220f0f0f01111111f0000f0111111100f0ff0cccccccf00ff0f8888888fff00004444444f000000000000000000f0333333300000ff22222220f0f0f0111111100f0ff00000000f0000f033333330fffff0333333300000ff0000000f000000000000000000f03333333f0000ff333333300f0fff22222220f0f0f0111111100f0ff0999999900ff00f999999900ff00f8888888fff0000111111100f0ff0 else 0xbbbbbbbffffff04444444fffff004444444f00ff00000000000000f08888888fffff007777777ffffff00000000000ff00000000000000f000000000000000bbbbbbbffffff04444444fffff00000000000000f0ffffffff00ffffbbbbbbbffffff04444444f00ff00000000000000f08888888fff00007777777ffffff00000000000fff000000000000ff08888888fff00006666666ff0fff0111111100ff000111111100f0ff0cccccccf00000f8888888fffff004444444f00ff00000000000000f0ffffffffffffff999999900ff00f8888888fff0000111111100f0ff0) else 0x8888888fff00004444444f00ff00444444400000ff33333330fffff0cccccccfffff0033333330fffff00000000f00ff00000000000000f0bbbbbbbffffff04444444f00ff0000000000ffff00000000000000f08888888fff00007777777ffffff00000000f00ff00000000000000f0cccccccfffff00bbbbbbbffffff07777777ffffff0000000000000f08888888fffff007777777ffffff04444444f00ff00000000000000f0bbbbbbbffffff04444444fffff0033333330fffff0000000000000f0111111100f0ff01111111000000f0000000ff000000000000000f000) else (if b < 60 then (if b < 59 then 0xcccccccfffff004444444f00ff003333333ffffff0000000000000f09999999fff0ff06666666ff0fff0111111100f0ff0000000000ff000cccccccfffff0033333330fffff00000000f0000f0000000000000f0000000000000009999999fff0ff06666666ff0fff0000000000ff000cccccccfffff003333333ffffff033333330fffff0000000000000f0777777700000ff4444444f00ff0033333330fffff0000000000000f0cccccccfffff002222222ffffff022222220fffff0111111100f0ff08888888fff0ff06666666ff0fff0111111100f0ff00000000000fff0 else 0xaaaaaaaffff0f04444444ff0ff0033333330fffff0111111100f0ff08888888fff0f005555555f0ff0f022222220f0f0f0111111100f0ff0aaaaaaaf0ff0f04444444f00ff00111111100f0ff0000000000000f0fffffff0ffffffcccccccfffff0022222220f0fff0111111100f0ff0ccccccc0ffff005555555f0ffff022222220f0f0f0111111100f0ff03333333000000f22222220f0f0f0111111100f0ff00000000f0000008888888fff00006666666ffffff0111111100f0ff0000000000ff000fffffff0ffff0fcccccccfffff0022222220f0f0f0111111100f0ff0) else 0x8888888fff00006666666ff0fff0333333300000ff111111100ffff08888888ffff0006666666ff0fff033333330fffff000000000000ff0aaaaaaaffff0f09999999ffffff06666666ff0fff0111111100ffff08888888fff0f004444444f00ff0033333330fffff0000000000000f08888888fff00006666666ff0fff0111111100ffff0000000000000f08888888fff0f005555555f0ffff022222220f0fff0111111100f0ff08888888fff00005555555f0ffff022222220f0fff000000000000ff0aaaaaaaffff0f04444444ff0ff00111111100f0ff0000000000000f0)) else (if b < 64 then (if b < 63 then (if b < 62 then 0xaaaaaaaffff0f04444444ff0fff0111111100f0ff0000000000000f000000000000000cccccccfffff002222222ff0fff0111111100f0ff0fffffffff0ffffcccccccfffff002222222ff0f0f0111111100f0ff05555555f0ffff0333333300000ff2222222ff0f0f0111111100f0ff077777770000fff6666666ff0fff033333330fffff0111111100f0ff08888888ffff0006666666ff0fff022222220f0fff0111111100f0ff0aaaaaaaffff0f04444444ff0ff00111111100f0ff000000000f0ff00cccccccfffff007777777ffffff02222222ff0f0f0111111100f0ff0 else 0x8888888fff00005555555f0ffff033333330fffff00000000000fff0aaaaaaaffff0f077777770000fff6666666ff0fff0111111100f0ff0cccccccfffff002222222ff0f0f0111111100f0ff000000000000ff0cccccccfffff006666666ff0fff03333333ffffff0111111100f0ff09999999fff0ff04444444f0ffff022222220f0f0f0111111100f0ff055555550000f0f4444444ff0ff00111111100f0ff0000000000000f077777770000fff6666666ff0fff0111111100f0ff0000000000000f0cccccccfffff002222222ff0fff02222222ff0f0f0111111100f0ff0) else 0xbbbbbbb0ff000f8888888fff000033333330fffff000000000000ff0aaaaaaaffff0f04444444ff0ff0011111110fffff0111111100f0ff08888888fff0ff05555555f0ffff022222220f0fff000000000000ff0000000000000008888888ffff0f06666666ff0fff0111111100ffff0fffffff00fffffcccccccfffff002222222ff0f0f0111111100f0ff06666666ff0fff0333333300000ff2222222ff0f0f0111111100f0ff0aaaaaaaffff0f04444444ff0ff002222222ff0f0f0111111100f0ff0aaaaaaaffff0f04444444ff0ff00333333300000ff111111100f0ff0) else (if b < 65 then 0x77777770f0ffff77777770000fff6666666ff0fff0111111100f0ff08888888ffffff05555555f0ffff022222220f0f0f0111111100f0ff08888888ffff0007777777ffffff022222220f0f0f000000000000ff09999999ffffff04444444f0fff0022222220f0f0f0111111100f0ff0aaaaaaaffff0f04444444ff0ff0022222220f0fff0111111100f0ff09999999fff0ff04444444f0fff0022222220f0f0f0000000000f0ff08888888fff0ff05555555f0ffff022222220f0fff0111111100f0ff0333333300000ff2222222ff0f0f0111111100f0ff00000000f00f000 else 0x77777770000fff6666666ff0fff022222220f0f0f0111111100ffff08888888fff0f005555555f0ffff022222220f0fff000000000000ff08888888ffff0006666666ff0fff033333330fffff0111111100ffff07777777f00ffff333333300000ff2222222ff0f0f0111111100f0ff08888888ffffff05555555f0ffff022222220f0fff0111111100f0ff09999999fff0ff04444444f0fff0022222220f0f0f0111111100000f0ddddddd00f0f0f4444444f00ff00333333300000ff111111100f0ff07777777000f0ff5555555f0ffff022222220f0f0f0111111100000f0)))) else (if b < 77 then (if b < 72 then (if b < 69 then (if b < 68 then (if b < 67 then 0xcccccccfffff002222222ff0f0f0111111100ffff0fffffff0ffffffaaaaaaaffff0f04444444ff0ff00111111100f0ff0666666600ff00f4444444f0fff0022222220f0f0f0111111100f0ff08888888fff0ff04444444f00fff033333330fffff0000000000000f08888888fff0ff04444444f00ff0033333330fffff0000000000000f08888888fff0f005555555f0ffff022222220f0f0f000000000000ff08888888ffff0006666666ff0fff0111111100ffff0000000000000f04444444f00ff00333333300000ff2222222ff0f0f01111111f0f0ff0 else 0xaaaaaaaffff0f09999999fff0ff06666666ff0fff0111111100ffff08888888ffff0f05555555f0ffff022222220f0fff0111111100f0ff09999999fff0ff04444444f0fff0022222220f0fff0111111100f0ff08888888fff00f06666666ff0fff0111111100ffff0111111100f0ff055555550000f0f4444444f00ff0011111110ff0ff0000000000000f0dddddddf000f0f9999999fff0ff04444444f00ff00000000000000f0cccccccfffff002222222ff0f0f0111111100ffff0111111100f0ff08888888fff00f06666666ff0fff0111111100ffff0000000000000f0) else 0xcccccccfffff002222222ff0f0f022222220f0fff0111111100f0ff08888888fff00006666666ff0fff0111111100f0ff0000000000ff0f0cccccccfffff0022222220f0f0f01111111f0f0ff000000000000ff09999999fff0ff04444444f00ff0022222220f0f0f0000000000f0ff08888888ffff0f06666666ff0fff0111111100ffff0111111100f0ff0cccccccfffff0022222220f0f0f01111111f0ffff0111111100f0ff08888888fff0ff05555555f0ffff022222220f0f0f000000000000ff09999999fff0ff04444444f0fff0022222220f0f0f000000000000ff0) else (if b < 71 then (if b < 70 then 0x77777770000fff4444444f00ff0033333330fffff0000000000000f0cccccccf00000f8888888fff0f004444444f00ff00000000000000f0cccccccfffff002222222ff0fff022222220f0fff0111111100f0ff08888888fff00f05555555f0ffff022222220f0f0f000000000000ff0cccccccfffff0033333330fffff00000000f000f00000000000000f08888888fffff005555555f0ffff033333330fffff0000000000000f0999999900ff00f8888888fff000033333330fffff0111111100f0ff08888888fff0f004444444f00fff033333330fffff0000000000000f0 else 0x8888888fffff005555555f0ffff022222220f0fff0111111100f0ff08888888fff0f004444444f0fff0022222220f0f0f0111111100f0ff08888888fffff005555555f0ffff022222220f0f0f0111111100f0ff08888888fff0f004444444f00fff022222220f0f0f0111111100f0ff08888888ffff0005555555f0ffff022222220f0f0f000000000000ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100ffff0bbbbbbbffffff04444444fffff00111111100f0ff0000000000000f0999999900ff00f8888888fff0000111111100f0ff0000000000000f0) else 0xcccccccfffff0022222220f0f0f0111111100f0ff00000000f0ff0f0cccccccfffff00aaaaaaaffff0f05555555f0ffff033333330fffff0dddddddffffff0aaaaaaaffff0f06666666ff0fff0111111100f0ff08888888fffff006666666ff0fff0111111100f0ff0000000000000f08888888fffff004444444f00fff022222220f0f0f0111111100f0ff08888888ffff0005555555f0ffff022222220f0fff0111111100f0ff08888888ffffff04444444f00fff022222220f0f0f0111111100f0ff08888888ffffff04444444f00ff0022222220f0f0f0111111100f0ff0)) else (if b < 75 then (if b < 74 then (if b < 73 then 0xcccccccfffff00aaaaaaaffff0f02222222ff0fff0111111100f0ff0cccccccfffff00aaaaaaaffff0f07777777ffffff000000000000ff09999999fff0ff05555555f0ffff022222220f0f0f01111111000000fcccccccfffff00bbbbbbbffffff02222222ff0fff0111111100f0ff0cccccccfffff006666666ff0fff02222222ff0fff0111111100f0ff0bbbbbbbffffff06666666ff0fff0333333300000ff111111100f0ff0cccccccfffff002222222ff0fff0111111100f0ff0111111100f0ff08888888fff0ff04444444f00fff022222220f0f0f0111111100f0ff0 else 0xcccccccfffff00aaaaaaaffff0f06666666ff0fff011111110fffff09999999fff0ff05555555f0ffff022222220fffff0111111100f0ff0eeeeeeeffffff09999999fff0ff05555555f0ffff033333330fffff06666666ff0fff055555550000f0f333333300000ff111111100f0ff09999999fff0ff05555555f0ffff022222220f0f0f0111111100000f0bbbbbbbffff0ff6666666ff0fff0333333300000ff111111100f0ff0aaaaaaaffff0f06666666ff0fff0333333300f0fff111111100f0ff0cccccccffffff0aaaaaaaffff0f06666666ff0fff0111111100f0ff0) else 0xcccccccfffff0033333330fffff00000000ff0000000000000000ff0cccccccfffff00aaaaaaaffff0f05555555f0ffff011111110fffff0cccccccfffff0033333330fffff02222222ff0fff0111111100f0ff0aaaaaaaffff0f05555555f0ffff0111111100f0ff000000000ffff00aaaaaaaffff0f05555555f0ffff033333330fffff000000000ffff0000000000000000aaaaaaaffff0f05555555f0ffff000000000ffff00aaaaaaaffff0f05555555f0ffff033333330fffff0333333300000ffaaaaaaaffff0f04444444ff0fff033333330fffff0111111100f0ff0) else (if b < 76 then 0x8888888fff00005555555f0ffff022222220fff0f000000000000ff08888888ffff0004444444f0fff0022222220f0f0f0111111100f0ff0333333300000ff22222220f0f0f0111111100f0ff00000000f0ff0f0cccccccfffff0022222220f0f0f0111111100f0ff00000000f0ff000cccccccffffff022222220f0f0f0111111100f0ff00000000f0ff0f08888888fffff006666666ff0fff0111111100f0ff000000000ffff00fffffff00ff00fcccccccfffff0022222220f0f0f0111111100f0ff08888888fff00004444444ff0ff0033333330fffff000000000000ff0 else 0xaaaaaaaffff0f0aaaaaaa00ff0f04444444f00ff00111111100f0ff0fffffff00fffff333333300000ff22222220f0f0f0111111100f0ff0fffffff0f0ffffcccccccfffff0022222220f0f0f011111110000ff08888888fff00007777777ffffff00000000000f0f000000000000ff0dddddddffffff0cccccccfffff002222222ff0fff0111111100f0ff0cccccccfffff002222222ff0fff0111111100f0ff0000000000000f0aaaaaaaffff0f04444444f00ff0011111110fffff0000000000000f08888888fff00005555555ffffff022222220f0f0f000000000000ff0))) else (if b < 83 then (if b < 80 then (if b < 79 then (if b < 78 then 0x8888888fffff00777777700000ff6666666ff0fff0111111100f0ff000000000000000777777700000ff6666666ff0fff0111111100f0ff08888888ffff0f06666666ff0fff0111111100f0ff000000000000ff0cccccccfffff002222222ff0fff0111111100f0ff000000000000ff0cccccccfffff003333333ffffff02222222ff0fff0111111100f0ff08888888fff00005555555f0ff00022222220f0f0f000000000000ff0fffffff0f0ffffcccccccfffff002222222ffff0f0111111100f0ff0fffffff00fffffaaaaaaa00ff0f04444444f00ff00111111100f0ff0 else 0x8888888fff00006666666ff0fff011111110fffff000000000000ff0777777700000ff6666666ff0fff0111111100f0ff00000000000ff00333333300000ff2222222ff0fff0111111100f0ff00000000f000f00cccccccfffff002222222ff0fff02222222ff0fff0111111100f0ff0cccccccfffff00333333300000ff2222222ff0fff0111111100f0ff000000000000000333333300000ff2222222ff0fff0111111100f0ff0aaaaaaaffff0f04444444ff0fff0111111100f0ff00000000ff0f0f0eeeeeeeffffff0cccccccfffff002222222ff0fff0111111100f0ff0) else 0x999999900ff0ff8888888fff00006666666ff0fff0111111100f0ff03333333f000fff333333300000ff22222220f0f0f0111111100f0ff0aaaaaaa0f00fff8888888fff000022222220f0f0f000000000000ff08888888ffff0f05555555f0ffff022222220f0f0f000000000000ff0cccccccfffff002222222ff0fff0111111100f0ff000000000000000333333300000ff22222220f0f0f01111111f0ffff0111111100f0ff0cccccccfffff0022222220f0f0f0111111100f0ff00000000f0fff008888888fff0000777777700000ff6666666ff0fff0111111100f0ff0) else (if b < 82 then (if b < 81 then 0x8888888fffff006666666ff0fff033333330fffff0111111100ffff0666666600ff0ff4444444f00ff0022222220f0f0f0111111100f0ff04444444f00ff00333333300000ff2222222ff0fff0111111100f0ff0777777700000ff6666666ff0fff04444444f00ff00111111100f0ff09999999fff0ff04444444f0ffff022222220f0f0f0000000000f0ff0aaaaaaa00ff0f08888888fff00004444444f00ff00111111100f0ff08888888fff00004444444fffff0033333330fffff000000000000ff08888888fff00007777777ffffff000000000f0f00000000000000ff0 else 0xfffffff000ffffcccccccfffff0022222220f0f0f0111111100f0ff0cccccccfffff0022222220f0f0f01111111fff0ff000000000000ff0777777700000ff6666666ff0fff033333330fffff0111111100f0ff05555555f0ffff0333333300000ff2222222ffff0f0111111100f0ff08888888fffff006666666ff0fff022222220f0fff0111111100f0ff0aaaaaaaffff0f04444444f00ff00333333300000ff11111110fffff0cccccccfffff009999999ffffff06666666ff0fff011111110fffff08888888fffff006666666ff0fff033333330fffff000000000000ff0) else 0x4444444f00ff00333333300000ff2222222ffff0f0111111100f0ff08888888fff00004444444ff0fff033333330fffff000000000000ff0cccccccfffff00aaaaaaaffffff02222222ff0fff0111111100f0ff0aaaaaaaffff0f04444444f00ff001111111fff0ff0000000000000f0333333300000ff22222220f0f0f01111111f000ff0111111100f0ff08888888ffff0f04444444f0fff0022222220f0f0f0111111100f0ff0dddddddffffff0aaaaaaaffff0f02222222ff0fff0111111100f0ff0333333300000ff22222220f0f0f0111111100f0ff00000000f00ff00)) else (if b < 86 then (if b < 85 then (if b < 84 then 0x8888888fff0ff04444444f0ffff022222220f0f0f0111111100f0ff09999999fff000f5555555f00ff0f22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220fffff0111111100000f09999999fff00f05555555f00fff022222220f0f0f0111111100f0ff08888888fffff004444444f0fff0022222220f0f0f0111111100f0ff08888888fff00006666666ffffff0111111100f0ff0000000000ff0f09999999fff0ff04444444f00fff022222220f0f0f0000000000f0ff0777777700000ff5555555f0ffff022222220f0f0f0111111100f0ff0 else 0xfffffff00fffffcccccccf0fff0022222220f0f0f0111111100f0ff08888888fff000088888880000fff4444444f00ff0022222220f0f0f04444444f00ff0022222220f0f0f01111111fff0ff01111111000000f7777777ffffff0777777700000ff22222220f0f0f0111111100f0ff0dddddddffffff0aaaaaaaffffff02222222ff0fff0111111100f0ff08888888fffff007777777ffffff022222220f0fff0111111100f0ff0eeeeeeeffffff04444444ff0ff002222222ff0f0f0111111100f0ff0eeeeeee00ffff04444444f00ff0022222220f0f0f0111111100f0ff0) else 0x8888888ffff0f05555555f0ffff022222220f0f0f0000000000f0ff0cccccccffffff0aaaaaaaffffff06666666ff0fff0111111100f0ff08888888fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888ffff0f04444444f0ffff022222220f0f0f0111111100f0ff0777777700000ff4444444f00ff0022222220f0fff0111111100f0ff077777770000fff4444444f00ff0022222220f0f0f011111110fffff08888888fff0ff04444444f00fff022222220f0fff0111111100f0ff077777770000fff4444444ff0ff0022222220f0f0f0111111100f0ff0) else (if b < 87 then 0x77777770000fff6666666f00fff022222220f0f0f0111111100f0ff0777777700f0fff4444444f00ff0022222220f0f0f011111110000ff08888888fff0f004444444ff0ff0022222220f0fff0111111100f0ff077777770000fff4444444f0fff0022222220f0f0f0111111100f0ff0aaaaaaaffffff04444444ff0ff0022222220f0fff0111111100f0ff077777770000fff4444444f00fff022222220f0f0f0111111100f0ff077777770000fff4444444f00ff0022222220f0f0f011111110ff0ff08888888fffff004444444fffff0022222220f0f0f0111111100f0ff0 else 0xeeeeeeeff0f00fdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffffeeeeeeeff0000f77777770000fff4444444f00ff0022222220f0f0f08888888fff00f04444444f00fff022222220f0fff0111111100f0ff0))))))
    | 5 => (if b < 80 then (if b < 40 then (if b < 20 then (if b < 10 then (if b < 5 then (if b < 3 then (if b < 2 then (if b < 1 then 0x7777777000ffff111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff011111110000ff0dddddddf0f0f0fbbbbbbb0ff00ff777777700fffff7777777000ffff111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff000000000000000eeeeeeeff0f00fdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff else 0xbbbbbbb0ff00ff7777777000ffff7777777000ffff111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff8888888fff0000111111100f0ff011111110000ff0dddddddf0f0fffbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff0000000000000f0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff33333330fffff0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff333333300000ff111111100f0ff0fffffff0ffffffdddddddf0f0f0fbbbbbbb0ff00ff) else 0x111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000000ffffffffffffffdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff0ffffffffffffffbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0eeeeeeeff0f00fbbbbbbb0ff00ff7777777000ffff22222220f0f0f011111110000ff0dddddddf0f0f0fbbbbbbb0ff00ff77777770f0ffff7777777000ffff111111100f0ff0dddddddf0f0f0f) else (if b < 4 then 0x33333330fffff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff33333330fffff0111111100f0ff0000000000000f000000000000000bbbbbbb0ff00ff7777777000ffff33333330fffff0000000000000f0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00ff00333333300000ff111111100f0ff0ffffffff0fffffbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0 else 0xffffffffffff0fbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff3333333000fff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff77777770ffffff7777777000ffff22222220f0f0f0111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0f8888888fff00004444444f00ff00333333300000ffbbbbbbb0ff00ff7777777000ffff33333330fffff022222220f0f0f011111110000ff0bbbbbbb0ff00ff7777777000ffff)) else (if b < 8 then (if b < 7 then (if b < 6 then 0x22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff777777700fffff7777777000ffff22222220f0f0f011111110000ff0bbbbbbb0ff00ff777777700fffff22222220f0f0f0111111100f0ff011111110000ff000000000000000bbbbbbb0ff00ff777777700fffff22222220f0f0f011111110000ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0bbbbbbb0ff00ff7777777000ffff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0000000000000f0 else 0xbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0eeeeeeeff0f00fbbbbbbb0ff00ff8888888fff000022222220f0f0f011111110000ff0bbbbbbb0ff0fff7777777000ffff333333300000ff22222220f0f0f0111111100f0ff0bbbbbbb0ff0fff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff011111110000ff0bbbbbbb0fff0ffbbbbbbb0ff0fff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff777777700fffff7777777000ffff) else 0x11111110000ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f00f011111110000ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0111111100000f0bbbbbbb0ff00ff7777777000ffff333333300ffff022222220f0f0f0111111100f0ff0dddddddf0fff0fbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff33333330000fff22222220f0f0f0111111100f0ff0fffffff0ffffff) else (if b < 9 then 0x7777777000ffff22222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00ff00111111100f0ff0000000000000f0bbbbbbb0ff00ff7777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0bbbbbbb0ff00ff8888888fff000022222220f0f0f0111111100f0ff0 else 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff07777777000ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f7777777000ffff4444444f00ff0022222220f0f0f011111110000ff0bbbbbbb0ff00ff7777777f00ffff))) else (if b < 15 then (if b < 13 then (if b < 12 then (if b < 11 then 0x6666666ff0fff0111111100f0ff0bbbbbbb0ff00ff7777777000ffff333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff00bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff333333300f0fff22222220f0f0f0111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0f8888888fff00004444444f00ff00000000000000f0fffffff0ffffff7777777000ffff333333300000ff22222220f0f0f0111111100f0ff000000000000000fffffff0ffffff333333300000ff22222220f0f0f0111111100f0ff0 else 0x8888888fff000033333330fffff022222220f0f0f011111110000ff0bbbbbbb0ff00ff7777777000ffff6666666ff0fff033333330fffff0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff0033333330fffff0000000000000f0dddddddf0f0f0f8888888fff00004444444f00ff00333333300000ff111111100f0ff0ffffffffff0fff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0f7777777000ffff4444444f00ff00000000000000f0dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff) else 0x111111100f0ff0bbbbbbb0ff00ff7777777000ffff5555555f0ffff022222220f0f0f011111110000ff0bbbbbbb0ff00ff7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00003333333000fff022222220f0f0f0111111100f0ff0bbbbbbb0ffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f7777777000ffff4444444f00ff0022222220f0f0f000000000000ff0bbbbbbb0ff00ff7777777ffffff07777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff) else (if b < 14 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00ff003333333000fff0111111100f0ff0bbbbbbb0ff00ff7777777f0fffff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff0fff7777777000ffff6666666ff0fff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000ff0bbbbbbb0ff00ff9999999fff0ff022222220f0f0f0111111100f0ff011111110000ff0bbbbbbb0ff00ffaaaaaaaffff0f077777770f0ffff7777777000ffff else 0xbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100ffff0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00fff0111111100f0ff0000000000000f000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0fff0111111100f0ff0eeeeeeeff0ff0f7777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff5555555f0ffff0333333300000ff22222220f0f0f0111111100f0ff09999999fff0ff07777777000ffff)) else (if b < 18 then (if b < 17 then (if b < 16 then 0x22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff777777700fffff4444444f00ff0022222220f0f0f011111110000ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0f00000000000000f0dddddddf0f0f0f7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f0dddddddf0f0f0f7777777000ffff4444444f00ff00111111100f0f00000000000000f0dddddddf0f0fff7777777000ffff4444444f00ff00111111100f0ff0000000000000f0 else 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f00f011111110000ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100000f0bbbbbbb0ff00ff7777777000ffff5555555f00fff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff000033333330000fff22222220f0f0f0111111100f0ff0777777700fffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0bbbbbbbfff00ffbbbbbbb0ff0fff7777777000ffff) else 0x111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff07777777000ffff4444444f00ff0033333330ff0ff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff0000777777700fffff22222220f0f0f011111110000ff07777777000ffff4444444f00ff0033333330000fff22222220f0f0f0111111100f0ff08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f0ff7777777000ffff4444444f00ff0022222220f0f0f011111110000ff000000000000000) else (if b < 19 then 0x4444444f00ff00333333300ffff0111111100f0ff0fffffffff0ffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f777777700fffff4444444f00ff0022222220f0f0f011111110000ff07777777f00ffff7777777000ffff333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffffbbbbbbbfff00ff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbbfff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0 else 0x8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff04444444f00ff004444444000ff00333333300000ff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff4444444000ff00333333300000ff22222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f011111110000ff0fffffffff0ffff7777777000ffff4444444f00ff0022222220f0f0f011111110000ff0dddddddf0f0f0f7777777000ffff)))) else (if b < 30 then (if b < 25 then (if b < 23 then (if b < 22 then (if b < 21 then 0x6666666ff0fff0111111100f0ff07777777000ffff4444444f00ff0033333330fffff033333330fffff0000000000000f07777777000ffff4444444f00ff00333333300f0fff22222220f0f0f0111111100f0ff0fffffff0ffffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0 else 0x7777777000ffff6666666ff0fff0111111100ffff0111111100f0ff0000000000000007777777000ffff4444444f00fff033333330fffff0000000000000f000000000000000000000000000007777777000ffff6666666ff0fff0111111100ffff07777777000ffff4444444f00ff0033333330fffff0000000000000f0000000000000f0000000000000007777777000ffff4444444f00ff0033333330fffff0000000000000f0ffffffffffff0f7777777000ffff4444444f00ff0033333330fffff0000000000000f000000000000000ffffffffff0fff7777777000ffff) else 0xf07777777ffffff07777777000ffff4444444f00ff0033333330fffff0000000000000f0cccccccf00000f7777777000ffff4444444f00ff0033333330fffff0000000000000f000000000000000cccccccf00000f7777777000ffff4444444f00ff00000000000000f07777777000ffff7777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330fffff0000000000000f0000000000000007777777000ffff4444444f00fff04444444f00ff0033333330fffff0000000000000f000000000000000) else (if b < 24 then 0x4444444f00ff0033333330fffff0000000000000f0000000000000008888888fff00004444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff004444444000ff0033333330fffff0000000000000f07777777f00ffff7777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330fffff03333333000fff0000000000000f077777770ffffff7777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330fffff00000000000ff00 else 0x7777777000ffff5555555f0ffff04444444f00ff0033333330fffff0000000000000f07777777000ffff6666666ff0fff022222220f0f0f0111111100ffff0111111100f0ff07777777000ffff4444444f00fff033333330fffff0111111100f0ff0000000000000f0000000000000007777777000ffff5555555f0ffff022222220f0fff0111111100f0ff07777777000ffff4444444f00ff0033333330fffff0111111100f0ff0000000000000f0fffffffffff0ff7777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff)) else (if b < 28 then (if b < 27 then (if b < 26 then 0x22222220f0f0f0111111100f0ff07777777000ffff4444444f00fff033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0cccccccf00000f7777777000ffff4444444f00ff00111111100f0ff0000000000000f07777777000ffff4444444f00ff0033333330fffff011111110000ff0000000000000f0777777700fffff7777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff5555555f0ffff022222220f0f0f000000000000f00000000000000f0 else 0x4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff003333333000fff022222220f0f0f0111111100f0ff077777770ffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff07777777ffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f011111110000ff07777777000ffff6666666ff0fff05555555f0ffff0) else 0x111111100f0ff07777777000ffff6666666ff0fff05555555f0ffff022222220f0f0f011111110000ff07777777000ffff6666666ff0fff05555555f0ffff022222220f0f0f000000000000ff07777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff000000000000ff0000000000000007777777000ffff5555555f0ffff022222220f0f0f000000000000ff07777777000ffff6666666ff0fff05555555f0ffff033333330fffff0111111100f0ff0000000000000007777777000ffff6666666ff0fff05555555f0ffff033333330fffff08888888fff0000) else (if b < 29 then 0x22222220f0f0f0111111100ffff0111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f000000000000ff0aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff04444444f00ff003333333000fff0111111100f0ff07777777000ffff5555555f0ffff04444444f00fff022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0dddddddf0f0f0f9999999fff0ff04444444f00ff00333333300000ff else 0x7777777000ffff4444444f00ff0033333330fffff02222222000f0f011111110000ff07777777000ffff6666666ff0fff04444444f00ff00333333300ffff0111111100f0ff0bbbbbbbfff00ff7777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff00333333300ffff022222220f0f0f0111111100f0ff0777777700fffff4444444f00ff003333333000fff022222220f0f0f0111111100f0ff0777777700fffff4444444f00ff0033333330fffff022222220f0f0f011111110000ff07777777000ffff4444444f00ff00))) else (if b < 35 then (if b < 33 then (if b < 32 then (if b < 31 then 0x333333300000ff111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0111111100000f0999999900f0fff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f011111110000ff077777770ffffff7777777000ffff4444444f00ff0022222220f0f0f011111110000ff07777777ffffff07777777000ffff4444444f00ff0022222220f0f0f011111110000ff0dddddddf0f0f0f8888888fff00004444444f000f00333333300000ff111111100f0ff0 else 0x8888888fff00004444444f00ff0022222220f0f0f01111111000000f7777777000ffff7777777000fff04444444f00ff0022222220f0f0f0111111100f0ff07777777fffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff01111111000000ffffffff00fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbbfff00ff4444444f00ff00) else 0x111111100000f08888888fff000077777770ffffff4444444f00ff0022222220f0f0f0111111100f0ff07777777ff0ffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff000000000000ff0ffffffffff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777ffffff07777777000ffff4444444f00ff0022222220f0f0f000000000000ff0eeeeeeeff0f00f) else (if b < 34 then 0x5555555f00fff022222220f0f0f0111111100f0ff0777777700fffff6666666ff0fff04444444f00ff0022222220f0f0f011111110000ff08888888fff00004444444f00ff003333333000fff022222220f0f0f0111111100f0ff0777777700ffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff09999999fff000f7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff077777770ffffff4444444f00ff003333333000fff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f0 else 0x77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0fffffffff0ffffbbbbbbb0ff00ff8888888fff000022222220f0f0f011111110000ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f000000000000ff0bbbbbbbffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff007777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff077777770fffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff0)) else (if b < 38 then (if b < 37 then (if b < 36 then 0x111111100f0ff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0000000000000f07777777000ff0f4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0ffffffffffff0f7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0ffffffffff0fff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0 else 0x4444444f00ff0022222220f0f0f0111111100ffff01111111000fff07777777f00ffff7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888ffff00077777770000fff4444444f00ff0022222220f0f0f000000000000000eeeeeeeff0f00f77777770000fff4444444f00ff0022222220f0f0f07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff011111110000ff0777777700fffff7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff07777777000ffff4444444f00fff022222220f0f0f0) else 0xf08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0bbbbbbb0ff00ff7777777000ff0f22222220f0f0f0111111100f0ff0000000000000f07777777000ffff7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff07777777000ffff4444444f00fff04444444f00fff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff) else (if b < 39 then 0x22222220f0f0f011111110000ff0000000000000f07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff01111111000fff0eeeeeeeff0f00f8888888fff000077777770000fff4444444f00ff0022222220f0f0f07777777000ffff4444444f00ff0022222220f0f0f0111111100ffff011111110000ff07777777000ffff4444444f00ff0022222220f0fff0111111100f0ff0 else 0xeeeeeeeffff00f777777700fffff4444444f00ff0022222220f0f0f011111110000ff000000000000000bbbbbbbfff00ff7777777f00ffff22222220f0f0f0111111100f0ff0777777700fffff777777700fffff4444444f00ff0022222220f0f0f011111110000ff08888888fff00f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777f00ffff4444444000ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0033333330f0fff0111111100f0ff0000000000000f0777777700fffff4444444f00ff00))))) else (if b < 60 then (if b < 50 then (if b < 45 then (if b < 43 then (if b < 42 then (if b < 41 then 0x22222220f0f0f011111110000ff0000000000000008888888ff000004444444f00ff0022222220f0f0f011111110000ff077777770f0ffff4444444f00ff002222222000f0f0111111100f0ff011111110000ff077777770ffffff777777700fffff4444444f00ff0022222220f0f0f011111110000ff0777777700fffff4444444f00ff0022222220f0f0f011111110000ff011111110000ff000000000000000777777700fffff4444444f00ff0022222220f0f0f011111110000ff0777777700fffff4444444f00ff0033333330f0fff022222220f0f0f011111110000ff0 else 0x7777777000ffff4444444f00ff0022222220f0f0f011111110000ff0bbbbbbbfff00ff7777777f00ffff7777777000ffff22222220f0f0f0111111100f0ff08888888ff000004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff077777770f0ffff4444444f00ff00333333300ffff022222220f0f0f0111111100f0ff0777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0eeeeeeeffff00f777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888ff00000777777700fffff4444444f00ff00) else 0xf0cccccccfffff00bbbbbbbfff00ff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f0ff8888888fff00004444444f00ff0022222220f0f0f011111110000ff077777770f0ffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888ff000007777777000ffff4444444f00ff0022222220f0f0f011111110000ff08888888fff0000777777700fffff4444444f00ff0022222220f0f0f011111110000ff077777770f0ffff777777700fffff4444444f00ff0022222220f0f0f011111110000ff0777777700fffff) else (if b < 44 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0fffffffff0ffff8888888fff00004444444f00ff0022222220f0f0f011111110000ff0eeeeeeeff0f00f9999999fff0ff04444444f00ff0022222220f0f0f011111110000ff099999990ff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff007777777f00ffff7777777000ffff22222220f0f0f0111111100f0ff0aaaaaaaffff0f0777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0fff8888888fff00004444444f00ff00111111100f0ff0 else 0x8888888fff00004444444f00ff00333333300ffff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00004444444f00ff0033333330000fff22222220f0f0f07777777000ffff4444444f00ff00333333300ffff022222220f0f0f011111110000ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0f00000000000000f0bbbbbbbfff00ff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0eeeeeeeff0f0ffdddddddf0f0f0f8888888fff00004444444f00ff00000000000000f0bbbbbbbfff0fff7777777000ffff)) else (if b < 48 then (if b < 47 then (if b < 46 then 0x11111110ff0ff0111111100f0ff0dddddddf0f0f0f8888888fff00f04444444f00ff00111111100f0ff0000000000000f0000000000000007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff0033333330fffff0000000000000f0bbbbbbb0ff00ff8888888fff000022222220f0f0f0111111100f0ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0f00000000000000f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0 else 0x4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0eeeeeeeff0f00fbbbbbbb0ff00ff8888888fff000022222220f0f0f000000000000ff0dddddddffffff0bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00005555555f0ffff022222220f0f0f011111110000ff0bbbbbbb0ff00ffaaaaaaaffff0f07777777000ffff6666666ff0fff0111111100f0ff08888888fff00007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0) else 0x111111100000f09999999fff00f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330000fff22222220f0f0f0111111100f0ff0cccccccfffff00bbbbbbb0ff0fff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff003333333000fff0111111100f0ff09999999fff0ff0) else (if b < 49 then 0x7777777000ffff2222222ff0f0f0111111100f0ff0fffffff0ffffffcccccccfffff004444444f00ff0022222220f0f0f0111111100f0ff0fffffff0ffffffcccccccfffff007777777000ffff22222220f0f0f0111111100f0ff000000000000000fffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff8888888fff0000111111100f0ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f00f011111110000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0 else 0xcccccccf00000f8888888fff00004444444f00ff00111111100f0ff0000000000000f0eeeeeeeff0f00f7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0fcccccccf00000f8888888fff00004444444f00ff00000000000000f000000000000000cccccccf00000f8888888fff00004444444f00ff00000000000000f0bbbbbbb0ff00ff7777777000ffff22222220f0f0f01111111f0f0ff0111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0f8888888fff00f04444444f00ff00000000000000f000000000000000bbbbbbb0ff00ff))) else (if b < 55 then (if b < 53 then (if b < 52 then (if b < 51 then 0x6666666ff0fff0111111100f0ff08888888fff00004444444f00ff0033333330fffff0000000000000f0000000000000f08888888fff00007777777000ffff6666666ff0fff0111111100ffff0111111100f0ff08888888fff00007777777000ffff4444444f00fff033333330fffff0000000000000f0000000000000008888888fff00007777777000ffff6666666ff0fff0111111100ffff0ffffffffff0fff8888888fff00007777777000ffff6666666ff0fff0111111100f0ff08888888fff00004444444f00ff00333333300f0fff22222220f0f0f0111111100f0ff0 else 0x7777777000ffff4444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff03333333000fff0000000000000f08888888fff000077777770ffffff4444444f00ff0033333330fffff0000000000000f0cccccccf00000f8888888fff00007777777000ffff4444444f00ff00000000000000f08888888ffff0008888888fff00007777777000ffff6666666ff0fff0111111100f0ff08888888fff00f07777777000ffff4444444f00ff0033333330fffff0000000000000f0000000000000008888888ffff0007777777000ffff) else 0xf08888888fff00004444444f00ff004444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330fffff00000000f000000000000000000f0cccccccfffff007777777000ffff4444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff004444444000ff0033333330fffff0000000000000f08888888fff00007777777f00ffff4444444f00ff0033333330fffff0000000000000f0bbbbbbb0ff00ff8888888fff000033333330fffff00000000000ff00000000000000f0bbbbbbbffffff0) else (if b < 54 then 0x33333330fffff011111110000ff0000000000000f08888888fff0000777777700fffff4444444f00ff0033333330fffff0000000000000f08888888fff0f007777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff5555555f0ffff022222220f0fff0111111100f0ff08888888fff00004444444f00ff0033333330fffff0000000000000f000000000000000ffffffffffffff8888888fff00004444444f00ff0033333330fffff0000000000000f0ffffffffffffff7777777000ffff4444444f00ff0033333330fffff0 else 0xcccccccfffff007777777000ffff6666666ff0fff033333330fffff0111111100f0ff08888888fff00006666666ff0fff05555555f0ffff022222220f0f0f011111110000ff08888888fff00007777777000ffff5555555f0ffff022222220f0f0f000000000000ff08888888fff00007777777000ffff6666666ff0fff05555555f0ffff033333330fffff0bbbbbbb0ff00ff8888888fff000033333330fffff000000000000f00000000000000f09999999fff0ff07777777000ffff4444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff00)) else (if b < 58 then (if b < 57 then (if b < 56 then 0x22222220f0f0f011111110000ff09999999fff0ff04444444f00ff0033333330fffff022222220f0f0f011111110000ff08888888fff00006666666ff0fff04444444f00ff00333333300ffff0111111100f0ff0eeeeeeeff0f0ff8888888fff00004444444f00ff0022222220f0f0f000000000000ff0cccccccfffff00777777700fffff5555555f0ffff022222220f0f0f0111111100f0ff0eeeeeeeffffff07777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff003333333000fff0111111100f0ff0 else 0x77777770ffffff4444444f00ff0022222220f0f0f011111110000ff0cccccccfffff007777777000ffff5555555f0ffff022222220f0f0f011111110000ff08888888fff00004444444f00ff0033333330fffff02222222000f0f011111110000ff08888888fff00004444444f00ff0022222220f0f000111111100f0ff000000000000ff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f011111110000ff08888888fff00004444444f000f00333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff008888888fff00005555555f0ffff0) else 0x111111100f0ff0cccccccfffff00777777700fffff6666666ff0fff022222220f0f0f0111111100f0ff0cccccccfffff007777777ffffff07777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00006666666ff0fff033333330fffff000000000000ff0bbbbbbb0ff00ff8888888fff000033333330fffff0111111100f0ff000000000000ff000000000000000bbbbbbb0ff00ff8888888fff000033333330fffff000000000000ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f00000000000000ff08888888fff0000) else (if b < 59 then 0x3333333000fff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff000033333330fffff022222220f0f0f000000000000ff0cccccccfffff007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff5555555f0ffff04444444f0fff0022222220f0f0f0111111100f0ff0aaaaaaaffff0f04444444f00ff0033333330fffff03333333000fff0111111100f0ff0cccccccfffff007777777f0fffff7777777000ffff22222220f0f0f0111111100f0ff0dddddddf0f0f0faaaaaaaffff0f04444444f00ff00333333300000ff else 0xfffffff00fffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f0fff0033333330fffff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00005555555f0ffff022222220f0f0f000000000000ff0eeeeeeeffff0ff9999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00005555555f0ffff022222220f0f0f000000000000ff0cccccccfffff00aaaaaaaffff0f07777777000ffff6666666ff0fff0111111100f0ff09999999fff0ff04444444f00ff00)))) else (if b < 70 then (if b < 65 then (if b < 63 then (if b < 62 then (if b < 61 then 0x22222220f0f0f0111111100f0ff08888888fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff00000000fff0000fffffffffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000fff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777fffffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff01111111000000f else 0x8888888fff00004444444f00fff022222220f0f0f000000000000ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0eeeeeeeffffff0777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbbffffff04444444f00ff003333333000fff022222220f0f0f0111111100f0ff08888888fff0000777777700ffff04444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0ffff8888888fff00004444444f00ff0022222220f0f0f000000000000ff0cccccccfffff0077777770ffffff4444444f00ff00) else 0x111111100f0ff0aaaaaaaffff0f09999999fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444fffff0022222220f0f0f0111111100f0ff07777777000ffff4444444fffff0033333330fffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f01111111fff0ff0111111100f0ff0eeeeeeeff0f00f8888888fff0ff04444444f00ff0022222220f0f0f000000000000ff0000000000000007777777000ffff4444444fffff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f) else (if b < 64 then 0x22222220f0f0f0111111100f0ff011111110000ff08888888fff0000777777700fffff4444444f00fff022222220f0f0f0111111100f0ff08888888fff000077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff003333333ffffff022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff04444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000ffff008888888fff000077777770fffff04444444f00ff0022222220f0f0f0 else 0xcccccccffffff07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff01111111000fff0bbbbbbbfff00ff8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff0f004444444f00ff00111111100f0ff0000000000000f09999999fff0ff07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00fff0)) else (if b < 68 then (if b < 67 then (if b < 66 then 0x111111100ffff011111110000ff08888888fff00f07777777000ffff4444444f00fff022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0ffffffffffffff7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff08888888ffff0004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff001111111f0f0ff0000000000000f0 else 0x777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00f0777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff09999999ffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff01111111000fff0cccccccfffff007777777000ffff4444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0) else 0x111111100f0ff07777777000ffff4444444f00ff002222222ff0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0022222220fff0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0033333330f0fff0111111100f0ff0000000000000f08888888ffff0004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888ffff000) else (if b < 69 then 0x777777700fffff22222220f0f0f0111111100f0ff08888888fff0000777777700fffff4444444f0fff0022222220f0f0f0111111100f0ff0bbbbbbb0fff0ff8888888fff000022222220f0f0f0111111100ffff0111111100f0ff0dddddddf0f0fff8888888fff00f04444444f00ff00111111100f0ff0000000000000f000000000000000777777700fffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0fff8888888fff00004444444f00ff0033333330fffff0000000000000f0cccccccfffff009999999fff0ff07777777f00ffff22222220f0f0f0 else 0xdddddddfff0f0f8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100ff0f0111111100f0ff0dddddddf0fff0f8888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00005555555f0ffff022222220f0f0f0111111100ff0f0111111100f0ff0bbbbbbb0fff0ff8888888fff000022222220f0f0f0111111100ff0f0111111100f0ff0bbbbbbb0ff0fff8888888fff000022222220f0f0f0111111100f0ff000000000000ff0cccccccfffff007777777f0fffff))) else (if b < 75 then (if b < 73 then (if b < 72 then (if b < 71 then 0x111111100f0f00000000000000f0ffffffffffffff777777700fffff4444444f00ff0022222220f0f0f011111110000ff0dddddddf0fff0f8888888fff00004444444f000f00111111100f0ff0000000000000f0aaaaaaaffff0f0777777700fffff4444444f00ff0022222220f0f0f011111110000ff0777777700fffff4444444f00ff0022222220f0f0f011111110000ff0000000000000009999999fff0ff0777777700fffff4444444f00ff0022222220f0f0f011111110000ff08888888fff0000777777700fffff4444444ff0ff0022222220f0f0f0111111100f0ff0 else 0x9999999fff00f04444444f00ff0022222220f0f0f0111111100f0ff0777777700fffff7777777000ffff4444444ff0ff0022222220f0f0f0111111100f0ff07777777f00ffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0222222200ff0f0111111100f0ff0777777700fffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0cccccccfffff007777777f00ffff777777700fffff22222220f0f0f0111111100f0ff0dddddddf0f0fff8888888fff00004444444f00ff00) else 0xff08888888fff00004444444f0fff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00004444444f00ff0022222220fff0f022222220f0f0f011111110000ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0f00000000000000f0000000000000008888888fff00004444444f0fff0022222220f0f0f011111110000ff08888888fff00004444444f00ff0033333330fffff0111111100f0f00000000000000f0aaaaaaaffff0f04444444f00ff00333333300ffff022222220f0f0f0111111100f0ff0cccccccfffff00) else (if b < 74 then 0x4444444f0fff0022222220f0f0f011111110000ff0cccccccfffff007777777000ffff5555555f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300ffff022222220f0f0f011111110000ff08888888fff00004444444ff0ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00004444444f00ff0022222220f0f0f011111110ff0ff011111110000ff08888888fff00004444444f00ff004444444f000f0033333330fffff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f00f0 else 0x7777777000ffff4444444f00ff0022222220f0f0f011111110ff0ff011111110000ff0bbbbbbb0ff00ff8888888fff000022222220f0f0f0111111100f00f000000000000ff08888888fff00007777777000ffff4444444f0fff0022222220f0f0f011111110000ff07777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff011111110000ff07777777000ffff4444444f00ff0022222220fff0f022222220f0f0f011111110000ff0dddddddf0f0f0f8888888fff00f04444444f00ff00111111100f0f00000000000000f0000000000000007777777000ffff)) else (if b < 78 then (if b < 77 then (if b < 76 then 0x11111110fffff0111111100f0ff0bbbbbbb0ff00ff8888888fff0ff022222220f0f0f0111111100f0ff000000000000ff0000000000000007777777000ffff4444444f0ffff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff000022222220f0fff0111111100f0ff000000000000ff0fffffff0ff0fff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00007777777ffffff022222220f0f0f000000000000ff07777777000ffff4444444ff0ff0022222220f0f0f0111111100f0ff011111110000ff0 else 0x8888888fff00007777777000ffff2222222ff0f0f0111111100f0ff09999999fff0ff07777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0cccccccfffff007777777000ffff22222220f0f0f01111111f0f0ff0111111100f0ff0dddddddf0f0f0f8888888fff00f04444444f00ff0033333330fffff0000000000000f000000000000000cccccccfffff007777777000ffff2222222ff0f0f0111111100f0ff0aaaaaaaffff0f07777777000ffff4444444f0ffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0) else 0x111111100f0ff07777777000ffff6666666ffffff04444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0111111100f0ff0fffffffff0ffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f0ffff022222220f0f0f0111111100f0ff0aaaaaaaffff0f07777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00005555555f0ffff022222220f0f0f000000000000ff0cccccccfffff00) else (if b < 79 then 0x22222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444ff0ff0022222220f0f0f011111110ff0ff0111111100f0ff0dddddddf0f0f0f8888888fff00f04444444f00fff0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f0fff0022222220fff0f0111111100f0ff07777777f0fffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888ffff00077777770000fff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff77777770000fff22222220f0f0f0 else 0xdddddddfff0fff8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888ffff0004444444f00ff00111111100f0ff0000000000000f0bbbbbbb0ff00ff8888888fff000077777770000fff22222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ff0f4444444f00ff00111111100f0ff0000000000000f07777777000ffff4444444f0fff004444444f0fff0022222220f0f0f0111111100f0ff07777777000ffff4444444f0fff00)))))) else (if b < 120 then (if b < 100 then (if b < 90 then (if b < 85 then (if b < 83 then (if b < 82 then (if b < 81 then 0x33333330fffff0000000000000f0fffffff0ffffffcccccccfffff00cccccccfffff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100ffff0000000000000f08888888fff00007777777000ffff4444444f0fff0022222220fff0f0111111100f0ff07777777000ffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0ffffffffffffff7777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0 else 0x4444444f00ff0033333330fffff00000000000ff00000000000000f08888888fff00007777777ffffff04444444f00ff0033333330fffff0000000000000f0cccccccf00000f8888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00006666666ff0fff06666666ff0fff0111111100ffff0111111100f0ff08888888fff00f04444444f00ff0033333330fffff033333330fffff0000000000000f000000000000000cccccccfffff00cccccccfffff002222222ff0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff0) else 0x111111100f0ff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f000000000000ff09999999fff0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff05555555f0ffff022222220f0f0f000000000000ff08888888fff00005555555f0ffff05555555f0ffff022222220f0f0f000000000000ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff06666666ff0fff0111111100f0ff09999999fff0ff09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff0000) else (if b < 84 then 0x22222220f0f0f0111111100f0ff0111111100f0ff0fffffff0fffffffffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff0ffffffffff0fff8888888fff00006666666ff0fff0111111100f0ff000000000000ff0fffffff0ffffffdddddddffffff0cccccccfffff0022222220f0f0f0111111100f0ff0fffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff0000000000000f0fffffff0ffffffcccccccfffff0033333330fffff022222220f0f0f0111111100f0ff08888888fffff004444444f00ff0033333330fffff022222220f0f0f0 else 0xfffffff0ffffffcccccccfffff00ccccccc0ffff0022222220f0f0f0111111100f0ff000000000000000fffffff0ffffffccccccc0ffff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff00ccccccc0ffff0022222220f0f0f0111111100f0ff00000000000000000000000000000ccccccc0ffff0022222220f0f0f0111111100f0ff0fffffffffffffffffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff0fffffff0ffffffcccccccfffff00333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffffcccccccfffff00)) else (if b < 88 then (if b < 87 then (if b < 86 then 0x33333330ffff00000000000000f0ffffffffffff0fcccccccf00000f8888888fff00004444444f00ff00000000000000f0fffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff000000000000000ffffffffff0fff8888888fff00006666666ff0fff0111111100ffff0111111100f0ff0ffffffffffff0f8888888fff00f04444444f00ff0033333330fffff0000000000000f000000000000000fffffff0ffffffcccccccfffff002222222ff0f0f0111111100f0ff0ffffffffffff0f8888888fff00004444444f00ff0033333330fffff0000000000000f0 else 0x4444444f00fff04444444f00ff0033333330fffff0000000000000f0000000000000008888888fff00006666666ff0fff0111111100ffff0111111100f0ff0000000000000008888888fff00f04444444f00ff0033333330fffff0000000000000f00000000000000000000000000000cccccccfffff002222222ff0f0f0111111100f0ff0ffffffffffff0f8888888fff00004444444f00ff0033333330ffff00000000000000f08888888fff00004444444f00ff0033333330fffff033333330ffff00000000000000f0000000000000008888888fff00004444444f00ff00) else 0x111111100f0ff000000000000000cccccccfffff002222222ff0f0f0111111100f0ff0000000000000f000000000000000cccccccfffff003333333ffffff02222222ff0f0f0111111100f0ff0cccccccf00000f8888888fff00004444444f00ff00000000000000f0000000000000f08888888fff00f04444444f00ff0033333330fffff0000000000000f0000000000000f0cccccccfffff0022222220f0f0f0111111100f0ff00000000f000000000000000000f0cccccccfffff008888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff0000) else (if b < 89 then 0x333333300000ff2222222ff0f0f0111111100f0ff0000000000000008888888fff00006666666ff0fff0111111100ffff00000000000fff000000000000000eeeeeeeffffff0cccccccfffff002222222ff0f0f0111111100f0ff0000000000000008888888ffff00077777770000fff6666666ff0fff0111111100f0ff0000000000000000000000000000077777770000fff6666666ff0fff0111111100f0ff0000000000000008888888ffff0006666666ff0fff0111111100f0ff000000000000ff000000000000000dddddddffffff0cccccccfffff002222222ff0f0f0 else 0xcccccccfffff002222222ff0f0f0111111100f0ff0000000000000008888888fff00f04444444f00fff04444444f00ff0033333330fffff0000000000000f0000000000000008888888ffff0006666666ff0fff0111111100ffff0111111100f0ff0000000000000008888888fff00f04444444f00fff033333330fffff0000000000000f000000000000000000000000000008888888ffff0006666666ff0fff0111111100ffff000000000000000cccccccfffff00333333300000ff2222222ff0f0f0111111100f0ff00000000000000000000000000000))) else (if b < 95 then (if b < 93 then (if b < 92 then (if b < 91 then 0xff00000000000000f08888888fff00f07777777ffffff04444444f00ff0033333330fffff0000000000000f0cccccccf00000f8888888fff00f04444444f00ff0033333330fffff0000000000000f000000000000000cccccccf00000f8888888fff00f04444444f00ff00000000000000f08888888fff00f08888888fff00f04444444f00ff0033333330fffff0000000000000f000000000000000cccccccfffff002222222ff0f0f02222222ff0f0f0111111100f0ff08888888fff00f04444444f00ff0033333330fffff0000000000000f000000000000000 else 0x7777777000ff0f4444444f00ff0033333330fffff0000000000000f0000000000000007777777000ff0f4444444f00ff0033333330fffff0000000000000f0cccccccfffff002222222ff0f0f0111111100f0ff00000000f000000000000000000f0cccccccffffff08888888fff00f04444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00fff033333330fffff00000000000fff0000000000000f0bbbbbbbffffff08888888fff00f04444444f00ff0033333330fffff0000000000000f08888888fff00f04444444f00ff0033333330fffff0) else 0x111111100f0ff000000000000000cccccccfffff0033333330fffff02222222ff0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100ffff0111111100f0ff000000000000ff0000000000000008888888fff00006666666ff0fff0111111100ffff000000000000ff08888888fff00007777777ffffff06666666ff0fff0111111100ffff0111111100f0ff08888888fff00006666666ff0fff0111111100ffff0111111100f0ff0111111100f0ff08888888fff00006666666ff0fff0111111100ffff0111111100ffff0111111100f0ff08888888fff00f0) else (if b < 94 then 0x3333333ffffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100ffff0111111100f0ff00000000000fff0000000000000008888888fff00006666666ff0fff0111111100f0ff00000000000fff08888888ffff0008888888fff000077777770000fff6666666ff0fff0111111100f0ff0000000000000008888888fff000077777770000fff6666666ff0fff0111111100f0ff0cccccccfffff0022222220f0f0f01111111f0f0ff0111111100f0ff0000000000000f09999999fff0ff08888888fff00006666666ff0fff0111111100ffff0 else 0x8888888fff00006666666ff0fff0111111100ffff0111111100f0ff0000000000000008888888ffff0008888888fff00006666666ff0fff0111111100f0ff000000000000ff0eeeeeeeffffff08888888fff00006666666ff0fff0111111100ffff0111111100f0ff0cccccccfffff00333333300000ff22222220f0f0f01111111f0f0ff0111111100f0ff000000000000000333333300000ff22222220f0f0f01111111f0f0ff0111111100f0ff09999999ffffff08888888fff00006666666ff0fff0111111100ffff0111111100f0ff000000000000000cccccccfffff00)) else (if b < 98 then (if b < 97 then (if b < 96 then 0x33333330fffff0000000000000f08888888fff00007777777000ff0f4444444f00ff0033333330fffff0000000000000f0cccccccfffff008888888fff00f04444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff00000000000fff0000000000000f08888888fff00004444444f00fff033333330fffff00000000000ff00000000000000f0cccccccf00000f8888888fff00004444444f00fff04444444f00ff00000000000000f08888888ffff0008888888fff00006666666ff0fff0111111100ffff0111111100f0ff0 else 0xcccccccf00000f8888888fff00004444444f00ff00000000000000f0cccccccf0000ffcccccccf00000f8888888fff00004444444f00ff00000000000000f0000000000000003333333f0000ff333333300000ff22222220f0f0f0111111100f0ff000000000000000cccccccf0000ff8888888fff00004444444f00ff00000000000000f00000000000000000000000000000999999900ff00f8888888fff0000111111100f0ff0cccccccf00000f8888888fff00004444444f00ff00000000000000f000000000000000cccccccffffff08888888fff00004444444f00ff00) else 0xf0cccccccfffff003333333f0000ff333333300000ff22222220f0f0f0111111100f0ff0cccccccf0000ff8888888fff00004444444f00ff0033333330fffff0000000000000f000000000000000999999900ff00f8888888fff00006666666ff0fff0111111100f0ff0cccccccf00000f8888888fff00004444444f00ff004444444f000000000000000000f0cccccccf00ff0fcccccccf00000f8888888fff00004444444f00ff00000000000000f0333333300000ff22222220f0f0f0111111100f0ff00000000f000000000000000000f0cccccccfffff00) else (if b < 99 then 0x7777777ffffff00000000000ff00000000000000f08888888fff00004444444f00ff004444444f00000033333330fffff0000000000000f0cccccccf00ff0f8888888fff00004444444f00ff0033333330fffff0000000000000f0ffffffffffffffcccccccf00000f8888888fff00004444444f00ff00000000000000f0cccccccf00000f8888888fff00004444444f00ff000000000000ff00000000000000f0cccccccf00000f8888888fff00007777777ffffff04444444f00ff00000000000000f0cccccccf00000fcccccccf00000f8888888fff00004444444f00ff00 else 0xfffffffffffff08888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00006666666ff0fff0111111100f0ff01111111000000f0000000000f000cccccccfffff00bbbbbbbffffff04444444f00ff0033333330fffff0000000000000f0bbbbbbbffffff08888888fff00007777777ffffff04444444f00ff00000000000000f08888888fff00007777777ffffff04444444f00ff000000000000ff00000000000000f08888888fff00007777777ffffff033333330fffff00000000000ff00000000000000f0000000000000008888888fff0000)))) else (if b < 110 then (if b < 105 then (if b < 103 then (if b < 102 then (if b < 101 then 0x22222220f0f0f0111111100f0ff08888888fff00004444444fffff004444444f00ff0033333330fffff0000000000000f08888888fffff004444444f00ff0033333330fffff00000000000ff00000000000000f0000000000000008888888fffff004444444f00ff0033333330fffff0000000000000f0ffffffff00ffff8888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00006666666ff0fff0111111100f0ff00000000000fff000000000000ff08888888fff00004444444f00ff0033333330fffff00000000f00ff00000000000000f0 else 0x8888888fff00006666666ff0fff0111111100f0ff0000000000ff000fffffff0ffffff8888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff0333333300000ff000000000000f0cccccccfffff0033333330fffff0111111100f0ff00000000f000000000000000000f000000000000000cccccccfffff0033333330fffff00000000f000000000000000000f08888888fff00004444444f00ff0033333330fffff000000000ffff00000000000000f0cccccccfffff003333333ffffff033333330fffff0) else 0xf0fffffff0ffffffcccccccfffff005555555f0ffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff003333333ffffff033333330fffff0000000000000f0cccccccffffff022222220f0f0f0111111100f0ff00000000f000000000000000000f0000000000000008888888fff00004444444f00ff003333333ffffff0000000000000f08888888fff00004444444f00ff0033333330fffff00000000f0000f0000000000000f0cccccccfffff0022222220f0f0f0111111100f0ff00000000f0000f0000000000000f000000000000000) else (if b < 104 then 0x33333330ffff00111111100f0ff0000000000000f0fffffffff0ffff9999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0fffffff0ffffffccccccc0ffff004444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff00ccccccc0ffff004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ccccccc0ffff004444444f00ff0022222220f0f0f0111111100f0ff0fffffffff0ffff9999999fff0ff04444444f00ff0022222220f0f0f011111110000ff0ffffffff0fffffaaaaaaaffff0f04444444f00ff00111111100f0ff0 else 0x9999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00005555555f0ffff022222220f0f0f000000000000f00000000000000f08888888fff00005555555f0ffff04444444f00ff0033333330fffff0000000000000f08888888fff00006666666ff0fff022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f04444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000009999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00)) else (if b < 108 then (if b < 107 then (if b < 106 then 0x22222220f0fff000000000000ff09999999fff0ff05555555f0ffff04444444f0fff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff006666666ff0fff02222222ff0f0f0111111100f0ff09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0000000000000f000000000000000aaaaaaaffff0f04444444ff0ff00111111100f0ff0000000000000f09999999fff0ff04444444f0fff0033333330fffff022222220f0f0f0111111100f0ff000000000000000aaaaaaaffff0f04444444ff0ff0033333330fffff0111111100f0ff0 else 0x77777770000fff6666666ff0fff022222220f0f0f0111111100f0ff08888888ffff0006666666ff0fff022222220f0f0f0111111100f0ff000000000000ff0bbbbbbbffffff09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0cccccccfffff004444444f00ff002222222ff0f0f0111111100f0ff0000000000000f09999999fff0ff06666666ffffff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff00005555555f0ffff022222220f0fff0111111100f0ff000000000000ff0000000000000008888888fff00005555555f0ffff0) else 0xf0000000000000008888888fff0f005555555f0ffff022222220f0fff0111111100f0ff0cccccccfffff004444444f00ff00333333300000ff2222222ff0f0f0111111100f0ff0000000000000004444444f00ff00333333300000ff2222222ff0f0f0111111100f0ff08888888fff00005555555f0ffff022222220f0fff0111111100f0ff00000000000fff0dddddddffffff09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888ffff00077777770000fff6666666ff0fff022222220f0f0f0111111100f0ff000000000000000) else (if b < 109 then 0x4444444f00ff0033333330fffff0000000000000f08888888fff0f005555555f0ffff022222220f0f0f000000000000f00000000000000f08888888fff00f05555555f0ffff04444444f00ff0033333330fffff0000000000000f09999999fff0ff04444444f0fff004444444f0fff0022222220f0f0f0111111100f0ff09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff0000000000000008888888ffff0006666666ff0fff022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f04444444f00fff033333330fffff0111111100f0ff0 else 0x8888888fff00006666666ff0fff0111111100ffff0111111100f0ff0000000000000f0000000000000008888888fff00006666666ff0fff0111111100ffff0000000000000f08888888fff00006666666ff0fff033333330fffff0111111100ffff0111111100f0ff07777777000ff0f4444444f00ff0033333330fffff0111111100f0ff0000000000000f0cccccccf00000f8888888fff00f04444444f00ff00111111100f0ff0000000000000f08888888fff00004444444f00fff033333330fffff000000000000ff0000000000000f09999999fff0ff08888888fff00f0))) else (if b < 115 then (if b < 113 then (if b < 112 then (if b < 111 then 0x111111100f0ff000000000000ff08888888fff00005555555f0ffff022222220f0fff022222220f0f0f000000000000ff0000000000000008888888fff00005555555f0ffff022222220f0f0f000000000000ff08888888fff000077777770000fff6666666ff0fff022222220f0f0f0111111100f0ff09999999fff0ff06666666ff0fff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff022222220f0f0f0111111100ffff000000000000ff08888888fff00005555555f0ffff022222220f0fff0111111100f0ff0000000000000f0 else 0x5555555f0ffff022222220f0fff000000000000f00000000000000f04444444f00ff00333333300000ff22222220f0f0f01111111f0f0ff0111111100f0ff0aaaaaaaffff0f04444444ff0ff004444444f00ff00111111100f0ff0000000000000f0aaaaaaaffff0f08888888fff00006666666ff0fff0111111100ffff0111111100f0ff0cccccccfffff004444444f00ff003333333ffffff022222220f0f0f0111111100f0ff08888888fff00005555555f0ffff022222220f0f0f0111111100f0ff00000000000fff08888888fff00005555555f0ffff022222220f0f0f0) else 0xf08888888fff000055555550000f0f4444444f00ff0033333330fffff0000000000000f0cccccccfffff009999999fff0ff04444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff0111111100ffff0000000000000f08888888fff00005555555f0ffff033333330fffff00000000000ff00000000000000f0cccccccf00000f8888888fff00005555555f0ffff04444444f00ff00000000000000f08888888fff00004444444f00ff0033333330fffff000000000000ff0000000000000f08888888fff0000) else (if b < 114 then 0x4444444f00ff0033333330fffff0000000000000f08888888fff00f05555555f0ffff022222220f0f0f000000000000f00000000000000f0000000000000008888888fff0f004444444f00ff0033333330fffff0000000000000f08888888fff00005555555f0ffff022222220f0f0f000000000000ff0000000000000f0ffffffff0fffff8888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff00000000f000f00000000000000f0dddddddffffff08888888fff00004444444f00ff0033333330fffff0 else 0xdddddddf0f0fffcccccccf00000f8888888fff00004444444f00ff00000000000000f04444444f00ff003333333f0000ff333333300000ff22222220f0f0f0111111100f0ff0cccccccf0000ff8888888fff00004444444f00ff00111111100f0ff0000000000000f000000000000000666666600ff00f4444444f00ff0022222220f0f0f0111111100f0ff08888888fff0f004444444f00ff0033333330fffff0111111100f0ff0000000000000f0aaaaaaa0f0000f8888888fff000022222220f0f0f000000000000f00000000000000f08888888fff00004444444f0fff00)) else (if b < 118 then (if b < 117 then (if b < 116 then 0x111111100f0ff0000000000000f08888888fff00004444444f00ff0033333330fffff01111111f0f0ff0000000000000f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0008888888fff00004444444f00ff0033333330fffff0000000000f0f00000000000000f08888888fffff004444444f00ff0033333330fffff0111111100f0ff0000000000000f08888888fff00007777777ffffff0111111100f0ff00000000000ff00000000000000f09999999fff0ff0666666600ff00f4444444f00ff0022222220f0f0f0111111100f0ff0 else 0x4444444f00fff033333330fffff022222220f0f0f000000000000ff0cccccccfffff009999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888ffff0006666666ff0fff04444444f00ff00111111100f0ff0000000000000f0aaaaaaaffff0f09999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330ffff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff003333333ffffff0) else 0x111111100f0ff077777770000fff6666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00fff022222220f0f0f0111111100f0ff00000000000fff0bbbbbbbffffff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888ffff0004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00f07777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff2222222ff0f0f0111111100f0ff08888888fff0000) else (if b < 119 then 0x111111100f0ff00000000000ff00000000000000f0aaaaaaaffff0f09999999fff0ff04444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000000fff08888888fff00004444444f00ff0033333330fffff022222220f0f0f000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff000000000000ff08888888fff00006666666ff0fff04444444f00ff00111111100ffff0000000000000f08888888fff00f04444444f00fff033333330fffff022222220f0f0f0 else 0xcccccccfffff009999999fff0ff05555555f0ffff022222220f0f0f0111111100f0ff000000000000000cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100f0ff08888888fffff004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff0000666666600ff00f4444444f00ff0022222220f0f0f0111111100f0ff08888888ffff0004444444f00ff0033333330fffff0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0fff0111111100f0ff0000000000000f08888888fff00006666666ff0fff0))))) else (if b < 140 then (if b < 130 then (if b < 125 then (if b < 123 then (if b < 122 then (if b < 121 then 0x22222220f0f0f0111111100f0ff08888888fff00004444444f00fff022222220f0f0f0111111100f0ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0fffffffffffff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff0f004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0eeeeeeeffffff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff00aaaaaaaffff0f05555555f0ffff022222220f0f0f0111111100f0ff0 else 0x5555555f0ffff022222220f0f0f022222220f0f0f000000000000ff08888888fff00004444444f00ff003333333ffffff022222220f0f0f0111111100f0ff0cccccccfffff008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000ffff008888888fff00004444444f00ff0022222220f0f0f011111110fffff0111111100f0ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff0ff04444444f00ff00) else 0x111111100f0ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0333333300000ff111111100f0ff000000000000000aaaaaaaffff0f06666666ff0fff0333333300000ff111111100f0ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100f0ff000000000000ff0cccccccfffff00aaaaaaaffff0f07777777ffffff06666666ff0fff0111111100f0ff000000000000000dddddddffffff0aaaaaaaffff0f06666666ff0fff0111111100f0ff08888888ffff0f04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff0000) else (if b < 124 then 0x5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff05555555f0ffff033333330fffff000000000000ff08888888fff00005555555f0ffff033333330fffff0111111100f0ff000000000000ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100f0ff0000000000000f0cccccccfffff00aaaaaaaffff0f06666666ff0fff033333330fffff0111111100f0ff0cccccccfffff00aaaaaaaffff0f06666666ff0fff02222222ff0f0f0111111100f0ff0eeeeeeeffffff0cccccccfffff00aaaaaaaffff0f06666666ff0fff0 else 0xcccccccfffff00aaaaaaaffff0f05555555f0ffff033333330fffff0aaaaaaaffff0f09999999fff0ff04444444f00fff022222220f0f0f0111111100f0ff08888888fff00005555555f0ffff033333330fffff022222220f0f0f000000000000ff09999999fff0ff05555555f0ffff0333333300000ff22222220f0f0f0111111100f0ff0aaaaaaaffff0f06666666ff0fff04444444f00ff00333333300000ff111111100f0ff0eeeeeeeffffff09999999fff0ff05555555f0ffff022222220f0f0f0111111100f0ff0cccccccfffff00bbbbbbbffffff0)) else (if b < 128 then (if b < 127 then (if b < 126 then 0x22222220f0f0f0111111100f0ff0cccccccfffff005555555f0ffff022222220f0f0f0111111100f0ff00000000f0ff0f000000000000000cccccccfffff0022222220f0f0f0111111100f0ff00000000f0ff0f0aaaaaaaffff0f04444444f00ff0033333330fffff0333333300000ff111111100f0ff0cccccccfffff008888888fff00006666666ff0fff033333330fffff000000000000ff0cccccccfffff00bbbbbbbffffff06666666ff0fff033333330fffff0111111100f0ff0cccccccfffff00aaaaaaaffff0f05555555f0ffff033333330fffff0111111100f0ff0 else 0x9999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff009999999fff0ff04444444f00fff022222220f0f0f0111111100f0ff0aaaaaaaffff0f08888888fff00005555555f0ffff022222220f0f0f000000000000ff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff000000000ffff009999999fff0ff08888888fff00005555555f0ffff022222220f0f0f000000000000ff0aaaaaaaffff0f05555555f0ffff0333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff00aaaaaaaffff0f04444444f0fff00) else 0xff0fffffffffff00f8888888fff00005555555f0ffff022222220f0f0f000000000000ff000000000000000fffffff00fffffcccccccfffff0022222220f0f0f0111111100f0ff08888888fff00007777777ffffff05555555f0ffff022222220f0f0f000000000000ff08888888fff0f004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0cccccccfffff0022222220f0f0f0111111100f0ff00000000f000f00000000000000f09999999fff0ff04444444f00ff0022222220f0f0f0000000000f0f00000000000000f0aaaaaaaffffff0) else (if b < 129 then 0x111111100f0ff00000000000f0f000000000000ff08888888fff00005555555f0ffff022222220f0f0f000000000000ff0000000000000008888888fff0ff08888888fff00005555555f0ffff022222220f0f0f000000000000ff000000000000000cccccccfffff0022222220f0f0f01111111f0ffff0111111100f0ff0000000000000008888888fff0ff05555555f0ffff022222220f0f0f000000000000ff00000000000000000000000000000cccccccfffff002222222ff0fff0111111100f0ff08888888fff00005555555f0ffff022222220f0f0f000000000000ff0 else 0x9999999fff0ff04444444f0ffff022222220f0f0f0111111100f0ff0fffffff00fffffcccccccfffff008888888fff000022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100f0ff000000000f0f00000000000000ff0dddddddffffff08888888fff00005555555f0ffff022222220f0f0f000000000000ff0cccccccfffff00333333300000ff22222220f0f0f0111111100f0ff00000000f000f0000000000000000333333300000ff22222220f0f0f0111111100f0ff00000000f000f008888888fff00006666666ff0fff0))) else (if b < 135 then (if b < 133 then (if b < 132 then (if b < 131 then 0x22222220f0f0f000000000000ff0000000000000008888888fffff006666666ff0fff033333330fffff0111111100f0ff08888888fff00006666666ff0fff05555555f0ffff022222220f0fff000000000000ff0fffffff00fffffcccccccfffff006666666ff0fff022222220f0f0f0111111100f0ff04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff00000000f000f00aaaaaaaffff0f04444444f00ff0022222220f0f0f011111110fffff0111111100f0ff08888888fff0ff05555555f0ffff022222220f0f0f0111111100f0ff000000000000ff0 else 0x8888888fff00005555555f0ffff022222220f0f0f000000000000ff09999999fff0ff04444444f00ff00333333300000ff22222220f0f0f0000000000f0f008888888fff00005555555f0ffff04444444f00fff022222220f0f0f000000000000ff09999999fff0ff0333333300000ff22222220f0f0f0111111100f0ff00000000f000f008888888fff00006666666ff0fff05555555f0ffff00000000000f0f000000000000ff0cccccccfffff00aaaaaaaffff0f022222220f0f0f01111111f0ffff0111111100f0ff08888888fff0ff06666666ff0fff05555555f0ffff0) else 0x111111100f0ff0bbbbbbbffffff04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0eeeeeeeffffff09999999fff0ff04444444f00ff0022222220f0f0f0000000000f0ff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0000000000000009999999fff0ff04444444f00ff0022222220f0f0f0000000000f0ff0aaaaaaaffff0f09999999fff0ff04444444f0ffff022222220f0f0f0111111100f0ff0cccccccfffff0022222220f0f0f0111111100f0ff00000000ff0000000000000000ff0eeeeeeeffffff0) else (if b < 134 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0dddddddffffff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff008888888fff00007777777ffffff022222220f0f0f000000000000ff0aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0000000000f0ff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff01111111000000feeeeeeeffffff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff09999999fff0ff08888888fff0ff04444444f00ff0022222220f0f0f0 else 0x9999999fff0ff07777777f00ffff333333300000ff22222220f0f0f0111111100f0ff0aaaaaaaffff0f04444444f00ff00333333300f0fff22222220f0f0f0111111100f0ff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0111111100000f0aaaaaaaffff0f04444444f00ff0033333330f0f0ff333333300000ff111111100f0ff08888888fff00004444444ff0ff0022222220f0f0f0111111100f0ff000000000000ff0cccccccfffff00aaaaaaaffff0f04444444f0ffff022222220f0f0f0111111100f0ff0aaaaaaaffff0f08888888fff0ff0)) else (if b < 138 then (if b < 137 then (if b < 136 then 0x22222220f0f0f0111111100f0ff08888888fff00004444444f00ff002222222ff0f0f0111111100f0ff0000000000000f0cccccccffffff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff0f004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff00aaaaaaaffff0f05555555f00ff0f22222220f0f0f0111111100f0ff055555550000f0f4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0bbbbbbbfff0fff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0 else 0x8888888fffff005555555f0ffff022222220f0f0f0111111100f0ff0fffffff00fffffaaaaaaaffff0f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff0111111100f0ff00000000f00f000000000000000f0cccccccfffff008888888fff00005555555f0ffff022222220f0f0f000000000000ff08888888fff00f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0aaaaaaaffff0f077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff08888888ffff00077777770000fff4444444f00ff00) else 0xf0ff0aaaaaaaffff0f09999999fff000f4444444f00ff0022222220f0f0f0111111100f0ff08888888fffff005555555f0ffff033333330fffff022222220f0f0f0111111100f0ff08888888fff0ff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff0000333333300000ff22222220f0f0f0111111100f0ff00000000f000f00aaaaaaaffff0f04444444f00ff0022222220f0f0f01111111fff0ff0111111100f0ff08888888fff0ff04444444f00ff0033333330fffff022222220f0f0f000000000000ff000000000000000) else (if b < 139 then 0x33333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220fff0f0111111100f0ff0000000000ff0f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00004444444f00ff00333333300000ff22222220f0fff0111111100f0ff0cccccccffffff09999999fff0ff04444444f00fff022222220f0f0f0111111100f0ff08888888fff00f05555555f0ffff04444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0 else 0x8888888fff00004444444f00ff0033333330ffffff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100000f08888888fff00004444444f00ff002222222ff0fff0111111100f0ff0000000000000f08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0f08888888fff00004444444f00ff0022222220f0f0f011111110ff0ff000000000000ff077777770000fff4444444f00ff00)))) else (if b < 150 then (if b < 145 then (if b < 143 then (if b < 142 then (if b < 141 then 0x22222220f0f0f0111111100f0ff09999999fff00f04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff09999999fff00f04444444f00ff0022222220f0f0f0111111100f0ff0111111100000f08888888fff00004444444f00ff00333333300f0ff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300f0fff22222220f0f0f0111111100000f08888888fff00f04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000f022222220f0f0f0111111100f0ff0 else 0x4444444f00ff0022222220f0f0f0111111100f0ff0111111100000008888888fff00004444444f00ff0022222220f0f0f0111111100f0fff111111100f0ff0cccccccfffff00bbbbbbbfff00ff7777777f00ffff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220fffff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100000f0000000000f0f00eeeeeeeffffff09999999fff000f4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbbfff00ff7777777f00ffff333333300000ff) else 0xff0fffffff00fffffeeeeeeeffffff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0fffffff000ffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0fffffffffffff08888888fff00004444444f00ff0022222220f0f0f0000000000f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000000000f9999999fff000f4444444f00ff0022222220f0f0f0111111100f0ff01111111000000f8888888fff0000) else (if b < 144 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbbffffff04444444fffff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00111111100f0ff01111111000000f00000000f0f000eeeeeeeffffff04444444f00ff0022222220f0f0f01111111fff0ff0111111100f0ff08888888fff0ff07777777ffffff04444444f00ff0022222220f0f0f000000000000ff000000000000000bbbbbbbffffff04444444fffff0022222220f0f0f0111111100f0ff08888888fff00007777777ffffff04444444f00fff022222220f0f0f0 else 0xfffffffff0f0ff8888888fff00004444444f00ff0022222220f0f0f0111111100000f0fffffff0f0ffff8888888fff00004444444f00ff0022222220f0f0f011111110000ff09999999fff0ff06666666ff0fff04444444f00ff0022222220f0f0f0000000000f0ff0bbbbbbbffffff04444444f00ff0022222220f0f0f0111111100f0ff000000000ffff008888888fff00007777777ffffff04444444f00ff0022222220f0f0f0000000000f0ff0cccccccfffff00bbbbbbbffffff07777777ffffff022222220f0f0f0111111100f0ff08888888fff0ff07777777ffffff0)) else (if b < 148 then (if b < 147 then (if b < 146 then 0x22222220f0f0f0111111100f0ff08888888fff00004444444f00fff022222220f0f0f0111111100ffff0111111100f0ff08888888fff00004444444f00fff022222220f0fff0111111100f0ff000000000000ff0000000000000008888888fff0f004444444f0fff0022222220f0f0f0111111100f0ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0ffffffffff00ff8888888fffff004444444f00ff0022222220f0f0f0111111100f0ff0fffffff00fffff8888888fff00004444444ff0ff0022222220f0f0f0111111100f0ff0 else 0x4444444ff0fff022222220f0f0f0111111100f0ff000000000000ff0aaaaaaaffffff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888ffff0f04444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0bbbbbbb0ff000f8888888fff000022222220f0f0f0111111100f0ff000000000000ff08888888ffff0004444444f00ff0022222220f0f0f011111110fffff0111111100f0ff08888888fff0ff04444444f00fff022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff0ff04444444f00fff0) else 0x8888888fff0000777777700000ff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220fffff0111111100f0ff0000000000000f0777777700000ff4444444f00ff0022222220f0f0f0111111100f0ff00000000000ff008888888fff0ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888fffff00777777700000ff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000777777700000ff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff0000) else (if b < 149 then 0x33333330fffff022222220f0f0f0111111100f0ff08888888fffff004444444f00ff0022222220f0f0f0111111100f0ff000000000ffff00cccccccffffff0aaaaaaaffff0f04444444f0ffff022222220f0f0f0111111100f0ff08888888ffff0f05555555f0ffff04444444f00fff022222220f0f0f0111111100f0ff0cccccccfffff008888888fff0f004444444f0fff0022222220f0f0f0111111100f0ff08888888fff00004444444f0fff0022222220f0f0f0111111100f0ff000000000000ff08888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0 else 0xfffffff0ffffff8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff003333333000000f22222220f0f0f0111111100f0ff0cccccccfffff008888888fff00f04444444f00fff022222220f0f0f0111111100f0ff09999999fff0ff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0fffffff00ff00f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f01111111fff0ff000000000000ff0777777700000ff4444444f00ff00))) else (if b < 155 then (if b < 153 then (if b < 152 then (if b < 151 then 0x111111100f0f00000000000000f0ffffffffffff0f8888888fff00f04444444f00fff022222220f0f0f0111111100f0ff0fffffffff0ffff8888888fff00004444444f0fff0022222220f0f0f011111110000ff0fffffffff0ffff8888888ff000004444444f00ff0022222220f0f0f011111110000ff0ffffffffffff0f8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0fffffff0ffffff8888888fff0f004444444f00ff0022222220f0f0f0111111100f0ff0ffffffffff0fff8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0 else 0x4444444f00fff022222220f0f0f0111111100f0ff0111111100f0ff077777770000fff4444444f00ff0022222220f0f0f022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0008888888ffff0004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f04444444f00fff022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00f04444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f000) else 0xf08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff0f004444444f00fff022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff0f004444444f00fff022222220f0f0f0111111100f0ff08888888fff00f0) else (if b < 154 then 0x4444444f00ff00111111100f0ff0000000000000f08888888fff00004444444f0fff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f04444444f00ff002222222ff0f0f0111111100f0ff0000000000000f0000000000000008888888ffff0004444444f0fff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff003333333000000f22222220f0f0f0111111100f0ff09999999ffffff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff003333333ffffff01111111f0f0ff0 else 0x8888888fff0f004444444f00ff0022222220f0f0f0111111100f0ff0111111100000f08888888ffff000777777700f0fff4444444f00ff0022222220f0f0f0111111100f0ff07777777000f0ff4444444f00ff0022222220f0f0f0111111100f0ff0111111100000f077777770f0ffff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0777777700f0fff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0ddddddd00f0f0f8888888fff0000)) else (if b < 157 then (if b < 156 then 0x22222220f0f0f0111111100f0ff08888888ffff00077777770000fff4444444f00ff0022222220f0f0f0111111100ffff00000000000000077777770000fff4444444f00ff0022222220f0f0f0111111100ffff08888888fff00f04444444f00fff022222220f0f0f0111111100f0ff000000000000ff077777770000fff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0 else 0x77777770000fff4444444f00ff0022222220f0f0f0111111100ffff08888888fff00004444444f00ff002222222ff0f0f01111111f0f0ff0000000000000f08888888fff0f004444444f00ff0022222220f0fff0111111100f0ff0000000000000f07777777000ff0f4444444f00fff022222220f0f0f0111111100f0ff0000000000000f08888888fff00f04444444f00fff04444444f00fff022222220f0f0f0111111100f0ff08888888fff00004444444f0fff0022222220fff0f0111111100f0ff0000000000ff000cccccccffffff08888888fff00f04444444f00fff0) else (if b < 158 then 0x111111100f0ff08888888fff0ff04444444f00fff022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00fff022222220f0fff0111111100f0ff0000000000000f08888888fff00f04444444f00ff0022222220f0fff0111111100f0ff0000000000000f08888888fff00f04444444f00fff022222220f0f0f0111111100f0ff00000000000000077777770000fff4444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888ffff0004444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0008888888fff0000 else 0xdddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff0fffffff0ffff0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff0f008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff0000777777700f0fff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf000f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f08888888fff00004444444ff0ff0022222220f0f0f0111111100ffff0)))))))
    | 6 => (if b < 49 then (if b < 25 then (if b < 13 then (if b < 7 then (if b < 4 then (if b < 2 then (if b < 1 then 0x111111100f0ff011111110000ff000000000000000bbbbbbb0ff00ff777777700fffff7777777000ffff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0000000000000f000000000000000bbbbbbb0ff00ff7777777000ffff33333330fffff022222220f0f0f0111111100f0ff000000000000000dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff00000000000000000000000000000dddddddf0f0f0fbbbbbbb0ff00ff7777777000ffff111111100f0ff0 else 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff333333300000ff22222220f0f0f0111111100f0ff000000000000000fffffff0ffffffbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0) else (if b < 3 then 0xdddddddf0f0f0f7777777000ffff4444444f00ff00111111100f0ff0000000000000f0dddddddf0f0f0f7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0bbbbbbb0ff00ff7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0dddddddf0f0f0fbbbbbbb0ff00ff else 0x111111100f0ff011111110000ff0bbbbbbb0ff00ff8888888fff0000777777700fffff7777777000ffff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff0fff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0bbbbbbb0ff00ff777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0)) else (if b < 6 then (if b < 5 then 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777f00ffff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00007777777000ffff7777777000ffff22222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff7777777000ffff22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00007777777000ffff22222220f0f0f0111111100f0ff011111110000ff000000000000000bbbbbbb0ff00ff8888888fff000022222220f0f0f0 else 0xffffffffffffffbbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffffbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000000ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff000000000000000eeeeeeeff0f00f7777777000ffff4444444f00ff0022222220f0f0f011111110000ff0eeeeeeeff0f00f777777700fffff) else 0x22222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff00000000000000000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff000000000000000000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000)) else (if b < 10 then (if b < 9 then (if b < 8 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0bbbbbbb0ff00ff7777777000ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffffbbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000fffffff0ffffff7777777000ffff4444444f00ff00 else 0x7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000000000000000007777777000ffff4444444f00ff0033333330fffff0000000000000f07777777000ffff4444444f00ff0033333330fffff033333330fffff022222220f0f0f0111111100f0ff0eeeeeeeff0f00f7777777000ffff) else 0x22222220f0f0f011111110000ff0777777700fffff7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff07777777000ffff5555555f0ffff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff5555555f0ffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000007777777000ffff6666666ff0fff05555555f0ffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0111111100f0ff0) else (if b < 12 then (if b < 11 then 0x4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000007777777ffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0fcccccccfffff008888888fff00004444444f00ff00333333300000ff111111100f0ff000000000000000dddddddf0f0f0f8888888fff00004444444f00ff00333333300000ff111111100f0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff011111110000ff0000000000000007777777000ffff4444444f00ff0033333330fffff0 else 0x7777777000ffff4444444f00ff003333333000fff022222220f0f0f0111111100f0ff077777770ffffff7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff00000000000000077777770ffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff07777777ffffff07777777000ffff) else 0x22222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff07777777000ffff6666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0777777700fffff7777777000ffff6666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0033333330fffff03333333000fff022222220f0f0f0111111100f0ff0))) else (if b < 19 then (if b < 16 then (if b < 15 then (if b < 14 then 0x7777777000ffff4444444f00fff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0ffffffffffff0f7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000ffffffffff0fff7777777000ffff4444444f00ff00 else 0x7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00fff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0000000000000007777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0000000000000f00000000000000000000000000000) else 0x111111100f0ff0000000000000f07777777f00ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000f0777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000f00000000000000f07777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0) else (if b < 18 then (if b < 17 then 0x4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff00000000000000000000000000000777777700fffff4444444f00ff0022222220f0f0f011111110000ff0777777700fffff777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff004444444000ff0022222220f0f0f0 else 0x77777770f0ffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff000000000000000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff000000000000000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f011111110000ff000000000000000777777700fffff) else 0x22222220f0f0f0111111100f0ff0000000000000008888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff077777770ffffff777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff077777770f0ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff077777770f0ffff777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0)) else (if b < 22 then (if b < 21 then (if b < 20 then 0x4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff000000000000000bbbbbbbfff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeffff00feeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f011111110000ff000000000000000eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f011111110000ff0777777700fffff7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff0000777777700fffff7777777000ffff4444444f00ff00 else 0x7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff07777777000ffff4444444f00ff0033333330f0fff022222220f0f0f0111111100f0ff011111110000ff0000000000000007777777000ffff4444444f00ff00333333300ffff022222220f0f0f0111111100f0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff011111110000ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff011111110000ff0eeeeeeeffff00f7777777000ffff) else 0x111111100f0ff0000000000000f09999999fff0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000009999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff07777777000ffff4444444f00ff0022222220f0f0f02222222000f0f0111111100f0ff011111110000ff0) else (if b < 24 then (if b < 23 then 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00008888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000dddddddf0f0f0f8888888fff00004444444f00ff00 else 0xdddddddf0f0f0f8888888fff00007777777000ffff4444444f00ff00111111100f0ff0000000000000f0bbbbbbb0ff00ff9999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff0000) else 0x111111100f0ff011111110000ff0bbbbbbbfff00ffbbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbbfff00ff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0bbbbbbb0ff0fff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0)))) else (if b < 37 then (if b < 31 then (if b < 28 then (if b < 27 then (if b < 26 then 0x8888888fff00004444444f00ff00111111100f0ff0000000000000f000000000000000eeeeeeeff0f00fdddddddf0f0f0f8888888fff00004444444f00ff00000000000000f0cccccccfffff00bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff00bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00007777777000ffff4444444f00ff0022222220f0f0f011111110000ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f0 else 0x8888888fff00007777777000ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0fffffff0ffffff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0eeeeeeeff0f00fdddddddf0f0f0f) else 0x111111100f0ff011111110000ff0000000000000008888888fff00004444444f00ff0033333330fffff022222220f0f0f011111110000ff08888888fff0000777777700fffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff6666666ff0fff05555555f0ffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000008888888fff00007777777000ffff4444444f00ff0033333330fffff0000000000000f0) else (if b < 30 then (if b < 29 then 0x5555555f0ffff04444444f00ff00111111100f0ff0000000000000f0cccccccfffff008888888fff00007777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff09999999fff0ff07777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000cccccccfffff007777777000ffff5555555f0ffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0033333330fffff022222220f0f0f011111110000ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0 else 0x8888888fff000077777770ffffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000008888888fff000077777770ffffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00007777777ffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff0000) else 0x22222220f0f0f0111111100f0ff000000000000000bbbbbbbffffff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff003333333000fff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff03333333000fff022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff003333333000fff022222220f0f0f0111111100f0ff08888888fff000077777770ffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0)) else (if b < 34 then (if b < 33 then (if b < 32 then 0x6666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0eeeeeeeff0f00f8888888fff00006666666ff0fff04444444f00ff0022222220f0f0f000000000000ff000000000000000eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f000000000000ff0bbbbbbbffffff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0bbbbbbbffffff07777777000ffff4444444f00ff0033333330fffff0 else 0xffffffffffffff7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0dddddddf0f0f0fcccccccfffff008888888fff00004444444f00ff00111111100f0ff0000000000000f0cccccccfffff007777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff0000777777700fffff) else 0x22222220f0f0f0111111100f0ff0ffffffffff0fff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff07777777000ffff7777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0) else (if b < 36 then (if b < 35 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000f08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00007777777000ffff4444444f00fff022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00007777777000ffff4444444f00fff0 else 0xbbbbbbb0ff00ff8888888fff000022222220f0f0f0111111100f0ff000000000000f00000000000000f09999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000f08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00f08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00f07777777000ffff) else 0x111111100f0ff0000000000000f08888888fff00004444444f00ff004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff00000000f000000000000000000f0cccccccfffff007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff004444444000ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00007777777f00ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0))) else (if b < 43 then (if b < 40 then (if b < 39 then (if b < 38 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff000000000000000000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff0000777777700fffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0 else 0x8888888fff000077777770ffffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0fff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000dddddddf0f0fff8888888fff00004444444f00ff00111111100f0ff0000000000000f09999999fff0ff08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff00bbbbbbbfff00ff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff0000777777700fffff) else 0x22222220f0f0f0111111100f0ff0eeeeeeeffff00f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0dddddddf0fff0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0aaaaaaaffff0f08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000aaaaaaaffff0f0777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff000077777770f0ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0) else (if b < 42 then (if b < 41 then 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff007777777f00ffff7777777000ffff22222220f0f0f0111111100f0ff08888888fff0000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f011111110000ff08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000008888888fff0000777777700fffff4444444f00ff0022222220f0f0f011111110000ff0ffffffffffffff8888888fff0000777777700fffff4444444f00ff00 else 0xdddddddf0fff0fdddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f0aaaaaaaffff0f0777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff000077777770f0ffff777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff0dddddddf0f0fffdddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f0cccccccfffff008888888fff00007777777f00ffff7777777000ffff22222220f0f0f0111111100f0ff09999999fff0ff0777777700fffff) else 0x11111110000ff011111110000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff011111110000ff08888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeff0f0ff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0)) else (if b < 46 then (if b < 45 then (if b < 44 then 0x22222220f0f0f0111111100f0ff011111110000ff0000000000000009999999fff0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000009999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00004444444f00ff0033333330f0fff022222220f0f0f0111111100f0ff011111110000ff0000000000000008888888fff00004444444f00ff00333333300ffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0 else 0x8888888fff00007777777000ffff4444444f00ff00333333300ffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff004444444f000f0022222220f0f0f0111111100f0ff0000000000000f0aaaaaaaffff0f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0f00000000000000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0f00000000000000f08888888fff00004444444f00ff00) else 0x111111100f0ff011111110000ff0dddddddf0f0f0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0f00000000000000f0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0111111100f0f00000000000000f000000000000000dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0f00000000000000f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000009999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0) else (if b < 48 then (if b < 47 then 0x4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0dddddddf0f0f0f8888888fff00004444444f00ff004444444f000f00111111100f0ff0000000000000f0aaaaaaaffff0f07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff00004444444f00ff0022222220f0f0f02222222000f0f0 else 0xbbbbbbb0ff00ff8888888fff00006666666ff0fff022222220f0f0f0111111100f0ff000000000000ff000000000000000bbbbbbb0ff00ff8888888fff000022222220f0f0f0111111100f0ff000000000000ff0bbbbbbbffffff09999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff09999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff09999999fff0ff09999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0ffffffffffffff8888888fff0000) else 0x22222220f0f0f0111111100f0ff0eeeeeeeff0f00f8888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0dddddddf0f0f0f8888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000dddddddf0f0f0f8888888fff00004444444f00ff0033333330fffff0000000000000f0cccccccfffff007777777000ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0ffffffffffffff9999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0))))) else (if b < 73 then (if b < 61 then (if b < 55 then (if b < 52 then (if b < 51 then (if b < 50 then 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff09999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0111111100f0ff0bbbbbbb0ff00ff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0dddddddf0f0f0f8888888fff00006666666ff0fff04444444f00ff00111111100f0ff0000000000000f0aaaaaaaffff0f09999999fff0ff07777777000ffff4444444f00ff00 else 0xdddddddf0f0f0f8888888fff00f04444444f00ff00111111100f0ff0000000000000f000000000000000000000000000007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f0000000000000f0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0111111100f0ff0000000000000f0ffffffffffff0fdddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f09999999fff0ff07777777000ffff) else 0x11111110ff0ff0111111100f0ff0dddddddf0f0f0f8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00007777777000ffff4444444f0fff0022222220f0f0f0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f000000000000000dddddddf0f0f0f8888888fff00004444444f00fff04444444f00ff00111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00ff0022222220f0f0f011111110ff0ff0111111100f0ff0) else (if b < 54 then (if b < 53 then 0x22222220f0f0f0111111100f0ff0111111100f0ff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0000000000000f0ffffffffffffffdddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f0eeeeeeeff0f00f8888888fff00004444444f00ff0022222220f0f0f000000000000f00000000000000f0dddddddf0f0f0fdddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0 else 0xffffffffffffff7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0ffffffffffffffffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00004444444f00ff00) else 0x111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffffffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0ffffffffffffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000)) else (if b < 58 then (if b < 57 then (if b < 56 then 0x33333330fffff033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff033333330fffff0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0033333330fffff033333330fffff0000000000000f07777777000ffff7777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000007777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0 else 0xfffffff0ffffffcccccccfffff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00007777777ffffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0cccccccfffff008888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0aaaaaaaffff0f09999999fff0ff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00) else 0x111111100ffff0111111100f0ff000000000000000000000000000008888888fff00f04444444f00ff0033333330fffff0000000000000f0000000000000000000000000000000000000000000cccccccfffff002222222ff0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0033333330fffff0000000000000f0000000000000f000000000000000000000000000008888888fff00004444444f00ff0033333330fffff0000000000000f000000000000000ffffffffffff0f8888888fff00004444444f00ff0033333330fffff0000000000000f0) else (if b < 60 then (if b < 59 then 0x7777777ffffff04444444f00ff0033333330fffff0000000000000f000000000000000cccccccf00000f8888888fff00004444444f00ff0033333330fffff0000000000000f00000000000000000000000000000cccccccf00000f8888888fff00004444444f00ff00000000000000f0000000000000008888888fff00004444444f00ff0033333330fffff0000000000000f000000000000000000000000000008888888fff00004444444f00fff04444444f00ff0033333330fffff0000000000000f000000000000000000000000000008888888fff00006666666ff0fff0 else 0xffffffffffff0f8888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000fffffff0ffffffcccccccfffff004444444f00ff0022222220f0f0f0111111100f0ff000000000000000cccccccfffff0022222220f0f0f0111111100f0ff00000000f000000000000000000f000000000000000cccccccfffff008888888fff00004444444f00ff0033333330fffff0000000000000f0000000000000008888888fff00004444444f00ff0033333330fffff00000000000ff00000000000000f0000000000000008888888fff0000) else 0x111111100ffff0111111100f0ff0000000000000008888888fff00f04444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000000000000000009999999fff0ff04444444f0fff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000f08888888fff00004444444f00ff0033333330fffff0111111100f0ff0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0))) else (if b < 67 then (if b < 64 then (if b < 63 then (if b < 62 then 0x5555555f0ffff022222220f0f0f000000000000f00000000000000f08888888fff00005555555f0ffff04444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000008888888fff00005555555f0ffff04444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00fff04444444f00ff0033333330fffff0111111100f0ff0000000000000f0000000000000008888888fff00006666666ff0fff022222220f0f0f0 else 0x8888888fff00004444444f00ff0033333330fffff0111111100f0ff00000000000ff00000000000000f08888888fff00007777777ffffff04444444f00ff0033333330fffff0111111100f0ff0000000000000f0cccccccf00000f8888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000cccccccf00000f8888888fff00004444444f00ff00111111100f0ff0000000000000f08888888fff00005555555f0ffff022222220f0f0f0111111100f0ff000000000000f00000000000000f0000000000000008888888fff0000) else 0x111111100f0ff0000000000000f0000000000000008888888fff00f04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000f0ffffffffffff0f8888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0cccccccfffff004444444f00ff0022222220f0f0f0111111100f0ff00000000f000000000000000000f0cccccccfffff008888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f0) else (if b < 66 then (if b < 65 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0cccccccf00000f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0033333330fffff022222220f0f0f000000000000f00000000000000f08888888fff00006666666ff0fff04444444f00ff0033333330fffff0111111100f0ff0000000000000f08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f04444444f00ff0033333330fffff022222220f0f0f0 else 0x8888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00005555555f0ffff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00005555555f0ffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000000ff00000000000000f08888888fff00007777777ffffff0) else 0x22222220f0f0f0111111100f0ff0aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f022222220f0f0f0111111100f0ff0111111100f0ff0cccccccfffff008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0cccccccfffff008888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0)) else (if b < 70 then (if b < 69 then (if b < 68 then 0x4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000cccccccfffff009999999fff0ff05555555f0ffff022222220f0f0f0111111100f0ff00000000000000000000000000000cccccccfffff00aaaaaaaffff0f06666666ff0fff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f022222220f0f0f0111111100f0ff000000000000ff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00004444444f00ff004444444f00ff00333333300000ff else 0xbbbbbbbffffff0aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff009999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0cccccccfffff009999999fff0ff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000cccccccfffff00aaaaaaaffff0f05555555f0ffff022222220f0f0f0111111100f0ff0aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0aaaaaaaffff0f09999999fff0ff0) else 0x22222220f0f0f0111111100f0ff000000000000000eeeeeeeffffff09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff05555555f0ffff022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff00006666666ff0fff05555555f0ffff022222220f0f0f000000000000ff0000000000000008888888fff00005555555f0ffff022222220f0f0f0111111100f0ff000000000000ff000000000000000000000000000008888888fff00005555555f0ffff022222220f0f0f000000000000ff0) else (if b < 72 then (if b < 71 then 0x8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff009999999fff0ff04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000009999999fff0ff04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff008888888fff00006666666ff0fff022222220f0f0f0111111100f0ff000000000000ff0dddddddffffff0aaaaaaaffff0f09999999fff0ff04444444f00ff00 else 0x8888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff00004444444f00ff0033333330fffff022222220f0f0f000000000000ff0aaaaaaaffff0f08888888fff00006666666ff0fff04444444f00ff00111111100f0ff0000000000000f0cccccccfffff00aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff0aaaaaaaffff0f09999999fff0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000009999999fff0ff0) else 0x111111100f0ff000000000000ff0dddddddffffff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100ffff0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00005555555f0ffff04444444f00ff00333333300000ff22222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0033333330fffff022222220f0f0f000000000000ff0)))) else (if b < 85 then (if b < 79 then (if b < 76 then (if b < 75 then (if b < 74 then 0x4444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00f05555555f0ffff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff0f004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff09999999fff0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0ffffffff0fffff8888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0aaaaaaaffff0f08888888fff00004444444f00ff0022222220f0f0f0 else 0x8888888fff00004444444f00ff0033333330fffff0333333300000ff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000f000f00000000000000f0dddddddffffff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff000055555550000f0f4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000f0aaaaaaaffff0f08888888fff0000) else 0x22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0111111100000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100000f08888888fff00004444444f00ff00333333300f0fff333333300000ff22222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff00333333300f0fff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000f0) else (if b < 78 then (if b < 77 then 0x4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100000f0cccccccfffff008888888fff00004444444f00ff00333333300f0fff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000008888888fff00007777777f00ffff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff000000000000000bbbbbbbfff00ff4444444f00ff00333333300000ff else 0x8888888fff00007777777ffffff07777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff333333300000ff22222220f0f0f0111111100f0ff0ffffffffffffff8888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0cccccccfffff00bbbbbbbfff00ff4444444f00ff00333333300000ff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000f0f00dddddddffffff08888888fff0000) else 0x111111100f0ff0000000000f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0fffffffffffff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff000000000000000fffffffffffff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0eeeeeeeffffff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff01111111000000f000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff01111111000000f)) else (if b < 82 then (if b < 81 then (if b < 80 then 0x4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0bbbbbbbffffff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00007777777ffffff06666666ff0fff04444444f00ff0022222220f0f0f000000000000ff0000000000000008888888fff00007777777ffffff04444444f00ff0022222220f0f0f000000000000ff0eeeeeeeffffff08888888fff00004444444f00ff0022222220f0f0f0 else 0xfffffff00fffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff0000000000f0ff0fffffffffffff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff01111111000000fcccccccfffff00bbbbbbbffffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0eeeeeeeffffff08888888fff0000) else 0x22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0fff022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff00004444444f00fff022222220f0f0f0111111100f0ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff000000000000ff0fffffffffff00f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0) else (if b < 84 then (if b < 83 then 0x4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff00004444444f00ff0022222220f0f0f011111110fffff0111111100f0ff0000000000000008888888fff0ff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff000000000000000000000000000008888888fff0ff04444444f00ff00 else 0x8888888fff0ff06666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fffff004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00fff022222220f0f0f0111111100f0ff000000000000ff0fffffff00fffff8888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000f0f00000000000000f09999999fff0ff08888888fff0000) else 0x22222220f0f0f0111111100f0ff0fffffff0ffffff8888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000ffff00000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000ffff008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000ff0000000000000000ff0cccccccfffff008888888fff00004444444f00ff0022222220f0f0f011111110fffff0111111100f0ff0))) else (if b < 91 then (if b < 88 then (if b < 87 then (if b < 86 then 0x3333333ffffff033333330fffff022222220f0f0f0111111100f0ff0cccccccffffff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff003333333ffffff022222220f0f0f0111111100f0ff09999999fff0ff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0cccccccfffff008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000cccccccfffff008888888fff00f04444444f00ff00 else 0xffffffffffff0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0fffffff0fffffffffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0ffffffff0fffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff00) else 0x111111100f0ff0000000000000f000000000000000ffffffffffff0f8888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0fffffffff0ffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0fffffffff0ffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff000000000000000fffffffff0ffff8888888fff00004444444f00ff0022222220f0f0f011111110000ff0fffffffffffffffffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0) else (if b < 90 then (if b < 89 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0ffffffffffff0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0f00000000000000f0fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffff0fff8888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0ffffffffffff0f8888888fff00f04444444f00ff0022222220f0f0f0 else 0x8888888fff00004444444f00ff0022222220f0fff022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0000000000000f0000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000f000000000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000f00000000000000f08888888fff00004444444f00fff0) else 0x22222220f0f0f0111111100f0ff0000000000000000000000000000077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff002222222ff0f0f0111111100f0ff0000000000000f000000000000000cccccccffffff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff0f004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000f0)) else (if b < 94 then (if b < 93 then (if b < 92 then 0x4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00f04444444f00fff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888ffff0004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0000000000000008888888fff00f04444444f00fff022222220f0f0f0111111100f0ff0000000000000f000000000000000000000000000008888888fff00f04444444f00fff022222220f0f0f0111111100f0ff0000000000000008888888ffff00077777770000fff4444444f00ff00 else 0x8888888fff00004444444f00fff022222220f0f0f0111111100f0ff000000000000ff0000000000000f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff000000000000f00000000000000f08888888fff00f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000000000000000008888888fff00f0) else 0x111111100f0ff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100ffff0111111100f0ff08888888fff00f07777777000ff0f4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000007777777000ff0f4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff00000000f000000000000000000f0cccccccffffff08888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0) else (if b < 96 then (if b < 95 then 0x77777770000fff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff000077777770000fff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f01111111f0f0ff0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0022222220f0fff0111111100f0ff0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0 else 0x8888888fff00004444444f00fff022222220f0f0f0111111100f0ff000000000000f00000000000000f08888888ffff0008888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff0000000000000008888888fff00004444444f0fff004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f09999999ffffff08888888fff00004444444f00ff0022222220f0f0f0111111100ffff0111111100f0ff08888888ffff0008888888fff0000) else 0xbbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000f0000f0000000000000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000ff0008888888fff00007777777000ff0f4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0))))))
    | 7 => (if b < 6 then (if b < 3 then (if b < 2 then (if b < 1 then 0x111111100f0ff011111110000ff000000000000000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000007777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000bbbbbbb0ff00ff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff00000000000000000000000000000bbbbbbb0ff00ff7777777000ffff22222220f0f0f0111111100f0ff0 else 0x4444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00007777777000ffff4444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0bbbbbbb0ff00ff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0) else 0x9999999fff0ff07777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff011111110000ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff011111110000ff08888888fff0000777777700fffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff0000777777700fffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff) else (if b < 5 then (if b < 4 then 0x22222220f0f0f0111111100f0ff08888888fff00008888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0dddddddf0f0f0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000dddddddf0f0f0f8888888fff00004444444f00ff00111111100f0ff0000000000000f09999999fff0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0 else 0x4444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000000ffffffffffffff7777777000ffff4444444f00ff00) else 0x8888888fff00004444444f00ff0033333330fffff0111111100f0ff0000000000000f000000000000000000000000000008888888fff00004444444f00ff0033333330fffff0000000000000f08888888fff00004444444f00ff0033333330fffff033333330fffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000007777777000ffff7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00007777777000ffff)) else (if b < 9 then (if b < 8 then (if b < 7 then 0x111111100f0ff0000000000000f08888888fff00005555555f0ffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff000000000000000aaaaaaaffff0f09999999fff0ff04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0111111100f0ff0000000000000008888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000f0 else 0x4444444f00ff0022222220f0f0f0111111100f0ff000000000000ff08888888fff00007777777ffffff04444444f00ff0033333330fffff022222220f0f0f0111111100f0ff0000000000000008888888fff00007777777ffffff04444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff008888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff0000000000000008888888fff00004444444f00ff00333333300000ff22222220f0f0f0111111100f0ff08888888fff00005555555f0ffff04444444f00ff0022222220f0f0f0) else 0xffffffffffff0f8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000fffffff0ffffff8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0cccccccfffff008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0cccccccfffff008888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00006666666ff0fff04444444f00ff0022222220f0f0f0111111100f0ff000000000000ff0000000000000008888888fff0000) else (if b < 11 then (if b < 10 then 0x111111100ffff0111111100f0ff0000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f000000000000000000000000000008888888fff00f04444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0 else 0x7777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff00000000f000000000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff000000000000f00000000000000f08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00fff04444444f00ff0022222220f0f0f0111111100f0ff0000000000000f0000000000000008888888fff00004444444f00ff0022222220f0f0f0) else 0x0)))
    | 8 => 0x8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff08888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0000000000000f08888888fff00004444444f00ff0033333330fffff022222220f0f0f0111111100f0ff08888888fff00007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0000000000000007777777000ffff4444444f00ff0022222220f0f0f0111111100f0ff0
    | 9 => 0x8888888fff00004444444f00ff0022222220f0f0f0111111100f0ff0
    | _ => 0
  certField w 56 (i % 32)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def state (s i : Nat) : List Nat :=
  let base := i * certStride s
  (List.range (certLength s i)).map (fun j => certWire s (base + j))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certWireHash (w : Nat) : Nat :=
  (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certHash (ws : List Nat) : Nat :=
  (ws.foldl (fun acc w => acc + certWireHash w) 0) % 4294967291

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certSalt : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1206994348
  | 3 => 58803830
  | 4 => 1814798098
  | 5 => 1814798098
  | 6 => 58803830
  | 7 => 3309649581
  | 8 => 3309649581
  | 9 => 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certBuckets : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 8
  | 3 => 128
  | 4 => 512
  | 5 => 1024
  | 6 => 512
  | 7 => 64
  | 8 => 8
  | 9 => 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certCapacity : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 32
  | 3 => 512
  | 4 => 4096
  | 5 => 4096
  | 6 => 2048
  | 7 => 256
  | 8 => 32
  | 9 => 1
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certDisplacement (s i : Nat) : Nat :=
  let b := i / 64
  let w := match s with
    | 0 => 0x0
    | 1 => 0x0
    | 2 => 0x3000a0002000f000000080005
    | 3 => (if b < 1 then 0x100070007000300030000000f0009000b0008000c00010039000000000010000d0010003b000000230004000100010001003d0012002500040013000200040000000000020005003d0012000000050009001f00130000000200050007000f0000000f000a002f0022000e00150003000c00030002000d0017000200000007 else 0x10001000300120005001b0003000300040016001700320004000a000d0000000d00000024000900050001000300150004002600000002000700000003000300210002002e0003000800000004000b000b002300090015001300010004000500080000000e000100140003000600040007000000060002000700020002)
    | 4 => (if b < 4 then (if b < 2 then (if b < 1 then 0x200000000001400070005000c00000001000200080001000100150002000000050006000100000024000100010002000100060000000000000006000a00060005000000000004000400050008001000000003000100020004000100030003000200050000000f001f00010007000100030008000500000008000000030009 else 0x10007000c0000000200020003000000060002000000000000000000070000000000100000000100000007000100050001000700050001000400100008000400000000000400090009000d0000000800010015000700050000000600020003000000020001000200070001000d001000000008000300020001000000020000) else (if b < 3 then 0xb000000000003000100010000000300000001000300010007000800040001000100000002000a0001000400010000000100000001000000040004000800000003000100030003000600040000000000000000000200030007000000010001000000020008000600000001000000000001000d000100030000000000010000 else 0x40001000100020000000000010005000000000002000400000000000c000800000001000000090001000100050000000000110000000300010003001f000000020000000300010000000200070001000100060009001b000300020001001600000007000800010000000200040001000d0000000000010000000100020007)) else (if b < 6 then (if b < 5 then 0x20001000200000000000700170005000000000000000000080007000100000003000100010002000000000001000c0004000000160000000100000005000000020000000000050000000000000003000000100000000400010003000600020000000000050008000000040001000100040000000000000000000100010001 else 0x5000200010008000000000003000300020000000a000c00010005000000000000000100050000000300000001000200020002000300020003000300040002000500030002000000060004000000000004000400030007000400000000000200000002000400000003000b00000000000400050000000c0001000000090003) else (if b < 7 then 0x6000400030000000900180001000000010001000000030000000400000001000400000000000400000005000100060002000100020002000000000003000100030000000000060001000700010000000200020006000000000001000200210000000200070000000400010001000000000000000100000002000000000000 else 0x100020002000200010002000000050004000a000000010000001c00000000000200030000000000080001000000000000000000030006000100060005000200000002000000140008000300000001000100070006000000000003000300020004000000040003000a000a0000000300040001000e000c0004)))
    | 5 => (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then 0x400030000000500010000000000010005000300040000000a000000000008000c0002000300010001000100080000000700030003000100030007000200040000000300000013000000000003000500040000000f000700000000000d000d0000000000030000000500010000000200010007000300010007000200050000 else 0x400020004000800000000000400090007000e000600010003000100020002000000010005000000020000001600000007000200000003000100000006000200040002000000040004000000000000000400030002000100000009000300040000000200000001000200010002000000020000000d0001000e0005) else (if b < 3 then 0x20006000800060005000e0000000d00020004000200000001000400000001000100000008000600000000000d0002000700080006000300000000000500070002000200060000000100010000001c000300030000000200000004000000030004000600000005000200030000000100000005000600000000000300000001 else 0xb0001000e0003000100020003000b000400020000000600020006000200030000000000060001000700000000000000000001000000000000000000020003000000010003000000000000000100030000000600000001000100120000000100010001000000000000000a0002000100030002000000000007000300000003)) else (if b < 6 then (if b < 5 then 0xa0001000d0000000200000002000200040001000200000000000100020005000000000002000300230000000600010006000300010000000200070002000c0000000000030002000400000002000200020003000400010006000c0002000200000003000100000000000f000e0001000b00040005000000000001000f0005 else 0xa00010001000600030006000000000001000200040002000300000006000000000003000700000001000100000000000000110001000500030001000000030003000100000000000d000000000001000b0002000a0006000000000000000500010007000000030001000e000000000006000000000000000100000001) else (if b < 7 then 0x10000000200010007000b00020003000400040000001200030001000200010002000300000000000700120008000000010000000200050000000d000800000001000600220014000d00040002000000020010000d000400010010000100010002000100000002000000030000000c00090000000300000013000900010000 else 0x100010000001300000000000100020001000300080000000200000000000b0008000b0000000100000016000600000001000200050001000000030000000200000000000600010002000400010001000500050000000100000003000600000007000000040003000100050001000400040003000000000000000200000000))) else (if b < 12 then (if b < 10 then (if b < 9 then 0x10007000100000000000200010000000000020000000400160004000c0006000900030000000000000000000200050003000000000003000200020001000100000000000200060000000100040000000000020002000400000006000300000002001000070000000800000000000300020001000000170002000100010005 else 0x1000000040002001700010001000100030000000000050000000000000002000100000000000300000005000700040001000f00010001000e0001000100070005000b00000000000a0004000000000007000100000001000100030000000400000000000400130002000000010003000500030002000100000000) else (if b < 11 then 0x10001000500000000000000030000000000000000000d0002001600040000000000000000000000000005000000020000000d000200080003000000090002000000000001000000000000001d0004000000050001000b000000010001000b0001000000050000000200010003000100070004000800000001000000070005 else 0x40001000b0006000000000006000000000000000100000003000c0000000500010001000300090005000500090000000200010000000500010004000200000002000000010000000800050009000300000000000e00000004000000000002000300000001000000010001000200010002000800010009000000000000)) else (if b < 14 then (if b < 13 then 0x400000001000000010005000000000000000100000000000000010002000000020001000100020005000800080002001100000001000100030000000000060000000500010006000100000000000300040000001c00020005000100000003000400000000000a0003000000050001001c0001000000000006000000010002 else 0xb000000020011000000000005000d000e000000000001000000000000000c000000180000000100020000000000020007001f00090007000000000001000c00060003000600000000000000010002000400040004000100000001000a000200020000000100000006000000000002000000030000000000020000000c0001) else (if b < 15 then 0x50000001300010007000000010007000000020006000300000000000f0000000800030005000000000003000800020008000200000008002c000000000000000300020001000000000024000f0002000400040002000200050009000000000006000100050002000100000000000300000008000a00010000000800010006 else 0xb000300030000000500030002000000000000000600080007000000000005000000030008000b00020009000000000001000000060000000000080000000a000200000010001b000000020000000000010000000500000000000100030000000f000100010002000000020004000100080004000900020000000100070006))))
    | 6 => (if b < 4 then (if b < 2 then (if b < 1 then 0x30001000400020005000700000004000b0000000000060000000a001500010000000000000005001e000200030000000300080006000000010003000f000200050000000000000002000100060000000800010002000000030000000800090000001200060000000000000000000500050001000200000000000100170000 else 0x20004000c00000000000100080001000100010008000900000008000000010001000000060001002c0016000500080000000000030007000200090001000200010000000f0008000000030000000000020000001000000003000b00000002000000000005000d000d00070000000100000009000300020005000000030000) else (if b < 3 then 0x1000500000000000c000400000001000000020005000000000003000300000000000100010000000100010009000b000100000005000000000001000000000000000100000001000200000001000e0008000200000002000b00020015000600040000000600010005000000000005000200050000000000000001000c0002 else 0x10000000800000010000000000001000500000005000b000200030002000700020000000000050003002b001500020002000a0000000000060007000e002d0001000300000010001300000003000000000001000100020011001000000007000000020000000400010000000500020003000b000000040001000000020005)) else (if b < 6 then (if b < 5 then 0x6000000000001000600030001000200020017000400010008000b00010001000500020000000000060008000100000002000300050004000b00030010000600040000000b00010000000000010000000000010001000100030000000f00030000000000040000000400030000000200010002000000010000000200020001 else 0x40005000400020001001500040000000200080000000300040006000000000001000200010000000300020000000000000005000d00040003000b00060005000200010001000600020000000000010006000300020000000000130007001d0000000300030005000100020003000100020009000700020002000f00030004) else (if b < 7 then 0x30003000400020009001e0007000800000005000000070004000000010002000c0005000000020000000800010002000000010000000500010000000700000000000300040003000b000d0001000100000004000b000100080002000000040000000200010001000b00010002000200110000000000010000000c else 0x100000005000100000007000100010001000f000000010028000500020001000100000004000200030003000000010000000200010001000600010001000400000003000700010005000d0002000d000200120002000400000000000200040005000600000003000100030001000800010003001a00000000000800040000)))
    | 7 => 0x20006000a0000000100000001000100020004000300070000000000070000000000020000000000000001000200010006000000000003000b00010001000100000006000000040004000d000000010004000100060001000500050000000c0002000000010001000100000004001000000000000400000000000500010001
    | 8 => 0x9000000000001000000060001
    | 9 => 0x0
    | _ => 0
  certField w 16 (i % 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certValue (s i : Nat) : Nat :=
  let b := i / 64
  let w := match s with
    | 0 => 0x0
    | 1 => 0x0
    | 2 => 0xb00006018c004600620172000000000000004901600008018000c0016100c8000000200060010000a000e0006300f200000090000901400040008001280135
    | 3 => (if b < 4 then (if b < 2 then (if b < 1 then 0x9800c92082000a002a60b400fe802e2028603c60dec014705d0017010ee00c0108810c2000004a80000000002a00e03088000840c0c00000000000008c00dcc0cc008090048060400000160042806000420066010e8000006e600c7006811f5028a110006c0118702ce0297028e0f0004460ad0076403b611b302e605a80e8c else 0xfc001c000000fa800b511020a000c000bf1010206f20020000010c0000000000000000012030000000000000a8001900302022c00000d70000002b200000460010806e410a00c6002000e400b6005e200a4008a0e661120079211040be90b20014610670c7207c6040602460ac60a090ef0108610c4029311a20ec00000) else (if b < 3 then 0x73200a80a630b66016602890b0300000c4811410fa0000010d30da00e4201c307f510440e8200ec10c303320da805e30ea0028006700eb4000004a6000000000ac001100f840a080e950f2603030f4204c00f2300000ba107100000026610f002a90d660149024800e20191000006d004a00000000007c002e00a40090f0000 else 0x7840d8111ca05e00e000f800480048605200d08014a0040045208c107a00c4001a8000002cc075211e701480120076800c401a008ad0bd5042407400f20054600000e80085203ef10a9009202aa010602400fe0090202650340009508a304c1028f090000860e6000e307a405e60163028205600c26011103100940090907f2)) else (if b < 6 then (if b < 5 then 0x4720000018c062008600cf20ef707800dc0032802900e6c01860b060e620f7502830b000ca001b510600180000001240183000000c80b100d2005e9109604f0109000000ab00f8a0d80112809230700034108d20000039300000c2401440000056400800100036205490c200be61174118b03520c2811a101820c950003090c else 0xb840ca3018d00000ec60444108a02ae09a00326028d08280e6810030d4000000c68049200000300028106c30e6a02f010c10e8f08b010c700550e9104490000018f10a808750a6609200f09102d070300d2104010220f150b6409b512000000044005ec0808000003ec0f4607e810c5078803c00ae001400911000003820720) else (if b < 7 then 0xba00000064003a00e8600000363000001e00df2000000000e3003600d000000000005a009e00208000005f009c000000e890ac30292028c05830000100202a811430c8805000b4700000fb10189008702470a290d4c08f000e00f40000000000690028700000b2c028503a607600ee2024403f1085502e110620fc401281020 else 0x10c603241066093004b208a20ea70e75000000490155008809600b4802880ce910cd03c30488110602c80a200d2805c00000006009c9002c10ed000000000000000011c60cc3000010000f6200000b68026001c608e00e74058005f1022004e00ee005ef0ccc10d203f006a010cc0000118100000aa005500448038006800407)))
    | 4 => (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then 0x7c000000000000047a60d2448a20000000000001093000000000000000000002048000017f04b0051e20000468d000000000a8000000000000000000000000000003f0a0000000018a7000000003e6400002e882bac4e8620d335803ee0000000004e400000000000000000000000000000128000000000000000000000 else 0x2510000000000fc00000000031c40ec000000000335017820000000000003de620470000000000000000266000003bef00004ead1b2a2de000000d320000000040e000003be9234c076041804e8d000004b200003f622db100000000000036081e8a000000000ae00e20188b000000000000000018ef000000000b260568) else (if b < 3 then 0x23c83fa200001ded0000000000000000000000000923000000001f8200001ce009550000000028a02449480124694b4600003caa000000000880460a0000224025e03a8000001c310c40248000005702042226b0000001400000322808644cc70aa83ef40da73f3533c6494600003ae045870000466700000000446600000000 else 0x26000c3200004a600000488e0000000017c8000000001568092000000000314100000000000000000000167524e8000000001460000043300000000036d50000000000000000396014a93b24000000000000000000002fa84147000017421ab42d400000000015c343401a4c50643808000000003be10e88040c50420000)) else (if b < 6 then (if b < 5 then 0x566402620821000000002d800000460744600000000000000000000037804ecc222016352ea01fa80000000000002df100003c66000000001f2f000000003720000048f0000000000000000000001500000007a2000000001d301f404b21106041910000258451c100002fe40000000000000000000000003c42332007d2550a else 0x32c313ec0000024000001b02105131a100002080000032a0000000000548000034b01000000001e2000055e753a009e026900000000000000000000049a000000000420d0244024200004f870000000012210000148344403dce3d9027e0000010623dc5119019e400004c0050000ae83f400000000000000000000043e00000) else (if b < 7 then 0x4ec02ea70000000029400000271100000000000000000000000000000000000008e80000400f000049600000000000000000000019a947e20000000002462760000012903db007ac00003fc91fb2000000000000000000000dc413900000000000000000000055494f7000000f0800000d6c00004a2000000fcc0000488d2ca0 else 0x3d28000000003fa003e200000000000000000000000000000000030000000000000022901e2d07b13070350604131d870bc000000392000014c846061ba81f004dc61dc047e33dcd0000520c000000000000000000000cac00001260000000000000250f0000000000000000000000000000000000000000000000000000))) else (if b < 12 then (if b < 10 then (if b < 9 then 0x51ec0000270000002664000043a335d5000000004088480c3ac40000000011620b42000000000ca6000029a000000000328000003d820000000000001f300000524400000dc000000000000016120000000034200407168020e4000054a8488c00000000000000002b084e600aa715a32ec32420000042801085000000000000 else 0x1a000005566097215d00a003463476c29c025804f130ba83048000000003dcc0000000000004210000044a20000000030101eca4b20100c0000000035a03b103c0120f300004c804906000000003060440406e8000055604802000044ed1fa61bc42ba00000490000004a4218132e4007e800004de50c204b2d3ef20000) else (if b < 11 then 0x16404f2310d2000018a10000000000004a81000033843d4c0000000000000208000000000000000018a6000000003a080000558139ec38602d50000050a00f7517400c8644441329000000000d060000000000004b530000000000000000000000003ba0000000000000144004a60c802f4000000000000000ac000052c4 else 0x3d400bb2000000000000056000000000094400000000232043670000000028e0000025090000000000000000000000003820550900000000194000000000000042a400000b60000000000000000000002c6932754100000047a3000000004ca63f073d15000035e3398119e7000000003f3200000000)) else (if b < 14 then (if b < 13 then 0x36e61f6029c30dc24662570000000000000000000000000048420ec6000000003d09000042460000084120e23d4107af000003a01cc5000048460da4064c3c4644813380000031200000000000003c800a4c2fe94d2d000000000000000006c00000000005cc20a400000263000000000000000000001a530b6b45d000000000 else 0xc22820000000000000000000002731356400000000000000000000408710c054720b4000000d2100000d23000038c03da401414da44bc5000000000e40000000003e860000000000005168564000005680000011d10000000000005740018100003ac0000040a70000000000001588178000000aee2b400000000000000000) else (if b < 15 then 0x14420000000047ec00000000000003a40be02d3000000c5000000d25166800003c6123b04d02245151c0095400000000000021a400000000000000002d0600001971162020a13283000020b2004400001a52000001c2067528904b60000000001eea4ac20000336045b0140000002fc0000006a847e10000 else 0x3bc204083366000036a34241000000001f83482501900d84000053631b0519cc22a64fe408c0498112a700001844253110d105e00000000010ac000000000000000000000db5000048ed3cc8194900001a2b076802c72be010c6340900000ee827c41bc047e00000000056ab11e100000000000046d00000184038043e400000)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then 0x24f51d64000000001920000000000000000000000000000000003f030000000054d200002e2000000000000000000000000000001f1000002da000000000398c0000000000000000000000000000000009492cd000004c273e6c48e1000000400c4d0000000045811ab22b7200003f88314014a03e62 else 0x3c8609483e83000000004242000000000000000029e00f430000000005040000000046ae000050864560000054420000000000000000006300002a4000000ff3000000000000000000000acc01422351128307a300000aa015400000000000000000000020e610d500002587000041a00000000015482a800ba0000000000da1) else (if b < 19 then 0x11324b850000000000001490000000000000000000003003506239cc00000000000008a80a0c00000000000049083e971520000000000000000004c4000000002f6010c2318000001544000039c0032a0000000048a04a400ba5000020240aec0000160056843e610aa60ba2530050c845c02e0846263e423ca80000 else 0xc15320000000000da8000040404a8215280d2d0000168138800000436220b00d0800001ae500001c8000000000000000000000000000000f8c1c300000000002c84ae025604361013044211a031e7000002f68558c0301000000000000000000002e49000000000000000036a001e025e31f0243e800003f47)) else (if b < 22 then (if b < 21 then 0x3f864806000053e2000000000000506100000000000026e00000000014a2486819e600000a6b4aa01824000000001da4444710cc48863bf700002cb022033e6027a0000034e02880000000000000000001c41fe628e8406b360000000000000000000340120a4b14000013800000412048ee000000000000444e000000000000 else 0x1c6394c0000000022c043290ccd00001b8a18a056a107c8000000000066000054a412e000000000000000000de4000017c60000000000000000000000002b200000000000001b241ee43ec411f100000000192200003371000044503bf348e400003b0303e01a95000000000000000047a200000d400000000000000000) else (if b < 23 then 0x1a7000008603d10000000001e4000000daa23710000000000001e202770000049c310a40000178c540000002c400000000039200000338900000ce400000726000031e80000000000000000062641eb0000000000001fd026a941064aad050036e92bc627a601b2000056462a004d80536212514800550655a03d6004a8 else 0x12b12b602ff51eac102512500000000000000000000021e6000008400cc038ec560c1ca452813be70fa03830024e18e4182200003fe24786000000000000422000003f310000000052b00000000000000b02000000002210000004e029600ba3506010880fea28040000000014ac14e00000368800000000000003481c404ee0))) else (if b < 28 then (if b < 26 then (if b < 25 then 0x49c2000000000de00000000008d500005380000018720000000000003d203b201c2600002db03e1022a0000000002308000000c8522d20ed00004085000000000000000054f2000014680000000000002ae055803b60000038483388000000000000280814b12bb600000e280000109235c855c100004a6d2c894f6d0000 else 0x5306019241a82c20000027e40000000046480000464a00000fa4000002c400000000319024841c504cc000004b6200004ce2000000000000000028510000000000000355000000000310000020a553e00000000023303e814de60201356016e80070000033003d611a284240000000000000000000003750490300000000) else (if b < 27 then 0xae61dc122c44d6000000000000035f107c6000000000f0524880000211200000000000000004022000000000000000000000000016900005287000000000000000004e447000000400025d00d22000023490470062010e400004a7023040000000053c0000000000000566b0000000000000000000013e00000000000000000 else 0x46cd00004acb1f0900000cf3022056c04bcd3b000000474c1c420be800000750236008620baa00000000000000002fc81d50004113b1000041903ff20000252f00000000040901c03fc14685000000000000160c486600c0486246c33b400000352600004c20000000004c400ee430e92ce009c04c6054802bc00000)) else (if b < 30 then (if b < 29 then 0x4902000052564bd009804a80000000000000000000000000000011022668000056e6000056000000454012630000122041e80000000051e011c02260210c35682f094300041006001f8900000b00302817603e201ec2000000000000000004600000000000002e6000005246000000000000000000000000000014432df00000 else 0x2f0803eb1b86000019090000112d2dd100000000000000000000080000000182000004320000000000000000000000000000000000000000000009e800000000000000003e0200002c090000000000000000162814af00000000000000001a0800000000000031a0000049e80000000011b0000017e94322191210500a8a) else (if b < 31 then 0x17a004123aec000012ac4da03f3300000000000036e0000000004c0a00001330000034d0466000003100000000000000000000001df251a00000000032c60c62074600000e00000031f50fd032f233044f001d60018c000011c60000066016e641c51a0d1f223c072e1500000000271037b000002e55000000003b90 else 0xf6000000cea0bad00000000000041e600003668000000001da03dd33e2141e048122391136024a00a6000003bac00001084456d13830000000051830e074c7000000000000040c2000000000000000016b140660000000000003cb451003b82488503c2000007b01ba00000))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then 0x49a6000000000000000000000000254d0743064d19c230b100000b8621e02680000000000000134028b2000000000000000000003f2b032400001944556c00002cc0000025b000000000448827234ea03bc10ce217a631b044c81f2c1063096020a30000364000003b66000040203ab012c000000d2c000000000ce6 else 0xaf20000000046932d00000014a3000000000000000047ed18210000000000000000000000001c604bc30000200800004e0000004ec60000000000c70bc63081272c0000000000002f410870000006500000434d00002603000020202be33760244300000000142800000000000024631a02000013a0522a000000000c460000) else (if b < 35 then 0x1065000000000000000026a0000000ec2e48000000002aa01035000015a61b6446ac09f5000002b1078c000000003708484300000cf6000000000000000000000000000000004f40000000000000000000003a7000001860108631c033400000000050ac00000000000000000000082035300000000000002224000031c85432 else 0x9a0000010a11cc453c2000048832fa0000000000000000000001d400000000000005520254c0000000000004c6c0000458000002fe80000000000002c80000010e6000000000000000048a6000000000000000000000000000028000000000009d000000000000000000000000002af0000000000000000000020440000)) else (if b < 38 then (if b < 37 then 0x34800d2033a0000038e126720000000025e64bc400000000042427800000213000002824264421002606000013c911d022462980263200000f07024c1fc002ac20a905e842e9000015ec1b82326005200000000033e000001eb3000000005032180014493e8d000016af243040620000000014d50000000000001ac02a20 else 0x245000000000000000000000000000002000016800000000000000000f68000000000000000000000000000000004d82000000004c150000008400000000000000001d2000000fa83f290000000000003e470e0a000042c741a60640036000000000273056293af03921000018801c8a44c045e000004ee40000000838a0) else (if b < 39 then 0x55a510d025300000000012a014894500000010280000316041c0000027c80cf500000000000000000000000000002e75000016604c020000000000000000000000000000000056aa02153c4c07f200003a3000000d33000000003c820000000023e11fc607ad0000000000000000124300000000 else 0x4b4000004faa000000000000000000000000000000000ce70000112c44b000000000190800001a32000040a03dc10000000035a825290000000000000000000000000000000018c611060000000000003290000000000000108000000000000020d00000000000000000000006e037f5000020ac11000000026c069500000000))) else (if b < 44 then (if b < 42 then (if b < 41 then 0x10560000000002c02d2012e8156013002fb5000012400000000000000000000000000000000000003db1000004051d424422198341ab0b62000000003588000012a60000108205a001c7000007e04f8600000000000020b143c62350544e00001c620000000032081866000000000000126c20a0484120cd357544860ea20000 else 0x4b6c00004a62414120280c601f4400000000000000005253000029232860036237c0000000003a00000000000000000013a9000000000ba40000000043470000000000001ec03f0010a205e63a60000000003900014c1820214014503ce80fe20ea337e800004d6d3ae104031f6844e23d0000000000000018d247c00000) else (if b < 43 then 0x28000003520000019d51b423c6011e000001fe800003fe0000010330000000000001d0004801cc03de048820000000024003546018000001c0100000000000045ad486c040033514870000046a0306601001b2200005146000000000000000000003f221b2b00001804000024e0073000000000100100000000000000000000 else 0x98816c2000000000000000000005507000000000000000000000000000025a042260000000000004f20000000002ac03664000000000402492000002280000000001368000000003f060000000010953f41000000003cc02aa400000000000000000000000000000000406a000000a226b10000250c1ba72a631512)) else (if b < 46 then (if b < 45 then 0x4dc00000016029430000000020a200000000000046b2000005240000562a36e30000000000003321337000000000324911f044c700000000133100000000480300000000095215084044038844f10000250025111e424ba03b2700000c894aa641c20dec516c0000000000004080000000003dc335c000000ac40564 else 0x284000004aae000045e63d02000000000000058844421cc810a04b904b221052000042600000000000000206000046883a4017ef0000452a00004f4600000000102d0000000051f20000000045c23f2f34c000000000000000001f0f26c00052000000000000000000002dc0558200003ba20a6800000000000020604fc0) else (if b < 47 then 0x34600000000000004c6510240000474818b200000000000006281ef242f1046c22324a304443000000001a92536c0aa204c0000000000000000000000000172000003726000000000000000029080000000000000000000000000000038c47600eac0000388c322000002081508d00002ad516410ca020b3000041a93f512370 else 0x1e863d0c0000000000000000000000000000000000004528408416f41023000019c400003470462047ac52b350e8000012b018e005c009a1000021c0218025031fa038e014b04e900e29000051282e8019841ac1000000002f830000546409000000000000000000000047a834a0000052c000000ac243800000252c00000000)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then 0x16c019b727e80ba9000000004be428502ee300003c2400000ba1000021200000000040c00512090800000000000000000406000000002ef0000000000000000000092b80000037400e6200000ae2000000004aca494100004668000000000000516e00004a2d000000000000000020ec0000000000000000000001200000 else 0xce02588000000000000000048ea000000004d2300000000000000000000534400000c43000052e13ce64d40386800000000000000001e0100002d86566a000004d2568715e0141217a8155252ed13860f201f2900003f3740a81e6024c01f9153651372000000003f201e04000000002520000000000000000000004c6d) else (if b < 51 then 0x1ec80000000000004d33522718c043c2000007a9000015b01d0151c200000db24c4613d144c437633dc21103080846822e001cf24e0605400c0a32a800000000000000003ea00000444c4aac198230e8000600000000284900000000000000000000000002f236294840325000000000000044050000307100000000 else 0x3628000005a111243ad508a04bd11068102000000000000024a64502398000000000000000000000000000000000000043ea000038a10000000000000c6c00003904000000000000020a148000000000000048c0044000000000000021011b6800003ec000002d900d3002000000468c00003e80000037e00000000000000320)) else (if b < 54 then (if b < 53 then 0x5181000009682e28510200000b9000002b0054f3468000001f6432e03cc100000eb046c00bb3000000000000000049e917610000000006420930254300000000094703a200000000482d000000000000000000000a6617b21b3325500000000042a5000026403800489053401ca54b172783000049660ac0000000000000 else 0x2e6814e81ca200000000206c0000546c00003be0000039a100000000000000003dd01e2615800df21a600ce100000000000029e3196000000000000000000000000021a000000000018400004b13000002c60000000030c00000000020b500000000000000002dd0000053b0000036c0000047203680544c0000) else (if b < 55 then 0x2bd107802740000020e0522c23901a8b14ad006011a00000333000000000196624092a6000000270000019a823a048230c08143500a30cb200002fe01b6017280000000011ac00203f01000000000000000000000000008046a843061f8f17064a8d00003aa00000000000003d420000000021c60000000001c1 else 0x3be6108306b200000000000000005280000000000000000025c00bb5000000001be23d48000000003e900000000000000f400000020400000528355100002460000022e044f0254023b100001f200a7500003ee824405080000000004b3001a43ea256af4b44000000001c000000000000002e3500002f20000000000000))) else (if b < 60 then (if b < 58 then (if b < 57 then 0x2f80000023431f4851a62d100000000000000000000000001f90444f3080000037c84f0602d20000503340c600003bc300000592000000004dc500000000000000000de200000000000000002408168c00a02f00390900000000000000001e92000002a000000723000027460000000030b032e83f7546ad0d80000000000000 else 0x34f01ead02b000000000412300003b500d00000049800000000000000000000000000000000000001ce40000000000000000094600000000448000000000000005f2000000000000000004f2440006a0000043a517030000000024a84f8010f2086c1f114e220000000000000000000024661701114d00004388000000004a07) else (if b < 59 then 0x1f230000548104160000000000005685000002091a4244841073486336f000004c0700003dc60da6000027c03c22000000000000000000004be20000000000000000118354350000468600004420148c4bc00000099500000000106400000000000000000000000000001f03000000003e8c02a6000047a009c60000 else 0x3261be70000000000000000000000000000000000004a220a943200202602820da000e0000000000d6000000000149100000000000000003cf600004bc2000000000000000000001b400f4c00004a0600000000000000001d8000000000494700000b8d00001f0c1d2200000000000000001d2600001e440000040a)) else (if b < 62 then (if b < 61 then 0x3c11ec742624ca02b92000000000000000028c30be641e2000000001140000000000a40000017041c640e800ac600000000000019c00000000000000000000000005151000000000000000000000680023044a300003450000000000000000000003c00000042d1486d0da912d200000000064312f50b280000513700003790 else 0x2d60000000001f80000000000000000021603940032900003b83000032c00000000050ec0000524717260000000000000000000003280000000000000cf400005200000000000940000007002b045147000000001dec000044484c26000023e000003511478000003d800bb00000302000000000344900000be20000217046ec) else (if b < 63 then 0x39a0373000001fd1116300004de00000000029503f46000002600000000000001b8b21a83f2100000ce837d523402900180637040000272020cc0000000045271230088802903c06510c0ba70000400633c314083c401f8c1420416020af3a840000000038cc55a40000462149405321000008e000000000244c000000000000 else 0x500b3de70f042771040412c4526042ca02e6572003c43bea51602b500c0712061de43881104c3c814e0d56730a20086113154b803d113c200c8846a1000011803c67000007a000000000000002e8000023800ea04681000000001a72000010cf28d146a2000017d256a20601000000004742106600003eb00000000000002ed0))))))
    | 5 => (if b < 32 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then 0x2ca052a048306ce0271061230000000065a338e6660700001db21a522d82212006c000005d48218000000000000000000000659452e000002bc669ca0000000000001da4170812cc61ac65404f6c0e8136273148238057a560a03f4c48a064ac00001a660000000000005126000032320000000000005c2e0b24186e43102c2e else 0x15b20000000076a317a100004a800000349000000f150000000047a87c20000069635526000000007c6773120a8065611786734025067a806f0315200246248c00000000000000000e551a437b23336200006d41000004c26fa900000000670060430000000007646e446266774020c0000000004df000000000070661e40000) else (if b < 3 then 0x782200003d8c506065e12c8841a000006d751e411121000060422ce177884260000000005a8000000000486105c454e21b815db130c2000019891221254200006be7000000000b20282800a30e9221280000000000002309000000000000000027c4420105675cb10000000000004522260600003de40381564200005dc22852 else 0x23000000000032a44b9100001ac8120045310000784c00003d214c8100000000750909306483000041501a4413c04d200000000000003c4f00006cb07d0c1c2826411aec6e536110000028065f8416a8452c00000b660f0400004d5064406c622c692930052647127cc074400000000000000000352475ac000000005cb00000)) else (if b < 6 then (if b < 5 then 0x30a0458000005b2035880f6868620000504c5180364601a1000002a3563100000000140019a87d883e04356074c24b90000000000000096c0000444174e0546000007c61000002204202000027f000005946602625600000626000000000796837e10000182600002f9545810703000074a60000404400000440398439e51602 else 0x7dc05352000000006340000052801c085720000059c010e0632e7066000015260b40012000001d405c0400003c4400000000000016a02ec0068a6a846f41000073694ef0000003a00dc02028000069471fa0000017263aa03e245fc6000000005140000000000000000053616ea7000054e054246bc6302000002a002be40b60) else (if b < 7 then 0x4be053a60000000000002860000020e9000000007ac509044b40000000006b8700001a083f454a8363220000192116815ec000005a8100002d400000000058c60e002622000065ec13604db055a2000000005e21452f27b0000060c4000021260000000000003fa634102406592000000000000000000000000000003389 else 0x614416ac7de00be800005c600ec00000000036c10000000000006a810000000000001d60448015e05800648014c025a35e860ec14b8316f30000648c65a06fa045e06e8e67a01d003b8026800e270000000024405dc05c88696100000d8408212a562e046e8753816d6048807e4025e40462052b000000000000))) else (if b < 12 then (if b < 10 then (if b < 9 then 0x7be62e6141e250416d8e604671802ee36ed01a2800000cc46c9268a623a6138c5d4e54ad00000be06cc055802ee56ca968c26b4d51870000000060c1000000001d8800007e812de400004f000000000002a040f042e800000dc622280ac100000000000003c3000021a02c246053000011e00000000029403a06170600007d20 else 0x1e680d405700228660c83f040000656c562c6f2215c0000062010441000000000000000000006b32000051002de006841201000035a8554400005963000045b008c640833fc755121e2172622f62000007cc0000498041e002847da90000364c22ac65e0000024f3148634843ee009260000349273a80f44208024d467e10c00) else (if b < 11 then 0xae27040000003d22e66646727d54fa0614124e52a013d926da077160b615e820d015d8165952be63cc932d04ee073e90fa037400000616d00005ca34500000000004ad564d0000000007e90362858c71840026c00004e80000000000000000000000000000000001a0a33e17a0273c80000392400000000346c2ef26dd5 else 0x56114ea100206ee00000132165c0658c4b7014cc000000005b242de200000000000000007b600000000000000000000001ac71006a0116423c8478413ca024a65b6017ac40c010e13d976e62000000001ab24ee1000001c0000000003a611ee900000000230849a02ea20000000053200000166d24c700000000000025d34b71)) else (if b < 14 then (if b < 13 then 0x14204a6809087b0542205b841b20446971e016ed4c405a4246c42a8062ad6aa1000063a712102f88000054850a01494000000000000000005d6006e065602ac469b50000000000000000000078c0023000001e8800003be85200136127125cc64a691040400147f131e402627b823d5170e4042c233205e70b2800001ee81eea else 0x1dc0158c53051b00758a00002c06258053e066002e224c0002a1600e3d260000446800007463624314e008c401843e60000000005389000000001c6c000000003b41102307e00000000053c268200000060072920000000007e86d4000004f0102a2676d3d652820280811806d1218e4584508503d50028072240000500c30e9) else (if b < 15 then 0x75601f010c011a040000168200a2000016460000000032620c206c4c664019e03a600000000007206d4f5a60000070a0000052204fc000006ac653e51e40000000004025280024236222050014ee06e24860000053880000578600000bc656b208000000000036805db0000031640000000009411260298024e0 else 0x534d6987000073600000000059c10000380a00000000000000007935390523200000000052400d413d604c8039e40b8e33400f7500000b323d20698201e2000021c600004530078400007ae600004f4c0000000000001a406aea1904722100000e6029081ea054a4168c1e20321218425b0013426003000054476fc0206064a7)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then 0x9a000004c603a8000000000072c000001805cc32a420000640113105360789200002282000064267d705882077200003691662235000000054639c30000034100000000000000006e80563038ec000025a06cc865862ac23c2244101b6416e42cc2444022e8754836612888100636e9070c7bc00bc102ad1dac6d1058625886 else 0x1bc700007ee30000000000006e266028000032ac27160d200b29026310864e7000000000716023400000000000002f2600006882156c00000000460000003f4477ac0c4800000000000000005c2c000037c70000000000001c80273100000000000054213600000017c87dc84e6042340000000036e8000000005d3404c46b41) else (if b < 19 then 0x6c1463016222284000034c00ca07860180024200000600c00000000340632e035321300458c2f8933003bea26662e8c28e037001a4c658940021580000000002c2066603b0247407ac40f402811174046a000003f0a0b8a5489426c01425160000011484bd500004841134a000071403f94000000000000254c78080000 else 0x4dd05d806b77000077801a4205c05887000029a06b336c6c2062000013a039e07d21622600003be023500fc049e000006162000038a024c46220548c658a1940334436c0000032b2098020e8650011a00748526c0cc17db56f640000000000002c28000017a0000000000000564c7d4607e153a24b636b620f08048019e6)) else (if b < 22 then (if b < 21 then 0x5ac00000468417e000006fc671a416060261000000006c267da804a0000024f200000667000000000000000000001ca2000000007a4624830000000000002bf30c2169004eb000000000552159011f22000061a62762248566a200003dc4267152303e122ea00000000007b2549140b00a816880262062835ea8548000000000 else 0x1b6c0000325266e0000000003b6500005ece0040624251e050b000000d602cc00606000019240aa000007ba841c6616038065e1200827a20616c6e631a123306554005e439c020a076265cd0000043700000796e4bc8186c5e0419d241e1216000000dc40282012600001528000000000000000000001b801700) else (if b < 23 then 0x6f4a00003b8566c21862318200004261000000005ac10000000000006f266e0005c6000067260da83b640d927720000006e100000000128025f224e4528800006140000079c0000058a055a72d8601c7000000005d3274170562091265210dc100004cc05828138400000cc70000000022b0653600004a286ca00000 else 0x5ee0000040006ca30000000055292f8e0000000003700000496038c047f061cc2e3255a03ae0771000005610000034286fe060005e480c666d2202a6136627c0000003c4000000000e463d965c630000000004c720861fcc000006740000000000000000000000007840102c00003de1320122350000000034030987000067c0))) else (if b < 28 then (if b < 26 then (if b < 25 then 0x2ab0193200003ee6000000003064270c5844326c57e603ec69203d647b040000000035c041010000348c46f16f82000032902ca25b622e0000002be248c01ee10b8b0e4a000029ec48e05341670222c407360cd21bc00000040001a027014a202ed32fe01cad6c8c244a27a6388d000068ac64a00000000015c44d90 else 0x40241c4060a20000530400000aa6640010a061e00000652676567ea03bc173681866362a1f8006a01348052a20200f4839a005e0052100000dc927a040864d80000079a24ed045294a6034b2702162236c6134e00662102000000c606d342ee07c6025c06d013b407ec10000000028e1000000000000000000000000) else (if b < 27 then 0x23260000000000002aa04f2c2e02000031b236622fab000027e00000000000002f0057e062827381000000006ac1602007c067d559825e801cc053c3000030c003004c080aec000000000000172800002220130200000940000058e26ee856825ea024ec44a02a306b020000000041ca0000000053e46e810000000000000000 else 0x1b841868338043802eec2ae200002960166309005c201402000079005f007d9500004f6046604620000030b2000050a14f806280230400001dec258756c526d042a00d6168a049a8390443c00e49220068e377002d002fa06c000083000060245242000000004e90422764d461520000646d00002a60604515c60a820e90)) else (if b < 30 then (if b < 29 then 0x484027302f6000002d2913c8634229ac000000005f4623835b2d108077d000003e803f250000115200005f666453476837c86dc42920760c464600000000000000005f400000000058a6792072e303cc00001e0056cd6e41404016c600000e443a2700000000000000e000000000000063270000000064a27685000000000000 else 0x252108c056601ee7218600000000022260c0000006ec47c06d04000069606bc154e40000000000000000000064610000256240ec2be06ce235e67ca800c35d6515403fc200000000309242763601750b40076a807c6654c2000000006b8600000000000000000000617008d21b42002664e1598000000000000000000a6661c0) else (if b < 31 then 0x46e037f316f034240000658272550792000000006d2105a10f801be80b0000007328000000000000610014c22d62000044e00000408807e615e200006be16200000000a600000000000015e6000000ac000058c0000077f0000000003c0a35400000304000000000000050d05ec221c874e260c906200000000070e000000000 else 0x3a010966758739925d6307080e022e4025a61b72540a45412e86418c3a26218445205de86c6039202fe45d0110a11d49538776c641c779e8475162a35e005910000016ae538e000073c60000000000000000000000000ce000000000000027904d60000064335446000064c76d0c00005bf15a001ec0000000006b4c01ec1980))))) else (if b < 48 then (if b < 40 then (if b < 36 then (if b < 34 then (if b < 33 then 0x16a155203f52412959000000646203c003e018c00000346103a134631aa80000000070c000002c000000000024421c0062e00000600461c6000000003c27000000000000608060486a402d0807c16ea44e0800005d725d6d000065370000000067e40186088000a000001f81084058c100002f8b00002ba075cc2484000054c0 else 0x41a5536632c20be23da138403a810000684d03405a2100000b9455687a71412800004649682928322c6005ec260430006ae061631ca31f606a4c35c62b60135402c038c313e22acc6466542000001e80026075625860158d6c0100005c956ea10c8062c646c000003fe300001ce02104291538602e80110035460d4662c03900) else (if b < 35 then 0x16e01ae000001c8100002aa200006b0104427ae124f66a043bc00ba261114ea03d450ba47da03a52058c21a642401a713a8d6b6a0de00c8368001081354e01003b8457c64e8151311542000067606da276207a88000037050000000000000b2735a050287ce42cf03b206a00538651840b410ce607605f420fe04072 else 0x6d00000024930000508c396653822c0225ec700063c41ce60a6705752b62668d62b077a02824342669b7020014ec40640522603544902600684045d05a401070000064826d6200000000000016e540a06b600000642009e100006aa0042000001483000000000000000000000c402dc45aa03e8700003dd400001f92000053a0)) else (if b < 38 then (if b < 37 then 0x13a105f2184655cd3ca2660252c0028c1661260179282b2000007e6a13a6000028612f204320096401c27220052033263ac605ca15a000000000270000000000000055c00000000000000000000078a037674fe0550000000000467041001b2c22662dc00000364000002d603e446aa449c05587710365045f2e50e01b8232c0 else 0x2bc05fa000000000400445640866664200004829068644c028800000000000006e2c00005ce0000071301a2065670000000000000000000007ac0000000061c36a213d120000000014710000228132f500002ce076f420d5000000006b202669000014e2000078303aaa22407980004429c001a624635fe2008c70f270202ec5) else (if b < 39 then 0x3e62604c00000c811da300002f4824c00a6219081da112ec6ba10f20110134a0000071a05a4700000000473177e10000000003c126e00c4d18e005d500002dc2658b00000000000000006c06066a000069e123a03f8056c43ce14fa100005ae000415702000054841ee00000000076606b0700002637604064e072d500000000 else 0x57613ba504c000000e801dcc6d323d114a514c200761265200006601000059470000260705027684000007a01de000002f52000000004d081dc272c44160644421614cf06de10000000001c6000000001da50000000000002b920000000070e12ca81b4c0ea1548100007480632358e6568818c172a04c217c2800001f400000))) else (if b < 44 then (if b < 42 then (if b < 41 then 0x45685ba000002b6165300661050700000000000016e305900f6045230da0000000001ef578854431654a00000000000022e900000c4230725bd05f2653400000000072e900000000000014e600002e6019e23a2500003d723f243f6000005c40526722b200000000000045690000000048017b8000000d80000032960000 else 0x58520000000017427f0036412c2206405a8d549010c864ad0f6929e036831a26258c0b46182032c168752da02a367e200000000066620dd516a66df034ec00001fe067200000000002700000366c582038282c803a450000000011c0146000c0363509c8418100003a24318b534567c209a160325d2400000000000018a04006) else (if b < 43 then 0x13460000000022220000000028484aa023e01e60000059e000005312000004c60000000000000000000040c21cb034e16502389061c209a25fe00664614c0061556722e000003c641042000005c16c81776414e83d0c12a00000584d00000f00000000003fa8000000000000102200007ca96088000071e9244715825c8a5001 else 0x314027e600007b0800000e40580600001dc1540707b0000036a500002040534300001cc600003a0000e65250030635282a4c00006d46568000000000000000000000000045401b922a4160600000000000002da969401c415d00224c4de07b0900000000000003d003471e660e64640700004750000022416120252074c00000)) else (if b < 46 then (if b < 45 then 0x658867ab000010c4350800000000244125222d2037a1000022d469a06520160045c017026268196000000000366000000000000000000000000033b22f46346007e4218804820000000018f5694116ec0dc82f077a66658d3c417b20256a38e225820000794064c500647be821a2000059a039f200007c881cc100007081 else 0x2fc000006e2009e037045e405c800000682100000d8122883c620000000069d40a21000004606eec6b120000610824001cac00004dc041a41f6c1c200dd2210600001b6e4946016042000000694207a165e22741394c60291d29022c000000000000000000001da200003ec41a153cc000004fc9000000002aec000053a166e2) else (if b < 47 then 0x6321000049200000146100000000000051300000316029211828000000002c211626600208a028a0000054b3000000000000774400004140000000000a2008e06b007ae019202e82420746e9604d2c0c0ac636e100003b0c02644dc147200b06116021551fc0632c6e0204a27692126c39813b663c60636d0000000014a00000 else 0x352071a106e4508002815a0600006e8c5ac700002250726000000000000000000000000000000000560c0000000000006dc563007701000059d024924ec004e161804f400b263ea0000000002ff500000000000034400000000023e861a22426200200004020000000005666348116c000000000000034830aa211c151200000)))) else (if b < 56 then (if b < 52 then (if b < 50 then (if b < 49 then 0x1aa45be008600c234a083aca692d000000003e6705e212300e4865a15903495168ef2088000009230000000035e13f0100000000000018100000000006e600004ca0000018c64be95b4257212fc45971078024a1356663c019005741180151f03cea00001ba042d022d237a020f554831a090c4318754de11f461e62 else 0x61e101067e6900002a204340000014707d485ec8000063a000005fac2ed61b62636c6b0639456ac45bf000000000038055e40000374168c07755070000003b2500001bc213e00a2c0f8c26a456a500006290000000006d8c00000000156000004be817b2597039a87d01154473a057ac3e40648d00006089324419a00b354ae0) else (if b < 51 then 0x1d063c063e520524000000004a00000074a854a13fc03cc109600000000002c64f100000000000006d2473201da00c4668600000000000002fa200007ba6446000005f0100003da0730100004730100916c221c013c200e36f2021c42c626a724a862af30bac272c29cc0000000077e07d002e2c7c403c81024005402e42 else 0x6e8636676e60000024d2000000000000336d000000000ac059a24a491eb53fad0000480064c3524600006ae257603ba463a10000742c12c031f526cc000000007c004a5000003d10000023607aa005410000000059ec00000000000074a0412000002c26144023e6000002065ae21a00000037221060000051d0200000000000)) else (if b < 54 then (if b < 53 then 0x4ae81bca3a44678000000732422a30e039a6000000000000000000005344000026a000000000000042e423e948e12263614260a7000050c05875316163e010c0785223d717200fac0000000000001640546108e178840000000031c07a2200005d463009250c00001583443022806fa800003da2000000000000000000003820 else 0x17606c8000000000000043262d061490642400000000266800005b4700003880190100000000000000001ca000000000277100001f2000000000753200000421278000003482517058c257c010500000342000006a92310816807e00663500000000538024805ecc5e8802e0062651c047a00ae600005d120320096208202466) else (if b < 55 then 0xb8c1ee6000007020000000014c100006a883c205d87000020266781000000000000000000003360000045a0036027c524602c42000028c80000610927704f2000001d206ca600005482000046a40ae0000042480000000053c00a6c000005475fec57a40d2c4831000001e0798600003e820000000000001240078100002a50 else 0x3f660000148064c46d2727f164d244006b2655827c892a403d4226b2247029a16cb13f322346624656d201406ec221f561c865cd62401b6036a413822c2c57a0280932e864236d2a1a060000118866c378015d70258160e060e80b02070160a1000017c007402ba2422100004350312078ec2b412ba617a60a000dca00000000))) else (if b < 60 then (if b < 58 then (if b < 57 then 0x588022a10c502740000000000000636654a033e0000004c100007120176600c600005ca000005e6026e124cb00004780000041c8000000001a600000592900007534316803c20000752054c4000000005a20000032a500004045000055046c4d6a606980000042807a63254012e000001de17e8d2ea600000000000000000e8c else 0x4ac06f607daa05067a26422600006f8024e35b4009ac00006802306013200000092000006e52000000003e2564c054a57b401db072814232436024ca1be032805c4623610000000060d27da70da222a00a40574057a86ce833a11780422461871a567a407f0671c0000016e1000000003a4000003e051af6638076c83320) else (if b < 59 then 0x42f2669000000be11d6c68e275e0258602c21c6058812e6d0000348021403ba00000000022600000549500000f2836206b243ae60000225200000000056a05c800e2068063047d4200000000535379a072122ec400006b752ecc4b230c026204028a6527526200c224c12fc12da24b300000000033c800000102000036a05ec6 else 0x540624a02c4006d22d80202418840ee02f650580006045e16a4156e0464062e44b20162061ea28d52e20000000005e01000000002660000029812b405fe35f4800000b2a488125c525460c6516605c87000042c05f2000001ec80000000000004da000000a427546000000006be0000000005cc000000000000000003da70000)) else (if b < 62 then (if b < 61 then 0x61064ba90000000000000560000033461500456600006b2169e0000016cc6a2420e070a112200422741540f13dc03ed22bec2324000064a3674d0000552c4688098166cf21e05d6137ad600d10d24e2049500000000003460000364800000000044c5d6400806a2022040000000001a20721222b240860864e5079446531 else 0x62a655c53aa834c81552000007497080000006c4000049e819cc02724ce00000052f0ce21590178838620c8608ec3f200000000000000ca224960000000000001f00000016f200002d225b434b0069e4594f69c1396a00006bc0318024a3646056a46ba02b8066a02bc2578033633b2476ea229563204ca1112005016eee0000) else (if b < 63 then 0xe210000000079e00000210010080000000069a200007240000045602e4641b20bc0000000000000016442c600000000354c00000f2600001ba90000216c09c0000075f232412b0000001030674052600000000000000000662000006442000000000000000008100000000000000b2151a06e6638e04ab5000000004ba0 else 0x378706600000398000000730000043a0000000006b0a00000000000078e05fc81ee43f8241613cf44180000011611a8034291482400900003061000030800000429026c014a10000088c00001860602b1b2243e016e226f07380000000000000000049013a2a22023281068810007ccc6a64000000000000430000005aaa7d63))))))
    | 6 => (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then 0x1c66062121261f062e212a0602c02c8531e03b4c1d6300000fc70000271015d200002cc8000001610000310223892de02574000000000000132c000002660000000000003d4000001e401fa2000029600c2208b225ac19c00000000030a92ca129b1000025a03280082817e301e2000022d004a0000000000000000000000000 else 0x3de1102716e80e3519613ee201cc1ea014e936e92ea023882063016012e220a207e010c8038012a200003e2002ec288020e73ba02ba012a619c3137001c61d403748164c0081022629b0161003e22d4116402ca00000000000001a4200003c70000038e0312028642b0129e12ce904803d6002220000042200003661048c3026) else (if b < 3 then 0x1ee10ae01d6600000c422b4c1c40114022ab000003880ba6000000002e001be00000000000002f4a000037cc00001c802ae0260015c01190120021d200002466000006a20460252025e0210018c31d48224d000000001fc026a034a900001dd00710062c05480000000000003bc025f032a02c502b8402400000000000003ac8 else 0x2ec004ec00003021000020662b42000000002310000000000a6006660000356001c3000000000528000005c00ce000000000318c0e723e8000001bf0000000000000220a000000000a460c60002015e20fec00001f26000005ec30911bc83083366039e01fe20fe105e036401aa80c2624000682000000001ba2000021e60000)) else (if b < 6 then (if b < 5 then 0x3bec032c28c6299100000000314900001006400129220fc000000f4138c101203fa9000037631da60aa0110c13e033000ea038a100003182000010012ee10000020c0f5216431ce22bc700000000000000000fe230a223c0000011a000001072000000000c68000015903000000000000000184118ec00c42220086d0bc02d8c else 0x284600002326000000000c803be31460113008ec08a43b67132232860000030c30cd0000000000003c6600000d2c000000002806000024e0000000002921020225500ee621032eec01a0000000a61fe70acd12ee3f11044428a900000000000000000d2103cc04202b060000188c00000000000021a000000000000018e222a4) else (if b < 7 then 0x214607060000000000000281380934c015092b6008e22e670f002d8e3fe20b4027c1202017c000000000000012c200003a8018c00800000000000000000000001720124c00000000000017800000336632c10a26000000001241000027600be00c402c083c200e60296223223c6913320f2015292990000028c100000000 else 0x2f463ea02be13a0010c90c2033e00000274113602e4027c0116800000000000000000000068620e02b800000152022e028a2000000000e400000088c224300002a4000003f9000003950000000001fe0088014c40a2039c6398d0006300619882d08108021282e410000000000003870306202e23aa025640ca61740))) else (if b < 12 then (if b < 10 then (if b < 9 then 0x2f211c480cc03da100002ba717320e64000000002d8d00000000000037600000000000000000014021e008e100000980000034092ea60d2026712e0200000000368230e60e483d8122cd0d80000000001f7215812b4108402d602f0611ec2e070f8406c017412db7058100c137a006462fc20d15026021c40000000000000560 else 0x3bc604a13c01000000000000106c3020000000000000000000003540000000000000000019a0000000000000000032e00fc138e831b02886132e3b2131a020c03ba63160000000000000206003f2044100001164000032202d8200000e0209210ce931f01092268133c023e025a2000027002872084802a2000000001da02c00) else (if b < 11 then 0x1ae03b6116001540176000000aac03c20000066c1bc6114601c220063ac90d4012601ee0024618f01aa60000106100001dcd2c4000001fca0200008204402f3225260e800ac325421ba01cc61bc03f811d462dc723692106000024c0044c16422b302bcd2780000012802cc01c09087035b029c00000050000e20aec00001151 else 0xa6239102a3004000c8807a20000202c1a08189034e0316638400000000000000000066206e60ca40b60000000000000000000000000000000000000292000002368000004e0000000000000210228e00000030213002c061d600000158c1e0002e0398a29431f40238011500720160c25c812862d230ae214923ec6)) else (if b < 14 then (if b < 13 then 0x5a00520000000002ee62b93000016e022213306000020c623a0402410600000000009612d402dac25a10000000018001c202246002c0a660660000007000eb02ec20b0000003920000013413983100009c00000220b234028200000000009411ec8000000a13e3022e6000023c600000412000005e20c661bed1f48230d2a50 else 0x27202a810ae111d0000030801f640000000026a8184c1dc1198000000ec63e8837490000000018cc00001201000000002db1000005c13ce02e42180c22c31a603589046109002ae7000010a934c8000000000000374420462f0c0000404000001876047202a017e2214800000000000000000000300205e10000000018603cc0) else (if b < 15 then 0xcc800000da801c003e4344003c026200000192000003b400000028217c23dc22fc82da720ea000018c238c00080000000002de40000000031401b2c2fa930e72ce217822b2001e62aa12dc0220411b0368026c030483320000000000482000038a02f0200000000000025c01f602fe00ce82db62b00406c2f4718821603 else 0x2f602d441fb200001b0000002ed417000000000000003f8d0000000031c11a2800002560074011e00000000000002bc31d830000000000000000000000001ce0000003002f520ac0264027a00000000011a12dcc0000000000001da2000007a01e60024200000000000000002c200000169233811380)))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then 0x1e201a0206c61b8306400000162c0000000027d001520000200800003970154800000ed0000000003860000011802b6c20211bc2368800000000104c10401484000000003e001c46308d00000000000030ca22c029ec3af00e461960088200001e432dc2000031a6000000002e470f8014021c112fe600000000000000003c40 else 0xfc216c1000031ad0f4409e00561257322860600322600001e2800001be10000000000003600100429401169164d000004041ef0316200003ec22e2002c1062216a1000017e0000000002c843027000015b03a2811602e890f04208627e03a64227206e020b2122024680e002303396006c20000162000003fe60cf500003740) else (if b < 19 then 0x128200002b6110e001ac26802b9202a102802f2035083d202da0259000001b6c1870052421662ae138e9000015c10fe600001c2827611020000022012c09318d3de7000008c01fea267038b20c020a003d0808811340000034e8000010a01420382000002b8500f236673fe022400e9210070d6000222e010fc608a82cc629c6 else 0x2200e20279003ec32a1086c160208603c0017c621201a48000019e2250018962a36244012621a060340000000000000000000003008000000002a2118810fed1c60132409cc4062140010a80c8600000e662e803b20306e2ae615c633a00000000028e6218000002ac839a00ee923862dc120433ec80360326003e118ed1de8)) else (if b < 22 then (if b < 21 then 0x3d9229e005a62ce805261f8000003f030ead236020e222650e2800003ee60000000014811940032018802a20000031423086000002012e952a6000003f061e83198909c23f0020d017a01f4600002bc618d035a035202c603e36304630ab332607c003e011202b070ee81a702eca1ec61786188d01e00dc213022fe8 else 0x2e612d2210ec00003f3500001242000034890a4003b2040100003e4000000000000036861dc0076830821fa438800d321b80350003a02da2000033600000228100000000000004e1090600000ba0000010b5000018203c8817e700000000000000000000000000000000342900000000000039030ba40000) else (if b < 23 then 0xfd22b0231a33b6605a13ee829013b06186119e02f411a2013042fe2086316603090000029c10000372026a92cc1000000003d413a48318700003fc82e602fa60cc617c1000032400acc0000000000002c80356105550000014409c139b029020c9502e133400000168800000000000030cc2d840fa0000018a0002600000000 else 0x366225803e213b602a1115c9310c0de836c022a12a80362029803ba1288104b016501f8425720442318300e440601d0017721c0f0e8635f53b4100002e2220892da11480234912f229420ac23a292865090125c92bc130e1166c3c7131d026c100a71a2610c011011e801440256500003d6130491021000005210de02f07))) else (if b < 28 then (if b < 26 then (if b < 25 then 0x1ca00000000010810960156028a02a000000254c15c4000000000000000012a0000000002ba61a9530c314e000002540326600001ec0000000a20fe3312600001a000760000014821f00094000000000000001a2000000002f541306000012662160398c2aa011003bc1000018e30fe000002d830000006000000b2000000000 else 0x1eed008703482e860ea316222e8b0c001ea23a1013a80da62140276c0e2914d206060f400e6837661e261568134d00001d8620c114a106a00a0c000024801c6800002fc63a7200002eb3010000000000000000003040306c0000398227e6296300000000232312260ecd0c890000357011662ee2000015c832c000002a101f08) else (if b < 27 then 0x21091a4000003dc623c80000078800000f92000013012f92000000002f400000000035c91366000020403c2c046411e1000000001f2024600000000015ec357615e000000a023350000010410b80000017e106a600000000082015a6398700000000000000000ca00000068000000000184022aa22501c26111214c13ee01d80 else 0x3fa820802ac90f1200003dc0054b00002b401d200a80230000e1000006012ee730302ba100000000000000001a803c2203013a493da01026042c14c02dc6182c1f282bcc0ba81a4601a434602ae82be0274003a40c2820a0014630e0000000000000160d00000ec00264405000000f813d800000000022e7302d00002f00)) else (if b < 30 then (if b < 29 then 0x37a200ec16a00a8c19002cb012e42900236633462d6137e01da825663a810fc4086229a020cd14c20e261a6100a03f1013a018cd01a628a837950f603200004017a22bc8168413c20000000000001a6d02c708c112ec0181000000002bc21ac02e620000116112210000000014a00086306800000000273000000000370011c0 else 0x3e600000000000000a422e8438903c6001e12d2c0000000010420e88000002a70988000012c0150036a000002f240000000028003b800ee00000036801803ca82db02000078000001fc7338006f00000242019a3000018ac17a60000020600001b4016c03aa1000026e002c21aa02bc00ad027b01a2228c000e03be218e0) else (if b < 31 then 0x29ee000035492e883b00000039f02e270dc0000000001ec2134308e0000032460be204c02ea51596226421e10000000000000000000000d2000012c6000000000000222630c200001580000000002c860580000000c0000021c500002ac0000009a01fc2000000003ec03752306018a230a00ec300002840000023201de6 else 0x2da4054915a03f552da600002f010c843363000013c0045200002ce021a60de62ee000000000102216620000000000003f84000000000ca801c501a131cd0e8424a0000003a100000000000000001fa01cc839c02df23f6000002e9200000000228009200261000001ec02872fc01972000000000000000000001e6300000ea6)))))
    | 7 => (if b < 2 then (if b < 1 then 0x1e60000000000240041075202e0010200860042012000a000800600064000c000a8047200620223022605b00340062601210000000002660206000000000000000005d00122018605e001800000000004ac0000026901c001c804f00142000004810168024300000000000000000000000001e8000006810661000000000000 else 0x521000004a3000007410061014000e000000610014100320720008800e1000000000000000000000000000000000000000000000000028000000000060c070600000580004c000004d00000000002a00188000000000002056900000000000000000000000004230040000004a104400022060d030000000212012c0707) else (if b < 3 then 0x3800000046406a90000025006c1000001000000000000000000000000000486000000000000000005a001e001e4014c052004730430000003a0022d00000000046500000204056803c0054900000487000000f20260074000600000000002000620024d000c01a6048003e60246000000000000000000000000000004a20000 else 0x6c006a804a604ad042c00000744000003e0000006e002200500000000a6020802c0002c0000040001f20420054800e402400320000000000000036004460000042d000004a70230016606800020066004a0042201c6010c00000160000001a001a807000602000000000000070106030000006c000005010021))
    | 8 => 0x4200200040006c004d0043000000000070000000000000000000120000006200000000000000000032002400210063004c000100500004000000000060006d
    | 9 => 0x0
    | _ => 0
  certField w 16 (i % 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hint (s : Nat) (ws : List Nat) : Nat :=
  let mixed := certHash ws * certSalt s % 4294967291
  let buckets := certBuckets s
  let displacement := certDisplacement s (mixed % buckets)
  let pos := (mixed / buckets + displacement) % certCapacity s
  certValue s pos


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev verified := closedState mapPerm state nStates hint

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part2_0 : span (verified 2) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part2_8 : span (verified 2) 5 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer2 : span (verified 2) 13 0 = true :=
  (@span_join (verified 2) 8 0 5 part2_0 part2_8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_0 : span (verified 3) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_8 : span (verified 3) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_16 : span (verified 3) 8 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_24 : span (verified 3) 8 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_32 : span (verified 3) 8 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_40 : span (verified 3) 8 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_48 : span (verified 3) 8 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_56 : span (verified 3) 8 56 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_64 : span (verified 3) 8 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_72 : span (verified 3) 8 72 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_80 : span (verified 3) 8 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_88 : span (verified 3) 8 88 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_96 : span (verified 3) 8 96 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_104 : span (verified 3) 8 104 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_112 : span (verified 3) 8 112 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_120 : span (verified 3) 8 120 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_128 : span (verified 3) 8 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_136 : span (verified 3) 8 136 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part3_144 : span (verified 3) 1 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer3 : span (verified 3) 145 0 = true :=
  (@span_join (verified 3) 128 0 17 (@span_join (verified 3) 64 0 64 (@span_join (verified 3) 32 0 32 (@span_join (verified 3) 16 0 16 (@span_join (verified 3) 8 0 8 part3_0 part3_8) (@span_join (verified 3) 8 16 8 part3_16 part3_24)) (@span_join (verified 3) 16 32 16 (@span_join (verified 3) 8 32 8 part3_32 part3_40) (@span_join (verified 3) 8 48 8 part3_48 part3_56))) (@span_join (verified 3) 32 64 32 (@span_join (verified 3) 16 64 16 (@span_join (verified 3) 8 64 8 part3_64 part3_72) (@span_join (verified 3) 8 80 8 part3_80 part3_88)) (@span_join (verified 3) 16 96 16 (@span_join (verified 3) 8 96 8 part3_96 part3_104) (@span_join (verified 3) 8 112 8 part3_112 part3_120)))) (@span_join (verified 3) 16 128 1 (@span_join (verified 3) 8 128 8 part3_128 part3_136) part3_144))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_0 : span (verified 4) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_8 : span (verified 4) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_16 : span (verified 4) 8 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_24 : span (verified 4) 8 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_32 : span (verified 4) 8 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_40 : span (verified 4) 8 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_48 : span (verified 4) 8 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_56 : span (verified 4) 8 56 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_64 : span (verified 4) 8 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_72 : span (verified 4) 8 72 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_80 : span (verified 4) 8 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_88 : span (verified 4) 8 88 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_96 : span (verified 4) 8 96 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_104 : span (verified 4) 8 104 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_112 : span (verified 4) 8 112 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_120 : span (verified 4) 8 120 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_128 : span (verified 4) 8 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_136 : span (verified 4) 8 136 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_144 : span (verified 4) 8 144 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_152 : span (verified 4) 8 152 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_160 : span (verified 4) 8 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_168 : span (verified 4) 8 168 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_176 : span (verified 4) 8 176 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_184 : span (verified 4) 8 184 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_192 : span (verified 4) 8 192 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_200 : span (verified 4) 8 200 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_208 : span (verified 4) 8 208 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_216 : span (verified 4) 8 216 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_224 : span (verified 4) 8 224 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_232 : span (verified 4) 8 232 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_240 : span (verified 4) 8 240 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_248 : span (verified 4) 8 248 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_256 : span (verified 4) 8 256 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_264 : span (verified 4) 8 264 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_272 : span (verified 4) 8 272 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_280 : span (verified 4) 8 280 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_288 : span (verified 4) 8 288 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_296 : span (verified 4) 8 296 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_304 : span (verified 4) 8 304 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_312 : span (verified 4) 8 312 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_320 : span (verified 4) 8 320 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_328 : span (verified 4) 8 328 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_336 : span (verified 4) 8 336 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_344 : span (verified 4) 8 344 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_352 : span (verified 4) 8 352 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_360 : span (verified 4) 8 360 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_368 : span (verified 4) 8 368 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_376 : span (verified 4) 8 376 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_384 : span (verified 4) 8 384 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_392 : span (verified 4) 8 392 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_400 : span (verified 4) 8 400 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_408 : span (verified 4) 8 408 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_416 : span (verified 4) 8 416 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_424 : span (verified 4) 8 424 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_432 : span (verified 4) 8 432 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_440 : span (verified 4) 8 440 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_448 : span (verified 4) 8 448 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_456 : span (verified 4) 8 456 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_464 : span (verified 4) 8 464 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_472 : span (verified 4) 8 472 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_480 : span (verified 4) 8 480 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_488 : span (verified 4) 8 488 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_496 : span (verified 4) 8 496 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_504 : span (verified 4) 8 504 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_512 : span (verified 4) 8 512 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_520 : span (verified 4) 8 520 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_528 : span (verified 4) 8 528 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_536 : span (verified 4) 8 536 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_544 : span (verified 4) 8 544 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_552 : span (verified 4) 8 552 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_560 : span (verified 4) 8 560 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_568 : span (verified 4) 8 568 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_576 : span (verified 4) 8 576 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_584 : span (verified 4) 8 584 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_592 : span (verified 4) 8 592 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_600 : span (verified 4) 8 600 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_608 : span (verified 4) 8 608 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_616 : span (verified 4) 8 616 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_624 : span (verified 4) 8 624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_632 : span (verified 4) 8 632 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_640 : span (verified 4) 8 640 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_648 : span (verified 4) 8 648 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_656 : span (verified 4) 8 656 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_664 : span (verified 4) 8 664 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_672 : span (verified 4) 8 672 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_680 : span (verified 4) 8 680 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_688 : span (verified 4) 8 688 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part4_696 : span (verified 4) 3 696 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer4 : span (verified 4) 699 0 = true :=
  (@span_join (verified 4) 512 0 187 (@span_join (verified 4) 256 0 256 (@span_join (verified 4) 128 0 128 (@span_join (verified 4) 64 0 64 (@span_join (verified 4) 32 0 32 (@span_join (verified 4) 16 0 16 (@span_join (verified 4) 8 0 8 part4_0 part4_8) (@span_join (verified 4) 8 16 8 part4_16 part4_24)) (@span_join (verified 4) 16 32 16 (@span_join (verified 4) 8 32 8 part4_32 part4_40) (@span_join (verified 4) 8 48 8 part4_48 part4_56))) (@span_join (verified 4) 32 64 32 (@span_join (verified 4) 16 64 16 (@span_join (verified 4) 8 64 8 part4_64 part4_72) (@span_join (verified 4) 8 80 8 part4_80 part4_88)) (@span_join (verified 4) 16 96 16 (@span_join (verified 4) 8 96 8 part4_96 part4_104) (@span_join (verified 4) 8 112 8 part4_112 part4_120)))) (@span_join (verified 4) 64 128 64 (@span_join (verified 4) 32 128 32 (@span_join (verified 4) 16 128 16 (@span_join (verified 4) 8 128 8 part4_128 part4_136) (@span_join (verified 4) 8 144 8 part4_144 part4_152)) (@span_join (verified 4) 16 160 16 (@span_join (verified 4) 8 160 8 part4_160 part4_168) (@span_join (verified 4) 8 176 8 part4_176 part4_184))) (@span_join (verified 4) 32 192 32 (@span_join (verified 4) 16 192 16 (@span_join (verified 4) 8 192 8 part4_192 part4_200) (@span_join (verified 4) 8 208 8 part4_208 part4_216)) (@span_join (verified 4) 16 224 16 (@span_join (verified 4) 8 224 8 part4_224 part4_232) (@span_join (verified 4) 8 240 8 part4_240 part4_248))))) (@span_join (verified 4) 128 256 128 (@span_join (verified 4) 64 256 64 (@span_join (verified 4) 32 256 32 (@span_join (verified 4) 16 256 16 (@span_join (verified 4) 8 256 8 part4_256 part4_264) (@span_join (verified 4) 8 272 8 part4_272 part4_280)) (@span_join (verified 4) 16 288 16 (@span_join (verified 4) 8 288 8 part4_288 part4_296) (@span_join (verified 4) 8 304 8 part4_304 part4_312))) (@span_join (verified 4) 32 320 32 (@span_join (verified 4) 16 320 16 (@span_join (verified 4) 8 320 8 part4_320 part4_328) (@span_join (verified 4) 8 336 8 part4_336 part4_344)) (@span_join (verified 4) 16 352 16 (@span_join (verified 4) 8 352 8 part4_352 part4_360) (@span_join (verified 4) 8 368 8 part4_368 part4_376)))) (@span_join (verified 4) 64 384 64 (@span_join (verified 4) 32 384 32 (@span_join (verified 4) 16 384 16 (@span_join (verified 4) 8 384 8 part4_384 part4_392) (@span_join (verified 4) 8 400 8 part4_400 part4_408)) (@span_join (verified 4) 16 416 16 (@span_join (verified 4) 8 416 8 part4_416 part4_424) (@span_join (verified 4) 8 432 8 part4_432 part4_440))) (@span_join (verified 4) 32 448 32 (@span_join (verified 4) 16 448 16 (@span_join (verified 4) 8 448 8 part4_448 part4_456) (@span_join (verified 4) 8 464 8 part4_464 part4_472)) (@span_join (verified 4) 16 480 16 (@span_join (verified 4) 8 480 8 part4_480 part4_488) (@span_join (verified 4) 8 496 8 part4_496 part4_504)))))) (@span_join (verified 4) 128 512 59 (@span_join (verified 4) 64 512 64 (@span_join (verified 4) 32 512 32 (@span_join (verified 4) 16 512 16 (@span_join (verified 4) 8 512 8 part4_512 part4_520) (@span_join (verified 4) 8 528 8 part4_528 part4_536)) (@span_join (verified 4) 16 544 16 (@span_join (verified 4) 8 544 8 part4_544 part4_552) (@span_join (verified 4) 8 560 8 part4_560 part4_568))) (@span_join (verified 4) 32 576 32 (@span_join (verified 4) 16 576 16 (@span_join (verified 4) 8 576 8 part4_576 part4_584) (@span_join (verified 4) 8 592 8 part4_592 part4_600)) (@span_join (verified 4) 16 608 16 (@span_join (verified 4) 8 608 8 part4_608 part4_616) (@span_join (verified 4) 8 624 8 part4_624 part4_632)))) (@span_join (verified 4) 32 640 27 (@span_join (verified 4) 16 640 16 (@span_join (verified 4) 8 640 8 part4_640 part4_648) (@span_join (verified 4) 8 656 8 part4_656 part4_664)) (@span_join (verified 4) 16 672 11 (@span_join (verified 4) 8 672 8 part4_672 part4_680) (@span_join (verified 4) 8 688 3 part4_688 part4_696)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_0 : span (verified 5) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_8 : span (verified 5) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_16 : span (verified 5) 8 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_24 : span (verified 5) 8 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_32 : span (verified 5) 8 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_40 : span (verified 5) 8 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_48 : span (verified 5) 8 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_56 : span (verified 5) 8 56 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_64 : span (verified 5) 8 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_72 : span (verified 5) 8 72 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_80 : span (verified 5) 8 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_88 : span (verified 5) 8 88 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_96 : span (verified 5) 8 96 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_104 : span (verified 5) 8 104 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_112 : span (verified 5) 8 112 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_120 : span (verified 5) 8 120 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_128 : span (verified 5) 8 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_136 : span (verified 5) 8 136 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_144 : span (verified 5) 8 144 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_152 : span (verified 5) 8 152 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_160 : span (verified 5) 8 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_168 : span (verified 5) 8 168 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_176 : span (verified 5) 8 176 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_184 : span (verified 5) 8 184 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_192 : span (verified 5) 8 192 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_200 : span (verified 5) 8 200 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_208 : span (verified 5) 8 208 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_216 : span (verified 5) 8 216 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_224 : span (verified 5) 8 224 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_232 : span (verified 5) 8 232 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_240 : span (verified 5) 8 240 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_248 : span (verified 5) 8 248 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_256 : span (verified 5) 8 256 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_264 : span (verified 5) 8 264 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_272 : span (verified 5) 8 272 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_280 : span (verified 5) 8 280 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_288 : span (verified 5) 8 288 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_296 : span (verified 5) 8 296 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_304 : span (verified 5) 8 304 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_312 : span (verified 5) 8 312 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_320 : span (verified 5) 8 320 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_328 : span (verified 5) 8 328 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_336 : span (verified 5) 8 336 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_344 : span (verified 5) 8 344 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_352 : span (verified 5) 8 352 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_360 : span (verified 5) 8 360 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_368 : span (verified 5) 8 368 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_376 : span (verified 5) 8 376 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_384 : span (verified 5) 8 384 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_392 : span (verified 5) 8 392 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_400 : span (verified 5) 8 400 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_408 : span (verified 5) 8 408 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_416 : span (verified 5) 8 416 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_424 : span (verified 5) 8 424 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_432 : span (verified 5) 8 432 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_440 : span (verified 5) 8 440 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_448 : span (verified 5) 8 448 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_456 : span (verified 5) 8 456 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_464 : span (verified 5) 8 464 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_472 : span (verified 5) 8 472 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_480 : span (verified 5) 8 480 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_488 : span (verified 5) 8 488 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_496 : span (verified 5) 8 496 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_504 : span (verified 5) 8 504 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_512 : span (verified 5) 8 512 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_520 : span (verified 5) 8 520 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_528 : span (verified 5) 8 528 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_536 : span (verified 5) 8 536 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_544 : span (verified 5) 8 544 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_552 : span (verified 5) 8 552 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_560 : span (verified 5) 8 560 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_568 : span (verified 5) 8 568 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_576 : span (verified 5) 8 576 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_584 : span (verified 5) 8 584 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_592 : span (verified 5) 8 592 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_600 : span (verified 5) 8 600 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_608 : span (verified 5) 8 608 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_616 : span (verified 5) 8 616 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_624 : span (verified 5) 8 624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_632 : span (verified 5) 8 632 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_640 : span (verified 5) 8 640 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_648 : span (verified 5) 8 648 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_656 : span (verified 5) 8 656 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_664 : span (verified 5) 8 664 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_672 : span (verified 5) 8 672 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_680 : span (verified 5) 8 680 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_688 : span (verified 5) 8 688 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_696 : span (verified 5) 8 696 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_704 : span (verified 5) 8 704 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_712 : span (verified 5) 8 712 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_720 : span (verified 5) 8 720 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_728 : span (verified 5) 8 728 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_736 : span (verified 5) 8 736 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_744 : span (verified 5) 8 744 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_752 : span (verified 5) 8 752 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_760 : span (verified 5) 8 760 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_768 : span (verified 5) 8 768 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_776 : span (verified 5) 8 776 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_784 : span (verified 5) 8 784 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_792 : span (verified 5) 8 792 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_800 : span (verified 5) 8 800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_808 : span (verified 5) 8 808 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_816 : span (verified 5) 8 816 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_824 : span (verified 5) 8 824 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_832 : span (verified 5) 8 832 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_840 : span (verified 5) 8 840 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_848 : span (verified 5) 8 848 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_856 : span (verified 5) 8 856 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_864 : span (verified 5) 8 864 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_872 : span (verified 5) 8 872 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_880 : span (verified 5) 8 880 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_888 : span (verified 5) 8 888 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_896 : span (verified 5) 8 896 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_904 : span (verified 5) 8 904 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_912 : span (verified 5) 8 912 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_920 : span (verified 5) 8 920 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_928 : span (verified 5) 8 928 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_936 : span (verified 5) 8 936 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_944 : span (verified 5) 8 944 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_952 : span (verified 5) 8 952 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_960 : span (verified 5) 8 960 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_968 : span (verified 5) 8 968 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_976 : span (verified 5) 8 976 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_984 : span (verified 5) 8 984 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_992 : span (verified 5) 8 992 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_1000 : span (verified 5) 8 1000 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_1008 : span (verified 5) 8 1008 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part5_1016 : span (verified 5) 1 1016 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer5 : span (verified 5) 1017 0 = true :=
  (@span_join (verified 5) 512 0 505 (@span_join (verified 5) 256 0 256 (@span_join (verified 5) 128 0 128 (@span_join (verified 5) 64 0 64 (@span_join (verified 5) 32 0 32 (@span_join (verified 5) 16 0 16 (@span_join (verified 5) 8 0 8 part5_0 part5_8) (@span_join (verified 5) 8 16 8 part5_16 part5_24)) (@span_join (verified 5) 16 32 16 (@span_join (verified 5) 8 32 8 part5_32 part5_40) (@span_join (verified 5) 8 48 8 part5_48 part5_56))) (@span_join (verified 5) 32 64 32 (@span_join (verified 5) 16 64 16 (@span_join (verified 5) 8 64 8 part5_64 part5_72) (@span_join (verified 5) 8 80 8 part5_80 part5_88)) (@span_join (verified 5) 16 96 16 (@span_join (verified 5) 8 96 8 part5_96 part5_104) (@span_join (verified 5) 8 112 8 part5_112 part5_120)))) (@span_join (verified 5) 64 128 64 (@span_join (verified 5) 32 128 32 (@span_join (verified 5) 16 128 16 (@span_join (verified 5) 8 128 8 part5_128 part5_136) (@span_join (verified 5) 8 144 8 part5_144 part5_152)) (@span_join (verified 5) 16 160 16 (@span_join (verified 5) 8 160 8 part5_160 part5_168) (@span_join (verified 5) 8 176 8 part5_176 part5_184))) (@span_join (verified 5) 32 192 32 (@span_join (verified 5) 16 192 16 (@span_join (verified 5) 8 192 8 part5_192 part5_200) (@span_join (verified 5) 8 208 8 part5_208 part5_216)) (@span_join (verified 5) 16 224 16 (@span_join (verified 5) 8 224 8 part5_224 part5_232) (@span_join (verified 5) 8 240 8 part5_240 part5_248))))) (@span_join (verified 5) 128 256 128 (@span_join (verified 5) 64 256 64 (@span_join (verified 5) 32 256 32 (@span_join (verified 5) 16 256 16 (@span_join (verified 5) 8 256 8 part5_256 part5_264) (@span_join (verified 5) 8 272 8 part5_272 part5_280)) (@span_join (verified 5) 16 288 16 (@span_join (verified 5) 8 288 8 part5_288 part5_296) (@span_join (verified 5) 8 304 8 part5_304 part5_312))) (@span_join (verified 5) 32 320 32 (@span_join (verified 5) 16 320 16 (@span_join (verified 5) 8 320 8 part5_320 part5_328) (@span_join (verified 5) 8 336 8 part5_336 part5_344)) (@span_join (verified 5) 16 352 16 (@span_join (verified 5) 8 352 8 part5_352 part5_360) (@span_join (verified 5) 8 368 8 part5_368 part5_376)))) (@span_join (verified 5) 64 384 64 (@span_join (verified 5) 32 384 32 (@span_join (verified 5) 16 384 16 (@span_join (verified 5) 8 384 8 part5_384 part5_392) (@span_join (verified 5) 8 400 8 part5_400 part5_408)) (@span_join (verified 5) 16 416 16 (@span_join (verified 5) 8 416 8 part5_416 part5_424) (@span_join (verified 5) 8 432 8 part5_432 part5_440))) (@span_join (verified 5) 32 448 32 (@span_join (verified 5) 16 448 16 (@span_join (verified 5) 8 448 8 part5_448 part5_456) (@span_join (verified 5) 8 464 8 part5_464 part5_472)) (@span_join (verified 5) 16 480 16 (@span_join (verified 5) 8 480 8 part5_480 part5_488) (@span_join (verified 5) 8 496 8 part5_496 part5_504)))))) (@span_join (verified 5) 256 512 249 (@span_join (verified 5) 128 512 128 (@span_join (verified 5) 64 512 64 (@span_join (verified 5) 32 512 32 (@span_join (verified 5) 16 512 16 (@span_join (verified 5) 8 512 8 part5_512 part5_520) (@span_join (verified 5) 8 528 8 part5_528 part5_536)) (@span_join (verified 5) 16 544 16 (@span_join (verified 5) 8 544 8 part5_544 part5_552) (@span_join (verified 5) 8 560 8 part5_560 part5_568))) (@span_join (verified 5) 32 576 32 (@span_join (verified 5) 16 576 16 (@span_join (verified 5) 8 576 8 part5_576 part5_584) (@span_join (verified 5) 8 592 8 part5_592 part5_600)) (@span_join (verified 5) 16 608 16 (@span_join (verified 5) 8 608 8 part5_608 part5_616) (@span_join (verified 5) 8 624 8 part5_624 part5_632)))) (@span_join (verified 5) 64 640 64 (@span_join (verified 5) 32 640 32 (@span_join (verified 5) 16 640 16 (@span_join (verified 5) 8 640 8 part5_640 part5_648) (@span_join (verified 5) 8 656 8 part5_656 part5_664)) (@span_join (verified 5) 16 672 16 (@span_join (verified 5) 8 672 8 part5_672 part5_680) (@span_join (verified 5) 8 688 8 part5_688 part5_696))) (@span_join (verified 5) 32 704 32 (@span_join (verified 5) 16 704 16 (@span_join (verified 5) 8 704 8 part5_704 part5_712) (@span_join (verified 5) 8 720 8 part5_720 part5_728)) (@span_join (verified 5) 16 736 16 (@span_join (verified 5) 8 736 8 part5_736 part5_744) (@span_join (verified 5) 8 752 8 part5_752 part5_760))))) (@span_join (verified 5) 128 768 121 (@span_join (verified 5) 64 768 64 (@span_join (verified 5) 32 768 32 (@span_join (verified 5) 16 768 16 (@span_join (verified 5) 8 768 8 part5_768 part5_776) (@span_join (verified 5) 8 784 8 part5_784 part5_792)) (@span_join (verified 5) 16 800 16 (@span_join (verified 5) 8 800 8 part5_800 part5_808) (@span_join (verified 5) 8 816 8 part5_816 part5_824))) (@span_join (verified 5) 32 832 32 (@span_join (verified 5) 16 832 16 (@span_join (verified 5) 8 832 8 part5_832 part5_840) (@span_join (verified 5) 8 848 8 part5_848 part5_856)) (@span_join (verified 5) 16 864 16 (@span_join (verified 5) 8 864 8 part5_864 part5_872) (@span_join (verified 5) 8 880 8 part5_880 part5_888)))) (@span_join (verified 5) 64 896 57 (@span_join (verified 5) 32 896 32 (@span_join (verified 5) 16 896 16 (@span_join (verified 5) 8 896 8 part5_896 part5_904) (@span_join (verified 5) 8 912 8 part5_912 part5_920)) (@span_join (verified 5) 16 928 16 (@span_join (verified 5) 8 928 8 part5_928 part5_936) (@span_join (verified 5) 8 944 8 part5_944 part5_952))) (@span_join (verified 5) 32 960 25 (@span_join (verified 5) 16 960 16 (@span_join (verified 5) 8 960 8 part5_960 part5_968) (@span_join (verified 5) 8 976 8 part5_976 part5_984)) (@span_join (verified 5) 16 992 9 (@span_join (verified 5) 8 992 8 part5_992 part5_1000) (@span_join (verified 5) 8 1008 1 part5_1008 part5_1016)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_0 : span (verified 6) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_8 : span (verified 6) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_16 : span (verified 6) 8 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_24 : span (verified 6) 8 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_32 : span (verified 6) 8 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_40 : span (verified 6) 8 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_48 : span (verified 6) 8 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_56 : span (verified 6) 8 56 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_64 : span (verified 6) 8 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_72 : span (verified 6) 8 72 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_80 : span (verified 6) 8 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_88 : span (verified 6) 8 88 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_96 : span (verified 6) 8 96 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_104 : span (verified 6) 8 104 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_112 : span (verified 6) 8 112 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_120 : span (verified 6) 8 120 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_128 : span (verified 6) 8 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_136 : span (verified 6) 8 136 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_144 : span (verified 6) 8 144 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_152 : span (verified 6) 8 152 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_160 : span (verified 6) 8 160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_168 : span (verified 6) 8 168 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_176 : span (verified 6) 8 176 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_184 : span (verified 6) 8 184 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_192 : span (verified 6) 8 192 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_200 : span (verified 6) 8 200 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_208 : span (verified 6) 8 208 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_216 : span (verified 6) 8 216 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_224 : span (verified 6) 8 224 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_232 : span (verified 6) 8 232 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_240 : span (verified 6) 8 240 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_248 : span (verified 6) 8 248 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_256 : span (verified 6) 8 256 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_264 : span (verified 6) 8 264 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_272 : span (verified 6) 8 272 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_280 : span (verified 6) 8 280 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_288 : span (verified 6) 8 288 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_296 : span (verified 6) 8 296 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_304 : span (verified 6) 8 304 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_312 : span (verified 6) 8 312 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_320 : span (verified 6) 8 320 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_328 : span (verified 6) 8 328 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_336 : span (verified 6) 8 336 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_344 : span (verified 6) 8 344 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_352 : span (verified 6) 8 352 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_360 : span (verified 6) 8 360 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_368 : span (verified 6) 8 368 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_376 : span (verified 6) 8 376 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_384 : span (verified 6) 8 384 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_392 : span (verified 6) 8 392 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_400 : span (verified 6) 8 400 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_408 : span (verified 6) 8 408 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_416 : span (verified 6) 8 416 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_424 : span (verified 6) 8 424 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_432 : span (verified 6) 8 432 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_440 : span (verified 6) 8 440 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_448 : span (verified 6) 8 448 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_456 : span (verified 6) 8 456 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_464 : span (verified 6) 8 464 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_472 : span (verified 6) 8 472 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_480 : span (verified 6) 8 480 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_488 : span (verified 6) 8 488 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_496 : span (verified 6) 8 496 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_504 : span (verified 6) 8 504 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part6_512 : span (verified 6) 4 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer6 : span (verified 6) 516 0 = true :=
  (@span_join (verified 6) 512 0 4 (@span_join (verified 6) 256 0 256 (@span_join (verified 6) 128 0 128 (@span_join (verified 6) 64 0 64 (@span_join (verified 6) 32 0 32 (@span_join (verified 6) 16 0 16 (@span_join (verified 6) 8 0 8 part6_0 part6_8) (@span_join (verified 6) 8 16 8 part6_16 part6_24)) (@span_join (verified 6) 16 32 16 (@span_join (verified 6) 8 32 8 part6_32 part6_40) (@span_join (verified 6) 8 48 8 part6_48 part6_56))) (@span_join (verified 6) 32 64 32 (@span_join (verified 6) 16 64 16 (@span_join (verified 6) 8 64 8 part6_64 part6_72) (@span_join (verified 6) 8 80 8 part6_80 part6_88)) (@span_join (verified 6) 16 96 16 (@span_join (verified 6) 8 96 8 part6_96 part6_104) (@span_join (verified 6) 8 112 8 part6_112 part6_120)))) (@span_join (verified 6) 64 128 64 (@span_join (verified 6) 32 128 32 (@span_join (verified 6) 16 128 16 (@span_join (verified 6) 8 128 8 part6_128 part6_136) (@span_join (verified 6) 8 144 8 part6_144 part6_152)) (@span_join (verified 6) 16 160 16 (@span_join (verified 6) 8 160 8 part6_160 part6_168) (@span_join (verified 6) 8 176 8 part6_176 part6_184))) (@span_join (verified 6) 32 192 32 (@span_join (verified 6) 16 192 16 (@span_join (verified 6) 8 192 8 part6_192 part6_200) (@span_join (verified 6) 8 208 8 part6_208 part6_216)) (@span_join (verified 6) 16 224 16 (@span_join (verified 6) 8 224 8 part6_224 part6_232) (@span_join (verified 6) 8 240 8 part6_240 part6_248))))) (@span_join (verified 6) 128 256 128 (@span_join (verified 6) 64 256 64 (@span_join (verified 6) 32 256 32 (@span_join (verified 6) 16 256 16 (@span_join (verified 6) 8 256 8 part6_256 part6_264) (@span_join (verified 6) 8 272 8 part6_272 part6_280)) (@span_join (verified 6) 16 288 16 (@span_join (verified 6) 8 288 8 part6_288 part6_296) (@span_join (verified 6) 8 304 8 part6_304 part6_312))) (@span_join (verified 6) 32 320 32 (@span_join (verified 6) 16 320 16 (@span_join (verified 6) 8 320 8 part6_320 part6_328) (@span_join (verified 6) 8 336 8 part6_336 part6_344)) (@span_join (verified 6) 16 352 16 (@span_join (verified 6) 8 352 8 part6_352 part6_360) (@span_join (verified 6) 8 368 8 part6_368 part6_376)))) (@span_join (verified 6) 64 384 64 (@span_join (verified 6) 32 384 32 (@span_join (verified 6) 16 384 16 (@span_join (verified 6) 8 384 8 part6_384 part6_392) (@span_join (verified 6) 8 400 8 part6_400 part6_408)) (@span_join (verified 6) 16 416 16 (@span_join (verified 6) 8 416 8 part6_416 part6_424) (@span_join (verified 6) 8 432 8 part6_432 part6_440))) (@span_join (verified 6) 32 448 32 (@span_join (verified 6) 16 448 16 (@span_join (verified 6) 8 448 8 part6_448 part6_456) (@span_join (verified 6) 8 464 8 part6_464 part6_472)) (@span_join (verified 6) 16 480 16 (@span_join (verified 6) 8 480 8 part6_480 part6_488) (@span_join (verified 6) 8 496 8 part6_496 part6_504)))))) part6_512)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_0 : span (verified 7) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_8 : span (verified 7) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_16 : span (verified 7) 8 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_24 : span (verified 7) 8 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_32 : span (verified 7) 8 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_40 : span (verified 7) 8 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_48 : span (verified 7) 8 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part7_56 : span (verified 7) 3 56 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer7 : span (verified 7) 59 0 = true :=
  (@span_join (verified 7) 32 0 27 (@span_join (verified 7) 16 0 16 (@span_join (verified 7) 8 0 8 part7_0 part7_8) (@span_join (verified 7) 8 16 8 part7_16 part7_24)) (@span_join (verified 7) 16 32 11 (@span_join (verified 7) 8 32 8 part7_32 part7_40) (@span_join (verified 7) 8 48 3 part7_48 part7_56)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part8_0 : span (verified 8) 5 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer8 : span (verified 8) 5 0 = true :=
  part8_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem part9_0 : span (verified 9) 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem layer9 : span (verified 9) 1 0 = true :=
  part9_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem allChecked (s : Nat) (hs : s ≤ 9) :
    ∀ i < nStates s, verified s i = true := by
  interval_cases s
  · simp [nStates]
  · simp [nStates]
  · exact fun i hi => span_ok layer2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok layer9 i (Nat.zero_le i) hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 28) (goal 28) s xsE) : False := by
  have hl := run_len h
  have hlen : xsE.length = 4 := by decide +kernel
  rw [hlen] at hl
  have hlo : 3 ≤ s := by omega
  interval_cases s
  · have hc := covers_ok h
    rw [show covers 28 3 xsE = false by decide +kernel] at hc
    contradiction
  · exact closedState_sound run_mapPerm allChecked 4 (by decide) 34 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 4 34)) h)
  · exact closedState_sound run_mapPerm allChecked 5 (by decide) 53 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 5 53)) h)
  · exact closedState_sound run_mapPerm allChecked 6 (by decide) 201 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 6 201)) h)
  · exact closedState_sound run_mapPerm allChecked 7 (by decide) 6 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 7 6)) h)
  · exact closedState_sound run_mapPerm allChecked 8 (by decide) 4 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 8 4)) h)
  · exact closedState_sound run_mapPerm allChecked 9 (by decide) 0 (by decide)
      (Run.perm (by decide +kernel : xsE.Perm (state 9 0)) h)

-- A matching ten-gate circuit tests for a nonempty input and rules out all three
-- ways to have at least two true inputs across two pairs.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tenGateCircuit : Circuit :=
  ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩,
    ⟨.and, [4,5]⟩, ⟨.or, [6,7]⟩, ⟨.or, [8,9]⟩, ⟨.or, [4,5]⟩,
    ⟨.not, [10]⟩, ⟨.and, [11,12]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ten_gates_suffice : HasCircuitSize 4 fE 10 := by
  refine ⟨tenGateCircuit, ?_, ?_, ?_⟩
  · simp [FanInTwo, tenGateCircuit, Set.mem_insert_iff, Set.mem_singleton_iff]
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_10409_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_10409 :
    ¬ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => decide (((List.ofFn x).count true) = 1)) 9) :=
  PEqualNP.Outside.L_meta_10409_aux.mainE PEqualNP.Outside.L_meta_10409_aux.noRunFull
