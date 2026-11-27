import Mathlib
import PEqualNP.Defs

/- The normalization, finite frontier certificate, and its kernel proofs are
by Digger-Rockwell, from public PR 801:
https://github.com/brilliant-hq/pequalnp-proofs/pull/801
Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
This file renames the helper namespace and adds the positive bound wrapper
requested by L-meta-722. The certificate data is unchanged. -/

namespace PEqualNP.Outside.L_meta_722_aux

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

abbrev fG : BFn 7 := fun x : Fin 7 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1)

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

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

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

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

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

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

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

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def rowsG : List ℕ := [72, 1, 44, 42, 42, 17, 44, 18, 18, 12, 18, 76, 18, 18, 44, 44, 42, 42, 72, 76, 42, 42, 20, 20, 18, 42, 42, 18, 18, 44, 10, 44, 18, 10, 76, 10, 10, 20, 10, 12, 44, 42, 44, 20, 20, 42, 18, 17, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 17, 20, 44, 0, 0, 1, 1, 8, 10, 12, 16, 42, 44, 44, 72, 76, 76, 4, 72, 2, 84, 81, 81, 34, 84, 33, 33, 68, 33, 76, 33, 33, 84, 84, 81, 81, 72, 76, 81, 81, 36, 36, 33, 81, 81, 33, 33, 84, 65, 84, 33, 65, 76, 65, 65, 36, 65, 68, 84, 81, 84, 36, 36, 81, 33, 34, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 34, 36, 84, 0, 0, 2, 2, 64, 65, 68, 32, 81, 84, 84, 72, 76, 76, 4, 88, 9, 46, 46, 43, 49, 108, 26, 50, 28, 82, 9, 19, 22, 37, 52, 66, 26, 73, 24, 6, 9, 22, 24, 48, 104, 106, 24, 66, 60, 24, 41, 3, 26, 92, 9, 14, 48, 74, 13, 100, 3, 6, 52, 28, 48, 6, 9, 5, 9, 24, 3, 11, 13, 19, 21, 35, 41, 24, 6, 24, 3, 48, 5, 73, 9, 6, 6, 24, 58, 45, 96, 24, 5, 77, 88, 104, 66, 85, 85, 83, 50, 92, 97, 49, 100, 41, 66, 35, 37, 22, 52, 9, 97, 74, 96, 5, 66, 37, 96, 48, 88, 89, 96, 9, 116, 96, 82, 3, 97, 108, 66, 69, 48, 73, 70, 28, 3, 5, 52, 100, 48, 5, 66, 6, 66, 96, 3, 67, 70, 35, 38, 19, 82, 96, 5, 96, 3, 48, 6, 74, 66, 5, 5, 96, 113, 86, 24, 96, 6, 78, 104]

def xsG : List ℕ := [0x2c295846531453359c643a3fb8289802458320240000625b5f33359800187f8800000000022, 0x643a3fb82898024583202c295846531453359c00187f88000000000220240000625b5f333598, 0x64c88a15d942050e24c64c88a15d942050e24cec818001da4a0c8ca44ec818001da4a0c8ca44, 0xc810000014416050441d73163690deeeae0adf70000000004000c08017ee100027dee63fca5d, 0xe043002920a700c17c93054c4382669cab7a10e010002700a633c05c0100c00d82119c035a0, 0x93054c4382669cab7a10e043002920a700c17c0100c00d82119c035a00e010002700a633c05c, 0xd73163690deeeae0adfc8100000144160504417ee100027dee63fca5d70000000004000c0801]

theorem rowsG_len : rowsG.length = 304 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 152 := by decide +kernel

theorem maskG : mask 152 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 152 zs &&& lo 152) ≠ lo 152 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 152) (goal 152) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 152) (goal 152) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 152) (goal 152) s xsG) :
    ¬ HasCircuitSize 7 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 10 h
  have hr : NatRun (mask 152) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 7 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 1
  | 6 => 33
  | 7 => 538
  | 8 => 598
  | 9 => 33
  | 10 => 1
  | _ => 0

def HT : Nat → Nat
  | 5 => 0xdd611f
  | 6 => 0xfe53d3a3d64f1a63c594f978b6e0a5adb61f2113a4a530079d85540f8bba5dd2886a48b285ee035564f9e51854d18ed04fba46784a6e940236183c8f33c93aea318daced2e2562d129c16e89271af4e1236a0ade220d47f71fe8f843157c290e0dfcddae0df576c20ccb5e260810c1cc078bbeac0713d0e806c4fd940610c25400062461
  | 7 => 0xfd96343dfb9783a0f5283f55f236e75ff1b60d88f17b05dcecf766c0ecf248d5ecc9c4b8ec3bdc78eae7ba6ce9bd6337e62dd1bfe5ac1669dff3fcf5deacc987dc773d50dc0aad49db3fd8bcd9910c14d78910fbd6ae5b78d5a2fcaed33cc1e9d26dfc1acfcb0c08cfbc9f39cedb0afbce92a99fcd031a03cc80da0ccb401a39cb008f84c95d108fc8bb62fdc7bfdd09c6278029c5a6782fc56ac579c54bc3c1c4ee630bc41e167ec3ae903bc29a700cc21613edc1a69267c163e0f0c136d903c13368a3c10aeb3bc0f38f1fbfeb81f0bf7ebbefbbd8d72ebb16946cb9254f3cb924e0bab7ab970fb79d5131b76cd2cbb607e29ab2115fa8b08fcb2fb065ab5caf9f313baf3f0fa0af1a9febae11d4c9accf2d42ac0d4dc2abd5c216abaf6c63ab56c7e4a8f88c49a8612040a85794f5a7f7cc56a7b60965a76f74f3a723d088a5dd00e7a4688f14a3c71584a35e2825a3190520a17c0f24a125de98a0e670eda064b9eea05017799fb102b49eaa2add9e69978b9e57df0a9ce57ba69cb252009be09b979b2845d19a657a4e9a37f4c799e0e2dc9958f94b98b6c50e9882c6ec97eb1110974ce91b96f5fdb896e7e80296e5debb96ca047596c69a9a95a7c17e950c4aab948686ba93e313ab936a9e8192b28c3d92542ea69248aad891d107cd9017c6769002d4218fdf9a238f1c08648ea9377c8ea44f308dfe1da58d7e73938d236d948cebd1398c93c9548a7d45848a466f868a2407c48921ecb788da42f388cc7828878d837785b7423a8585081d854268648512c72e84eaf1c38496c9af84788b18839a1f7c835188ac832d036c8312f79c80b3c4f680a722917ffa18eb7e6c3f307e0776f47dad418e7d5391e07d2f66907befe7a27bab044e7ad6f9a37a8a06df7a2ac0f079271a60790e446c788b7bdc785d4c7e78212b1277b5102f77927fc6771360c376d2f74275891b0f752df6bd74e9988c7462fdfa732313d772691a9172236ed171dd4fea71d742ad71c1a12271809fb77141c89170e38f3570d7e3f4708907936f8f320d6f647eff6f4708746e5104176d307bc36b4e62c26aca4c896ab8c48b6a2cdd6e69958d08695687b36778624f675dba75673c336266e9479d66782cd76611036665d570cc65ce8e1065a44656658d31556585f0d7657a23fa653334056515b07f64c25f1864a4287263a6e7c963a0bce7634b8974628cb536626cfdcc623cd0c06209485961e5276b61c98c59611f3cb9604e23525fee6dcb5f7af4145f4e3b745f446cc35f2fdaac5f2164d45eda2c125ebd7c575e74df1e5e2220545e12bed15dbb742b5db567495d0430b75c5c95495b3c2df45aa854c15a37b4e95a11b6b758ef4a3d587ec319587b3a195838e3e05804ac4557f477c957607c3756f13806566fc32d55edcaac55a409c15538b87a5506be2654b43b2154aa01f4541295e453b5def553ad85a65385665352d5cb0452276b0b522747135211ef0d516bbd825155caa35132ecbe50f9ee88509619b550833c8d5049705f4f8995d84f2fa5ba4f03e43e4ee609074e9c92844e770d3b4e6f7b334e27a6c14dfdfaf14daf9f864d817e4a4d2155fc4c7d16344c6c05e74b2acac34b1659524ad9140e4abf659849fe06c9498e2f72496a896a493ffddf48a832294839ea2147d9ca92473e5aeb4684d09d4627c4c14626f4ff44e82467441e658b42abcbe9427bb2f6425762d9418d50f1410d181c40a54ae0403b77b43fa8632c3f29ad063f263fc03eee8b763e9ef0f33e92fec93e54328a3e52b2b13e4499803e23e8fe3d5a09743d59124b3c954c973c5d837e3b65837e3b52f3553a334cb2396185ab39378dcb38ffdb2538e2a866388672e3382ad20338005e5b37965656378bd75a3779f1e0376d9a1a3764e4523763737436f046e136847c523677f0e7357cc2493541e30f3514d0df3463d30b34553a1c33ff310c331f73f6330ecdaf32728a4f3226c88732130ade31dc63ce30f577fb30e284a830aeec71302f1d942fada3ef2fa1e1282f614b182f5844752ec2ea062e95a0f12e94b2b62e85fbde2e794d532e263ca92d5d19702d1f09912d032ce52cf7410d2c798f3f2b79f8622a93a7b529e4664229793b5a2961de482916c061289654cc2890cf6f284732bc27f473f2272305492719be3c271487a62692bd382649208525f21b2c25d056db258302542526307f25122b9724eef5622489406a24816d44242e7e172422e17b23cdfd75236b8b6822bf1c92226378312250dab621887bfc20be5f4520bcb00620aa000c2063aef5201a9e9a1fdb250c1f9d7f091f053a371ee8ec381e878e391e5c5c0e1e4e88dd1de4e9821da8c2aa1d5c1a861c8c66c71c44e4811c2ca3681c062ced1bedd1421be8d9f61bc3ee661bc1160c1bb9b09e1b7e87cb1b08de681ace1c141aa837701a97806b1a7561cd1a5a16291a241b4019ac366d198f4971194f1ce81929eb801918cc5519098ce1189d0d7117fd0fdc17fb359e17e9285d176bbf8c173798a716fa722a166a0e0e15dc9b2b156c0b0b14ff0da214d5466a148881c5140c4a9d1376f37c133013ac131385a812d4ad9f12d353e2120a3261118bfbb811606d131127e8471127dc8710fd7a7a10ed010f10eca7d410d816a410c4e517108ec73a10484a76102295ec0ffa185f0f957bbb0f188c360f090b640f07dc5f0f004bab0eaef3c40e9596dd0e68266d0e6333d30df3cea60deae7480dc980d10da8c1620da81bcf0d7587f00c4c59590c354a1c0c2d98a80c2c7df50b8f18910b327f680b312c8909499bce093f7c8d08dffe480855c444084d3eb2083cf03907f6caa607cb57bb07b8000c0782ba820761c02e06e3bfd906e1952306ced56e06b4d7a80664569a064d00c5064292490611512e05f8b86f05639b27054941800505dba70502e6f6044a095804218d7b031613a00311184c02b59792028eeffe01fd25a101e5a81e01b0c16201ad7fd6011e4dc0011c3b7a010201fb0080ceb3000fba77
  | 8 => 0xf844eb18f75b7806f68a4f60f471fe0bf298e003f010bda3ee57469dee3b3ffceb48a7a1e9bd6337e49a36d4e295095de2847438e066f18dddf519bbdd3f0a5cd7a1a777d70b2e22d607f0f0d4c7fc1ed3e1e5c4d31c2be9d193e500cfcb0c08cefc8e4bce4b95f9cc59c06fcaf83f8bcaaa77fcc9a5eeafc95d108fc928233ec7bfdd09c7734453c68d3205c58eef19c56ac579c472ba57c423c0c7c32d7ec4c31c9544c2235909c2173eb6c1d6dd10c19d3d19c057e972c02a2b5bc0278946bec3f443bdea7445bc6b33a1bbbc8696bb92301cbaf9af33ba83d9fbb99a5a5fb84c6ac0b76cd2cbb591cac0b188eee6b1330ff2b0c2ecdeb065ab5cafa01d56af9400adaf84c1c8aef4ed79aeb0bf2eac56c7d6ac095859aacabe7daa9b227aaa8f91cdaa86b36baa39452baa0fb79eaa0e6470a974ef36a9558699a83d5a87a76f74f3a62db652a5ec56b0a5dd00e7a46b5062a45da683a44aa94ea3b55f9ca3b1bceaa29cc882a249187ea1f3ca0fa1dcbb6ea1920403a16299eca09238b0a091e144a06f10319f9323909f67d2219eaa2add9d48183a9d3af5819cb84ab09cac4b569c9fc5cb9b8894d19b541f2f9ac376ae9a5ea04099ff604798b617f9975958b6973bc578966ec7b696185b7b95f89e9595df916a94ca93299491a0439401996693a059f9929684959281dfca926a2e28925527eb921ec29d91e5743591b935d691416b74913886d0912da89890304f2b8fd0176c8f9899cc8f879c278ef96d818e8ff4728d23f2d78ceee8e28c65d4fd8c1b89898bffdbae8bce1e378baa95d48b7d14de8b73a33d8b5f769e8b01cd3b8a8933fa89bf4f8888ac0b2288ab77ab88383d818790d2b5877ae6e88658568084c9408384a5f16b8468915584674ed783c5201483ac0fb8838d30628264224f825c93c781ec0a3481c4dd0180d0afd58093a509808ff3788080f8668041792e7f8332737f70dd097e4862bf7cbd0b497befe7a27bddcfaa7b0563907ad6f9a379e31172799dabdf799ab6a178ff6a9d78c741177807d7677804ba9b77881d007748a92f771dea927708f0a076198e2175dbabf77579f13d7564e56a75616bfa753a58357467a984737ba1a37327da377309cbae72972da0728f050772461c7f72236ed171abba1d717ef6307141c891712ad972704cad7c7002a4ae6fcd139e6ea0ef846e616d646df0627e6da58baa6d61f8ac6d307bc36c104ceb6b4e62c26b3a47bf6b0a0e626b02621a6ab8c48b6a2d6e3e6a01b083696d9441696319386962df9c68ca5d00671a6bd8670fbd6166acf40f65f489ed65b72d7264ee198c6469fc0e6416c52e63f4022063d71a9863caa3f663b05acf638f00fe637e5fdf631c334962f7f8a162da4b9d62c93f0062b1b5f7620c9c65620c2bb161f22f6f61cd64186187c3d76185a49e617474eb611f3cb960cf33886087f5716037868660161a845fd3858b5ef9b7155e59d3765dcc401d5db83f975db567495d740adb5d26d4385c9ed6775c74e8c65c545a6f5bee281c5bb82d475b87bd555b0ada6e5a54a78a5a11b6b759dc679359b67e9f59663e725929515a58ef4a3d5810af9857ebaf8b56cd827c56c2a3f95650920055d3a76855298927546de3a75447abb8543f279c53e287b653c3328e53a8fdde5391a326527351e651aeec11517d531a50ff9ddf504e4f3c4ff27dd84fa4b7364f8c27894f8995d84f6500014f0caaff4ee609074e6f7b334e68f8104df6d3d74dcc94d64dc3b5084d8ce2a84c946ceb4c8d89374c85a47a4bdc90e54bbfe4d54af5730c4acc59104a53aac24a13cccc49ca858649ca834149c5f65d493d6ab448e5bd5248b19445488cbd67482a7ffd4826ceeb47d9ca92471c50dc46f65ca9468ed220456054fa4526c8db44b9547944925e224445e229444548d84421c1d143915f9f437cb5b042de7ce6422a8208421f851541f9ff45411f4c224110d1e440db443e40a54ae0402aab263fa8cf0f3f29ad063ecbfa643e68c3203e4f43413e4499803e1d8db53d9b91793d99b6473c8963e43c60638a3c18701d3c0fd2a43b725a783b52f3553afd2d103ab1b7373ab0b1173a4b5ab63a28ba0d3a1f011a396185ab38d448fa38b3b281381c8b8b3817f5a737859f553764522c3710e57836c6495436876b84361a2b3c361328ef35dc16a634dbf99b3446020b343ac7bd33ff310c33b55681337cf3d43322c5ac3317a8543248a15e31cce117318ca120317595ef315f7129315e83fb31314c51312fc38c311fc44730dfac562f99e1002f5844752ee594f92ece9e922e95a0f12e94b2b62e35f0762dff1e162d81fa032cffc4a52cfe96e62cd91e732c896fc32c75d1222c4ecc532bde7f4f2b46c8892b46109b2a765ff42a35072c29e0524e29afa622290e671e28f5bdca28a73f7e28910dd7284732bc2837b005281215d5280dab5d27f473f227f3224727f050de278a9335277e62a72724debd27100eb626b1200626ae719d26a5f493264715dc2646e37e2644212b2626ae0d261f55d425eeb2ec25c4ab8d2549d4c1253dba9a25022efa24f8441c24ee807a24e7b7b224bdc48324b22d5c2468ec63243ef5db24049f4824039b0d23d343b6236965d422b9d6ea222121fc2216386221f549fb2128927520d92bab209fd61a209474151fa00e4d1f7dd0991f3659131f0629771efbdcc51e826cdd1de4e9821dcd259f1d63f6c41d1b9d871ce4cb271c98a1981c8f25171c66bd881bf0bf271bedd1421be8e64b1be571b61b3479641aa8ec261a8a9fb519e07f54197b53e9192bc4fd1929eb801916563118955333182ab7c617ef9b2c17169dbb16affb5816a1122a15e89f871596cd17159238731583769814c13473143311d713ffc2a213f599f513ef2f4213d3a8c613c29c7d138a40a313899981131431b312f44bf512e9481e1260199c122999ca11d1ac97110a798610c92f1e10c4e5170ffa185f0fd237200f44e1f50f1dd2520f07dc5f0eb8e78b0e55dc110e10f3970dde152d0da60b6a0d8f50140d72285e0d2eb0410d1da50b0cd0dd4d0c83ef610c5d99290b981fda0b3a57aa0af5a8850ad2de9709f111d5093f7c8d091b410c090ef41d08de816708c288a708bdff080898958c084248f5082854bd081f7b8f081a2ee60810f5dc07fffdff07f6caa607dbf4a307b3820607469d600721d2090646dbcd0633e4ea058d81b7055e92f9053d418a0524bd0404c608ab0499596a048469db042165a003edc27803e9516c0355853a02ed397402d4dc53029506d70282d467027aae2b022dda50022b8f8e0217631001fd25a101d9d47d01d52cda013f3f480100f65b00b759a8
  | 9 => 0xee3b3ffcd4c7fc1ec7bfdd09c2173eb6bc6b33a1aa39452ba76f74f394ca9329925527eb88ac0b227b0563907ad6f9a378c7411775dbabf77141c891671a6bd85b0ada6e5391a3264a13cccc40db443e3e4499803c18701d3afd2d103ab0b1173a1f011a2bde7f4f2b46c8892837b005278a9335236965d4209fd61a1efbdcc515923873
  | 10 => 0x7141c891
  | _ => 0

def PT : Nat → Nat
  | 5 => 0x29320
  | 6 => 0x1843615ec640760c0e0b18a9723132c66a2bacc482d18a2352063d0684608881af98907e2065e26a2bacc542d98ab9b33102c44c7a0c84c218917331408a6a0d78c509718b12f31420c4402dcd80c21a085b3612e662a110c10c413114d313
  | 7 => 0x13f08015f371000660ae4c055c1b890c33085860c9f0c05a9980b852071c820292080cda1a02f6a02930ea0130d05a408187c105840402c74d41e41a02957241b440c0e4989a408205030118e6c091c409ab9b00597301cc6a0ba841175ba815d34138e200000c40d69b09ec3513b020c7b4d04381b004d3715ec202c14810011b88f03616ce40cba840c6d1021e710635e6e26a8d81929820d63401566e0f7cd805493814a36215c6c0128c041d9b0bc63104046a0570d45ab1a82eaa6127c2043b4dc1ef1b808510094a60206c9001c1b03672702f22086d0d402c580bc836007c200f74d80ec082bf03705e6200ad4cc5758812f21032c46e0aa885db11818c01063ae680428880399281b910448d6c2b8cd44728830e63405d6e20a34d44d51a02283160066830d8840430812973610b2e80be8818428829a731529a68078040c469a819810152820a9a8d402c39018733016c62871840c5298a0d736028e208334dc41d9809e11022fc6c24b8d854698b1802076a86e066040c8498285810029a6c0bb8d01479038c010048c208488dc1a39a811b37034c62c358d40311a896b37008c6288649c04a9a80c830547f642d9c8147208207d1043c2c484fc4156a9a006c320492462028401f81b02eab0495460601481575bb00861046ce40639cd8042080b9d3613cc202588d02531281e07211c8206b8cd85f89a00c93207d4602211c90171a810c340000000d3c8502c08114d35007c2080148112d98b16335002244000cc06299b80c821033020402c414da1b83c03602ec60cd54d00d79a88841031006a263881c698828d2b6232c40c0fc4145b18a8273503f840e5c04104331227f105722602ee88110c92020d30409a6a25c4418521b09e01001a06070bc4024c0802ee3301ca2051689409f0801863503fe60234c4041f0810e3371070680f00d00bb181af937010068275cd410b1821ac351064602d0c405ee1b800a10225c62e8f8409dd90299910430c6c11a4d807253110136018220a216d84698819ab3701c820af7cd010c1032f71058386020dc984641a01e11042626e27d4811089a8aac270226680290d44649b805530130c6e0bf8dc1a18811c71058f2602704d446088082736007668235cdc1359a00c332348e20c36c81c2c881a6d3507da40cc45c950b1b83d53703d86e2c4440c599b01d81044d46e0219c84420820e4a0138c20c30440d0c102be210085e20a9f4d44091028143308ec40696cdc4261808b63161006e2c444110d182a3f10011a6600ac804449021af36105e6e021c4040e13046f1000ee6029f0c50ec880a477247f840a2144083710380a1047b86a068cd09e39a8b313505a86a0368814461b00383700a06c3265cc181983af610048e20034c4090b1a80a63013ce2007208402cba802e34016668051840e370828e33511b26e0118c581311388c37034e62e764408011b0b431030d6660bded88001b008472329a6e06d4c850788284d36164466112480dd79a83613411646e036c80dca1282d53600026e11a8404241809701000b2ec09a4d40011a88003502f220c618d006908212e31410c200fdcc05b71023f035075840f0e8d44608822a9721180204aa0400739b80e5b1204e6e0164410cf90b8e330116e6e2e4cd015c9b0950306290602000d014a880311105102602f7cd417c9a812234010e2065c44140818992a22037220c91c40c231b89ea2071a620001cd40cc882847315406660d50d404308319810032c40e210418d51a809c2205d86a2a5440c3e0831e710310b4a20ecdc4728804693504d46c0688c8d08180b55360244660b90d41f69038eb30735e6291f4402375b105810664a6a071c4041f083324360620200ba9c4e24102b9235056a6a24fc40c591903481000b36c4ad0d0423980c482068746822c8d40ec881a9510464a6e04f4d40899b002e3603ce2082f0c55251b82f71033cc20abadc9575b981e11062c66c00e8d4554882adb3705f2680d988108e9082d437038c204c4188d7c9b040a10114a62ebac4001f8819123506c06a26d4d809f8808813612f220ac45c90461a04381008f8206144d05311b80a92061486207f8d8434991a5b31504c608320d810b1b03421064986086a4c1a309b03dd3405d62026604181c9a8123360
  | 8 => 0x1a73180d72707420003c4181a7a880170404d40609395019881826203057c600004180f580834e210614e00c6d401b39804075001a202093cd0075b900c6040642000dcd401038a0291070036420c84140ddb8801a0101e680085c1812880018e0200ec420afcc00c083022604024ea0086c801af82014102049cc60484081630282e6050214c0011814015b8040100049ea005c4001008181d725018e2e05ecc02039803a30502220a0804080f38903a70601c6a00869c01efb000671705020802041400380826103031cc607041003081012b50049c2007c40802b03020a5003d4020ded0012081003106028e080604140d38b011b50079c0200c40016d3002da4002420a0f98180c700808a5003420601dc180e08180170505e20207d8081b19801eb410214a003a90018db8000a6105ee0403988c1f302001104021684076dc00d082002a6001e20800acc010883826603049ea8039d001b080018f3102c20603ad800c7a1825e32034c080a44000c7290046210402080544140db8180a1070076c004dd801e701012625018e4a07dc140051880910605ec0e03041015f0280270402b4e00abd800308381b10503c20206540017b0300410600ce0e035c4c0b882803750042e060e9c0c133818156060382000b69c01308000e1030256c003040c08da903110005cc0602981c0e08280210404e208067c141030801d305072c06093c8012881803b1207be0402840008881025e40064c0a03440804d9800662700a20606840400080824f1000420602d81015f22829b70034c060f78140030080070205166007ed000b08201c30605cc0404ec8400000014104020208019c1006530823713028c0a03ad000408000ba6001e6600004081b1a000a70304ec42039d4006103819f40055c2006780c07bb800b70707e200089c040db030041000176c000981010b0a00772406f6a0022d400d88001db050436a00e9c140330200c60300f442046cc80588081d107006e2403840819b1082fb61057eca063c08060828093600516800af900075a8031704058200019c4c0d383001105010208070dc010d2001f10400ae0c04dcc01a718021715016206011c1412a818137210806a003c41415a8281850600ce460ac4040388302f70400820a0444000451802ea610042020f3c041fb0180d6050654c0075c0c0e08102450201168002c4100fb81000b71057e0a00181c08d2000eb3003a6080f78100038382b1020266a00018100c79a801602057e640afd080db83823107033c0a0a44140008181cb0606d6600afc400e388019e6002144205c41810b0b80f10000546002ec84018838131030302080f39800388183cf30033c860bdc1c1e72281410702420e086dc00453002bf15061660063c481f538022100033eca039cc01738181a7010046a00be8040308001234000ae46086d001888182510400348208d81c0239303810005d6a2059c400238180d107080660051c04043b001271000220006541408380819101079c6008980c0ab92011b6101eec0076c100b53002be60038ee00a1dc007b90811b5101820c0c4410045b000e37007be0a085c400888382f10301ae080284181ef82014604057c2402c41409da000d7050102040f3cd000301819102018c0c05ad8015881828370033e640bacc411b02819f6300c20a05ad4016b0181e605052204039c400638083cf65064c0601440409d98019e4605e2040269c00eb90802105078202029c400eb828185040246e00e58100cf200087100454420b440c1f302809107026ee001c4100db91840b6003ac2c07a9000c73282310400cc0e0459400052880a7040714a0063c0c0952800ca0702a2060d395016391807605033e2a0d380403380826a40036c0a05dc840e383016b700056a0011c040c281809103055c04045884060800027100054e0104d8009882002b10003662006d84090800396060114800afd14079b0011a700462060a440c00da080c60700ac060af98c07d90813360000e060ec40c05b908011070382020b9c18033018206030034e20914001cd3800170601d6e003c41c0f52082eb010074a0035c501a79802110104f4c00018181c08180d707031ec0067848145a8007703024660074c0c15a820407600456e206440c08d18035e04083660068408085a001560300ee4c06d81c03b0301db210222060d3c0401881014100069e6805ed00145b001025002c204071c100bd9083775005e208049d001d582812b7003960606c41c045b801410606820202dc1409083010a6202020c08d884205a8003b2002f4600118040cf8080b10201ac4808581810d1000160502e20e042d8015781001b0105ce0a08d81800da8827b31057e620abd001508303170605cc08046cc01bba0001a21
  | 9 => 0xe54001e6800440000731800f50001c20000408007aa001e32000a08003c8000881801e40001e2000000000799001503000a040078d0007a9001104001ca0003cc000718000f40001c40007d9000f32000e60003ec0003d8c00f29000500
  | _ => 0

def dA : Nat := 0xfffffffffffffffffff0000000000000000000fffffffffffffffffff

def setA (xs : List Nat) : List Nat := xs.map (moveBits dA 76)

theorem runA {s ws} (h : NatRun (mask 152) (goal 152) s ws) :
    NatRun (mask 152) (goal 152) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 23 j
    if e = 0 then xsG else
      let r := mv (mask 152) (e % 4096) (St d (s + 1) (e / 8192))
      if e / 4096 % 2 = 1 then setA r else r

def S (s j : Nat) : List Nat := St (10 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 12 0 (NN s)

def ori (zs : List Nat) : List Nat :=
  let az := setA zs
  if hk zs ≤ hk az then zs else az

theorem ori_ok {u ys} (h : NatRun (mask 152) (goal 152) u ys) :
    NatRun (mask 152) (goal 152) u (ori ys) := by
  unfold ori
  dsimp only
  split
  · exact h
  · exact runA h

def poolG : List Nat := [0xc53008ac320b8, 0x1380202cdf2acb0, 0x1380713ca8320ac, 0xc5301cab2e099, 0x2c03008df2b0a8, 0x1384f01cac2e0c8, 0x13c0714cdf2e0a8, 0x2c53138ab32099, 0xc0714cb0264ab, 0x2c5301ca82c0df, 0x13c07138ac320b8, 0x85300cac2e0c8, 0x1380714cc82e0ac, 0x14c0702ca8264b8, 0x80714cc82e0ac, 0x1340112cac320b8, 0x24044000df2acb0]

def Z (s : Nat) := bar 152 S NN idx ori poolG s

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel
theorem z10 : span (Z 10) 1 0 = true := h10y0
theorem h9y0 : span (Z 9) 11 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 11 11 = true := by decide +kernel
theorem h9y2 : span (Z 9) 11 22 = true := by decide +kernel
theorem z9 : span (Z 9) 33 0 = true := (@span_join (Z 9) 22 0 11 (@span_join (Z 9) 11 0 11 h9y0 h9y1) h9y2)
theorem h8y0 : span (Z 8) 12 0 = true := by decide +kernel
theorem h8y1 : span (Z 8) 12 12 = true := by decide +kernel
theorem h8y2 : span (Z 8) 12 24 = true := by decide +kernel
theorem h8y3 : span (Z 8) 12 36 = true := by decide +kernel
theorem h8y4 : span (Z 8) 12 48 = true := by decide +kernel
theorem h8y5 : span (Z 8) 12 60 = true := by decide +kernel
theorem h8y6 : span (Z 8) 12 72 = true := by decide +kernel
theorem h8y7 : span (Z 8) 12 84 = true := by decide +kernel
theorem h8y8 : span (Z 8) 12 96 = true := by decide +kernel
theorem h8y9 : span (Z 8) 12 108 = true := by decide +kernel
theorem h8y10 : span (Z 8) 12 120 = true := by decide +kernel
theorem h8y11 : span (Z 8) 12 132 = true := by decide +kernel
theorem h8y12 : span (Z 8) 12 144 = true := by decide +kernel
theorem h8y13 : span (Z 8) 12 156 = true := by decide +kernel
theorem h8y14 : span (Z 8) 12 168 = true := by decide +kernel
theorem h8y15 : span (Z 8) 12 180 = true := by decide +kernel
theorem h8y16 : span (Z 8) 12 192 = true := by decide +kernel
theorem h8y17 : span (Z 8) 12 204 = true := by decide +kernel
theorem h8y18 : span (Z 8) 12 216 = true := by decide +kernel
theorem h8y19 : span (Z 8) 12 228 = true := by decide +kernel
theorem h8y20 : span (Z 8) 12 240 = true := by decide +kernel
theorem h8y21 : span (Z 8) 12 252 = true := by decide +kernel
theorem h8y22 : span (Z 8) 12 264 = true := by decide +kernel
theorem h8y23 : span (Z 8) 12 276 = true := by decide +kernel
theorem h8y24 : span (Z 8) 12 288 = true := by decide +kernel
theorem h8y25 : span (Z 8) 12 300 = true := by decide +kernel
theorem h8y26 : span (Z 8) 12 312 = true := by decide +kernel
theorem h8y27 : span (Z 8) 12 324 = true := by decide +kernel
theorem h8y28 : span (Z 8) 12 336 = true := by decide +kernel
theorem h8y29 : span (Z 8) 12 348 = true := by decide +kernel
theorem h8y30 : span (Z 8) 12 360 = true := by decide +kernel
theorem h8y31 : span (Z 8) 12 372 = true := by decide +kernel
theorem h8y32 : span (Z 8) 12 384 = true := by decide +kernel
theorem h8y33 : span (Z 8) 12 396 = true := by decide +kernel
theorem h8y34 : span (Z 8) 12 408 = true := by decide +kernel
theorem h8y35 : span (Z 8) 12 420 = true := by decide +kernel
theorem h8y36 : span (Z 8) 12 432 = true := by decide +kernel
theorem h8y37 : span (Z 8) 12 444 = true := by decide +kernel
theorem h8y38 : span (Z 8) 12 456 = true := by decide +kernel
theorem h8y39 : span (Z 8) 12 468 = true := by decide +kernel
theorem h8y40 : span (Z 8) 12 480 = true := by decide +kernel
theorem h8y41 : span (Z 8) 12 492 = true := by decide +kernel
theorem h8y42 : span (Z 8) 12 504 = true := by decide +kernel
theorem h8y43 : span (Z 8) 12 516 = true := by decide +kernel
theorem h8y44 : span (Z 8) 12 528 = true := by decide +kernel
theorem h8y45 : span (Z 8) 12 540 = true := by decide +kernel
theorem h8y46 : span (Z 8) 12 552 = true := by decide +kernel
theorem h8y47 : span (Z 8) 12 564 = true := by decide +kernel
theorem h8y48 : span (Z 8) 12 576 = true := by decide +kernel
theorem h8y49 : span (Z 8) 10 588 = true := by decide +kernel
theorem z8 : span (Z 8) 598 0 = true := (@span_join (Z 8) 384 0 214 (@span_join (Z 8) 192 0 192 (@span_join (Z 8) 96 0 96 (@span_join (Z 8) 48 0 48 (@span_join (Z 8) 24 0 24 (@span_join (Z 8) 12 0 12 h8y0 h8y1) (@span_join (Z 8) 12 24 12 h8y2 h8y3)) (@span_join (Z 8) 24 48 24 (@span_join (Z 8) 12 48 12 h8y4 h8y5) (@span_join (Z 8) 12 72 12 h8y6 h8y7))) (@span_join (Z 8) 48 96 48 (@span_join (Z 8) 24 96 24 (@span_join (Z 8) 12 96 12 h8y8 h8y9) (@span_join (Z 8) 12 120 12 h8y10 h8y11)) (@span_join (Z 8) 24 144 24 (@span_join (Z 8) 12 144 12 h8y12 h8y13) (@span_join (Z 8) 12 168 12 h8y14 h8y15)))) (@span_join (Z 8) 96 192 96 (@span_join (Z 8) 48 192 48 (@span_join (Z 8) 24 192 24 (@span_join (Z 8) 12 192 12 h8y16 h8y17) (@span_join (Z 8) 12 216 12 h8y18 h8y19)) (@span_join (Z 8) 24 240 24 (@span_join (Z 8) 12 240 12 h8y20 h8y21) (@span_join (Z 8) 12 264 12 h8y22 h8y23))) (@span_join (Z 8) 48 288 48 (@span_join (Z 8) 24 288 24 (@span_join (Z 8) 12 288 12 h8y24 h8y25) (@span_join (Z 8) 12 312 12 h8y26 h8y27)) (@span_join (Z 8) 24 336 24 (@span_join (Z 8) 12 336 12 h8y28 h8y29) (@span_join (Z 8) 12 360 12 h8y30 h8y31))))) (@span_join (Z 8) 192 384 22 (@span_join (Z 8) 96 384 96 (@span_join (Z 8) 48 384 48 (@span_join (Z 8) 24 384 24 (@span_join (Z 8) 12 384 12 h8y32 h8y33) (@span_join (Z 8) 12 408 12 h8y34 h8y35)) (@span_join (Z 8) 24 432 24 (@span_join (Z 8) 12 432 12 h8y36 h8y37) (@span_join (Z 8) 12 456 12 h8y38 h8y39))) (@span_join (Z 8) 48 480 48 (@span_join (Z 8) 24 480 24 (@span_join (Z 8) 12 480 12 h8y40 h8y41) (@span_join (Z 8) 12 504 12 h8y42 h8y43)) (@span_join (Z 8) 24 528 24 (@span_join (Z 8) 12 528 12 h8y44 h8y45) (@span_join (Z 8) 12 552 12 h8y46 h8y47)))) (@span_join (Z 8) 12 576 10 h8y48 h8y49)))
theorem h7y0 : span (Z 7) 12 0 = true := by decide +kernel
theorem h7y1 : span (Z 7) 12 12 = true := by decide +kernel
theorem h7y2 : span (Z 7) 12 24 = true := by decide +kernel
theorem h7y3 : span (Z 7) 12 36 = true := by decide +kernel
theorem h7y4 : span (Z 7) 12 48 = true := by decide +kernel
theorem h7y5 : span (Z 7) 12 60 = true := by decide +kernel
theorem h7y6 : span (Z 7) 12 72 = true := by decide +kernel
theorem h7y7 : span (Z 7) 12 84 = true := by decide +kernel
theorem h7y8 : span (Z 7) 12 96 = true := by decide +kernel
theorem h7y9 : span (Z 7) 12 108 = true := by decide +kernel
theorem h7y10 : span (Z 7) 12 120 = true := by decide +kernel
theorem h7y11 : span (Z 7) 12 132 = true := by decide +kernel
theorem h7y12 : span (Z 7) 12 144 = true := by decide +kernel
theorem h7y13 : span (Z 7) 12 156 = true := by decide +kernel
theorem h7y14 : span (Z 7) 12 168 = true := by decide +kernel
theorem h7y15 : span (Z 7) 12 180 = true := by decide +kernel
theorem h7y16 : span (Z 7) 12 192 = true := by decide +kernel
theorem h7y17 : span (Z 7) 12 204 = true := by decide +kernel
theorem h7y18 : span (Z 7) 12 216 = true := by decide +kernel
theorem h7y19 : span (Z 7) 12 228 = true := by decide +kernel
theorem h7y20 : span (Z 7) 12 240 = true := by decide +kernel
theorem h7y21 : span (Z 7) 12 252 = true := by decide +kernel
theorem h7y22 : span (Z 7) 12 264 = true := by decide +kernel
theorem h7y23 : span (Z 7) 12 276 = true := by decide +kernel
theorem h7y24 : span (Z 7) 12 288 = true := by decide +kernel
theorem h7y25 : span (Z 7) 12 300 = true := by decide +kernel
theorem h7y26 : span (Z 7) 12 312 = true := by decide +kernel
theorem h7y27 : span (Z 7) 12 324 = true := by decide +kernel
theorem h7y28 : span (Z 7) 12 336 = true := by decide +kernel
theorem h7y29 : span (Z 7) 12 348 = true := by decide +kernel
theorem h7y30 : span (Z 7) 12 360 = true := by decide +kernel
theorem h7y31 : span (Z 7) 12 372 = true := by decide +kernel
theorem h7y32 : span (Z 7) 12 384 = true := by decide +kernel
theorem h7y33 : span (Z 7) 12 396 = true := by decide +kernel
theorem h7y34 : span (Z 7) 12 408 = true := by decide +kernel
theorem h7y35 : span (Z 7) 12 420 = true := by decide +kernel
theorem h7y36 : span (Z 7) 12 432 = true := by decide +kernel
theorem h7y37 : span (Z 7) 12 444 = true := by decide +kernel
theorem h7y38 : span (Z 7) 12 456 = true := by decide +kernel
theorem h7y39 : span (Z 7) 12 468 = true := by decide +kernel
theorem h7y40 : span (Z 7) 12 480 = true := by decide +kernel
theorem h7y41 : span (Z 7) 12 492 = true := by decide +kernel
theorem h7y42 : span (Z 7) 12 504 = true := by decide +kernel
theorem h7y43 : span (Z 7) 12 516 = true := by decide +kernel
theorem h7y44 : span (Z 7) 10 528 = true := by decide +kernel
theorem z7 : span (Z 7) 538 0 = true := (@span_join (Z 7) 384 0 154 (@span_join (Z 7) 192 0 192 (@span_join (Z 7) 96 0 96 (@span_join (Z 7) 48 0 48 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 h7y0 h7y1) (@span_join (Z 7) 12 24 12 h7y2 h7y3)) (@span_join (Z 7) 24 48 24 (@span_join (Z 7) 12 48 12 h7y4 h7y5) (@span_join (Z 7) 12 72 12 h7y6 h7y7))) (@span_join (Z 7) 48 96 48 (@span_join (Z 7) 24 96 24 (@span_join (Z 7) 12 96 12 h7y8 h7y9) (@span_join (Z 7) 12 120 12 h7y10 h7y11)) (@span_join (Z 7) 24 144 24 (@span_join (Z 7) 12 144 12 h7y12 h7y13) (@span_join (Z 7) 12 168 12 h7y14 h7y15)))) (@span_join (Z 7) 96 192 96 (@span_join (Z 7) 48 192 48 (@span_join (Z 7) 24 192 24 (@span_join (Z 7) 12 192 12 h7y16 h7y17) (@span_join (Z 7) 12 216 12 h7y18 h7y19)) (@span_join (Z 7) 24 240 24 (@span_join (Z 7) 12 240 12 h7y20 h7y21) (@span_join (Z 7) 12 264 12 h7y22 h7y23))) (@span_join (Z 7) 48 288 48 (@span_join (Z 7) 24 288 24 (@span_join (Z 7) 12 288 12 h7y24 h7y25) (@span_join (Z 7) 12 312 12 h7y26 h7y27)) (@span_join (Z 7) 24 336 24 (@span_join (Z 7) 12 336 12 h7y28 h7y29) (@span_join (Z 7) 12 360 12 h7y30 h7y31))))) (@span_join (Z 7) 96 384 58 (@span_join (Z 7) 48 384 48 (@span_join (Z 7) 24 384 24 (@span_join (Z 7) 12 384 12 h7y32 h7y33) (@span_join (Z 7) 12 408 12 h7y34 h7y35)) (@span_join (Z 7) 24 432 24 (@span_join (Z 7) 12 432 12 h7y36 h7y37) (@span_join (Z 7) 12 456 12 h7y38 h7y39))) (@span_join (Z 7) 48 480 10 (@span_join (Z 7) 24 480 24 (@span_join (Z 7) 12 480 12 h7y40 h7y41) (@span_join (Z 7) 12 504 12 h7y42 h7y43)) h7y44)))
theorem h6y0 : span (Z 6) 11 0 = true := by decide +kernel
theorem h6y1 : span (Z 6) 11 11 = true := by decide +kernel
theorem h6y2 : span (Z 6) 11 22 = true := by decide +kernel
theorem z6 : span (Z 6) 33 0 = true := (@span_join (Z 6) 22 0 11 (@span_join (Z 6) 11 0 11 h6y0 h6y1) h6y2)
theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel
theorem z5 : span (Z 5) 1 0 = true := h5y0
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

theorem scr_xs6 : scr 152 6 poolG xsG = true := by decide +kernel

theorem root7 : S 7 355 = xsG := by decide +kernel
theorem root8 : S 8 389 = xsG := by decide +kernel
theorem root9 : S 9 18 = xsG := by decide +kernel
theorem root10 : S 10 0 = xsG := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 152) (goal 152) s xsG) : False := by
  interval_cases s
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have := run_len h; simp [xsG] at this
  · have h1 := scr_no poolG h
    rw [scr_xs6] at h1
    contradiction
  · rw [← root7] at h
    exact bar_all ori_ok checked 7 (by decide) 355 (by decide) h
  · rw [← root8] at h
    exact bar_all ori_ok checked 8 (by decide) 389 (by decide) h
  · rw [← root9] at h
    exact bar_all ori_ok checked 9 (by decide) 18 (by decide) h
  · rw [← root10] at h
    exact bar_all ori_ok checked 10 (by decide) 0 (by decide) h

end PEqualNP.Outside.L_meta_722_aux

theorem PEqualNP.Outside.L_meta_722 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 1)) s → 11 ≤ s := by
  intro s hs
  by_contra hsmall
  obtain ⟨C,hfan,hsize,hev⟩ := hs
  apply PEqualNP.Outside.L_meta_722_aux.mainG PEqualNP.Outside.L_meta_722_aux.noRunFull
  exact ⟨C,hfan,by omega,hev⟩
