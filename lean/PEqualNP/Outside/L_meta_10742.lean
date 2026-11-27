import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10742_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run1T {α : Type} (inv : α → α) (meet join : α → α → α) (tag : α → Bool)
    (y : α) (u : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop,
    (∀ u0, u0 ≤ 1 → P u0 [y]) →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), s % 2 = 0 → tag a = false →
      P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (c = true → tag a = false ∧ tag b = false) →
      (ka = true → tag a = false) → (kb = true → tag b = false) →
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 2) (a :: b :: r)) → P u ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {tag : α → Bool} {y : α}

theorem Run1T.done {u0 : ℕ} (hu0 : u0 ≤ 1) : Run1T inv meet join tag y u0 [y] :=
  fun _ d _ _ _ => d u0 hu0

theorem Run1T.perm {s xs zs} (p : List.Perm xs zs) (h : Run1T inv meet join tag y s xs) :
    Run1T inv meet join tag y s zs := fun P d q u b => q p (h P d q u b)

theorem Run1T.one {s a r} (save : Bool) (he : s % 2 = 0) (ht : tag a = false)
    (h : Run1T inv meet join tag y s (inv a :: kept save a r)) :
    Run1T inv meet join tag y (s + 1) (a :: r) := fun P d q u b => u save he ht (h P d q u b)

theorem Run1T.two {s a b r} (c ka kb : Bool)
    (hc : c = true → tag a = false ∧ tag b = false)
    (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
    (h : Run1T inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run1T inv meet join tag y (s + 2) (a :: b :: r) := fun P d q u v => v c ka kb hc hta htb (h P d q u v)

theorem Run1T.fold {P : ∀ t ws, Run1T inv meet join tag y t ws → Prop}
    (done : ∀ u0 (hu0 : u0 ≤ 1), P u0 [y] (Run1T.done hu0))
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run1T inv meet join tag y s xs),
      P s xs h → P s zs (Run1T.perm hp h))
    (one : ∀ {s a r} (save : Bool) (he : s % 2 = 0) (ht : tag a = false)
      (h : Run1T inv meet join tag y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run1T.one save he ht h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (hc : c = true → tag a = false ∧ tag b = false)
      (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
      (h : Run1T inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run1T.two c ka kb hc hta htb h))
    {t ws} (h : Run1T inv meet join tag y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run1T inv meet join tag y s xs, P s xs h')
    (fun u0 hu0 => ⟨Run1T.done hu0, done u0 hu0⟩)
    (fun hp ⟨h', ih⟩ => ⟨Run1T.perm hp h', perm hp h' ih⟩)
    (fun k he ht ⟨h', ih⟩ => ⟨Run1T.one k he ht h', one k he ht h' ih⟩)
    (fun c a b hc hta htb ⟨h', ih⟩ => ⟨Run1T.two c a b hc hta htb h', two c a b hc hta htb h' ih⟩)
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

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem Run1T.map {α β : Type} (e : α → β)
    {inv : α → α} {meet join : α → α → α} {tag : α → Bool}
    {inv' : β → β} {meet' join' : β → β → β} {tag' : β → Bool}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    (htag : ∀ a, tag' (e a) = tag a)
    {y : α} {s : ℕ} {ws : List α} (h : Run1T inv meet join tag y s ws) :
    Run1T inv' meet' join' tag' (e y) s (ws.map e) := by
  induction h using Run1T.fold with
  | done u0 hu0 => exact Run1T.done hu0
  | perm hp _ ih => exact Run1T.perm (hp.map e) ih
  | @one s a rest save he ht _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run1T.one save he ((htag a).trans ht) ih
  | @two s a b rest conj ka kb hc hta htb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run1T.two conj ka kb
      (fun h => ⟨(htag a).trans (hc h).1, (htag b).trans (hc h).2⟩)
      (fun h => (htag a).trans (hta h)) (fun h => (htag b).trans (htb h)) ih

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
  | cons g gs ih => intro w; rw [wiresFrom_cons, ih]; simp; omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]; exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by subst h; simp

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
  funext x; unfold val; rw [getD_wiresFrom _ _ _ (by simp)]; simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1; apply List.map_congr_left; intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCount (gs : List Gate) : ℕ := gs.countP (fun g => isNot g.op)
def binCount (gs : List Gate) : ℕ := gs.countP (fun g => !isNot g.op)

theorem notCount_add_binCount (gs : List Gate) : notCount gs + binCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [notCount, binCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNot g.op <;> simp <;> omega

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
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_notCount (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) :
    notCount (simplify op m ins).1.toList ≤ (if isNot op then 1 else 0) := by
  cases op <;> simp only [simplify, isNot]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;> simp [simpAnd, notCount, isNot]
    split_ifs <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;> simp [simpOr, notCount, isNot]
    split_ifs <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot, notCount, isNot]
  · simp [notCount]
  · simp [notCount]

theorem simplify_binCount (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) :
    binCount (simplify op m ins).1.toList ≤ (if isNot op then 0 else 1) := by
  cases op <;> simp only [simplify, isNot]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;> simp [simpAnd, binCount, isNot]
    split_ifs <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;> simp [simpOr, binCount, isNot]
    split_ifs <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot, binCount, isNot]
  · simp [binCount]
  · simp [binCount]

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
      rename_i j k; by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg; subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k; by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg; subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j; cases hg; exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
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
      · rename_i j k; by_cases hjk : j = k
        · subst hjk; simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k; by_cases hjk : j = k
        · subst hjk; simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

theorem simplify_none_of_inl (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (h : ∃ c, Sum.inl c ∈ ins) : (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := h
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simpAnd]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases b <;> simp [simpAnd]
      · cases a <;> simp [simpAnd]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simpOr]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases b <;> simp [simpOr]
      · cases a <;> simp [simpOr]
    · simp at hlen
  · have hl1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; simp [simpNot]
    · simp at hl1

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpStep_len_le (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
  simp only [simpStep, List.length_append]
  cases (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 := simpStep_len_le n acc g
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem simpPass_notCount (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    notCount (simpPass n gs acc).2 ≤ notCount acc.2 + notCount gs := by
  induction gs with
  | nil => intro acc; simp [simpPass, notCount]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : notCount (simpStep n acc g).2 ≤ notCount acc.2 + (if isNot g.op then 1 else 0) := by
      simp only [simpStep, notCount, List.countP_append]
      have := simplify_notCount g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      simp only [notCount] at this; omega
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3]; simp only [notCount, List.countP_cons] at h1 h2 ⊢
    cases hg : isNot g.op <;> simp [hg] at h2 ⊢ <;> omega

theorem simpPass_binCount (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    binCount (simpPass n gs acc).2 ≤ binCount acc.2 + binCount gs := by
  induction gs with
  | nil => intro acc; simp [simpPass, binCount]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : binCount (simpStep n acc g).2 ≤ binCount acc.2 + (if isNot g.op then 0 else 1) := by
      simp only [simpStep, binCount, List.countP_append]
      have := simplify_binCount g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      simp only [binCount] at this; omega
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3]; simp only [binCount, List.countP_cons] at h1 h2 ⊢
    cases hg : isNot g.op <;> simp [hg] at h2 ⊢ <;> omega

theorem simpPass_len_drop (m v : ℕ) (b : Bool) (gs : List Gate) :
    ∀ acc : List (Sum Bool ℕ) × List Gate,
      (∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      v < acc.1.length → acc.1.getD v (Sum.inl false) = Sum.inl b →
      (simpPass m gs acc).2.length + (gs.countP (fun g => decide (v ∈ g.inputs)))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [simpPass]
  | cons g gs ih =>
    intro acc hok hvl hvb
    have hstep_v : v < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have hstep_b : (simpStep m acc g).1.getD v (Sum.inl false) = Sum.inl b := by
      simp only [simpStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hvb
    have ih' := ih (simpStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hstep_v hstep_b
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, List.countP_cons, List.length_cons]
    by_cases hv : v ∈ g.inputs
    · have hnone : (simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        have hg := hok g List.mem_cons_self
        apply simplify_none_of_inl _ _ _ (by simpa using hg.1) (fun hop => by simpa using hg.2 hop)
        exact ⟨b, List.mem_map.2 ⟨v, hv, hvb⟩⟩
      have hlen0 : (simpStep m acc g).2.length = acc.2.length := by
        simp only [simpStep, hnone, Option.toList_none, List.append_nil]
      simp only [hv, decide_true, ite_true]; omega
    · have hlen1 := simpStep_len_le m acc g
      simp only [hv, decide_false, Bool.false_eq_true, ite_false]; omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ SCleanL n acc.2 ∧
  ∀ i : ℕ, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc → SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
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
      intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs; exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2) (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]; apply List.map_congr_left; intro a _; exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none => rw [hr1] at hpg'; simp only [Option.toList_none, List.append_nil] at hpg'; exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'; simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'; exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by have := (List.getElem?_eq_some_iff.1 hpg').1; simp at this; omega
          subst hpe; rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'; subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil; rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]; exact (hi i).2

def Has1Not (n : ℕ) (f : BFn n) (s b : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.gates.length ≤ s ∧ binCount C.gates ≤ b ∧ notCount C.gates ≤ 1 ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem exists_sclean1 {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s b : ℕ)
    (h : Has1Not n f s b) :
    ∃ gs o, gs.length ≤ s ∧ binCount gs ≤ b ∧ notCount gs ≤ 1 ∧ SCleanL n gs ∧
      o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hbin, hnot, hev⟩ := h
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨hop, hlen⟩ := hfan g hg; refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x; refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i; by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := le_trans (by simpa using simpPass_len n C.gates (init, [])) hsz
  have hbc : binCount acc.2 ≤ b := le_trans (by simpa [binCount] using simpPass_binCount n C.gates (init, [])) hbin
  have hnc' : notCount acc.2 ≤ 1 := le_trans (by simpa [notCount] using simpPass_notCount n C.gates (init, [])) hnot
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso; obtain ⟨y, y', hne⟩ := hnc; apply hne
    have h1 := ((hinv y).2.2 C.output).2; have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2; rw [← hev y, ← hev y']
    show (wiresFrom C.gates (List.ofFn y)).getD C.output false = (wiresFrom C.gates (List.ofFn y')).getD C.output false
    rw [← h1, ← h2]; rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by have hv := ((hinv y).2.2 C.output).1; rw [hst] at hv; exact hv
    refine ⟨acc.2, o, hlen, hbc, hnc', (hinv y).2.1, ho, ?_⟩
    intro x; have hv := ((hinv x).2.2 C.output).2; rw [hst] at hv; rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [← hv]; rfl

def substIn {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => match c i with | Sum.inl b => b | Sum.inr j => x j

def initSubst {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) : List (Sum Bool ℕ) :=
  List.ofFn fun i : Fin n => match c i with | Sum.inl b => Sum.inl b | Sum.inr j => Sum.inr j.val

theorem sclean_fanInTwo {m : ℕ} {gs : List Gate} (hcl : SCleanL m gs) (o : ℕ) : FanInTwo ⟨gs, o⟩ := by
  intro g hg; obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
  rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
  · exact ⟨by simp [hop], by simp [hin]⟩
  · rcases hop with hop | hop <;> exact ⟨by simp [hop], by simp [hin]⟩

theorem restrict_sclean_drop {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (hnot : notCount gs ≤ 1)
    (hev : ∀ x, val gs n o x = f x) :
    Has1Not m (fun y => f (substIn c y))
      (gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs)))
      (gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs))) := by
  have hok_inv : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop), by simp [hin]⟩
    · rcases hop with hop | hop
      · exact ⟨Or.inl hop, by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop), by simp [hin]⟩
  have hok_drop : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    intro g hg; obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop with hop | hop <;> exact ⟨by simp [hin], by simp [hop]⟩
  set init := initSubst c
  set acc := simpPass m gs (init, [])
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y; refine ⟨by simp [init, initSubst], by intro p g hg; simp at hg, ?_⟩
    intro i; by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with | inl b => simp [statValid, statVal] | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := fun y =>
    simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hv_init : init.getD v.val (Sum.inl false) = Sum.inl false := by simp [init, initSubst, v.isLt, hv]
  have hlen_drop := simpPass_len_drop m v.val false gs (init, []) hok_drop (by simp [init, initSubst, v.isLt]) hv_init
  simp only [List.length_nil, zero_add] at hlen_drop
  change acc.2.length + gs.countP (fun g => decide (v.val ∈ g.inputs)) ≤ gs.length at hlen_drop
  have hnc_acc : notCount acc.2 ≤ 1 := le_trans (by simpa [notCount] using simpPass_notCount m gs (init, [])) hnot
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c0 =>
    exfalso; obtain ⟨y, y', hne⟩ := hnc_sub; apply hne
    have h1 := ((hinv y).2.2 o).2; have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2; rw [← hev (substIn c y), ← hev (substIn c y')]; unfold val; rw [← h1, ← h2]; rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    have hbc_le : binCount acc.2 ≤ acc.2.length := by have := notCount_add_binCount acc.2; omega
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', by dsimp only; omega, by dsimp only; omega, hnc_acc, ?_⟩
    intro y; have h1 := ((hinv y).2.2 o).2; rw [hst] at h1; dsimp only; rw [← hev (substIn c y)]; exact h1

theorem simpPass_acc1_len (m : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc; have h1 := ih (simpStep m acc g); have h2 : (simpStep m acc g).1.length = acc.1.length + 1 := by simp [simpStep]
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, h1, h2, List.length_cons]; omega

theorem simpPass_acc1_getD (m : ℕ) (gs : List Gate) (i : ℕ) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, i < acc.1.length →
      (simpPass m gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hi; have hstep : i < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, ih (simpStep m acc g) hstep]; simp only [simpStep]; exact getD_snoc_ne _ _ _ _ (by omega)

theorem simpPass_append (m : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    simpPass m (gs₁ ++ gs₂) acc = simpPass m gs₂ (simpPass m gs₁ acc) := List.foldl_append

theorem restrict_sclean_drop2 {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (hnot : notCount gs ≤ 1)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (hev : ∀ x, val gs n o x = f x)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g)
    (hvin : v.val ∈ g.inputs) (hop : g.op = GateOp.not ∨ g.op = GateOp.and) :
    Has1Not m (fun y => f (substIn c y)) (gs.length - 2) (gs.length - 2) := by
  have hok_inv : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
    intro g' hg'; obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop'), by simp [hin]⟩
    · rcases hop' with hop' | hop'
      · exact ⟨Or.inl hop', by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop'), by simp [hin]⟩
  have hok_drop : ∀ g' ∈ gs, g'.inputs.length ≤ 2 ∧ (g'.op = GateOp.not → g'.inputs.length ≤ 1) := by
    intro g' hg'; obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop' with hop' | hop' <;> exact ⟨by simp [hin], by simp [hop']⟩
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
  set init := initSubst c
  set acc1 := simpPass m pre (init, [])
  set acc2 := simpStep m acc1 g
  set acc := simpPass m post acc2
  have hacc_eq : acc = simpPass m gs (init, []) := by
    rw [hsplit, simpPass_append]; rfl
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y; refine ⟨by simp [init, initSubst], by intro q g' hg'; simp at hg', ?_⟩
    intro i; by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with | inl b => simp [statValid, statVal] | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := fun y =>
    hacc_eq ▸ simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hnc_acc : notCount acc.2 ≤ 1 := by
    rw [hacc_eq]; exact le_trans (by simpa [notCount] using simpPass_notCount m gs (init, [])) hnot
  have hv_init : init.getD v.val (Sum.inl false) = Sum.inl false := by simp [init, initSubst, v.isLt, hv]
  have hv1 : acc1.1.getD v.val (Sum.inl false) = Sum.inl false := by
    rw [simpPass_acc1_getD m pre v.val (init, []) (by simp [init, initSubst, v.isLt])]; exact hv_init
  have hl1 : acc1.1.length = n + p := by rw [simpPass_acc1_len]; simp [init, initSubst, hplen]
  have hcl_g := hcl p g hg
  have hg_res : (simplify g.op (m + acc1.2.length) (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none ∧
      ∃ b0 : Bool, (simplify g.op (m + acc1.2.length) (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 = Sum.inl b0 := by
    rcases hcl_g with ⟨hnotg, j, _, hin⟩ | ⟨hor_and, j, k, _, _, _, hin⟩
    · rw [hin] at hvin; have hjv : j = v.val := (List.mem_singleton.1 hvin).symm; subst hjv
      rw [hnotg, hin, List.map_cons, List.map_nil, hv1]; exact ⟨rfl, true, rfl⟩
    · rcases hop with hnotg | hand
      · rcases hor_and with h | h <;> rw [h] at hnotg <;> cases hnotg
      · rw [hin] at hvin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
        rcases hvin with h | h
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD k (Sum.inl false) <;> simp [simplify, simpAnd]
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD j (Sum.inl false) <;> simp [simplify, simpAnd]
  obtain ⟨hnone_g, b0, hb0⟩ := hg_res
  have hacc2_len : acc2.2.length = acc1.2.length := by simp only [acc2, simpStep, hnone_g, Option.toList_none, List.append_nil]
  have hacc2_1_len : acc2.1.length = n + p + 1 := by simp [acc2, simpStep, hl1]
  have hacc2_np : acc2.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    simp only [acc2, simpStep]; rw [getD_snoc_len _ _ _ _ hl1]; exact hb0
  have hacc_np : acc.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    rw [simpPass_acc1_getD m post (n + p) acc2 (by omega)]; exact hacc2_np
  have hne_o : n + p ≠ o := by
    intro ho_eq; obtain ⟨y, y', hne⟩ := hnc_sub; apply hne
    have h1 := ((hinv y).2.2 o).2; have h2 := ((hinv y').2.2 o).2
    rw [← ho_eq, hacc_np] at h1 h2; rw [← hev (substIn c y), ← hev (substIn c y')]; unfold val; rw [← ho_eq, ← h1, ← h2]; rfl
  obtain ⟨q, g', hqg', hnp_in⟩ : ∃ (q : ℕ) (g' : Gate), gs[q]? = some g' ∧ n + p ∈ g'.inputs := by
    rcases hnd p hplt with h | h
    · exact absurd h hne_o
    · exact h
  have hq_gt : p < q := by have := (hcl q g' hqg').lt (n + p) hnp_in; omega
  have hg'_post : g' ∈ post := by
    have hlt_q : q < gs.length := (List.getElem?_eq_some_iff.1 hqg').1
    have hq_sub : q - (p + 1) < post.length := by have : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
                                                  omega
    have hget : post[q - (p + 1)] = g' := by
      have h1 : gs[q]? = post[q - (p + 1)]? := by
        conv_lhs => rw [hsplit]
        rw [List.getElem?_append_right (by omega)]
        have : q - pre.length = (q - (p + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      rw [hqg', List.getElem?_eq_getElem hq_sub] at h1; exact Option.some.inj h1.symm
    rw [← hget]; exact List.getElem_mem hq_sub
  have hpost_pos : 1 ≤ post.countP (fun g => decide (n + p ∈ g.inputs)) :=
    List.countP_pos_iff.2 ⟨g', hg'_post, by simp [hnp_in]⟩
  have hdrop_post := simpPass_len_drop m (n + p) b0 post acc2
    (fun g0 hg0 => hok_drop g0 (by rw [hsplit]; simp [hg0])) (by omega) hacc2_np
  change acc.2.length + post.countP (fun g => decide (n + p ∈ g.inputs)) ≤ acc2.2.length + post.length at hdrop_post
  have hpre_len := simpPass_len m pre (init, [])
  simp only [List.length_nil, zero_add] at hpre_len
  change acc1.2.length ≤ pre.length at hpre_len
  have htot_len : gs.length = p + 1 + post.length := by rw [hsplit]; simp [hplen]; omega
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c0 =>
    exfalso; obtain ⟨y, y', hne⟩ := hnc_sub; apply hne
    have h1 := ((hinv y).2.2 o).2; have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2; rw [← hev (substIn c y), ← hev (substIn c y')]; unfold val; rw [← h1, ← h2]; rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    have hbc_le : binCount acc.2 ≤ acc.2.length := by have := notCount_add_binCount acc.2; omega
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', by dsimp only; omega, by dsimp only; omega, hnc_acc, ?_⟩
    intro y; have h1 := ((hinv y).2.2 o).2; rw [hst] at h1; dsimp only; rw [← hev (substIn c y)]; exact h1

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir; split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) : a = b := by
  unfold redir at heq; split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir; by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]; congr 2; omega
  · simp only [hlt, ite_false]; have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha, List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool, (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u', wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]; apply List.map_congr_left; intro a ha; exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]; rw [List.append_assoc]; exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc, ← List.append_assoc w₁ [b] (u ++ [c])]; exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ binCount gs' ≤ binCount gs ∧ notCount gs' ≤ notCount gs ∧
      SCleanL n gs' ∧ o' < n + gs'.length ∧ ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by simp [gs']; omega
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  have hnc' : notCount gs' ≤ notCount gs := by
    conv_rhs => rw [hsplit]
    simp only [gs', notCount, List.countP_append, List.countP_cons, List.countP_map, Function.comp_def]
    omega
  have hbc' : binCount gs' ≤ binCount gs := by
    conv_rhs => rw [hsplit]
    simp only [gs', binCount, List.countP_append, List.countP_cons, List.countP_map, Function.comp_def]
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg; by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']; rw [List.getElem?_append_left (by simp; omega)]; exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg; exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']; rw [List.getElem?_append_right (by simp; omega)]; simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0; have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e])), by simp [hin]⟩
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k,
          redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e])),
          redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e])),
          fun heq => hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e])) (fun e => hd0 (by rw [hin]; simp [e])) heq),
          by simp [hin]⟩
  refine ⟨gs', o', hlen', hbc', hnc', hcl', ho', ?_⟩
  intro x; unfold val
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by rw [length_wiresFrom]; simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg; obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg; rw [List.getElem_drop] at hgk; rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by simp only [gs', wiresFrom_append]; rw [← lw₁]; simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]; simpa [w₁, b] using hu2
  rw [heq1, heq2]; show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]; exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

abbrev invFT {n : ℕ} : BFn n × Bool → BFn n × Bool := fun p => (invF p.1, false)
abbrev meetFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (meetF p.1 q.1, false)
abbrev joinFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (joinF p.1 q.1, false)

theorem countP_le_one_not_live (gs : List Gate) (o p a : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (ha : a ∈ g.inputs) (hne : a ≠ o)
    (hc : gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1) : ¬ Live gs o (p + 1) a := by
  intro hl; rcases hl with rfl | ⟨q, hq, g', hg', ha'⟩
  · exact hne rfl
  · obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
    have hq_post : g' ∈ post := by
      have hlt : q < gs.length := (List.getElem?_eq_some_iff.1 hg').1
      have hq' : q - (p + 1) < post.length := by have hlen : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
                                                 omega
      have hget : post[q - (p + 1)] = g' := by
        have h1 : gs[q]? = post[q - (p + 1)]? := by
          conv_lhs => rw [hsplit]
          rw [List.getElem?_append_right (by omega)]
          have : q - pre.length = (q - (p + 1)) + 1 := by omega
          rw [this, List.getElem?_cons_succ]
        rw [hg', List.getElem?_eq_getElem hq'] at h1; exact Option.some.inj h1.symm
      rw [← hget]; exact List.getElem_mem hq'
    have hpos : 0 < post.countP (fun g => decide (a ∈ g.inputs)) := List.countP_pos_iff.2 ⟨g', hq_post, by simp [ha']⟩
    rw [hsplit, List.countP_append, List.countP_cons] at hc; simp only [ha, decide_true, ite_true] at hc; omega

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]; constructor
  · rintro ⟨hlt, hl⟩; by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩; have := (hcl q g' hg').lt _ hin; omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp; rw [hg] at hg'; cases hg'; exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live_1not (n : ℕ) (useTag : Bool) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hnot : notCount gs ≤ 1)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (tagged : ℕ → Bool)
    (htag : ∀ a, a < n → tagged a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or)) :
    let encW := fun a => (val gs n a, decide (a < n) && tagged a)
    ∀ d p, p + d = gs.length →
      Run1T (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false)
        (2 * binCount (gs.drop p) + notCount (gs.drop p)) ((liveList gs n o p).map encW) := by
  intro encW d
  induction d with
  | zero =>
    intro p hp
    have hdrop : gs.drop p = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]; simp only [binCount, notCount, List.countP_nil]
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a; rw [mem_liveList, List.mem_singleton]; constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    have ho_tag : encW o = (val gs n o, false) := by
      simp only [encW, Prod.mk.injEq, true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases holt : o < n
      · right; by_cases hto : tagged o = true
        · exact absurd rfl (htag o holt hto).1
        · exact Bool.eq_false_iff.2 hto
      · left; exact holt
    have hdone : Run1T (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false) 0 ([o].map encW) := by
      simp only [List.map_cons, List.map_nil, ho_tag]; exact Run1T.done (by omega)
    exact Run1T.perm (hperm.map encW) hdone
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hdrop_eq : gs.drop p = g :: gs.drop (p + 1) := by
      have hg_el : gs[p] = g := (List.getElem?_eq_some_iff.1 hg).2
      rw [← hg_el]; exact List.drop_eq_getElem_cons hplt
    have hnot_drop : notCount (gs.drop p) ≤ 1 := by
      have hspl : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      rw [hspl] at hnot; simp only [notCount, List.countP_append] at hnot ⊢; omega
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    have hguard : ∀ a ∈ g.inputs, decide (Live gs o (p + 1) a) = true → (useTag && (encW a).2) = false := by
      intro a ha hlive
      have h2 : (encW a).2 = false := by
        simp only [encW, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases halt : a < n
        · right; by_cases hta : tagged a = true
          · have ⟨hne, hc, _⟩ := htag a halt hta
            exact absurd (of_decide_eq_true hlive) (countP_le_one_not_live gs o p a g hg ha hne hc)
          · exact Bool.eq_false_iff.2 hta
        · left; exact halt
      simp [h2]
    have hnot_or : ∀ a ∈ g.inputs, g.op ≠ GateOp.or → (useTag && (encW a).2) = false := by
      intro a ha hne_or
      have h2 : (encW a).2 = false := by
        simp only [encW, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases halt : a < n
        · right; by_cases hta : tagged a = true
          · exact absurd ((htag a halt hta).2.2 p g hg ha) hne_or
          · exact Bool.eq_false_iff.2 hta
        · left; exact halt
      simp [h2]
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) := List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]; rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a; rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]; constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run1T.perm (hp2.map encW) IH
      have hval : encW (n + p) = invFT (encW j) := by
        apply Prod.ext
        · funext x; simp only [encW, invF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
        · simp [encW, show ¬ n + p < n by omega]
      rw [List.map_cons, kept_map, hval] at IH'
      have hnot_rest : notCount (gs.drop (p + 1)) = 0 := by
        rw [hdrop_eq] at hnot_drop; simp only [notCount, List.countP_cons, hop, isNot, ite_true] at hnot_drop ⊢; omega
      have hidx_eq : 2 * binCount (gs.drop p) + notCount (gs.drop p) =
          (2 * binCount (gs.drop (p + 1)) + notCount (gs.drop (p + 1))) + 1 := by
        rw [hdrop_eq]; simp only [binCount, notCount, List.countP_cons, hop, isNot]; simp; omega
      have heven : (2 * binCount (gs.drop (p + 1)) + notCount (gs.drop (p + 1))) % 2 = 0 := by omega
      rw [hidx_eq]
      exact Run1T.perm (hp1.map encW).symm (Run1T.one _ heven (hnot_or j (by simp [hinp]) (by simp [hop])) IH')
    · have hjm := hin j (by simp [hinp]); have hkm := hin k (by simp [hinp])
      have hp1a : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) := List.perm_cons_erase hjm
      have hkm' : k ∈ (liveList gs n o p).erase j := (hnd0.mem_erase_iff.2 ⟨Ne.symm hjk, hkm⟩)
      have hp1 : (liveList gs n o p).Perm (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        hp1a.trans ((List.perm_cons_erase hkm').cons j)
      have hnr : (((liveList gs n o p).erase j).erase k).Nodup := (hnd0.erase j).erase k
      have hj_ne_r : j ∉ ((liveList gs n o p).erase j).erase k := fun h =>
        (hnd0.mem_erase_iff.1 (List.mem_of_mem_erase h)).1 rfl
      have hk_ne_r : k ∉ ((liveList gs n o p).erase j).erase k := fun h =>
        ((hnd0.erase j).mem_erase_iff.1 h).1 rfl
      have hp2 : (liveList gs n o (p + 1)).Perm ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
          (kept (decide (Live gs o (p + 1) k)) k (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr hk_ne_r) ?_⟩
          · rw [mem_kept, mem_kept]; rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ (List.mem_of_mem_erase (List.mem_of_mem_erase h)) rfl
          · rw [mem_kept]; rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact hj_ne_r h
        · intro a; rw [hstep a, List.mem_cons, mem_kept, mem_kept, (hnd0.erase j).mem_erase_iff, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]; constructor
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
      have IH' := Run1T.perm (hp2.map encW) IH
      have hval : encW (n + p) = (if decide (g.op = GateOp.and) then meetFT (encW j) (encW k) else joinFT (encW j) (encW k)) := by
        rcases hop with hop | hop
        · simp only [hop, decide_true, ite_true]; apply Prod.ext
          · funext x; simp only [encW, meetF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, show ¬ n + p < n by omega]
        · have hne : GateOp.or ≠ GateOp.and := fun h => GateOp.noConfusion h
          simp only [hop, hne, decide_false, Bool.false_eq_true, ite_false]; apply Prod.ext
          · funext x; simp only [encW]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, show ¬ n + p < n by omega]
      have hand_guard : decide (g.op = GateOp.and) = true → (useTag && (encW j).2) = false ∧ (useTag && (encW k).2) = false := by
        intro ha; have hgop : g.op = GateOp.and := of_decide_eq_true ha
        exact ⟨hnot_or j (by simp [hinp]) (by simp [hgop]), hnot_or k (by simp [hinp]) (by simp [hgop])⟩
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      have hidx_eq : 2 * binCount (gs.drop p) + notCount (gs.drop p) =
          (2 * binCount (gs.drop (p + 1)) + notCount (gs.drop (p + 1))) + 2 := by
        rw [hdrop_eq]; rcases hop with hop | hop <;> simp [binCount, notCount, hop, isNot] <;> omega
      rw [hidx_eq]
      exact Run1T.perm (hp1.map encW).symm
        (Run1T.two _ _ _ hand_guard (hguard j (by simp [hinp])) (hguard k (by simp [hinp])) IH')

open Classical in
theorem exists_run_1not {n : ℕ} (useTag : Bool) (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (tagged : ℕ → Bool) (s b : ℕ)
    (htag_fn : ∀ (gs : List Gate) (o : ℕ), gs.length ≤ s → notCount gs ≤ 1 → SCleanL n gs →
      (∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) →
      (∀ x, val gs n o x = f x) →
      ∀ a, a < n → tagged a = true →
        a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
        (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or))
    (h : Has1Not n f s b) :
    ∃ u, u ≤ s + b ∧ u ≤ 2 * b + 1 ∧ ∃ ws : List (BFn n × Bool),
      ws.Sublist (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val)) ∧
      Run1T (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (f, false) u ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ binCount gs ≤ b ∧ notCount gs ≤ 1 ∧
      SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hbc, hnot, hcl, ho, hev⟩ := exists_sclean1 f hnc s b h
    exact ⟨gs.length, gs, o, rfl, hbc, hnot, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hbc, hnot, hcl, ho, hev⟩ := exists_sclean1 f hnc s b h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hbc, hnot, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hbc, hnot, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp; by_contra! hbad; obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hbc', hnot', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    exact Nat.find_min hex (by omega) ⟨gs', o', rfl, le_trans hbc' hbc, le_trans hnot' hnot, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  let encW := fun a => (val gs n a, decide (a < n) && tagged a)
  have hsum := notCount_add_binCount gs
  refine ⟨2 * binCount gs + notCount gs, by omega, by omega, (liveList gs n o 0).map encW, ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val)) = (List.range n).map encW := by
      apply List.ext_getElem; · simp
      · intro i h1 h2; simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, encW]
        have hi : i < n := by simpa using h1
        apply Prod.ext
        · exact (val_input gs n ⟨i, hi⟩).symm
        · simp [hi]
    rw [e]; exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev; rw [← hf]
    have hrun := run_live_1not n useTag gs o hcl ho hnot hnd tagged (htag_fn gs o (by omega) hnot hcl hnd hev) gs.length 0 (by omega)
    simpa only [List.drop_zero] using hrun

theorem run1T_len {α inv meet join tag y u xs} (h : @Run1T α inv meet join tag y u xs) :
    xs.length ≤ u / 2 + 1 := by
  induction h using Run1T.fold with
  | done u0 hu0 => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save he _ _ ih => cases save <;> simp [kept] at ih ⊢ <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

abbrev NatRun1T (k : Nat) (useTag : Bool) :=
  Run1T (fun w => (w &&& mask k) ^^^ mask k)
        (fun a b => (a &&& b) &&& mask k)
        (fun a b => (a ||| b) &&& mask k)
        (fun w => useTag && w.testBit (2 * k))

theorem mask_testBit_lt {k i : Nat} (hi : i < 2 * k) : (mask k).testBit i = true := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega]

theorem mask_testBit_ge {k i : Nat} (hi : 2 * k ≤ i) : (mask k).testBit i = false := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show ¬ i < k + k by omega]

theorem run1T_bits {k useTag y u xs} (h : NatRun1T k useTag y u xs) (i j : Nat)
    (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi := mask_testBit_lt hi; have hmj := mask_testBit_lt hj
  induction h using Run1T.fold with
  | done _ _ => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb, hmi, hmj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem bits_le_even {k useTag y u xs} (h : NatRun1T k useTag y u xs) (he : u % 2 = 0)
    (i j : Nat) (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ a ∈ xs, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  have hmi := mask_testBit_lt hi; have hmj := mask_testBit_lt hj
  induction h using Run1T.fold with
  | done _ _ => exact hw _ (by simp)
  | perm hp _ ih => exact ih he (fun a ha => hw a (hp.mem_iff.1 ha))
  | one _ he0 _ _ _ => omega
  | two conj ka kb _ _ _ _ ih =>
    apply ih (by omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at had <;>
      rcases had with rfl | hr <;> first
        | (simp only [Nat.testBit_and, Nat.testBit_or, hmi, hmj, Bool.and_true]; grind)
        | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := Nat.xor w (Nat.shiftRight w k)
def cov (k : Nat) : List Nat → Nat | [] => 0 | a :: t => Nat.lor (diff k a) (cov k t)
def diffUp (k w : Nat) : Nat := Nat.land (Nat.shiftRight w k) (Nat.xor w (lo k))
def covUp (k : Nat) : List Nat → Nat | [] => 0 | a :: t => Nat.lor (diffUp k a) (covUp k t)

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    have e : cov k (a :: t) = diff k a ||| cov k t := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih]
    simp only [diff, Nat.xor_eq, Nat.shiftRight_eq, Nat.testBit_xor, Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

theorem cov_perm (k : Nat) {xs ys : List Nat} (p : xs.Perm ys) : cov k xs = cov k ys := by
  apply Nat.eq_of_testBit_eq; intro i
  apply Bool.eq_iff_iff.2; rw [cov_bit, cov_bit]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, p.mem_iff.1 ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, p.mem_iff.2 ha, h⟩⟩

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    have e : covUp k (a :: t) = diffUp k a ||| covUp k t := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih]
    simp only [diffUp, Nat.land_eq, Nat.xor_eq, Nat.shiftRight_eq, Nat.testBit_and, Nat.testBit_shiftRight,
      Nat.testBit_xor, lo, Nat.testBit_two_pow_sub_one, hi, decide_true, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

theorem required {k useTag u ws} (h : NatRun1T k useTag (goal k) u ws) :
    (Nat.land (cov k ws) (lo k)) = lo k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.land_eq, Nat.testBit_and]; by_cases hi : i < k
  · have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2; by_contra! hh
      exact hy (run1T_bits h i (k + i) (by omega) (by omega) hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem required_up {k useTag u ws} (h : NatRun1T k useTag (goal k) u ws) (he : u % 2 = 0) :
    (Nat.land (covUp k ws) (lo k)) = lo k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.land_eq, Nat.testBit_and]; by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2; by_contra! hh
      apply hy; apply bits_le_even h he (k + i) i (by omega) (by omega)
      intro a ha; specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

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

theorem score_bound_even {k useTag y u ws} (h : NatRun1T k useTag y u ws) (he : u % 2 = 0)
    (hl : ws.length = u / 2 + 1) (v : Nat → Nat)
    (hand : ∀ a b, v ((a &&& b) &&& mask k) ≤ v a + v b)
    (hor : ∀ a b, v ((a ||| b) &&& mask k) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run1T.fold with
  | done u0 hu0 => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih he (p.length_eq.trans hl)
  | one _ he0 _ _ _ => omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run1T_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by omega) (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) : Nat :=
  value6 (Nat.testBit v a) (Nat.testBit v b) (Nat.testBit v c)
    (Nat.testBit v d) (Nat.testBit v e) (Nat.testBit v f)

theorem eval6_bound {k useTag y u ws} (h : NatRun1T k useTag y u ws) (he : u % 2 = 0)
    (hl : ws.length = u / 2 + 1) (a b c d e f : Nat)
    (ha : a < 2 * k) (hb : b < 2 * k) (hc : c < 2 * k)
    (hd : d < 2 * k) (he' : e < 2 * k) (hf : f < 2 * k) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  have hma := mask_testBit_lt ha; have hmb := mask_testBit_lt hb; have hmc := mask_testBit_lt hc
  have hmd := mask_testBit_lt hd; have hme := mask_testBit_lt he'; have hmf := mask_testBit_lt hf
  apply score_bound_even h he hl
  · intro v w
    simpa only [eval6, Nat.testBit_and, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_and, Nat.testBit_or, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (a b c d e f : Nat) : List Nat → Nat → Bool
  | [], n => Nat.blt 0 n
  | w :: ws, n => let v := eval6 a b c d e f w; Nat.blt v n && sumBelow a b c d e f ws (n - v)

theorem sumBelow_iff (a b c d e f : Nat) (ws : List Nat) (n : Nat) :
    sumBelow a b c d e f ws n = true ↔ (ws.map (eval6 a b c d e f)).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih =>
    simp only [sumBelow, Bool.and_eq_true, Nat.blt_eq, ih, List.map_cons, List.sum_cons]; omega

def codeOK (k : Nat) (c : Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (a, b, c0, d, e, f) := c
  Nat.ble k a && Nat.blt a (2 * k) && Nat.ble k b && Nat.blt b (2 * k) &&
  Nat.ble k c0 && Nat.blt c0 (2 * k) && Nat.blt d k && Nat.blt e k && Nat.blt f k

def poolOK (k : Nat) (pool : List (Nat × Nat × Nat × Nat × Nat × Nat)) : Bool :=
  pool.all (codeOK k)

def scr62 (pool : List (Nat × Nat × Nat × Nat × Nat × Nat)) (zs : List Nat) : Bool :=
  pool.any fun (a, b, c, d, e, f) => sumBelow a b c d e f zs 3

theorem eval6_goal_eq3 {k a b c d e f : Nat}
    (ha1 : k ≤ a) (ha2 : a < 2 * k) (hb1 : k ≤ b) (hb2 : b < 2 * k)
    (hc1 : k ≤ c) (hc2 : c < 2 * k) (hd : d < k) (he : e < k) (hf : f < k) :
    eval6 a b c d e f (goal k) = 3 := by
  have hgt : ∀ i, k ≤ i → i < 2 * k → (goal k).testBit i = true := by
    intro i hi1 hi2; simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi1, show i - k < k by omega]
  have hlt : ∀ i, i < k → (goal k).testBit i = false := by
    intro i hi; simp [goal, Nat.testBit_shiftLeft, show ¬ k ≤ i by omega]
  simp [eval6, value6, hgt a ha1 ha2, hgt b hb1 hb2, hgt c hc1 hc2, hlt d hd, hlt e he, hlt f hf]

theorem scr62_no {useTag u zs} {pool : List (Nat × Nat × Nat × Nat × Nat × Nat)}
    (hp : poolOK 62 pool = true) (h : NatRun1T 62 useTag (goal 62) u zs)
    (he : u % 2 = 0) (hl : zs.length = u / 2 + 1) : scr62 pool zs = false := by
  rw [scr62, List.any_eq_false]
  intro ⟨a, b, c, d, e, f⟩ hmem
  have hok := List.all_eq_true.1 hp _ hmem
  simp only [codeOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  intro hbad
  have hlt := (sumBelow_iff a b c d e f zs 3).1 hbad
  have hge := eval6_bound h he hl a b c d e f hok.1.1.1.1.1.1.1.2 hok.1.1.1.1.1.2 hok.1.1.1.2
    (by omega) (by omega) (by omega)
  have hg3 := eval6_goal_eq3 hok.1.1.1.1.1.1.1.1 hok.1.1.1.1.1.1.1.2 hok.1.1.1.1.1.1.2 hok.1.1.1.1.1.2
    hok.1.1.1.1.2 hok.1.1.1.2 hok.1.1.2 hok.1.2 hok.2
  omega

def lo62 : Nat := 0x3fffffffffffffff
def mask62 : Nat := 0xfffffffffffffffffffffffffffffff
def goal62 : Nat := 0xfffffffffffffffc000000000000000

theorem lo62_eq : lo62 = lo 62 := by decide
theorem mask62_eq : mask62 = mask 62 := by decide
theorem goal62_eq : goal62 = goal 62 := by decide

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

def moveOK (k : Nat) (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) &&
  (moveBits p.1 p.2 (mask k) == mask k) &&
  (moveBits p.1 p.2 (goal k) == goal k) &&
  (!p.1.testBit (2 * k)) &&
  (!(p.1 <<< p.2).testBit (2 * k))

theorem move_run1T {k useTag u ws} (h : NatRun1T k useTag (goal k) u ws) (tag d : Nat)
    (hok : moveOK k (tag, d) = true) :
    NatRun1T k useTag (goal k) u (ws.map (moveBits tag d)) := by
  simp only [moveOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hz, hm⟩, hy⟩, ht1⟩, ht2⟩ := hok
  rw [← hy]
  exact Run1T.map _
    (fun a => by rw [(move_hom tag d hz _ _).2.2, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).2.1, hm])
    (fun a => by rw [moved tag d (2 * k) a hz, ht1, ht2]; rfl)
    h

def hw (seed w : Nat) : Nat :=
  let x := Nat.land (Nat.land w 4294967295 + Nat.land (Nat.shiftRight w 32) 4294967295 * 3 +
    Nat.land (Nat.shiftRight w 64) 4294967295 * 7 + Nat.land (Nat.shiftRight w 96) 4294967295 * 11 + seed) 4294967295
  let y := Nat.land (Nat.xor x (Nat.shiftRight x 16) * 2246822519) 4294967295
  Nat.land (Nat.xor y (Nat.shiftRight y 13) * 3266489917) 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := Nat.land (hz seed zs) 16777215

theorem ori_move_ok {k useTag u ys} (seed tag d : Nat) (hok : moveOK k (tag, d) = true)
    (h : NatRun1T k useTag (goal k) u ys) :
    NatRun1T k useTag (goal k) u (let img := ys.map (moveBits tag d); if Nat.blt (hk seed img) (hk seed ys) then img else ys) := by
  dsimp only; split_ifs
  · exact move_run1T h tag d hok
  · exact h

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if Nat.blt (lo + 1) hi then
      let mid := (lo + hi) / 2
      if Nat.ble (read mid) h then bsr read h f mid hi else bsr read h f lo mid
    else lo

def eraseOne (x : Nat) : List Nat → Option (List Nat)
  | [] => none
  | y :: ys => if Nat.beq x y then some ys else match eraseOne x ys with | none => none | some r => some (y :: r)

theorem eraseOne_perm {x : Nat} : ∀ {ys r : List Nat}, eraseOne x ys = some r → ys.Perm (x :: r)
  | [], _, h => by simp [eraseOne] at h
  | y :: ys, r, h => by
    simp only [eraseOne] at h
    split at h
    next heq => cases h; rw [Nat.eq_of_beq_eq_true heq]
    next =>
      cases he : eraseOne x ys with
      | none => rw [he] at h; cases h
      | some r' => rw [he] at h; cases h; exact ((eraseOne_perm he).cons y).trans (List.Perm.swap _ _ _)

def isPermFast : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, ys => (match eraseOne x ys with | none => false | some r => isPermFast xs r)
  | _, _ => false

theorem isPermFast_sound : ∀ {xs ys : List Nat}, isPermFast xs ys = true → xs.Perm ys
  | [], [], _ => List.Perm.refl _
  | [], _ :: _, h => by simp [isPermFast] at h
  | x :: xs, ys, h => by
    simp only [isPermFast] at h
    cases he : eraseOne x ys with
    | none => rw [he] at h; cases h
    | some r => rw [he] at h; exact ((isPermFast_sound h).cons x).trans (eraseOne_perm he).symm

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (u : Nat) (zs : List Nat) : Bool :=
  let j := idx u zs
  decide (j < N u) && isPermFast zs (S u j)

def checkNot (useTag : Bool) (slack : Nat) (ok : List Nat → Bool) (a : Nat) (ra : List Nat) : Bool :=
  if useTag && a.testBit 124 then true else
  let w := Nat.xor (Nat.land a mask62) mask62
  let vz := Nat.lor (covUp 62 ra) (diffUp 62 w)
  (!Nat.beq (Nat.land vz lo62) lo62 || ok (w :: ra)) &&
  (Nat.beq slack 0 || !Nat.beq (Nat.land (Nat.lor vz (diffUp 62 a)) lo62) lo62 || ok (w :: a :: ra))

def scanNot (useTag : Bool) (slack : Nat) (ok : List Nat → Bool) : List Nat → List Nat → Bool
  | [], _ => true
  | a :: xs, pre => checkNot useTag slack ok a (pre ++ xs) && scanNot useTag slack ok xs (a :: pre)

theorem scanNot_sound (useTag : Bool) (slack : Nat) (ok : List Nat → Bool) :
    ∀ (xs pre : List Nat), scanNot useTag slack ok xs pre = true →
      ∀ {a r}, xs.Perm (a :: r) → ∃ ra, (pre ++ r).Perm ra ∧ checkNot useTag slack ok a ra = true := by
  intro xs; induction xs with
  | nil => intro _ _ a r hp; have := hp.length_eq; simp at this
  | cons x xs ih =>
    intro pre h a r hp
    simp only [scanNot, Bool.and_eq_true] at h
    by_cases hax : x = a
    · subst hax
      have pr : r.Perm xs := hp.cons_inv.symm
      exact ⟨pre ++ xs, List.Perm.append_left pre pr, h.1⟩
    · have hxmem : x ∈ r := by
        have := hp.mem_iff.1 List.mem_cons_self
        exact (List.mem_cons.1 this).resolve_left hax
      have hp' : xs.Perm (a :: r.erase x) := by
        have p1 : (x :: xs).Perm (x :: a :: r.erase x) :=
          hp.trans ((List.perm_cons_erase hxmem).cons a |>.trans (List.Perm.swap _ _ _))
        exact p1.cons_inv
      obtain ⟨ra, hra, hck⟩ := ih (x :: pre) h.2 hp'
      have hpr : (pre ++ r).Perm ((x :: pre) ++ r.erase x) :=
        (List.Perm.append_left pre (List.perm_cons_erase hxmem)).trans List.perm_middle
      exact ⟨ra, hpr.trans hra, hck⟩

def checkW (odd : Bool) (slack : Nat) (ok : List Nat → Bool) (a b : Nat) (ta tb : Bool)
    (r : List Nat) (base sa sb w : Nat) : Bool :=
  let sw := if odd then diff 62 w else diffUp 62 w
  let vz := Nat.lor base sw
  (!Nat.beq (Nat.land vz lo62) lo62 || ok (w :: r)) &&
  (Nat.beq slack 0 ||
    ((ta || !Nat.beq (Nat.land (Nat.lor vz sa) lo62) lo62 || ok (w :: a :: r)) &&
     (tb || !Nat.beq (Nat.land (Nat.lor vz sb) lo62) lo62 || ok (w :: b :: r)))) &&
  (Nat.blt slack 2 || ta || tb ||
    !Nat.beq (Nat.land (Nat.lor (Nat.lor vz sa) sb) lo62) lo62 || ok (w :: a :: b :: r))

def checkPair (useTag odd : Bool) (slack : Nat) (ok : List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let ta := useTag && a.testBit 124
  let tb := useTag && b.testBit 124
  let base := if odd then cov 62 r else covUp 62 r
  let sa := if odd then diff 62 a else diffUp 62 a
  let sb := if odd then diff 62 b else diffUp 62 b
  checkW odd slack ok a b ta tb r base sa sb (Nat.land (Nat.lor a b) mask62) &&
  (ta || tb || checkW odd slack ok a b ta tb r base sa sb (Nat.land (Nat.land a b) mask62))

def scanWith (useTag odd : Bool) (slack : Nat) (ok : List Nat → Bool) (a : Nat) :
    List Nat → List Nat → Bool
  | [], _ => true
  | b :: xs, pre => checkPair useTag odd slack ok a b (pre ++ xs) && scanWith useTag odd slack ok a xs (b :: pre)

def scanPairs (useTag odd : Bool) (slack : Nat) (ok : List Nat → Bool) :
    List Nat → List Nat → Bool
  | [], _ => true
  | a :: xs, pre => scanWith useTag odd slack ok a xs pre && scanPairs useTag odd slack ok xs (a :: pre)

theorem scanWith_sound (useTag odd : Bool) (slack : Nat) (ok : List Nat → Bool) (a : Nat) :
    ∀ (xs pre : List Nat), scanWith useTag odd slack ok a xs pre = true →
      ∀ {b r}, xs.Perm (b :: r) → ∃ ra, (pre ++ r).Perm ra ∧ checkPair useTag odd slack ok a b ra = true := by
  intro xs; induction xs with
  | nil => intro _ _ b r hp; have := hp.length_eq; simp at this
  | cons x xs ih =>
    intro pre h b r hp
    simp only [scanWith, Bool.and_eq_true] at h
    by_cases hbx : x = b
    · subst hbx; exact ⟨pre ++ xs, List.Perm.append_left pre hp.cons_inv.symm, h.1⟩
    · have hxmem : x ∈ r := (List.mem_cons.1 (hp.mem_iff.1 List.mem_cons_self)).resolve_left hbx
      have hp' : xs.Perm (b :: r.erase x) :=
        (hp.trans (((List.perm_cons_erase hxmem).cons b).trans (List.Perm.swap _ _ _))).cons_inv
      obtain ⟨ra, hra, hck⟩ := ih (x :: pre) h.2 hp'
      have hpr : (pre ++ r).Perm ((x :: pre) ++ r.erase x) :=
        (List.Perm.append_left pre (List.perm_cons_erase hxmem)).trans List.perm_middle
      exact ⟨ra, hpr.trans hra, hck⟩

theorem scanPairs_sound (useTag odd : Bool) (slack : Nat) (ok : List Nat → Bool) :
    ∀ (xs pre : List Nat), scanPairs useTag odd slack ok xs pre = true →
      ∀ {a b r}, xs.Perm (a :: b :: r) →
        ∃ ra, (pre ++ r).Perm ra ∧
          (checkPair useTag odd slack ok a b ra = true ∨ checkPair useTag odd slack ok b a ra = true) := by
  intro xs; induction xs with
  | nil => intro _ _ a b r hp; have := hp.length_eq; simp at this
  | cons x xs ih =>
    intro pre h a b r hp
    simp only [scanPairs, Bool.and_eq_true] at h
    by_cases hax : x = a
    · subst hax
      obtain ⟨ra, hra, hck⟩ := scanWith_sound useTag odd slack ok x xs pre h.1 hp.cons_inv
      exact ⟨ra, hra, Or.inl hck⟩
    · by_cases hbx : x = b
      · subst hbx
        have hp' : xs.Perm (a :: r) := (hp.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨ra, hra, hck⟩ := scanWith_sound useTag odd slack ok x xs pre h.1 hp'
        exact ⟨ra, hra, Or.inr hck⟩
      · have hxmem : x ∈ r := by
          have := hp.mem_iff.1 List.mem_cons_self
          rcases List.mem_cons.1 this with h1 | h2
          · exact absurd h1 hax
          · exact (List.mem_cons.1 h2).resolve_left hbx
        have hp' : xs.Perm (a :: b :: r.erase x) := by
          have p1 : (a :: b :: r).Perm (x :: a :: b :: r.erase x) :=
            (((List.perm_cons_erase hxmem).cons b).trans (List.Perm.swap _ _ _) |>.cons a).trans (List.Perm.swap _ _ _)
          exact (hp.trans p1).cons_inv
        obtain ⟨ra, hra, hck⟩ := ih (x :: pre) h.2 hp'
        have hpr : (pre ++ r).Perm ((x :: pre) ++ r.erase x) :=
          (List.Perm.append_left pre (List.perm_cons_erase hxmem)).trans List.perm_middle
        exact ⟨ra, hpr.trans hra, hck⟩

def okChild (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List (Nat × Nat × Nat × Nat × Nat × Nat))
    (u : Nat) (zs : List Nat) : Bool :=
  (Nat.beq (u % 2) 0 && Nat.beq zs.length (u / 2 + 1) && scr62 pool zs) || found S N idx u (ori zs)

def bar1T (useTag : Bool) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat)
    (pool : List (Nat × Nat × Nat × Nat × Nat × Nat)) (u i : Nat) : Bool :=
  let ws := S u i
  if Nat.beq u 0 then !Nat.beq ws.length 1 || !(match ws with | [w] => Nat.beq w goal62 | _ => false)
  else if Nat.beq u 1 then
    (match ws with
      | [w] => !Nat.beq w goal62 && (useTag && w.testBit 124 || !Nat.beq (Nat.xor (Nat.land w mask62) mask62) goal62)
      | _ => true)
  else
    let slack := u / 2 + 1 - ws.length
    let odd := Nat.beq (u % 2) 1
    (!odd || scanNot useTag slack (okChild S N idx ori pool (u - 1)) ws []) &&
    scanPairs useTag odd slack (okChild S N idx ori pool (u - 2)) ws []

theorem covUp_cons (a : Nat) (r : List Nat) : covUp 62 (a :: r) = Nat.lor (diffUp 62 a) (covUp 62 r) := rfl
theorem cov_cons (a : Nat) (r : List Nat) : cov 62 (a :: r) = Nat.lor (diff 62 a) (cov 62 r) := rfl

theorem lor_comm_nat (a b : Nat) : Nat.lor a b = Nat.lor b a := Nat.or_comm a b
theorem lor_assoc_nat (a b c : Nat) : Nat.lor (Nat.lor a b) c = Nat.lor a (Nat.lor b c) := Nat.or_assoc a b c

theorem checkW_fire {useTag S N idx ori pool u' slack a b ta tb r base sa sb w ka kb}
    (hp : poolOK 62 pool = true)
    (hr : ∀ {v ys}, NatRun1T 62 useTag (goal 62) v ys → NatRun1T 62 useTag (goal 62) v (ori ys))
    (hck : checkW (Nat.beq (u' % 2) 1) slack (okChild S N idx ori pool u') a b ta tb r base sa sb w = true)
    (hbase : base = if Nat.beq (u' % 2) 1 then cov 62 r else covUp 62 r)
    (hsa : sa = if Nat.beq (u' % 2) 1 then diff 62 a else diffUp 62 a)
    (hsb : sb = if Nat.beq (u' % 2) 1 then diff 62 b else diffUp 62 b)
    (hta : ka = true → ta = false) (htb : kb = true → tb = false)
    (hka : ka = true → 1 ≤ slack) (hkb : kb = true → 1 ≤ slack)
    (hkab : ka = true → kb = true → 2 ≤ slack)
    (hrun : NatRun1T 62 useTag (goal 62) u' (w :: kept ka a (kept kb b r))) :
    ∃ j < N u', NatRun1T 62 useTag (goal 62) u' (S u' j) := by
  have hcov : Nat.land (if Nat.beq (u' % 2) 1 then cov 62 (w :: kept ka a (kept kb b r)) else covUp 62 (w :: kept ka a (kept kb b r))) lo62 = lo62 := by
    rw [lo62_eq]
    by_cases hodd : Nat.beq (u' % 2) 1 = true
    · simp only [hodd, ite_true]; exact required hrun
    · simp only [hodd, Bool.false_eq_true, ite_false]
      have hev : u' % 2 = 0 := by simp only [Nat.beq_eq] at hodd; omega
      exact required_up hrun hev
  have hok : okChild S N idx ori pool u' (w :: kept ka a (kept kb b r)) = true := by
    simp only [checkW, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.blt_eq, Nat.lor_eq, Nat.land_eq] at hck
    simp only [Nat.beq_eq] at hbase hsa hsb hcov
    simp only [Nat.land_eq] at hcov
    cases ka <;> cases kb <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcov ⊢
    · have h1 : (base ||| if u' % 2 = 1 then diff 62 w else diffUp 62 w) &&& lo62 = lo62 := by
        rw [hbase]; by_cases hodd : u' % 2 = 1 <;> simp only [hodd, ite_true, ite_false] at hcov ⊢
        · rw [cov_cons, Nat.lor_eq] at hcov; rw [Nat.or_comm]; exact hcov
        · rw [covUp_cons, Nat.lor_eq] at hcov; rw [Nat.or_comm]; exact hcov
      exact hck.1.1.resolve_left (by simp [h1])
    · have htb' := htb rfl; have hkb' := hkb rfl
      have h1 : ((base ||| if u' % 2 = 1 then diff 62 w else diffUp 62 w) ||| sb) &&& lo62 = lo62 := by
        rw [hbase, hsb]; by_cases hodd : u' % 2 = 1 <;> simp only [hodd, ite_true, ite_false] at hcov ⊢
        · rw [cov_cons, cov_cons, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : (cov 62 r ||| diff 62 w) ||| diff 62 b = diff 62 w ||| (diff 62 b ||| cov 62 r) := by ac_rfl
          rw [e]; exact hcov
        · rw [covUp_cons, covUp_cons, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : (covUp 62 r ||| diffUp 62 w) ||| diffUp 62 b = diffUp 62 w ||| (diffUp 62 b ||| covUp 62 r) := by ac_rfl
          rw [e]; exact hcov
      have h2 := (hck.1.2.resolve_left (by omega)).2
      exact h2.resolve_left (by simp [htb', h1])
    · have hta' := hta rfl; have hka' := hka rfl
      have h1 : ((base ||| if u' % 2 = 1 then diff 62 w else diffUp 62 w) ||| sa) &&& lo62 = lo62 := by
        rw [hbase, hsa]; by_cases hodd : u' % 2 = 1 <;> simp only [hodd, ite_true, ite_false] at hcov ⊢
        · rw [cov_cons, cov_cons, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : (cov 62 r ||| diff 62 w) ||| diff 62 a = diff 62 w ||| (diff 62 a ||| cov 62 r) := by ac_rfl
          rw [e]; exact hcov
        · rw [covUp_cons, covUp_cons, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : (covUp 62 r ||| diffUp 62 w) ||| diffUp 62 a = diffUp 62 w ||| (diffUp 62 a ||| covUp 62 r) := by ac_rfl
          rw [e]; exact hcov
      have h2 := (hck.1.2.resolve_left (by omega)).1
      exact h2.resolve_left (by simp [hta', h1])
    · have hta' := hta rfl; have htb' := htb rfl; have hkab' := hkab rfl rfl
      have h1 : (((base ||| if u' % 2 = 1 then diff 62 w else diffUp 62 w) ||| sa) ||| sb) &&& lo62 = lo62 := by
        rw [hbase, hsa, hsb]; by_cases hodd : u' % 2 = 1 <;> simp only [hodd, ite_true, ite_false] at hcov ⊢
        · rw [cov_cons, cov_cons, cov_cons, Nat.lor_eq, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : ((cov 62 r ||| diff 62 w) ||| diff 62 a) ||| diff 62 b =
              diff 62 w ||| (diff 62 a ||| (diff 62 b ||| cov 62 r)) := by ac_rfl
          rw [e]; exact hcov
        · rw [covUp_cons, covUp_cons, covUp_cons, Nat.lor_eq, Nat.lor_eq, Nat.lor_eq] at hcov
          have e : ((covUp 62 r ||| diffUp 62 w) ||| diffUp 62 a) ||| diffUp 62 b =
              diffUp 62 w ||| (diffUp 62 a ||| (diffUp 62 b ||| covUp 62 r)) := by ac_rfl
          rw [e]; exact hcov
      exact hck.2.resolve_left (by simp [hta', htb', h1]; omega)
  simp only [okChild, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, found, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨he, hl⟩, hscr⟩ | ⟨hj, hp'⟩
  · rw [scr62_no hp hrun he hl] at hscr; cases hscr
  · exact ⟨idx u' (ori _), hj, Run1T.perm (isPermFast_sound hp') (hr hrun)⟩

theorem zero_done1T {α inv meet join tag y u ws} (h : @Run1T α inv meet join tag y u ws) :
    u = 0 → ws = [y] := by
  induction h using Run1T.fold with
  | done _ _ => intro _; rfl
  | perm p _ ih => intro hu; rw [ih hu] at p; exact List.perm_singleton.1 p.symm
  | one => intro hu; omega
  | two => intro hu; omega

theorem one_done1T {α inv meet join tag y u ws} (h : @Run1T α inv meet join tag y u ws) :
    u = 1 → ws = [y] ∨ ∃ a, ws = [a] ∧ tag a = false ∧ inv a = y := by
  induction h using Run1T.fold with
  | done _ _ => intro _; exact Or.inl rfl
  | perm p _ ih =>
    intro hu; rcases ih hu with rfl | ⟨a, rfl, hta, ha⟩
    · exact Or.inl (List.perm_singleton.1 p.symm)
    · exact Or.inr ⟨a, List.perm_singleton.1 p.symm, hta, ha⟩
  | @one s a r save he ht hsub _ =>
    intro hu
    have hs0 : s = 0 := by omega
    have hsub' := zero_done1T hsub hs0
    cases save <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hsub'
    · injection hsub' with h1 h2; subst h2; exact Or.inr ⟨a, rfl, ht, h1⟩
    · injection hsub' with _ h2; cases h2
  | two => intro hu; omega

theorem bar1T_sound {useTag S N idx ori pool} {u i : Nat}
    (hp : poolOK 62 pool = true)
    (hb : bar1T useTag S N idx ori pool u i = true)
    (hr : ∀ {v ys}, NatRun1T 62 useTag (goal 62) v ys → NatRun1T 62 useTag (goal 62) v (ori ys))
    (h : NatRun1T 62 useTag (goal 62) u (S u i)) :
    ∃ q < u, ∃ j < N q, NatRun1T 62 useTag (goal 62) q (S q j) := by
  by_cases hu0 : u = 0
  · subst hu0; have heq := zero_done1T h rfl
    simp [bar1T, heq, goal62_eq] at hb
  · by_cases hu1 : u = 1
    · subst hu1
      simp only [bar1T, Nat.beq_eq, show (1 : Nat) ≠ 0 by omega, ite_false, ite_true] at hb
      rcases one_done1T h rfl with heq | ⟨a, heq, hta, ha⟩
      · simp [heq, goal62_eq] at hb
      · simp only [heq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', mask62_eq, goal62_eq, Nat.land_eq, Nat.xor_eq] at hb
        have hta' : (useTag && a.testBit 124) = false := hta
        have ha' : (a &&& mask 62 ^^^ mask 62).beq (goal 62) = true := by rw [Nat.beq_eq]; exact ha
        cases hu : useTag <;> cases ht : a.testBit 124 <;> simp_all
    · have hu2 : 2 ≤ u := by omega
      simp only [bar1T, Nat.beq_eq, hu0, hu1, ite_false, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
      have aux : ∀ u0 ws, NatRun1T 62 useTag (goal 62) u0 ws → u0 = u → ws.Perm (S u i) →
          ∃ q < u, ∃ j < N q, NatRun1T 62 useTag (goal 62) q (S q j) := by
        intro u0 ws hrun; induction hrun using Run1T.fold with
        | done u1 hu1' => intro h1 _; omega
        | perm p _ ih => intro h1 p2; exact ih h1 (p.trans p2)
        | @one s a r save he ht hsub _ =>
          intro h1 p2
          have hsu : s = u - 1 := by omega
          have hodd : u % 2 = 1 := by omega
          have hsn : scanNot useTag (u / 2 + 1 - (S u i).length) (okChild S N idx ori pool (u - 1)) (S u i) [] = true :=
            hb.1.resolve_left (by simp [hodd])
          obtain ⟨ra, hra, hck⟩ := scanNot_sound useTag _ _ (S u i) [] hsn p2.symm
          simp only [List.nil_append] at hra
          have hsub' : NatRun1T 62 useTag (goal 62) (u - 1) (((a &&& mask 62) ^^^ mask 62) :: kept save a ra) := by
            rw [← hsu]; exact Run1T.perm ((keep_perm hra save a).cons _) hsub
          have hcov : Nat.land (covUp 62 (((a &&& mask 62) ^^^ mask 62) :: kept save a ra)) lo62 = lo62 := by
            rw [lo62_eq]; exact required_up hsub' (by omega)
          have hta' : (useTag && a.testBit 124) = false := ht
          have hlen := run1T_len hsub'
          have hplen := p2.length_eq
          simp only [checkNot, hta', Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true,
            Bool.not_eq_true', Nat.beq_eq, mask62_eq, Nat.lor_eq, Nat.land_eq, Nat.xor_eq] at hck
          have hok : okChild S N idx ori pool (u - 1) (((a &&& mask 62) ^^^ mask 62) :: kept save a ra) = true := by
            cases save <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcov hlen ⊢
            · have e1 : (covUp 62 ra ||| diffUp 62 (a &&& mask 62 ^^^ mask 62)) &&& lo62 = lo62 := by
                rw [covUp_cons, Nat.lor_eq, Nat.land_eq] at hcov; rw [Nat.or_comm]; exact hcov
              exact hck.1.resolve_left (by simp [e1])
            · have hsl : u / 2 + 1 - (S u i).length ≠ 0 := by
                have := hra.length_eq; simp only [List.length_cons] at hplen hlen; omega
              have e1 : ((covUp 62 ra ||| diffUp 62 (a &&& mask 62 ^^^ mask 62)) ||| diffUp 62 a) &&& lo62 = lo62 := by
                rw [covUp_cons, covUp_cons, Nat.lor_eq, Nat.lor_eq, Nat.land_eq] at hcov
                have e2 : (covUp 62 ra ||| diffUp 62 (a &&& mask 62 ^^^ mask 62)) ||| diffUp 62 a =
                    diffUp 62 (a &&& mask 62 ^^^ mask 62) ||| (diffUp 62 a ||| covUp 62 ra) := by ac_rfl
                rw [e2]; exact hcov
              exact hck.2.resolve_left (by simp [hsl, e1])
          simp only [okChild, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, found, decide_eq_true_eq] at hok
          rcases hok with ⟨⟨he', hl'⟩, hscr⟩ | ⟨hj, hp'⟩
          · rw [scr62_no hp hsub' he' hl'] at hscr; cases hscr
          · exact ⟨u - 1, by omega, idx (u - 1) (ori _), hj, Run1T.perm (isPermFast_sound hp') (hr hsub')⟩
        | @two s a b r conj ka kb hc hta htb hsub _ =>
          intro h1 p2
          have hsu : s = u - 2 := by omega
          have hmod : Nat.beq (u % 2) 1 = Nat.beq ((u - 2) % 2) 1 := by congr 1; omega
          obtain ⟨ra, hra, hcp⟩ := scanPairs_sound useTag _ _ _ (S u i) [] hb.2 p2.symm
          simp only [List.nil_append] at hra
          have hlen := run1T_len hsub
          have hplen := p2.length_eq
          have hralen := hra.length_eq
          have hka : ka = true → 1 ≤ u / 2 + 1 - (S u i).length := by
            intro hka'; cases kb <;> simp [kept, hka'] at hlen hplen <;> omega
          have hkb : kb = true → 1 ≤ u / 2 + 1 - (S u i).length := by
            intro hkb'; cases ka <;> simp [kept, hkb'] at hlen hplen <;> omega
          have hkab : ka = true → kb = true → 2 ≤ u / 2 + 1 - (S u i).length := by
            intro hka' hkb'; simp [kept, hka', hkb'] at hlen hplen; omega
          rcases hcp with hcp | hcp
          · simp only [checkPair, Bool.and_eq_true, Bool.or_eq_true, mask62_eq] at hcp
            have hsub' : NatRun1T 62 useTag (goal 62) (u - 2)
                ((if conj then (a &&& b) &&& mask 62 else (a ||| b) &&& mask 62) :: kept ka a (kept kb b ra)) := by
              rw [← hsu]; exact Run1T.perm ((keep_perm (keep_perm hra kb b) ka a).cons _) hsub
            rw [hmod] at hcp
            cases conj with
            | false =>
              obtain ⟨j, hj, hres⟩ := checkW_fire hp hr hcp.1 rfl rfl rfl hta htb hka hkb hkab hsub'
              exact ⟨u - 2, by omega, j, hj, hres⟩
            | true =>
              obtain ⟨hca, hcb⟩ := hc rfl
              have hca' : (useTag && a.testBit 124) = false := hca
              have hcb' : (useTag && b.testBit 124) = false := hcb
              have hck : checkW (Nat.beq ((u - 2) % 2) 1) _ _ _ _ _ _ _ _ _ _ ((a &&& b) &&& mask 62) = true :=
                hcp.2.resolve_left (by cases hu : useTag <;> simp_all)
              obtain ⟨j, hj, hres⟩ := checkW_fire hp hr hck rfl rfl rfl hta htb hka hkb hkab hsub'
              exact ⟨u - 2, by omega, j, hj, hres⟩
          · simp only [checkPair, Bool.and_eq_true, Bool.or_eq_true, mask62_eq] at hcp
            have hsub_swap : NatRun1T 62 useTag (goal 62) (u - 2)
                ((if conj then (b &&& a) &&& mask 62 else (b ||| a) &&& mask 62) :: kept kb b (kept ka a ra)) := by
              have he : (if conj then (a &&& b) &&& mask 62 else (a ||| b) &&& mask 62)
                  = (if conj then (b &&& a) &&& mask 62 else (b ||| a) &&& mask 62) := by
                cases conj <;> simp [Nat.and_comm, Nat.or_comm]
              rw [← he, ← hsu]
              refine Run1T.perm (List.Perm.cons _ ?_) (Run1T.perm ((keep_perm (keep_perm hra kb b) ka a).cons _) hsub)
              cases ka <;> cases kb <;> simp [kept]
              exact List.Perm.swap _ _ _
            rw [hmod] at hcp
            cases conj with
            | false =>
              obtain ⟨j, hj, hres⟩ := checkW_fire hp hr hcp.1 rfl rfl rfl htb hta hkb hka (fun hb' ha' => hkab ha' hb') hsub_swap
              exact ⟨u - 2, by omega, j, hj, hres⟩
            | true =>
              obtain ⟨hca, hcb⟩ := hc rfl
              have hca' : (useTag && a.testBit 124) = false := hca
              have hcb' : (useTag && b.testBit 124) = false := hcb
              have hck : checkW (Nat.beq ((u - 2) % 2) 1) _ _ _ _ _ _ _ _ _ _ ((b &&& a) &&& mask 62) = true :=
                hcp.2.resolve_left (by cases hu : useTag <;> simp_all)
              obtain ⟨j, hj, hres⟩ := checkW_fire hp hr hck rfl rfl rfl htb hta hkb hka (fun hb' ha' => hkab ha' hb') hsub_swap
              exact ⟨u - 2, by omega, j, hj, hres⟩
      exact aux u (S u i) h rfl (List.Perm.refl _)

theorem bar1T_all {useTag S N idx ori pool} {cap : Nat}
    (hp : poolOK 62 pool = true)
    (hr : ∀ {u ys}, NatRun1T 62 useTag (goal 62) u ys → NatRun1T 62 useTag (goal 62) u (ori ys))
    (hc : ∀ u ≤ cap, ∀ i < N u, bar1T useTag S N idx ori pool u i = true) :
    ∀ u ≤ cap, ∀ i < N u, ¬ NatRun1T 62 useTag (goal 62) u (S u i) := by
  intro u; induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar1T_sound hp (hc u hu i hi) hr hh
    exact ih q hq (by omega) j hj h

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj; rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_testBit_ge {n : ℕ} (a : BFn n) (l : List ℕ) (j : ℕ) (hj : l.length ≤ j) :
    (encL a l).testBit j = false := by
  rw [encL_testBit, List.getD_eq_default _ _ (by simp; omega)]

def encT {n : ℕ} (l : List ℕ) (k : ℕ) (useTag : Bool) (p : BFn n × Bool) : Nat :=
  encL p.1 l ||| (if useTag && p.2 then 1 <<< (2 * k) else 0)

theorem encT_and_mask {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) : encT l k useTag p &&& mask k = encL p.1 l := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, encT, Nat.testBit_or]; by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    cases hb : (useTag && p.2) <;> simp [hm, Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge p.1 l j (by omega); simp [hm, he]

theorem encT_tag {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    (useTag && (encT l k useTag p).testBit (2 * k)) = (useTag && p.2) := by
  rw [encT, Nat.testBit_or, encL_testBit_ge p.1 l (2 * k) (by omega), Bool.false_or]
  cases useTag <;> cases p.2 <;> simp [Nat.testBit_shiftLeft]

theorem encT_inv {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    encT l k useTag (invFT p) = (encT l k useTag p &&& mask k) ^^^ mask k := by
  rw [encT_and_mask l k hl useTag p]
  simp only [encT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq; intro j; rw [Nat.testBit_xor, encL_testBit, encL_testBit]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    simp [hm, hjl, invF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]; simp [hm]

theorem encT_and {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (meetFT p q) = (encT l k useTag p &&& encT l k useTag q) &&& mask k := by
  simp only [encT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;> simp [hm, hs, encL_testBit, hjl, meetF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (meetF p.1 q.1) l j (by omega); simp [hm, he]

theorem encT_or {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (joinFT p q) = (encT l k useTag p ||| encT l k useTag q) &&& mask k := by
  simp only [encT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;> simp [hm, hs, encL_testBit, hjl, joinF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (joinF p.1 q.1) l j (by omega); simp [hm, he]

namespace Sub6
abbrev fG : BFn 6 := fun x : Fin 6 → Bool => (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)
def taggedFn (_ : ℕ) : Bool := false
theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 9) (_ : notCount gs ≤ 1) (_ : SCleanL 6 gs)
    (_ : ∀ p, p < gs.length → 6 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 6 + p ∈ g.inputs)
    (_ : ∀ x, val gs 6 o x = fG x) : ∀ a, a < 6 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h
def rowsG : List ℕ := [1, 1, 2, 7, 8, 8, 8, 12, 12, 12, 12, 24, 32, 32, 7, 12, 17, 24, 7, 12, 24, 7, 17, 12, 24, 3, 3, 3, 4, 4, 2, 7, 16, 16, 16, 17, 17, 17, 17, 24, 32, 32, 7, 17, 12, 24, 7, 17, 24, 7, 12, 17, 24, 6, 6, 6, 2, 7, 24, 24, 32, 7, 9, 33, 10, 15, 9, 10, 40, 13, 14, 28, 44, 25, 33, 40, 9, 9, 9, 9, 10, 10, 10, 33, 33, 40, 40, 11, 19, 35, 20, 36, 18, 23, 20, 18, 48, 21, 19, 25, 49, 28, 36, 48, 20, 20, 20, 20, 18, 18, 18, 36, 36, 48, 48, 22, 14, 38, 34, 39, 26, 56, 34, 34]
def xsG : List ℕ := [0x80001e2398f626e20acc788e65400b, 0xdf87004b387004b23e24400ce24400c, 0xb98f626c0001e222e65400b0acc788, 0x310002800e7fbff4c153080019a8ff0, 0x30e7fbff50002800c19a8ff01530800, 0xee780d10a780d109000030000003000]
def NN : Nat → Nat
  | 7 => 2
  | 8 => 2
  | 9 => 93
  | 10 => 68
  | 11 => 310
  | 12 => 322
  | 13 => 237
  | 14 => 291
  | 15 => 20
  | 16 => 24
  | 17 => 1
  | 18 => 1
  | _ => 0
def dictChunk (b : Nat) : Nat := if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x400001100000111101220040122004020000008000000888091002009100201000000040000000000000000000000080000000000000000000000000000001cc7b1360000f111732a00585663c400e63d813000070003904000c2221e000331ec4d80003c445cca80161598f100180f22640001e200041000008887800080010000000f100020800004443c000400020039fedfd0010400002221fc00200000010fe0dec7cca801fd598ffe00e7f97f50000000008887f00410000004c7b1360000d000020800184443c000203cf994000a00002221e0010400000101e44c800010000000000000000000080000200000000000000000000000003c7e9a60c0200480445bf9820980180063d893000068000104000c2221e000001e548801e548983b71fe63b71fe6000001e2180f2264008887800410000000000f108c7b126004443c002080018000007884000800002221e001040000000003c0731ec49801110f01c820006000001c0398f626c00888780e410003000000d000c7b126004443c00208001800000388603c899882b31e23995002c00000100101e44c8000000000000000000000800000200000000000000000000000021080000000000000000000000000000000000400000000000000000000000000000004400000000000000000000000000000000000000000000000 else 0x54c7b1360000d011732a00585663c402a63d89b000060000000000000000001531ec4d800010045c48801604880100a98f5e6f98f626e2eacc78be65400b054c7a136000000117122005812200402863d893000068000104000c2221e0014300bc5731ee4dc41598f11cca80160a180500a1805008000000000000000050c02114000091110122004012200402860100200004000000000000000000140003c4731ec4dc41598f11cca8016090001e2398f666e20acc788e65400b0443f8f7bcc7b1371f5663fff32a00782203cf99e63da9b882b31e23995002c1101e44c80001444404880100488010088001e2398f626e20acc788e65400b040000f11cc7b937105663c4732a005820000788e63d89b882b31e23995002c100003c47000404441598f11cca8010080001e2318f624e20acc788e65400b040000f108001111105663c4032a004020000708e63d89b880910023891002010000380731ec4dc41598f11cca8016080001a2018f626e20acc788065400b040000c014c7b136000000000000000020000588c601002882b31e23995002c100002847300805440488011c4880100800010021804008000000000000000040000711cc7b137105663c4732a005820000308e03c8998809100238910020100000c47000044440488011c488010080000423800002220244008e244008) else if Nat.blt b 3 then 0x8c3f977ac3f977b7fffe7fffffe7ff8461c012c61c012c8f89100338910030230e009630e00960000000000000000110002800e7fbff4c153080019a8ff008800140043f977a60a984000cd47f804400080021c07ac0010400002221e002200010010fe4de800000000000000011000000087004b00000000000000000843f937a80004000000000000000000421c07ac4000800002221e001040000210e009620000000000000000000000100700c9187f20d4d19a8ff4f530877080000000000000000000000000000002e63df9be63df9b8bbb71e2fbb71e2c1731efcda0007c445ddb8f161db8f100b98f7a6e98f7e6e2e65400b0acc78805cc7b9370c02f151732a00585663c402e63da9b203cf998b995002c2b31e201731ed4d80007c445cca80161598f100b98f666f8001e222e65400beacc78805cc7b13673fcffb1732a00585663fc02e63d89b00007888b995002c2b31e201731ec4d80003c40008200001110f000b9805e2b98f766e2eacc788e65400b05c079f33cc7b737175663c4732a00582e000788e63d99b8bab31e23995002c17000084700008445c488011c4880100b800022000006222e244008024400805c000010000021117122004012200402c60180200007880010400002221e001531efcdf31ef4dc41598f11cca80160a98f626c0001a22202440080244008 else if Nat.blt b 4 then 0x143c7ffb7fc7fdb7f0fffffdffffffd8a18027c8fe3fcdb882b31e23995002c50c013e4731ec4dc41598f11cca8016280001e23f8ff36e20acc788e65400b1400008013c06884000000000000000084000a0039feffd3054c200066a3fc0420004000c013e40008200001110f002078ffb4c78ffb4dc1dbbff31dbbff3103c7f0a63004c80e0a99c398cd5ff8081e034421e0344240000c000000c00040c013200f1fc29b83357fe02a670e620600910060091000000000000000001030048800000000000000000000000080000a00183eed13054c200066a3fc0400001001c1f66c80000000000000002000000006009100000000000000000100000000000000000000000000000006e7fdbbf61fcfbdbffff3ffffff3ffc373fecdff0003c445cca8017d598f101b9ff66fd8701eb23e65400feacc78c0dcffb37e8000f111732a00585663c406e63da9b21fcfbd8b995002c2b31e203731eccdf0e03d645cca8017d598f101b98f626c8701eb22e65400b0acc7880dcc7b1360000f111732a00585663c406e1c012c40001088b891002009100203700000410e009645c4880100488010198701eb39ff66fe20acc788e65400b0c8000f11cffb37f105663c4732a0058621fcfbde63da9b882b31e23995002c310e03d6731ec4dc41598f11cca80161887004b3800002220244008e244008 else 0x188c7b52673fdffa60a984018cd47f80c4000f8879feffd3076e3e0076e3fc0620007001cff7fe982a610003351fe0310002c21e7fbff4c153080019a8ff018800151073fdffa60a984000cd47f80c4000a0039feffd3054c200066a3fc06200050000007c4182a610003351f003100020006709d90c153080019a8ff018800040073fd2fa6089040008904380c400000039c256c000000000000000061ffffffaf1ff69b83b77fe63b77fe630e7fbff5e0fbb64c19a8ff015308001873fdffac07953260cd47f80a984000c39feffd5802e403066a3fc054c200061cff7fea31ed49983351fe02a6100630e7fbff50002800c19a8ff015308001873fdbfa800040060cd47f80a984000c39fedfd4000200000000000000000061cff5fea000500183351fe02a6100030e7fa5f50000800c112087011208001873fd0ea00004006089043808904000c21c0b2c4000a0030448200044820006101e54c80005001822410002241000300002800600b900c1120800112080018000140000014006089040008904000afe3fcdb860178a8b995002c2b31e2057f1fe6d80003c445cca80161598f102b98f626c6009f222e65400b0acc78815cc7b1360000f111732a00585663c40a9e037cae63dc9b882b31e23995002c543008010c01220000000000000000028e0fbf6798f6a6e20acc788e65400b) else if Nat.blt b 8 then (if Nat.blt b 6 then 0x1dcc7b53673fdffa60a984000cd47f80ee63da9b0000f88bbddd202c6fb3e207731ec4d9ce13f645cca80161598f103b780f908e7fbff4c153080019a8ff01d8c03c057fffffe60a984000cd47f80ec601a0239feffd3054c200066a3fc0760005001cff7fe982a610003351fe03affffffd600b900c19a8ff015308001d7fffffe8001c0060cd47f80a984000e5802e40bffffff3054c200066a3fc0720007c47ffffffdc3ff9f11fff9ff6390003802ffffffcc153080019a8ff01c800151073fdffb70bba4040df67fc0e4000a00b9feffd3054c200066a3fc0720005001cff7fe982a610003351fe038e7fbff798f6a6ee1becff8f77480b1c73fdffbcc7b53660cd47f80a984000e39feffde000a08b86fb3fe3ddd202071cff7fee300d01183351fe02a6100031ffffffdffffffffffffffffffffff18f3fdffaf3fdffa60edc7f80edc7f80c79feffd79c2f6c3066a3fc054c200063cff7feb0fe5dedffff9ffffff9ffe31e7fbff587f2ef4c19a8ff0153080018f3fdffac38165860cd47f80a984000c79fea7539feffd3054c21c066a3fc063ce17b63cff7fe982a610003351fe03187f2ef5e7fbff4c153080019a8ff018c381658f3fdffa60a984000cd47f80c603ca9939feffd3054c200066a3fc0630005041cff7fe982a610003351fe031600b900e7fbff4c153080019a8ff0 else if Nat.blt b 7 then 0x6bc380258c3802591f122006712200635e1c0124e1c01240780000138000011af0e001200e009203c0000080000008d5070049387004b010000004e00000467ffffbff8c02f159f76fbfff76fbc7b3ffff5ffffff5ffcfbb7dfffbb7dffd9f3fecdfe0003c447cca801fd598f18cf98f666f8001e222e65400beacc78867cc7b1377ffefff9f32b807f567bffb3e63d89ba1c07ac8f995003fab31e319f31ec4dc0003c445cca80161598f10cf180400afffd7ff3e65700feacf7ff678000f11cffb37f1f5663c6732a007b3c000000a1c012c8f891003389100319dfffaffe30080167d59efffccae01ece87004b300000023e24400ce24400c673c068850c0200480001800000180033860178ae63dc9b882b31e23995002d9c300801430080167c48e01fc48e01ece180400a0001000000000000000000670000f11cc7b137105663c4732a005b38000400860100200000000000000019c0000847000004440488011c488010ce00000020000000000000000000000638c020043384ac88f2098038445bfa310000000bfff07744000c013800c1dc77fffffff31efcdddfff9ff7fff9f163bffffffde7fbff6efffcffb1ffcff81dffffffe8001f1177ffe7fd8ffe7c40effffdff40007888b995002c2b31e2077cff7fea0005845df7d9ff02ee90103b98f6a6ce7fbff6ef77480b1becff8 else 0x6fcffb77fc3f9f7b1f32a007f5663c637e7fd9bfe1c07ac8f995003fab31e31bf3fecdff0e039647c488019c488018df9ff66ff0001e222e65400b0acc7886fcffa37fc3802591f122007f12200637e7c152ee7c152e8f89100338910031bf3e08977fffaffe7ccae01fd59effedf9f044bb87014b23e24400ce24400c6fc3f977bc3f977b7fffe7fffffe7ffb7e1fc9bde1c03ac8f89100338910031bf0fe4def0e019647c488019c488018df87024b38701eb23e65400ceacc78c6fc380f59cffb37f1f5663c6732a007b7e1c07ace7fd9bf8f89100338910031bf0e03d670e049647d598f19cca8018df8701cb39ff66fe3e24400ce24400c6fc380b59cf8235d1f122006712200637e1c052ce7c112e8f89100338910031bf0e019673fecdfc7c488019c48801edf8700cb387f26f63e24400ce24400c6fc380659c3812591f122006712200637e1c01ace1c01ac8f89100338910031bf0e009670e029647c488019c488018df87004b387006b23e24400ce24400c6fc380259c3802591f122006712200637e1c012ce1c012c0000000000000001bf0e009660e009247c488019c488018df0001e239ff66fe20acc788e65400b6f8000001438025800000000000000037a7fd9bfc0006000000000000000001bd0e03d6731ec4dc41598f11cca8016dc0701eb39ff62fe30acc78ce65400f) else if Nat.blt b 9 then 0x7bffffdee3ffffeeefeddffb8eddffbbdffffbff79feffdfffffffffffffffdeffffc3b8ce13b23bea670ee3357fe8f5670bd93ffffffdd1dbbff4fdbbff77a73fdffbffff4eee8cd5ffa7a99c3bbd19c2764ffff8777466affd3d4ce1dde8ce10320ce10323a22470e822470e8eff8fff6ff8fff6f2eedf78beedf78b77fc7f9b73c06f959732b8058567bc43bfe3fcdb80007888b995002c2b31e21df31ec4dcc013e445cca80161598f10ef780f10a780df2900413000088b78077bc068857ffebff9f32b807f567bffbbbffffffde3fed3fffffffffffffffdddf1fe6dcf01b212000060000006000eef80d12a780d109000030000003000773c7fda73c7fda6e0eddff98eddff9bb9e037cafe3fcdbc82b3de23995c02ddcf01b215f1fe6da000060000006000ee780d90a780f109000030000003000773c06a95fc068959012380471238043b9e0354ade0344240000c000000c001dcf01a654f01a6564048e010048e010ee780d10a780d329000030000003000773c068853c068848000180000018003b980244080000000000000000000001ccf018210c012202000060000006000dffffffff9ff6efffffffffffffffff6ffffebffcf8225d9f567bfff32b807b7e7fdfbfe7fdfbf8fbb71e3fbb71e3dbf3fefdff3fefdfc7d598f19cca801edf9ff76ff9f05eba3e65400feacc78c else if Nat.blt b 10 then 0x7ff384ed9ffff2ffffdf7ffe7bbbc3fbff9c256cf9c256c8f89100338910031ffce12b670e009647c488019c488018ff9ff6effe7fbff6ff77480ffbecffc7fcffb37ff384fd91f32a007f5663c63fe7c112ef9c256c8f89100338910031ff0e07d67ffffffdffff9f19fff9ffeff8702cb3e7fbff6ff77480cfbecffc7fc381659c3816597f9b240679b24063fe1c07acffffdff8fab31e33995003dff0e01967cff6fec7c488019c488018ff87004b3e7095b23e24400ce24400c7fc380259c3802591f12200671220063fdfc3766ffffdfffffffffffffffffdfef01f215ffffffb82a670003357fe0ff780d90affff7fd0000300000030007fbc068857f86adc8000180000018003fd802e40b9feffd3054c200066a3fc1fe300d015ffffffffeeef01ff7dfffeff180680ae7fbff4c153080019a8ff07f800140173fdffa60a984000cd47f83fbfffffffe3fedbf86fbffe3ddde02dfdffffffef01f21383357fe02a67000fefffffff0003800c19a8ff015308007f7fffbffbc06c848000180000018003fbfc356ede0344240000c000000c001fdcff7feec01720183351fe02a61000fee7fbff70002800c19a8ff015308007f3f86ecdffff8eee8cd5ffa7a99c3bbf9e03e429e03e4270448e000448e001fcf01a214f01a212000060000006000f7ffffddfffffddddfdbbff7fdbbff7 else 0xfffffffffffffffffffffffffffffff7ffffffffffffffee0eddff80eddff83ffffffffe1c0facbffff3ffffff3e31ffffffffef01fe57dffffff63ffff10ffffff7ffff0dfbb3e65700feacf78c7fffffbffc380f591f32a007f5663c63fffff8ff19c27ecffddde1fc6fbfff1fffffc3bdfffbffffeeef0fff7dfffeffff0fdbbfffffffff77780cfbefffc7fff86addff86add9f12380671238063fffc356effc356e40000c000000c001fffe1ab770e029647c488019c488018ffe7fbff7e7fbff6ffffcffcfffcffc7ff3fdffbcffb77f7fdf67fe7bba407bff9feffde1c0b2cbfefb3ff3ddd2031ffcff7fef0e0596183351fe02a61000ffe709fb39ff66fe3eacc78ce65400f
def wireAt (i : Nat) : Nat := Nat.land (Nat.shiftRight (dictChunk (i / 32)) (125 * (i % 32))) 0x1fffffffffffffffffffffffffffffff
def stateWires : Nat → Nat → List Nat | 0, _ => [] | n + 1, ids => wireAt (Nat.land ids 0x1ff) :: stateWires n (Nat.shiftRight ids 9)
def htChunk_7 (_ : Nat) : Nat := 0x61bf9c2c8c43
def stChunk_7 (_ : Nat) : Nat := 0x983f96a904a749de69a4
def htChunk_8 (_ : Nat) : Nat := 0x61bf9c2c8c43
def stChunk_8 (_ : Nat) : Nat := 0x983f96a904a749de69a4
def htChunk_9 (_ : Nat) : Nat := 0xdb3905d9b31dd9034cd3bd7cd324f2cd6924c94142c85360c75e64c6ede2c2f9f9beb647bd38cabbb687b9ec9fb15f16afd2c3af0a4ba8bb24a706a0a6cb64a45e1e9acf42989ec39422708ad4d589423e8135608000637faa387f9e907f2c5f7f08767eee507bc6047ab18e77059575c69b716fb36d817b6d43b76a5f9768d4cc67010d6012b85ff8b55cb57c58909a55281c5475e3546bd85421625110bf4ddbdf4d7c234c77b94be6414bb3ac498caa47e0a547cee44346cc4271d1422c00422a6c41cdc83e0d493c33ce3b497238037934d6e534c47d2d95ca2af6f72ad5e62154671fd7ac1dd2e31c404e19da7118dac116ce10160362155d4415584614caa811c7700d8c350ac38e0a35f009518008404a02dfb2
def stChunk_9 (b : Nat) : Nat := if Nat.blt b 1 then 0x83bcdc49a482c99e69a4812960eec4d2409eb4795bcd204a58bb9d709a172cee6d074d241622e74d24082b479232d344a5a1c1de6a3252c35cead4d1296713079a4094b2483bf9e69a583bf93490322d19e69a4812960ee757a68a0b077ea69202e59c41de6a7252c1dfabf480b96770779a6920b3883bcd504a5a3cadfc90172d0a4cfe4d0b96712f7f2405cb0773ad5264e583bf9e69a49ac99e6a34812968f2b481285cb0d73ad5204e586bf9e69a482c1e00f34d24161ae757a6894b077f2a9342e5 else if Nat.blt b 2 then 0x933cd349035ac1e02fd4d24168f2b65a4094b47943f9342e5a141de6a3252d060efe4d0b960efe79a691cb077f3cd34925a3ca1344a172c1de69a4712964cf35826894b1173b11342e583bcd849a482c1dd8b44812968d38481285cb077ab01562e583bf980a7172d1e5c90250b960ef24d24094b47963f9202e583bf5e69a482c1dfab74d0b960eec5aa4c94b077f3cd489059839d6a90252c45cec0558b968f414d1285cb4796240942e5933f9e69a482c35d8b548129673077f240b2b0779a91204a5 else 0x1077f269206359441dfcf34d2c1de69a481b561ae74d2409eb07782ad204a59ccc1ce90252c45ceb74d0b960efe5aa40b2b077ea692041583bfde69a482c45cec3510b9622f84d2405cb0779a8d206b593bf9e69a482c1dfcf34d2416792f7f2405cb2c83bf9e690583b9d80ab192c1dfce44d241622fd4d2405cb077f3cd7490583bf9e6b4482d2e0ef34d241660fe4d2405cb077aae9202e586b9d6a90252c1dfcf351a4168f2b921285cb0779a8d204a5
def htChunk_10 (_ : Nat) : Nat := 0xdb3905d9b31dd9034cd3bd7cd324f2cd6924c94142c85360c75e64c6ede2beb647bd38cabbb687b9ec9fb7747bafd2c3af0a4ba8bb24a706a0a6cb64a45e1ea423719acf42993a11989ec394227089423e8000637faa387f9e907bc6047ab18e770595716fb36a5f9768d4cc6012b858909a5475e3546bd85110bf4ddbdf4d7c234bb3ac47e0a547cee44346cc4271d1422c003e65c33e0d493c33ce34d6e534c47d2d95ca2af6f72ad5e62154671fd7ac1c404e19da7118dac114caa811c7700a35f009518008404a02dfb2
def stChunk_10 (b : Nat) : Nat := if Nat.blt b 1 then 0x83bd580ab172c1de49a4812960efd79a6920b077eadd342e583bf9e6a4482cc1ceb548129622e7602ac5cb267f3cd349059cc1dfc902cac1de6a44812960ef37126920b2679a69204a583bb1349027ac1de6d94d2416773683a6920b1173a692041586b9d5a9a252ce260f348129649077f3cd34b077f26920645a33cd3490252c1dceaf4d14160efd4d2405cb077eafd202e59dc1de69a482ce20ef35412960efe79a6926b2679a8d204a586bf9e69a482c1e00f34d24161ae757a6894b077f2a9342e5 else if Nat.blt b 2 then 0x83bc15690252ce660e748129622e75ba685cb077f2d52059583bf5349020ac1dfef34d241622f84d2405cb0779a8d206b593bf9e69a482c1dfcf34d24160eed4d24094b2c83bf9e690583b9d80ab192c1dfce44d241622fd4d2405cb077f3cd7490583bf9e6b4482c1dfc97480b96970779a6920b0779a69206c5983f93490172c1deaba480b960efe79a8d20b0779a8d204a5933cd349035ac1e02fd4d241683077f2685cb077f3cd348e583bf9e69a492c1de69a4712960ef36126920b07762d1204a5 else 0x83bf9349031aca20efe79a6960ef34d240dab0d73a69204f5
def htChunk_11 (b : Nat) : Nat := if Nat.blt b 1 then 0x395f0638f22e38ca1f3897913848e437e5d737cfef37c57c365f9435335e34ab4833fce8322f9a32245d31bf96311078310e2730d58d301d2b2fda172ea5772e83a12e41622e3fb62d4b522d37d62d33292c49f12b93392b1f7e2a135229018028f6c3289c4f271b0325f79b25f30e2562ce24be88235868225695211314208db92082371fd7ac1fabc51fa4dd1f98391ec4701e9d421e0b571df83f1dd9281d7f221cf4811caffc1c92051b68131a437d19e06f19cb4319b20d18f16318a1af17ecda179dd1176a5e17133a163bd81620e915992b1587a91574b91535ca14720f14305313c305136d82133d62123e3d11db8a11d0a611053b10568e101e360f8bf00f87330f4ce80e5bf60e035a0e01500dec8e0d9a6a0d8c350d852f0c73930c3e3f0bcfa30bcc280b48eb0b30340ac9f7088fcd088ecb08806f08789f07c36007b58c0722f607154f0714b306a7770602a005862b04d3c904c737046d460406b303491b0331b802ea530207e701db7a01798700e81500e6eb00e08f002bb1 else if Nat.blt b 2 then 0x99c33399b8fb98dbc097b6ed96c18294a68093980b93039f92e7a791312990fa9e90d7c9907a61903a528f67a88ef9688d7b768d0eea8b1e808b00898ad4d58a4a0887adc986f87786e4ee85fc06858abe83f62d82666c80be46806bd18000637fc5717f46087e523f7df8b17c766e7b77437aac8678928378304678017677b96477b373772ed37601d2755e8173d5af733493716aab70d0317092aa6f8f866eee6b6ad09e69d19569b62c67e247678eb2678b4b6787f36772ce6750cf6661f165d423651e0563d45a6321d8622fa36008495fd36b5ea5475e49705d94fa5d3a865bdc2a5b8f295ac8695a27c75a157a5892f657dcb456573b55c70d553d0a551451542f2c52d2c551cfb451085c50ec874cc4154c14f84baeb64ba4144b3c224a71dd4a0225497ab948c565487cd1479eb6468cdd468c4146659e463517462f3c44ae8644332a44037c43b19a4314fc4271d1424927422c4641a2b54173f240c04a40af9d406a1f3fae373f258e3cd37a3b71753af14f3ac1a13a12c339645b else 0xeb95cde6855be4bd24e28f67e1fad1db4f28db3905da8df0d94e57d133b7d09723ca1167c9f583c4d889c35e34c28cb1c1b3fcbf17c9bc9124bad407ba9a3dba53afba08e7b9ec9fb7e93db653a2b60014b01139af4abdaeda35aea312ae6accacf4e1aa2defaa2685a70615a6a64ea44603a33378a17aeda162eca0f8c8a0e4aaa069faa015c39f9b739f675c9eae239c9fee9c4c739bfdcb9b58419a96ed9a7304
def stChunk_11 (b : Nat) : Nat := if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x83b9d34903418da0ee74d241004a69341de69a48129a0efe79a692044683bd53490250b9a69314d240942e683ba53490250b9a0ee752240942e697bf93490250b9a570773b55202e683bcd34902b929a75074d240942e69c41de6ab48129a2f0773a692039683bcd34902a929a0ee757a6894276a141de69a2a929a0ee74d241062e688b9d809a480b9a0efe79b0d3490683b9d3490421f1a0ee771269202e6a3cc5fc9a480b9a4ce74d240942e6a3cadce90250b9a630773a40f84a688bf9ce9a480b9a712f73a40942e683b9db09a480b9a0ef373a69264a683b9d3490250c1a0ee74d24094486 else 0xa14993490250b9a0efe73a692027683bd5809a480b9a0ee74d240c84a683b9d3490250d1a8b074d240942e683b9d3890250b9a1ae755a40942e68741ddc9a48129a0efd73a69202e683bf9ea9a480b9a10e74d240942e683b9d3494250b9a0ee74d241044a683bf9e29a480b9a4b0773a68942e683bcd469a48129a0efe73a91202e683bf9e69a4815da0efe79a692055683bcd349030129a0efe4d240c658683bf9349025119a0ee74ea40942e683b9d34902509da0ee752a40942e6a14a60efe4d0b9a0ef373a692085683b9d6a90389298014795a40942e5a3b8d3490250b9a4cfe73a69202e6) else if Nat.blt b 3 then 0x95c1dce90250b9a8f077f269202e683bf9fcf34d241a0ef373a69204e683b9d6e9a17045a0eee5a240942e683b9d4490290b9a630778269204a6a5cf60e9a480b9a8ef365269204a683b9d3490430b9a0ef373a69206a60041dfa9a480b960ee761a885c11683b9d6890278b9a0ee75e240942e68739d6890250b9a0ef34d240ba4a683b9d6290250b9a0ee74d240922e683bf9e69a48129a6f077f269202e683b9d3490338b9a1ae75aa69204a686b9d3493250b9a0ef84d2405c116a3b55909a480b9a0efe79a69200a683b9d869a19045a490779b9d344a683b9d349025105a0efe4d259202e6 else if Nat.blt b 4 then 0x9a41dfc9a480b9a0ee74d240c44a683b9d3490268b9a1ae74d240a44a688b9d869a250b9a0ee74d24072116933cdce9a48129a0efe73a69242e68741dceb448129a0ee74d2409e2e683b9d569a250c9a730773a40b24a683b9d348e250b9a0ef358268aa4a683bcd4690250b9a0ef04d240942e683b9d869a17045a0efe79a69202469a41d3490250b9a0ee75ca40942e6a3cc5e69a48129a0ee74d248942e69339d609a250b9a0ee74d240802e690b9d3490250b9a22f373a69204a683b9d809017061a0efe79a692043683b9d34902511da0ee761269202e683bf9e6c04d241a0efd4d2407c2e6 else 0x83bf9e6cc4d241a0efe73a8d202e686b9d6a9025015a0ee75124094326a1c1dfc9a480b9a530773a68fa4a6a04f60e9a48129a2b0773a69202e683bfdd89a480b9a73077f3cd349068741dfcf34d241a69074d241082e683bf9dc9a480b9a8efe64269202e694c1dfcf34d241a0ee74d249082e600499e69a481296693183a40942e683bd93490250b9a1ae74d2409c2e69ec1dfc9a480b9a0ee751a40942e698c1dce92250b9a4ce74d240d62e6a141dcea3250b9a0efe4d240c64a683bf9c69a480b9a0efe73a691c2e683bb93490250b9a8ec84d240942e69ec1d4090250b9a0efe76269202e6) else if Nat.blt b 7 then (if Nat.blt b 6 then 0x9f41d3490250b9a0efe73ad1202e69339d349030929a0ef373a69244a683b9d56902509da0ee751240942e683bb95a9a250b9a1ae74d2409427683b9d7490250b9a570779b9d204a6a3c1dfcf34d241a0ee75a240942e6a5c1dce9a480b9a710748174942e683b9d3490250c9a0ee756a689e2e69e41dfcf34d241a0efa4d240942e683b9d869a1f0b9a710779a40b04a6a441de69a48129a0ee64d240942e686c1dceb548129a14e74d240942e683bcd349035929a0efe79a692056683b9daa9a480b9a0f027f3cd3490683b9d80a7250b9a0eea4d240a42e683b9dc29a48129a0ee75ba687c2e6 else 0xa041dce9a48129a0ee75da40942e683bcd349045129a0ee751a40d62e693bf9ce9a480b9a0ef34d240cc4a683bf9ce9a480b9a0efe79a6920056a641dfcf34d241a0ee74d2409435683b9d34902809da22e74d2406c2e68639d3490250b9a0efc73a69202e683bcdcea348129a0ee84d240942e693b9d3490250b9a0ee74d240942e68741dcead4d129a59077f39d202e683bcddc9a48129a990779a69204a6a3ce26290250b9a0ef373a69204f683b9d5e9a250b9a830773a68942e68bb9d3490408b9a0efe73ae9202e683bf9e69a481c1a6b074d240942e69641dce90250b9a0ee76026920326) else if Nat.blt b 8 then 0x83b9d3490368b9a52e74d2410a2e6933cd34902a929a0ee74d2409446683b9d34903f129a0ef373a89204a683c01dc9a480b9a8f2483a68942e683bcdceba48129a510773a68942e6a3c1d969a48129a0ee75ea69202e683bcdceb448129a0efe75269202e6a141dfc9a480b9a8f064d240942e68b41dce9a480b9a5ee753a68942e683bb16a9a48129a0eec4d24c942e600435ceb54812960ef54d2406c2e683bfdce9a480b9a0eea4d240942e683b9d6490250b9a0ee74d241082e683bcdced54d241a0eec55a40942e683bbd3490250b9a0ee75a2b4942e686bb13490250b98010779a8d204a5 else if Nat.blt b 9 then 0x83b9d3690250b9801077f3cd3490583bb16a9025015a0ee74d240d02e683bf94e9a2c0b9a0eec4d2409c2e683bf9e6e74d241a0efe79a692087683b9d3490358b9a8f2464268942e683b9d34923e129a0ee7602ac5c11683bf9cece4d241a0eec4d240a44a683b9d4290250b9a0ee761a68ae2e683b9d5a9a25015a630e73ad5204a683b9d469030929a0efe73a692046683b9d9c9a48129a0ee74d240d22e69ec1d3490428b9a0efe79aad34906a3cad3490250b9a0efe79b213490695c920ee7250b9a20e74d240942e699c1d3490250b9a710779a40b24a695c1dcecb48129a51077f39d342e6 else 0xa339d3490250b9a8ecc4d240942e683bad3490250b9a0efe79a692052683be13490250e5a0efe73a69206160041dfc9a4818d60ee74d240942f683b9d3490428b9a0efe79a69201f683bf9ce9a4818da0f0073a69202e683b9d889a17045a0efe79ba934906a141d3490358b9a0ee76ab2d3490686b9d3490250b9a870779a68aa4a69c41dfcf34d241a0ee75b240942e683bcdce9a48211a0ee74d240942a6
def htChunk_12 (b : Nat) : Nat := if Nat.blt b 1 then 0x37cfef37c57c365f9435335e34d8ec34ab48345e7533fce8322f9a31bf96315d8331107830de3f30d58d301d2b2fda172ea5772e83a12e3fb62d4b522d37d62c49f12b93392b1f7e2b1c9a2a135229018028f6c3289c4f271b0325f79b25f30e2599682562ce24be88235868226a79225695208db92082371fd7ac1fa4dd1f98391e9d421e0b571df83f1dd9281d7f221cf4811caffc1c92051c6fb71b681319e06f19b20d18f16318ad7d18a1af179dd1176a5e17271417133a167679163bd81620e915992b1587a91574b91535ca14720f144c1414305313c305136d82135297133d621323cc124fff123e3d11db8a11d0a611156e11053b10b1e010568e101e360fb77f0f96080f8bf00f4ce80e5bf60e4b230e035a0e01500dec8e0c73930c3e3f0c11690bcfa30bcc280b48eb0b3034091c22088fcd088ecb08806f08789f07f21107c36007b58c0722f607154f0714b306a77706374905862b04d3c904c737046d460406b303491b0331b80207e701db7a00e81500e6eb00e08f002bb1 else if Nat.blt b 2 then 0x93039f92e7a791312990fa9e90d7c9907a61903a528fdc8c8f67a88d7b768d0eea8c8d988b1e808b00898a4a0889af2487adc986f87786e4ee85fc06858abe83f62d82666c8134c480be46806bd18000637fc5717f46087f40317e523f7df8b17c766e7b77437af0367aac8678928378304678017677b96477b373772ed37601d2755e8173d5af733493722cea716aab70d0317092aa6f8f866eee6b6ad09e69d19569b62c67e247678b4b6787f36772ce6750cf6661f165d423651e0563d45a6321d8622fa36008495fd36b5ed74c5ea5475e49705d94fa5d3a865bdc2a5b8f295a27c75a157a59f9f859ea825892f6586f2a57dcb4553d0a551451549afa52d2c551cfb451085c50ec874df0174cc4154ba4144b3c224a71dd4a022548c565487cd1479eb6468cdd468c4146659e463517462f3c44ae8644332a43b19a4314fc4271d1424927422c4641e6c741a2b54173f240da3340c04a40af9d406a1f3f258e3cd37a3b71753af14f3a12c339645b395f0638f22e38ca1f38979137e5d7 else 0xf7dc52f60a3deb95cde7df23e4bd24e28f67e1fad1de68d2db4f28db3905da8df0d94e57d133b7d09723cb68e8ca1167c4d889c39bcbc28cb1c1b3fcbc9124bb73c5bad407ba9a3dba53afba08e7b9ec9fb99e0fb653a2b60014b5ef38b01139afc1c7af4abdaeda35aea312add040acf4e1ab2bafaa2defaa2685a70615a6a64ea44603a33378a17aeda162eca0f8c8a0e4aaa069faa015c39f9b739eae239d62099c9fee9c4c739bfdcb9b58419a96ed9a730499c33398dbc097b6ed96c18294a68093980b
def stChunk_12 (b : Nat) : Nat := if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x41dce9a481a0c6c0083bed3490250b98010773a6920802530024d0779a69204a60041dfcf34d24088c0083bd53490250b98010773a69204a0430020ee94d240942e60041dcea4481285cc0097bf93490250b98012b83b9daa901730020ee7481e8942e60041de69a4815c94c009d41d3490250b98013883bcd56902530022f0773a69203960041de69a4815494c0083b9d5e9a2509d801077f269205e1730020ee74d241062e600445cec04d2405cc0083bf9e6c34d2418010773a6920843e30020ee771269202e60051e62fe4d2405cc009339d3490250b98013183b9d207c25300222fe73a69202e60041dced84d2405cc0083bcdce9a499298010773a69204a1830020ee74d24094486 else 0x5160e9a481285cc0083b9d3890250b98010d73aad204a1730021d0777269204a60041dfae74d2405cc0083bf9ea9a480b9801077cbcd349025300210e74d240942e60041dce9a4a1285cc0083b9d3490411298010773a69202e0db0020efe78a69202e60041dce9a4812c5cc0083b9d34902508d8012583b9d344a1730020ef351a69204a60041dfce7522405cc0083b9d348f250b9801077f3cd34902bb0020ee74d240942c60041dfcf34d240aac0083bcd3490301298010772a69204a1730020ee74d240742e60041dfc9a4818cb0c0083b9d3a90250b98010773a69204a13b51e0efe55a69202e70041dcea5481285cc00a14a60efe4d0b98010779b9d349042b0024cfe73a69202e6) else if Nat.blt b 3 then 0x41dce9a480b826c0083bb96890250b98010773a892052173002630778269204a60041dfcf36a26920c00a5cf60e9a480b98010773a6920861730020ef373a69206a6000020efd4d2405ca0083b9d6890278b98010773af1204a1730020ef34d240ba4a60041dceb1481285cc0083b9d3490248b9801077f3cd34902530026f077f269202e60041dce9a4819c5cc0086b9d6a9a481298010d73a69264a1730020ee76b269202e60041df09a480b822c0083bf9e69a480298012483bcdce9a2530020ee74d240944160041de6d04d24094c0083bf93496480b9801077f39d349013b0020ef560269202e6a3d0e0ef34d24094e0083b9d349032129801076e269204a1730020ee74d24094346 else if Nat.blt b 4 then 0x499e6e74d24094c0083bf9ce9a490b98010e83b9d68902530020ee74d2409e2e60041dfcdd4d2405cc0083b9d569a250c9801077f39d349003b002730773a40b24a60041dce9a471285cc0083bcd4690250b98010773a40b84a1730020ef04d240942e60041dce9a4812852c0083bf9e69a480918013483a69204a1730020ee75ca40942e60051e62f34d24094c0083b9d3492250b98010773a69204017300242e74d240942e600445e6e74d24094c0083bf9e69a4810d8010773a69204a23b0020ee761269202e60041dce9a481280ec0083bf9e6c04d241801077ea69203e173002570773a40942e60051e0efe4d2405cc0083bf9fcf34d2418010779b9d34902730020ee75ba685c116 else 0x50e0efe4d2405cc0094c1dce9a3e929801409ec1d34902530022b0773a69202e60041dfeec4d2405cc009cc1dfcf34d2418010e83bf9e69a48300269074d241082e60041dfcee4d2405cc0094c1dfcf34d2418010773a692484173000012679a69204a5004d26307481285cc0083bd93490250b98010773a69204a1e30021ae74d2409c2e6004f60efe4d2405cc0083b793490250b98010773a8d204a173002630773a48942e600499ce9a481ac5cc0083bf9349031929801077f38d34901730020efe73a691c2e60041ddc9a481285cc009ec1d4090250b9801077f3b1349017300269077f269202e60041dce9a4818894c0083b9d3490268b98010d73a6920522530020ee74d24072116) else if Nat.blt b 8 then (if Nat.blt b 6 then 0x41de6e74d24894c0083b9d56902509d8010773a89204a1730020eee56a68942e6a3c1dfcb04d2405ce0086b9d34902509d8010773ae9204a173002570779b9d204a60051e0efe79a6920c0083b9d6890250b98014b83b9d34901730020ee74d240943260041dcead4d13c5cc0083b9d3490360b98010773a69204a05b00279077f3cd349060041dce9a4812866c0083be93490250b98014883bcd34902530020ee64d240942e60041dce9a480f45cc008539d3490250b98010779a69206b2530020efe79a69205660041dced54d2405cc0083b9d4c90250b980107813f9e69a4830020ee770a69204a60041dceb74d0f85cc0083bf9e6cc4d241801077f39d46901730020ee75124094326 else if Nat.blt b 7 then 0x49dfce74d2405cc0083bcd3490331298013f83bf934901730020efe73a69202e60041dfcf34d2400ac00a641dfcf34d2418010773a69204a1ab0020ee74d240a027600445ce9a480d85cc008639d3490250b9801077e39d34901730020ef373a8d204a60041dd09a481285cc0093b9d3490250b98010773a69204a1430020ee74d240942e60043a0ee756a6894c009641dfce7480b98010779bb93490253002990779a69204a60051e7131481285cc0083bcdce9a4813d8010773abd344a173002830773a68942e60041dfce75d2405cc0083bf9e69a481c18013583a69204a173002590773a40942e60041dcec04d24064c009f41d3490250b9801077f39d68901730024ce74d240c24a6 else 0x51e49074d1285cc0083bcdceba481298012883b9d344a1730028f0765a69204a60041dcebd4d2405cc0083bcdceb448129801077f3a934901730020ee74d230942e60050a0efe4d2405cc008b41dce9a480b98012f73a9d344a1730020ee74d2405c1960041dd8b54d24094c0083bb13493250b9801077aa6920361730020ee74fa40942e60041dfee74d2405cc0083ba93490250b98010773ac9204a1730020ee74d241082e60041de6e76aa6920c0083bb15690250b98010777a69204a1730020ee74d2407e2e60041dceb4569285cc0086bb13490250b98000083bcd4690252802810773a69204a60041dcebb481285cc0083b9d34900701d8010779a69208a2530020ee751a40d62e6) else if Nat.blt b 9 then 0x41dfcf34d2410ec0083b9d3490358b9801077f3cd34903bb0020ee74d248f84a60041dfcf34d240f0c0083b9d80ab17045801077f39d9c9a4830020eec4d240a44a60041dcea1481285cc0083b9d869a2b8b98010773ab5344a02b002630e73ad5204a60041dcea34818494c0083bf9ce9a481198010773b3934902530020ee74d240d22e6004f60e9a482145cc0083bf9e6ab4d241801077f3cd909a4830020ee74d234942e6004ae4907739285cc008839d3490250b98013383a69204a173002710779a40b24a6004ae0ee765a4094c009441dfce74d0b98010773a69206d1730024cf34d240aa4a60041dce9a481288cc0083b9d34903f1298010779b9d44902530020f0077269202e6 else if Nat.blt b 10 then 0x519ce9a481285cd3194c1dceab250b9c010775a69204a1730020efe79a69205260041df09a4812872c0083b9d204a17059801077f39d349030b00001077f269206350041dce9a481285ec0083b9d3490428b9801077f3cd34900fb0020efe73a69206360041dcee04d24094c0083c01ce9a480b9801077f3cdd49a48300235077f3cd349060041dced565a6920c0086b9d3490250b98013883bf9e69a48351e0f027f269202e70041dceb6481285cc0083bcdce9a482118010773a69204a1530020ee74da40942e6000020efe79a6920a0083b7d3490250b98010773a6920681730020efe53a68b02e60041dced34d24094c0083bb13490270b98010773a69224a03b0020efe79b9d34906 else 0x10773a69204a04b0020efe79a69205f6
def htChunk_13 (b : Nat) : Nat := if Nat.blt b 1 then 0x5bdc2a5b98435a9a1e5a27c75a0a80599ba757c81557197f562c2f56076c552c9f54f82454710854585453d13953a43650ec874fdbab4d68024c6d4a44799143e90940dbc240c04a400d583f12263e6b2c3e26e93e08873d3ae03c69c13c397a3c372a3beb2f3af14f3adeeb3ac5023ac1a139e56639526a38f02d378e70365a4135ae0b35650b35335e33975a32515a3131fb310e2730b50d304f6d301fbf301d2b30108f2fceec2fae522e83a12dbcbe28f6c328efbd289c4f28773c2847da27ecce263f50257b49247ae32329de21fef920141d1fed011f05ff1eb3a91e893d1dfa6d1dd9281d8ddc1cf1d01a402b1a01aa19b8b91952dd18b7f918663417597c1686f4162f9515fcf11571ce14b8921405b41337461310e7128f9b125b311011020f75900e5bf60db8470d83fc0d35b50c9c3c0be6fa0ba85f0b68f20b31c40b30340a143f099b6508866807cb8a0714b306ef2306658405fcb205b7de05267e050d0104bdf2047181044e76044221041bf80345d20331b801efe9008e52 else 0xeec864e61716e1c55ae06ee0df5d29dee370dc43dfd94e57d93832d89d64d85a14d77407d52336d516d0d4653fd11675cf985bcb742cc88347c1b3fcbaf4f4bad1eab9ec9fb9002bb7bfefb653a2b303fdb2c415b12a2aaf4abdaeff71aea312aad276aa63f6a9d6d0a7a5a8a77234a5bd96a5473ba394b7a34f4ea1c9b6a1909ba1781aa06cf19e3f8f9d773f9af7fd9a0d7397b6ed972a3996d5f59548a194fab094ca0892065f91f39e9019798f67a88ec3748c664c8b0e53890f3f89053488ff5488b1c38767b986f877863b2c85fc0684c5c6840922806b8d8059e07f56fc7e7a397e25de7d510b7c56957bdd517ac4417aac867a947f78f4bf77d36c7490dd740f307352cf71f5e8716aab700aa46f9a1c6a5e2d69b0d369754f69457b66c8c9665841650e7c640c3a61859560d9ce605b5a6008495f6e0a5e8d465e49705db3fe5bf210
def stChunk_13 (b : Nat) : Nat := if Nat.blt b 4 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x9e41dce9a481285cf0773b253490250b9c010773a69204a13b4ae0ee764240942e783c09fce74d2405cf0773ab5344a17091e0ee74d2409442173c1dce9a48128642e7a6c1dce9a481285cf1783b9d869a480b9e0efe73b3134901738020ef54d240942e683b9d34902511886f3783b9d3490250b9e0ee74d240ac4a173c1dce9a481285c1770041de69a4815494d0e83bf9ce9a480b9e0ee74d240984a173c1de6e74d240940a7a3c1de69a481285cf0773a813490250b9e0ee74d240d655173c1dce9a4b240942e794c1dfce74d2405cf0773a69204a170ade0f0273a69204a173d1e0ec84d240942e783b9d349a481285ce009339d3490250b9a0ee766269204a173c1deae74d240942e7 else 0x83b9d3490289285cf2983b9d609a250b9e690773a69204a173c5e0ee74d240942e783b9d3490250b85cf479c41d3490250b9e0ee74d241104a173c1de6e74d240b24a783b9d3490381285cf3183bf9ce9a480b9e0ee7582692052253d1e0efe73a69202e70041dfcf34d24094d077f2692058250b9e0ef373a69204a123c1dce9a481a0942e783b9d3490290b822f0773b053490250b9e79077f39d3490173cf60e9a481cc942e783bcdce9a4812886f0773a69204a17079e710773a40b04a173c1de6e760269204a7a441dce9a481285cf3183b9d3490250b9e8f0773a69204a173c1dcec04d2405c17783bf9e6e74d24094f2a83b9d3490250b9e0ee74d240d64a173ca5ce9a481cc942e7) else if Nat.blt b 3 then 0x83b9d3490331285cf4f83b9d3490250b9c010777269204a1734a60ee761a68942e783c1dce9a481285ce00a3b213490250b9a0ee74d2409438173c1dfce74d2405c057a641dfce74d2405cf0773a69204a170b5e0efe73a69205a173c1dced564269202e783b9d80ab481285ce0083b9d3490278b9a0ee74d2410870173ce60ef373a69204a798c1dce90381285ce0083b9d869a17045a2f0773b013490173c1ddce74d240942e7a3b9d909a481285ce009a41d3490250b9a0ee74d240942e02bc1dceab4d1285c117a641dce9a481285ce0083b9d3492250b9a2f077f39d3490173802570773a40942e683b9dc69a481285ce00a3c1dfc9a480b9a0ee74d240c255253c1dfce74d240e02e7 else 0x41dceb4481285cd077f269204a218b9e9d0773a69204a1738020ee74d2409432697c1dce9a481285cf2673a692055250b9e0ef373a69204a173c1dceab4d240942e783b9d909a481285cf4283b9d569a250b9e0ee762269204a173c1dce9e4d240942e783b9d3490250d85cf2283b9d3490250b9e0ee750240e64a173c1de6e74d240e04a70041dced54d2405cd0773a69204a17011e0ee74d240a42e0fbc1dce9a48128622e783b9d3490389285cf0773a89204a17045e0ee755a690e4a1738020ee751a40942e683b9d5c9a481285cf0773a69208a250b9e0ee74d2409445173c5dce9a481286c2e783b9d3490250c822f0773a692085250b9e0ef373a69204a0bbc1dcec34d2405c117) else if Nat.blt b 6 then (if Nat.blt b 5 then 0x9c41dfce74d2405cf077539d3490250b9e0ee75f269204a173c1dce9a481f4942e70041dfce74d2405cd0773a69204a1f0b9e0ee753a69204a173c1dce9a481d0942e78741dce9a4814894f3883b9d3490250b9e0ee74d240942e01bc1dce9a481285c2570041dce9a481285cd077f39dce9a480b9e0efe73a692087173c1dcec54d240942e783b9d3490250e45cf0773a69204a17031e630773aad204a173c1dcee74d240942e783b9d3490439285cf3883bcd3490250b9e0ee759a69204a173c1dcec04d2405c11783b9d3490250b804f077f39d569a480b9c010773a89204a17341dfce764269202e783bf9ce9a480b822e0083b9d7490250b9a130773a69204a173c1dce9a481285c1d7 else 0x83ba93490250b83ef0773a69207c38129e0ee74d24094391b3c1dce9a48148942e70041dce9a481288cd0773a8d2055250b9e0ee74d240942e103c1dce9a481286e2e783b9d869a250b822f0773b2d3490250b9e0ee74d240ca4a173c1dfce74d2405c1f78a41dce9a481285ce00a141dfc9a480b9a0ee74d241124a173c1de6f373a69204a786c1dce9a481285cf0779b9d3490250d9e0ee75ba689436173c1dce9a481285c1c783b9d3490250b83ef077f39d6a9a480b9c010775269204a1734e2630773a40942e70041dce9a482105cd4283bf9ce9a480b9e0ee760240b04a173c1dce9a481e4942e786b9d3490250b80af0773a69204a17089e0ef84d2409436173c1dceb54d240942e7) else if Nat.blt b 7 then 0x83bd1ce9a481285cf0773a69203617045e0efe73a692055173c1dfcf34d240942e783bcdce9a4812840f0773a692057250b9c010d73a69204a1735120ee74d240942e795c1dce9a481285ce000041dfcf34d24160ee74d240a64a173c1dce9a4ca40942e70041dce9a481a05cd3883a692058250b9e0ef373ad53490253c1dceb74d240942e70041dfcf373a6920d077f39d34902c0b9c010773a69206b17341dfce74d2405c21783c19ce9a481285cf0773a69204a17005e0ee758269204a173c1dce9a481285c12783b9d34902c1285cf0b83b9d3490250b9e2f0773a692036173c1dfce74d240a42e783b9d3490379285cf0773a69204a17085e0ee756a69204a173ca60ee74d2407c2e7 else 0x41dd89a481285c05783b9d8090250b82ef0773a692081250b9e0ee74d240f64a173c1dce9a48174942e783b9d3490250b800f0779b9d609a48129c010773a69208517341dce9a481285c1078c41dce9a481285cf318739d3490250b9e0ee74d24d204a173d1e52e74d240942e7
def htChunk_14 (b : Nat) : Nat := if Nat.blt b 1 then 0x50ec874fdbab4c6d4a4af38f47a858478fd74549d444799143e909424da240e1dd40c04a400d583f12263e6b2c3e12523e08873d5b5a3d3ae03c69c13c397a3c372a3beb2f3af14f3adeeb3ac50239e56639526a38f02d382c27378e70365a4135ae0b35650b35335e33975a32515a3131fb30b50d304f6d301d2b30108f2fceec2fae522f4daf2e83a12dbcbe2b1c9a297acb28f6c328efbd289c4f28773c2847da27ecce263f50257b49247ae32329de222bdb21fef920f52f20141d1fed011f05ff1eb3a91e893d1dfa6d1dd9281d8ddc1cf1d01c729f1c5baa1b3bb91b33021a402b1a01aa19d8e119d82019b8b91952dd18b7f918663417597c16637c162f9515fcf11571ce14b8921337461310e7128f9b1011020f75900e86bc0e5bf60db8470d83fc0d35b50c9c3c0c20aa0be6fa0ba85f0b68f20b31c40b30340a143f099b6508ba840886680819a207cb8a0714b306ef2306658405fcb205b7de05267e050d0104bdf2047181044e76044221041bf80345d20331b801efe9008e52 else if Nat.blt b 2 then 0xb12a2aaf4abdaeff71aef528aecacdaea312adb20dad8849aad276aa63f6a9d6d0a7a5a8a77234a5e441a5bd96a5473ba394b7a34f4ea1c9b6a1909ba1781aa06cf19f36c99e3f8f9d773f9af7fd9a0d739923f6986a4797b6ed972a3997159b96d5f59550149548a194ca0892065f91f39e91b5b290d6f59019798f67a88ec3748c664c8b0e53896fdb890f3f89053488ff5488b1c3886269882ab78767b986f877863b2c85fc0684c5c6845bb280f625806b8d8059e07f84237f56fc7e7a397e25de7d510b7cbe0e7c56957bdd517b45547b19d77ac4417aac867a947f78f4bf77d36c77c9177490dd740f307371297352cf71f5e8716aab700aa46f9a1c6c146d6beb966bd5166a5e2d69b0d369754f69457b670c7966c8c966ae04665841654e4c650e7c640c3a62a9bb6185956102f960d9ce605b5a6008495f6e0a5ed3f25e8d465e49705db3fe5c38be5bf2105bdc2a5a9a1e5a8c805a27c75a0a80599ba757c81557197f562c2f56076c552c9f54f82454710854585453d13953a436 else 0xfa6766f8b1a2f2538ceec864ea6522e1c55ae06ee0df5d29dee370dd4d52dc43dfd94e57d93832d89d64d85a14d77407d52336d516d0d4653fd11675cf985bcb742cc88347c1bbaec1b3fcbaf4f4bad1eab9ec9fb97ddcb9002bb7bfefb6ca24b66569b653a2b2c415
def stChunk_14 (b : Nat) : Nat := if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x4ae0ee764240942e70041e04fe73a69202e70041dcead4d1285c2470041dce9a48128842e70047e0ee74d240942e70041dce9a48128642e7005360ee74d240942e70045e0ee761a69202e70041dfce766269202e7000020ef54d240942e60041dce9a481288c437004de0ee74d240942e70041dce9a481fc942e70041dce9a48158942e70041e08e74d240942e70041dce9a481285c177000020ef34d240aa4a60043a0efe73a69202e70041dce9a48130942e70041de6e74d240940a70051e0ef34d240942e70041dcea04d240942e70041dce9a481acaa2e70041dce9a4b240942e7004a60efe73a69202e70041dce9a481285c2b70041e04e74d240942e70051e0ec84d240942e70041dce9a4d240942e7000024ce74d240942e60041dcecc4d240942e70041deae74d240942e7 else 0x41dce9a481c0942e7004c60efe73a69202e70041dceb04d240a44a70051e0efe73a69202e7000020efe79a69204a60041dfc9a48160942e70041de6e74d240942470041dcecd4d240942e70041dce9a481e0940770041dce9a481285c0f70047a0ee74d240942e70041dce9a481a0942e70041dce9a481485c1170041dce9a4816c942e70041dce9a481c8942e70041dcec14d240942e7004f20efe73a69202e7004f60e9a481cc942e70041de6e74d240944370041dce9a481285c1e70041dce9a4822c942e70041de6e760269204a7005220ee74d240942e7004c60ee74d240942e70051e0ee74d240942e70041dfcf373a69204a7004aa0ee74d240942e70041dce9a481ac942e7004f20ee74d240942e70041dcec94d240942e70041de6e76a269204a7000020ee74d24094276) else if Nat.blt b 3 then 0x41dced564269202e70041dcec055a40942e7000020ee74d2409e2e60041dce9a48210e02e7004e60ef373a69204a7004c60ee7481c0942e70045e0ee760269202e70041ddce74d240942e70000269074d240942e60041dce9a481285c0570041dceab4d1285c117005320ee74d240942e7004820ee74d240942e7000020ee74d248942e60045e0efe73a69202e7000020ee74d240940760041dce9a481285c0e700002570773a40942e60041dcee34d240942e7000028f077f269202e60041dce9a48184aa4a70041dfce74d240e02e70041dce9a48144942e7004a60ee758268942e7004d20ee74d240942e70045e0ee74d240942e70041dce9a481285c2e7004720ee74d240942e70051e71074d240942e70041dcedd4d240942e70041dce9a48220942e70041de6e74d240b24a7 else if Nat.blt b 4 then 0x20ee76aa69202e60041dce9a481285c0470041dce9a48128622e7a3c1dceb04d240942e80041dce9a4c240942e7005420ee74d240942e70052a0ee74d240942e70041dce9a481c4942e70041dcea2481285c1170041dce9a481285c1570041dce9a481285c1a7000020ee751a40942e60041dceae4d240942e70041dce9a48228942e70041dce9a481288a2e70041dced24d240942e70041dce9a4812864117a3c1dce9a48148942e80041dce9a48214942e70041de6e74d240941770041dcec34d2405c1170041dce9a48198942e70053e0ee74d240942e7000020eee4d240942e6004a60ee761a68942e70041e0ee74d240942e70041dce9a48128702e70041dfce74d2405c057005320efe73a69202e70041dce9a48150942e70041dce9a481285c2d70041dfce74d240b42e7 else 0x41dce9a481dc942e7004e20ef34d240942e70041dceb34d240942e70041dce9a481e0942e70041dcec04d2405c1170041dce9a481285c0d70041dce9a481285c0270041dfce755a69202e7000020ee751240942e60041dfce764269202e70041e06e74d240942e70041dfce74d2405c117000020ee75d240942e6004260ee74d240942e70041dced14d240942e70041dce9a481285c1d7000020ee75a240942e60053a0ee74d240942e7004660ee74d240942e7000020ee74d24094326004be0ee74d240942e700499ce9a48154942e70041de6e74d240942e70041dceab4d240942e70041dcec84d240942e70050a0ee755a68942e70041dcec44d240942e70041dce9e4d240942e70041dce9a481286c2e70048a0ee74d240942e70041dcea0481cc942e70041de6e74d240e04a7) else if Nat.blt b 7 then (if Nat.blt b 6 then 0x41dceb54d240942e7004e20efe73a69202e70041dceda4d240942e70041dd4e74d240942e70041dcebe4d240942e7004b60ee74d240942e70046a0ee74d240942e70041dce9a481f4942e7000020efe73a69202e60041dce9a481287c2e70041dcea74d240942e70041dce9a481d0942e70041dce9a481285c1470043a0ee74d240a44a7004e20ee74d240942e70043e0ee74d240942e70041dce9a481285c0370041dce9a481285c257000020ee74d240942e60041dfce773a69202e70041dfce74d2410e2e70041dce9a481285c2670041dfce74d240f02e70041dce9a4aa40942e70041dcec54d240942e70041dce9a48128722e70041dce9a481285c0c7004c60ee755a40942e7004fe0ee74d240942e70041dcee74d240942e70041e0ae74d240942e70041dce9a4821c942e7 else 0x41dce9a481285c2070041dced74d240942e70041dce9a481286e2e70041dcecb4d240942e70041dce9a48194942e70041dfce74d2405c1f70041dcec74d240942e70041de6e768a69204a7004520ee74d240942e70000285077f269202e60041dce9a48224942e70041de6f373a69204a7004360ee74d240942e7004760efe73a69202e70041de6e74d240943670041dceb74d1286c2e70041dce9a481285c1c70041dce9a481285c1f7005260ee74d240942e70048e0ee74d240942e70041dfce75aa69202e7000020eea4d240942e6004e2630773a40942e7000020ee74d241082e60050a0efe73a69202e70046a0efe73a69202e70041dcedb4d240942e70041dce9a481e4942e700435ce9a481285c0570041dceac4d240942e70041dce9a481285c2270041df09a481286c2e7) else if Nat.blt b 8 then 0x41dceb74d240942e7000020efe79b9d349060041dfce74d240b02e70041deee74d240942e70041dcea94d240942e7000020ee74d240d62e60041dcecf4d240942e70041dce9a4817c942e70041dfce74d2405c2170041e0ce74d240942e70041dce9a481285c0170041dceb04d240942e70041dce9a481285c1270044a0ee74d240942e70041dce9a48160942e70042e0ee74d240942e70045e0ee74d2406c2e70041dfce74d240a42e70041dce9a481bc942e70041dce9a481285c2170041dcead4d240942e7004a60ee74d2407c2e798ca60ee74d240942e80041dd49a481285c1f70041dce9a481f0e04a70041dce9a48128723670041dce9a48148942e70041dfce74d240ea2e70044e0ee74d240942e7000020ee74d240944660041dcea348154942e70041dce9a48128762e7 else if Nat.blt b 9 then 0x41dd89a481285c0570046e0ee74d240942e70041dce9a48204942e70041dce9a481ec942e70041dce9a48174942e70041dce9a481285c0070041dce9a481b8942e70041de6e758269204a7000020ee74d2410a2e60041dce9a481285c107004620ee74d240942e7004c61ce74d240942e70041dce9a49a40942e70051e52e74d240942e70041de8e74d240942e70041dce9a480d85c1170041dfce74d240aa2e70041dfcf34d240942e70041de6e74d240942070041dce9a4815c942e70041dcec64d240942e7000021ae74d240942e6005120ee74d240942e7004ae0ee74d240942e70000001077f3cd349050041dce9a481285c0670041dce9a4814c942e70041dce9a4ca40942e70041dfce74d240be2e7004ca0ee74d240942e7000020ee74d240d02e60041de6e75aa69204a7 else 0xa3c1dceab4d240942e80041dce9a481d8942e70041dce9a48178942e7
def htChunk_15 (_ : Nat) : Nat := 0xa7a5a8a5bd969a0d7396d5f588b1c37e25de7aac86740f30716aab66584157c81557197f562c2f54710830108f247ae31f05ff1571ce14b89207cb8a
def stChunk_15 (_ : Nat) : Nat := 0x83b9d609a481285cf0773a692058250b9e0ee74d240a44a173c1dce9a481285c20783b9d3490250b83ef0773ad53490250b9c01077f39d34901734e20ee74d240942e70041dce9a481285cd0773a692087250b9e0ef373a69204a173c1dceab4d240942e783b9d909a481285cf0773a69204a1b0b9e0ee74d240942e02bc5e0ee74d240942e783b9d3490381285cf3183b9d3490250b9e8f0773a69204a173c1dce9a481285c177
def htChunk_16 (_ : Nat) : Nat := 0xad8849a7a5a8a5bd969a0d7396d5f588b1c37e25de7b19d77aac86740f30716aab66584162a9bb5c38be57c81557197f562c2f54710830108f247ae31f05ff1571ce14b89207cb8a
def stChunk_16 (_ : Nat) : Nat := 0x83b9d34902f9285cf0773ac13490250b9e0ee74d240b04a173c1dce9a48148942e783b9d3490250b840f0773a69204a1707de0ee75aa69204a173c6a0ee74d240942e70041dfce74d2405cd3883b9d3490250b9c010773a69204a17341dce9a4821c942e783b9d34903c1285cf0773b453490250b9e0ef373a69204a173c1dceab4d240942e783b9d909a481285cf0773a69204a1b0b9e0ee74d240942e02bc5e0ee74d240942e783b9d3490381285cf3183b9d3490250b9e8f0773a69204a173c1dce9a481285c177
def htChunk_17 (_ : Nat) : Nat := 0x716aab
def stChunk_17 (_ : Nat) : Nat := 0x20ee74d240942e6
def htChunk_18 (_ : Nat) : Nat := 0x716aab
def stChunk_18 (_ : Nat) : Nat := 0x20ee74d240942e6
def HT (u i : Nat) : Nat := match u with
  | 7 => Nat.land (Nat.shiftRight (htChunk_7 (i / 128)) (24 * (i % 128))) 16777215
  | 8 => Nat.land (Nat.shiftRight (htChunk_8 (i / 128)) (24 * (i % 128))) 16777215
  | 9 => Nat.land (Nat.shiftRight (htChunk_9 (i / 128)) (24 * (i % 128))) 16777215
  | 10 => Nat.land (Nat.shiftRight (htChunk_10 (i / 128)) (24 * (i % 128))) 16777215
  | 11 => Nat.land (Nat.shiftRight (htChunk_11 (i / 128)) (24 * (i % 128))) 16777215
  | 12 => Nat.land (Nat.shiftRight (htChunk_12 (i / 128)) (24 * (i % 128))) 16777215
  | 13 => Nat.land (Nat.shiftRight (htChunk_13 (i / 128)) (24 * (i % 128))) 16777215
  | 14 => Nat.land (Nat.shiftRight (htChunk_14 (i / 128)) (24 * (i % 128))) 16777215
  | 15 => Nat.land (Nat.shiftRight (htChunk_15 (i / 128)) (24 * (i % 128))) 16777215
  | 16 => Nat.land (Nat.shiftRight (htChunk_16 (i / 128)) (24 * (i % 128))) 16777215
  | 17 => Nat.land (Nat.shiftRight (htChunk_17 (i / 128)) (24 * (i % 128))) 16777215
  | 18 => Nat.land (Nat.shiftRight (htChunk_18 (i / 128)) (24 * (i % 128))) 16777215
  | _ => 0
def S (u j : Nat) : List Nat := match u with
  | 7 => let p := Nat.land (Nat.shiftRight (stChunk_7 (j / 32)) (40 * (j % 32))) 0xffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 8 => let p := Nat.land (Nat.shiftRight (stChunk_8 (j / 32)) (40 * (j % 32))) 0xffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 9 => let p := Nat.land (Nat.shiftRight (stChunk_9 (j / 32)) (49 * (j % 32))) 0x1ffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 10 => let p := Nat.land (Nat.shiftRight (stChunk_10 (j / 32)) (49 * (j % 32))) 0x1ffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 11 => let p := Nat.land (Nat.shiftRight (stChunk_11 (j / 32)) (58 * (j % 32))) 0x3ffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 12 => let p := Nat.land (Nat.shiftRight (stChunk_12 (j / 32)) (67 * (j % 32))) 0x7ffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 13 => let p := Nat.land (Nat.shiftRight (stChunk_13 (j / 32)) (67 * (j % 32))) 0x7ffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 14 => let p := Nat.land (Nat.shiftRight (stChunk_14 (j / 32)) (76 * (j % 32))) 0xfffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 15 => let p := Nat.land (Nat.shiftRight (stChunk_15 (j / 32)) (67 * (j % 32))) 0x7ffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 16 => let p := Nat.land (Nat.shiftRight (stChunk_16 (j / 32)) (67 * (j % 32))) 0x7ffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 17 => let p := Nat.land (Nat.shiftRight (stChunk_17 (j / 32)) (58 * (j % 32))) 0x3ffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 18 => let p := Nat.land (Nat.shiftRight (stChunk_18 (j / 32)) (58 * (j % 32))) 0x3ffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | _ => []
def symTag : Nat := 0x3ffffffc00000000fffffff
def symD : Nat := 28
theorem sym_ok : moveOK 62 (symTag, symD) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := let img := zs.map (moveBits symTag symD); if Nat.blt (hk 1 img) (hk 1 zs) then img else zs
theorem ori_ok {u ys} (h : NatRun1T 62 false (goal 62) u ys) : NatRun1T 62 false (goal 62) u (ori ys) := ori_move_ok 1 symTag symD sym_ok h
def bsrFuel : Nat → Nat
  | 7 => 2
  | 8 => 2
  | 9 => 8
  | 10 => 8
  | 11 => 10
  | 12 => 10
  | 13 => 9
  | 14 => 10
  | 15 => 6
  | 16 => 6
  | 17 => 2
  | 18 => 2
  | _ => 0
def idx (u : Nat) (zs : List Nat) : Nat := bsr (HT u) (hk 1 zs) (bsrFuel u) 0 (NN u)
def poolG : List (Nat × Nat × Nat × Nat × Nat × Nat) := [(63, 62, 68, 11, 12, 16), (91, 90, 96, 39, 40, 44), (96, 63, 88, 3, 12, 16), (68, 91, 116, 31, 40, 44), (62, 63, 68, 12, 0, 4), (90, 91, 96, 40, 28, 32), (64, 62, 88, 16, 3, 11), (92, 90, 116, 44, 31, 39), (96, 68, 71, 7, 11, 12), (68, 96, 99, 35, 39, 40), (88, 96, 118, 12, 3, 16), (116, 68, 118, 40, 31, 44), (63, 62, 91, 7, 3, 12), (91, 90, 63, 35, 31, 40), (118, 64, 68, 4, 2, 12), (118, 92, 96, 32, 30, 40), (62, 68, 118, 12, 3, 7), (90, 96, 118, 40, 31, 35), (62, 68, 118, 12, 0, 11), (90, 96, 118, 40, 28, 39), (71, 91, 118, 12, 7, 11), (99, 63, 118, 40, 35, 39), (64, 62, 88, 16, 2, 7), (92, 90, 116, 44, 30, 35)]
theorem poolG_ok : poolOK 62 poolG = true := by decide +kernel
def Z (u : Nat) := bar1T false S NN idx ori poolG u
abbrev Ok (u a b : Nat) := ∀ i, a ≤ i → i < b → Z u i = true
theorem z0 : Ok 0 0 (NN 0) := by simp [Ok, NN]
theorem z1 : Ok 1 0 (NN 1) := by simp [Ok, NN]
theorem z2 : Ok 2 0 (NN 2) := by simp [Ok, NN]
theorem z3 : Ok 3 0 (NN 3) := by simp [Ok, NN]
theorem z4 : Ok 4 0 (NN 4) := by simp [Ok, NN]
theorem z5 : Ok 5 0 (NN 5) := by simp [Ok, NN]
theorem z6 : Ok 6 0 (NN 6) := by simp [Ok, NN]
set_option maxHeartbeats 0 in
theorem z7 : Ok 7 0 (NN 7) := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxHeartbeats 0 in
theorem z8 : Ok 8 0 (NN 8) := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxHeartbeats 0 in
theorem z9 : Ok 9 0 (NN 9) := span_ok (by decide +kernel : span (Z 9) 93 0 = true)
set_option maxHeartbeats 0 in
theorem z10 : Ok 10 0 (NN 10) := span_ok (by decide +kernel : span (Z 10) 68 0 = true)
set_option maxHeartbeats 0 in
theorem z11_0 : Ok 11 0 100 := span_ok (by decide +kernel : span (Z 11) 100 0 = true)
set_option maxHeartbeats 0 in
theorem z11_100 : Ok 11 100 200 := span_ok (by decide +kernel : span (Z 11) 100 100 = true)
set_option maxHeartbeats 0 in
theorem z11_200 : Ok 11 200 300 := span_ok (by decide +kernel : span (Z 11) 100 200 = true)
set_option maxHeartbeats 0 in
theorem z11_300 : Ok 11 300 310 := span_ok (by decide +kernel : span (Z 11) 10 300 = true)
theorem z11 : Ok 11 0 (NN 11) := (range_split (range_split z11_0 z11_100) (range_split z11_200 z11_300))
set_option maxHeartbeats 0 in
theorem z12_0 : Ok 12 0 100 := span_ok (by decide +kernel : span (Z 12) 100 0 = true)
set_option maxHeartbeats 0 in
theorem z12_100 : Ok 12 100 200 := span_ok (by decide +kernel : span (Z 12) 100 100 = true)
set_option maxHeartbeats 0 in
theorem z12_200 : Ok 12 200 300 := span_ok (by decide +kernel : span (Z 12) 100 200 = true)
set_option maxHeartbeats 0 in
theorem z12_300 : Ok 12 300 322 := span_ok (by decide +kernel : span (Z 12) 22 300 = true)
theorem z12 : Ok 12 0 (NN 12) := (range_split (range_split z12_0 z12_100) (range_split z12_200 z12_300))
set_option maxHeartbeats 0 in
theorem z13_0 : Ok 13 0 80 := span_ok (by decide +kernel : span (Z 13) 80 0 = true)
set_option maxHeartbeats 0 in
theorem z13_80 : Ok 13 80 160 := span_ok (by decide +kernel : span (Z 13) 80 80 = true)
set_option maxHeartbeats 0 in
theorem z13_160 : Ok 13 160 237 := span_ok (by decide +kernel : span (Z 13) 77 160 = true)
theorem z13 : Ok 13 0 (NN 13) := (range_split z13_0 (range_split z13_80 z13_160))
set_option maxHeartbeats 0 in
theorem z14_0 : Ok 14 0 80 := span_ok (by decide +kernel : span (Z 14) 80 0 = true)
set_option maxHeartbeats 0 in
theorem z14_80 : Ok 14 80 160 := span_ok (by decide +kernel : span (Z 14) 80 80 = true)
set_option maxHeartbeats 0 in
theorem z14_160 : Ok 14 160 240 := span_ok (by decide +kernel : span (Z 14) 80 160 = true)
set_option maxHeartbeats 0 in
theorem z14_240 : Ok 14 240 291 := span_ok (by decide +kernel : span (Z 14) 51 240 = true)
theorem z14 : Ok 14 0 (NN 14) := (range_split (range_split z14_0 z14_80) (range_split z14_160 z14_240))
set_option maxHeartbeats 0 in
theorem z15 : Ok 15 0 (NN 15) := span_ok (by decide +kernel : span (Z 15) 20 0 = true)
set_option maxHeartbeats 0 in
theorem z16 : Ok 16 0 (NN 16) := span_ok (by decide +kernel : span (Z 16) 24 0 = true)
set_option maxHeartbeats 0 in
theorem z17 : Ok 17 0 (NN 17) := span_ok (by decide +kernel : span (Z 17) 1 0 = true)
set_option maxHeartbeats 0 in
theorem z18 : Ok 18 0 (NN 18) := span_ok (by decide +kernel : span (Z 18) 1 0 = true)
theorem checked : ∀ u ≤ 18, ∀ i < NN u, Z u i = true := by
  intro u hu; interval_cases u
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
  · exact fun i hi => z11 i (Nat.zero_le i) hi
  · exact fun i hi => z12 i (Nat.zero_le i) hi
  · exact fun i hi => z13 i (Nat.zero_le i) hi
  · exact fun i hi => z14 i (Nat.zero_le i) hi
  · exact fun i hi => z15 i (Nat.zero_le i) hi
  · exact fun i hi => z16 i (Nat.zero_le i) hi
  · exact fun i hi => z17 i (Nat.zero_le i) hi
  · exact fun i hi => z18 i (Nat.zero_le i) hi
def RootG (u : Nat) : Bool := (Nat.beq (u % 2) 0 && Nat.beq xsG.length (u / 2 + 1) && scr62 poolG xsG) || found S NN idx u (ori xsG)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 9 10 = true := by decide +kernel
theorem noRunFull (u : Nat) (hu : u ≤ 18) (h : NatRun1T 62 false (goal 62) u xsG) : False := by
  have hmin : 10 ≤ u := by
    have hl := run1T_len h
    change 6 ≤ u / 2 + 1 at hl
    omega
  have hr := span_ok rootChecked u hmin (by omega)
  unfold RootG at hr
  rw [Bool.or_eq_true] at hr
  rcases hr with hscr | hf
  · simp only [Bool.and_eq_true, Nat.beq_eq] at hscr
    have hbad := scr62_no poolG_ok h hscr.1.1 hscr.1.2
    rw [hbad] at hscr; cases hscr.2
  · simp only [found, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact bar1T_all poolG_ok ori_ok checked u hu _ hf.1 (Run1T.perm (isPermFast_sound hf.2) (ori_ok h))
theorem rowsG_len : rowsG.length = 124 := by decide +kernel
theorem enc_inputsG : (List.ofFn fun (i : Fin 6) => ((fun x : Fin 6 → Bool => x i), taggedFn i.val)).map (encT rowsG 62 false) = xsG := by decide +kernel
theorem enc_goalG : encT rowsG 62 false (fG, false) = goal 62 := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG → Nat.land (cov 62 zs) (lo 62) ≠ lo 62 := by decide +kernel
theorem noCircuit : ¬ Has1Not 6 fG 9 9 := by
  intro h
  obtain ⟨u, hu, _, ws, hsub, hrun⟩ := exists_run_1not false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn 9 9 htag_fn h
  have hr : NatRun1T 62 false (encT rowsG 62 false (fG, false)) u (ws.map (encT rowsG 62 false)) :=
    Run1T.map (encT rowsG 62 false) (fun a => encT_inv rowsG 62 rowsG_len false a) (fun a b => encT_and rowsG 62 rowsG_len false a b) (fun a b => encT_or rowsG 62 rowsG_len false a b) (fun a => encT_tag rowsG 62 rowsG_len false a) hrun
  rw [enc_goalG] at hr
  have hsub' : (ws.map (encT rowsG 62 false)).Sublist xsG := by rw [← enc_inputsG]; exact hsub.map _
  by_cases he : ws.map (encT rowsG 62 false) = xsG
  · rw [he] at hr; exact noRunFull u hu hr
  · exact proper_failG _ (List.mem_sublists.2 hsub') he (required hr)
end Sub6

namespace Main
abbrev fG : BFn 7 := fun x : Fin 7 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def cSub3 : Fin 7 → Sum Bool (Fin 6) | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩ | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩ | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩ | ⟨3, _⟩ => Sum.inl false | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩ | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩ | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
def cSub2 : Fin 7 → Sum Bool (Fin 6) | ⟨0, _⟩ => Sum.inr ⟨4, by omega⟩ | ⟨1, _⟩ => Sum.inr ⟨3, by omega⟩ | ⟨2, _⟩ => Sum.inl false | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩ | ⟨4, _⟩ => Sum.inr ⟨1, by omega⟩ | ⟨5, _⟩ => Sum.inr ⟨0, by omega⟩ | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
theorem sub3_eq : (fun y : Fin 6 → Bool => fG (substIn cSub3 y)) = Sub6.fG := by funext y; revert y; decide +kernel
theorem sub2_eq : (fun y : Fin 6 → Bool => fG (substIn cSub2 y)) = Sub6.fG := by funext y; revert y; decide +kernel
theorem fG_singleton : ∀ v : Fin 7, fG (fun i => decide (i = v)) = false := by decide +kernel
def taggedFn (a : ℕ) : Bool := decide (a = 2 ∨ a = 3)
theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 11) (hnot : notCount gs ≤ 1) (hcl : SCleanL 7 gs)
    (hnd : ∀ p, p < gs.length → 7 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 7 + p ∈ g.inputs)
    (hev : ∀ x, val gs 7 o x = fG x) : ∀ a, a < 7 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a halt hta
  have ha23 : a = 2 ∨ a = 3 := by simpa [taggedFn] using hta
  have hdrop : ∀ (v : Fin 7) (c : Fin 7 → Sum Bool (Fin 6)), c v = Sum.inl false → (fun y => fG (substIn c y)) = Sub6.fG →
      v.val ≠ o ∧ gs.countP (fun g => decide (v.val ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → v.val ∈ g.inputs → g.op = GateOp.or) := by
    intro v c hcv heq
    have hnc6 : ∃ y y' : Fin 6 → Bool, fG (substIn c y) ≠ fG (substIn c y') := by
      have hf : ∀ y, fG (substIn c y) = Sub6.fG y := congrFun heq
      simp only [hf]; exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    refine ⟨?_, ?_, ?_⟩
    · intro ho; have h1 : fG (fun i => decide (i = v)) = true := by rw [← hev, ← ho, val_input]; simp
      rw [fG_singleton v] at h1; cases h1
    · by_contra! hgt
      have hsub := restrict_sclean_drop fG c v hcv hnc6 gs o hcl hnot hev
      rw [heq] at hsub; obtain ⟨C, hfan, hsz, hbc, hnc', hevC⟩ := hsub
      exact Sub6.noCircuit ⟨C, hfan, by omega, by omega, hnc', hevC⟩
    · intro p g hg hvin
      rcases hcl p g hg with ⟨hop, _, _, _⟩ | ⟨hop, _, _, _, _, _, _⟩
      · have hsub := restrict_sclean_drop2 fG c v hcv hnc6 gs o hcl hnot hnd hev p g hg hvin (Or.inl hop)
        rw [heq] at hsub; obtain ⟨C, hfan, hsz, hbc, hnc', hevC⟩ := hsub
        exact absurd ⟨C, hfan, by omega, by omega, hnc', hevC⟩ Sub6.noCircuit
      · rcases hop with hop | hop
        · have hsub := restrict_sclean_drop2 fG c v hcv hnc6 gs o hcl hnot hnd hev p g hg hvin (Or.inr hop)
          rw [heq] at hsub; obtain ⟨C, hfan, hsz, hbc, hnc', hevC⟩ := hsub
          exact absurd ⟨C, hfan, by omega, by omega, hnc', hevC⟩ Sub6.noCircuit
        · exact hop
  rcases ha23 with rfl | rfl
  · exact hdrop ⟨2, by omega⟩ cSub2 rfl sub2_eq
  · exact hdrop ⟨3, by omega⟩ cSub3 rfl sub3_eq
def rowsG : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 7, 7, 7, 7, 14, 14, 14, 14, 33, 33, 64, 64, 64, 7, 14, 28, 33, 56, 7, 28, 33, 56, 32, 32, 32, 16, 16, 16, 8, 8, 56, 56, 56, 56, 28, 28, 28, 28, 33, 33, 64, 64, 64, 56, 28, 14, 33, 7, 56, 14, 33, 7, 33, 12, 9, 17, 65, 18, 34, 66, 36, 68, 15, 23, 39, 71, 15, 30, 46, 78, 35, 37, 65, 66, 68, 9, 9, 9, 9, 9, 17, 17, 17, 17, 36, 34, 96, 18, 17, 80, 9, 72, 60, 58, 57, 120, 60, 30, 29, 92, 49, 41, 96, 80, 72, 36, 36, 36, 36, 36, 34, 34, 34, 34, 97, 76]
def xsG : List ℕ := [0x40034450ff9c7c1dcc0c00015230f07, 0x3c00220a0027fce0aa000000460ff38, 0x183e0f101004bff02ab03c000ce0ffc0, 0x18012ffc00f83c4063383ff02ac0f000, 0x9ff38f00088281183fce2a800000, 0x7fe71f07000d1141548c3c1f3030000, 0xc01c88a4007222900070000001c0000]
def NN : Nat → Nat
  | 7 => 8
  | 9 => 223
  | 10 => 23
  | 11 => 1577
  | 12 => 152
  | 13 => 3338
  | 14 => 640
  | 15 => 2144
  | 16 => 786
  | 17 => 358
  | 18 => 147
  | 19 => 14
  | 20 => 4
  | 21 => 1
  | _ => 0
def dictChunk (b : Nat) : Nat := if Nat.blt b 21 then (if Nat.blt b 10 then (if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x100400137e50550000002307f9c000008020008bb282a8000001183fce0000040100045014044000000081e070000020080000cc20aa000000460ff380000100400004410000000000000000000008020000200888c0f0f82303c3e000004000000ff801540000008c1fe00000020000003fc00aa000000460ff0000000d800000000008401e011000000000004c000000000000000000000000000001400000000000000000000000000000080000222080000000000000000000004000000000000000000000000000000080000888200000000000000000000004000000100000000000000000000000200000000000000000000000000000002007c8320a4400000021007838000001003e01101aa8000c01183fffc00000000004cf901100000008401e0000000000002630800000000000000000000000000113240550000002307f9c0000000000088a20000000000000000000000000004441000000000000000000000000000220080000000000000000000000000008100800000000000000000000000000304000000000000000000000000000008f801100000008401e000000000000047400880000004200f0000000000000208000000000000000000000000000000800000000000000000000000000000010000000000000000000000000000000000000000000000000 else 0x310400067e10440000002100780000018820000220800000000000000000000c0b1ff65d979540000008c1fe7e00006058ff80cc2eab03c3e0ce0ffff0000300c780044140081e0704400000000010143fe51f072200000010803c1c000080a1ff20d839100000008401e0e00004050ff804c0c880000004200f0700002008780004040000000000000000000100000031f002200000010803c00000080000010f801100000008401e000000400000000800000000000000000000019840000441000000000000000000000a8200002208000000000000000000004410004df941100000008401e00000022080023eca022000000040f0000000110400117650550000002307f9c000008820008aa28000000000000000000004410000ff841540000008c1fe00000022080004fc20880000004200f000000110400024c10000000000000000000008820000ff082a8000001183fc00000044100007984044000000081e0000000220800028820000000000000000000011040000c41000000000000000000000882000033080000000000000000000044100001504000000000000000000002208000088200000000000000000000110400004010000000000000000000008800000f900088000000103c000000044000007980044000000081e000000022000003c40022000000040f000) else if Nat.blt b 3 then 0xb30c78004414000000000000000000057c43c00020204200f008800000000029821e000101000000000000000000014610f00008080000000000000000000a2287fc8360e440000002100783800051043c088a22000000000000000000028821e018f811100000008401e0000014410f0047c08880000004200f000000a20878020c04000000000000000000051043c000a02000000000000000000028821e000101000000000000000000013f080000882010803c0220000000000930400004410000000000000000000047c00008882004200f008800000000023e000008f80131007804c401e0000011f000000080010803c02200000000008f800000000008401e011000000000045c00000000004200f0088000000000218000000000000000000000000000010600000000000000000000000000000820000023e00440000002100780000041000001040000000000000000000002080000001000000000000000000000104000000000000000000000000000007f800000400008c1fe01540000000003e40000022000040f000220000000001e6100019f841120780019401e000000f308000088200103c000880000000007980000044000081e000440000000003c40000022000040f0002200000000014410000110400000000000000000000800000000000000000000000000 else if Nat.blt b 4 then 0x4441000023e0044000000210078000022208000008000000000000000000001110400000100000000000000000000088820000000000000000000000000001bbac7fc66e16eec7fe71fd187838000d9963fe0f30b088000000103c0000006ccb1ff01985800000000000000000035f50ff814c0c10803c0220000000001a2287fce3e0ee6060000a9187838000d1143fe7170773030000548c3c1c000688a1ff20d839100000008401e0e00034450ff8c7c0dcc0c00015230f070001a2287fc62e06e6060000a9187838000d1143fe11f032200000010803c00000688a1ff009818000000000000000000344400f80440400000000000000000019f840001e61019401e0112078000000cfc20000620804200f008800000000063e000002000021007804400000000030450ff80000d548c3fff30300070001820000060800a206000088180000000911003e013010000000000000000000488801f00880800000000000000000021f000001000010803c0220000000001002007c62a02e6060000a91878380007fc43c0022020460ff00aa0000000003fe10000110402307f80550000000001f718f00088280103c00088000000000fa88780044040081e000440000000005fc63c00220a0460ff38aa0000000002fe31e001105021007804400000000017718f00088281183fce2a800000 else 0x4ff9c78024c1408c1fe71540000000027fce3c00620a0460ff38aa0000000013fe71e00198502307f9c550000000009ff38f000a8281183fce2a8000000004ff9c7800441408c1fe71540000000027fce3c00200a0460ff38aa0000000013fa71e00110502307f9c550000000009f738f00088281183fce2a8000000004f71c78004414000000000000000000277cc3c0000020460ff38aa0000000013ba61e00010102307f9c550000000009dd30f00000081183fce2a8000000004e61878133e444400000021007800002730c3c000202000000000000000000137e50000110402100780440000000009bf28000080201183fce2a8000000004d71c7800441408401e711000000000267c80000000004200f0088000000001318400000000000000000000000000096e38f000882810803ce220000000004971c7800441408401e7110000000002430c3c00000204200f38880000000011fe40000100002307f80550000000008f920000088000103c00088000000004741c780044140081e07044000000002380e3c00220a0040f0382200000000118061e0000010020781c110000000008bb28000080201183fce2a800000000455140011545000000000000000000022a8a00002208000000000000000000111440000000000000000000000000008882000222080000000000000000) else if Nat.blt b 7 then (if Nat.blt b 6 then 0x1e0000010012186044000000210079c0f000000800155102a8000001183fce078000004000a208000000000000000003ebff79ff88892f558fffffb8300c701f4ff9cf806cc9408c1fe71540000000fa7fce7c02664a0460ff38aa00000007d3fe73e00112542307fffd500018003e37559ff88cd2fff8ffffffe3ffff01f1aaa8ffc40087aac7ffffdc1806380f8801043e20041d10300c7440c031c07c22a020012220000000000000000003e019010009110000000000000000001f008808006888000000000000000000f80440400244400000000000000000003811480000000021e07ffc4380000000dff3cf00088281183fce2a8000000005ffbc7fc66e16eec7fe71fd187838002ffde3fe1370b0460ff38aa0000000017fef1ff0398582307f9c55000000000bff78ff80cc2c1183fce2a8000000005ff9c7800c41408c1fe7154000000002ffce3c00220a0460ff38aa0000000013fef1ff21d8793307f9c5d401e0e0009ff78ff80cc2ebb83ffe2ee0ffff0004ff9c7838555c4cf9fe7175e07ff80027fce3c09bf2a2660ff38ba803c000013fe71e04d71502307f9c550000000009ff38f022eca8bb83fce2ee0ff380004ff9c7811545408c1fe71540000000027fce3c08a22a0460ff38aa0000000013fe71e019f8513307f9c5d401e000009ff38f004fc289983fce2ea00f00 else 0x1e0011050013fe704400000021007800f0008828009ff38088000000103c00078004414004fe9c1540000008c1fe703c00220a0027dce0aa000000460ff381e0011050013ea70550000002307f9c0f0008828009ee38000000000000000078004414004f61c1540000008c1fe703c00220a0027b0e022000000040f0381e0011050013cc7011000000020781c0f0008828009e438088000000103c0e078004414004bf9c1540000008c1fe703c00220a0024fce0880000004200f381e00110500125c7044000000210079c0f0008828008fb382a8000001183fce078004414004711c044000000081e0703c00220a002380e022000000040f0381e0011050003ee301100000002078000f00088280017f182200000010803c0078004414000bb8c1540000008c1fe703c00220a000598600000000000000001e0011050000c03011000000020781c0f0008808001ff102a8000001183fc0078004404000fa88044000000081e0003c00200a0027fce0aa000000460ff381e000501000288200000000000000000f0000808009df302200000010803c0078000404004e61800000000000000003c00020200057c40880000004200f001e000101000298200000000000000000f00008080014610000000000000000078000404000a20800000000000000003c000002002774c0aa000000460ff38) else if Nat.blt b 8 then 0x1e0455150013dc700000000000000000f0222888001441000000000000000007808541c004ff9c1540000008c1fe703c03665affaffcedee0c0001563ff3f1e01b32d7fd3fe76550000002307f9c0f00d996bfe3771b7b830000558ffcfc78067e14004ff9c175007804cc1fe703c03265affa7fcedfe8c3fff763ff3f1e0193050013fe70550000002307f9c0f00999283e9ff392a8000001183fce078043e04000a20802100780440000003c017f1af027fce8ba803c02660ff381e00bb8d7813fe745dc1fe717707f9c0f005dc6bc01771a2ee0ff38bb83fce07802dc35e04ff9d1540000008c1fe703c01665affb7fcfcaa000000460ff3f1e00b30d7813fe74550000002307f9c0f0057c4bc015f1226200f0098803c0078028c25e00a30900000000000000003c013f0a0027fce0ba803c02660ff381e0097050013fe70550000002307f9c0f0049828009ff382a8000001183fce078023e04000a20802100780440000003c010602000510400000000000000001e0079850013fe705581e0006707f9c0f0028828009ff382a8000001183fce07800c4b5ff6ff9f9540000008c1fe7e3c00625affa7fcecaa000000460ff3f1e0031050017fe70550000002307f9c0f000a828009ff382a8000001183fce0780044941f6ff9e9540000008c1fe7e3c00220a0027fce0aa000000460ff38 else if Nat.blt b 9 then 0x1ff10001800688a0a206000e88180000ff84fc2c00bff782ea00f009983fce07fc26e16005ffbc1540000008c1fe703fe11f03000d114010803c0220000001ff0798580365df04481e00065007fc0ff83cc2c00366580040f000220000007fc0e6b7ff039add7707fffddc1fffe3fe0730b000ddd62ab03c000ce0fff81ff029818006bea04400000021007800ff80ec2c00bff782a8000001183fce07fc06616005ffbc1540000008c1fe703fe0330b000d99600000000000000001ff019858000c0b119c1ffff560787c0ff804c0c003445000000000000000007fc000060002028444000638081e1f03c1b06faffb400fd54fc3fff31f003f1e0d837d7fd20076aa7e1fff98f801f8f0608bebfedff3f2a9c00f811f3fcfc7817fe75e00b30d02307f9c550000003c09ff3af027fce8bb83fce2ee0ff381e04ff9d7813dc7408c1fe7154000000f027fcebc092e3a2660ff38ba803ce07813fe75e04711d06707f9c5581e0703c09ff3af005fc689983fce2ea00f001e04ff9d7802dc3408c1fe7154000000f027fcebc01661a0460ff38aa0000007813fe75e00310d02307f9c550000003c09ee3af027fce8aa000000460ff381e04d7150013fe70550000002307f9c0f0267c88009cc3004200f008800000078117654004701c06707f9c5581e0703c08aa2a0027fce0aa000000460ff38 else 0x2000000000001000000000000000000100000000000000000000000000000007fdbfe7fe00b32d02307f9fd50000003fedff3ff00189681183fcfea8000001ff65d978000c0b008c1fe7f54000000ffaffdeffebff7bffe3ffffff8ffffc7fd7fef7ff1bbadfff1ffffffc7fffe3febff3bf00d9969558ffcffb8300001ff5443187c6aaa3f706018eab1ffff8ffa7fcefc03665a0460ff38aa0000007fd3fe77e00312d46707fffd581e1f03fe9003bf07c3bf9cc7c00fd53f0fff1ff38f83800688a0aa461e0f98180000ff986c1c003445055230f07cc0c00007fca3e0e000a22802100783c40000003fe43b0f0027fde0ba803c1e660ff381ff21d878011c0f019401e0f120781c0ff906c1c001445004200f07880000007fc8360e000202802100783c40000003fe40007006003c00070001c01c00f81ff20003800080a00000000e00000000ff8ddd6ffebff7bffe3ffffff8ffffc7fc6eeb7ff1bfadfff1ffffffc7fffe3fe3775bff8ddd6fff8ffffffe3ffff1ff1bbadffc4c0b7bbc7ffffde1f87f8ff8ddc6fc03665a5563ff3fee0c00007fc6aea7ff1aba9bb918783ee461e0e3fe35553ff8d554fff8ffffffe3ffff1ff19b858017fef0ff461e0fbb1ff9c0ff8cdc2c00377587fa30f07dd8ffce07fc62e06001a2282a918783e60600003fe200430f8d5547ee0c031d563ffff) else if Nat.blt b 15 then (if Nat.blt b 12 then (if Nat.blt b 11 then 0x2001860000060800a206000088180001000c1800003040051030000440c0000800608a1ff20003a88180002206000e40030400002e3081440c0001103000020018200000e1808a206000088180001000c10000031f0073030000548c3c00800608000018600288180002206000040030400000c1801440c000110300002001820000060800a206000088180001000c1000002000051030000440c0000800488801f20c828000000000000000400244400f8044040000000000000002001002007ce3a0ae6060000a9187839000801003e6000551030000440c001c8002cc31e065517000000000000000040014450ff906c1c880000004200f072000a2087808140c000000000000000100051043c000202000000000000000080023e000020402021007804400000040011f000000000010803c022000000200082000008100800000000000000010004100000000000000000000000000800080000038f821100000008401e004000400000087c00880000004200f00200011040008541800000000000000010000000000c8824000000000000000080000000004441000000000000000004000000000147c10880000004200f0020000000000a18080000000000000001000000000040a04000000000000000080000000002040200000000000000004000000000047c00880000004200f00 else 0x2001b32c7fdf7e5ee6060000a9187839000d9963fe7bf0f73030000548c3c1c8006ccb1ff3bf87b98180002a461e0e40036658ff9cfc3dcc0c00015230f072001b22c7fdf7e5ef7060000ab1ff9f9000d9163fe73f0ffbc3f0f8778ffffc8006c8b1ff39f87b98180002a461e0e40035f50ff9c7c1ddc8c3c037230f072001a7287fce3e0ee6060000a9187839000d3143fe71f0773030000548c3c1c80068ca1ff7cf93b98180002a461e0e40034650ff9c7c1dcc0c00015230f072001a2287fdf3e4ee6060000a9187839000d1143fe71f0773030000548c3c1c800688a1ff38f83a88180002206000040034450ff9c741dcc0c00015230f072001a2287fce2e0ee6060000a9187839000d1143fe7040751030000440c001c800688a1ff30d83b98180002a461e0e40034450ff984c1d440c000110300072001a2287fcc040ea206000088180039000d1143fe6000751030000440c001c800688a1ff28f839100000008401e0040034450ff906c1c0000000000000002001a2287fc62e06a206000088180001000d1043c070e0651030000440c000080068821e018301288180002206000040034400000c7c01cc0c00015230f0020019f8400067e10ee461e01b9187801000c9820003260851030000440c000080063e00001a2002a9187806606000040031f00000c1001548c3c033030000) else if Nat.blt b 13 then 0x2003b72e7fce7e1ee6060000a9187839001d3953fe71f0773030000548c3c1c800e98a9ff7cf93b98180002a461e0e40074c54ff9c7c1dcc0c00015230f072003a22a7fce3e0ee6060000a9187839001c7c10003040055230f00cc0c0000800e3e080002000021007804400000040070c04002e7c81cc0c00015230f0020038602000e1808a206000088180001001c3010003040051030000440c0000800e180800000002a918783e606000040061f040001000010803c0220000002002af8a7808140c08401e011000000100153053c0002020000000000000000800a7e180045514021007804400000040051f040000000010803c022000000200286020000000000000000000000010011a173fe0330baac0f0f83383fffc800854180001104000000000000000040040a040000000000000000000000020020402001910480000000000000001001020100088820000000000000000080081008002040200000000000000004004080400002000000000000000000200204020000000000000000000000010010001001c08a4001c00000070000080080008000000000000000000000004003f758ff9cfc3dcd0fc001da30f072001e2287fce3e0ee6060000a9187839000dfd63fe73f0f77230f00dc8c3c1c8006eeb1ff39f87bbb1ff9c7f461e0e40036e58ff9cfc3dcc0c00015230f07 else if Nat.blt b 14 then 0x2006441200081008000000000000000100322090000000000000000000000008017fef1ff7df97bbb1ff9c7f461e0e400bff78ff9cfc3ddd8ffce3fa30f072005ffbc7fc8761e08c1fe7154000001002ffde3fe3370b5563ff38ee0c00008017fe71e0397072ab1ff9c77060000400bff38f00d9829558ffce3b8300002005ff9c78067e14eec7fe71fd187801002ffce3c03260a5563ff38ee0c00008017fe71e00310502307f9c55000000400bee78ffbefcbdcc0c00015230f072005f73c7fce7e1ee6060000a9187839002f91e3fe73f0f7343f038768c3c1c8017bee1ff38f83bb9187806e461e0e400bdd70ff98001d558ffce3b8300072005e7387fce3e0ee6060000a9187839002f31c3fef9f2773030000548c3c1c801798e1ff38f83b98180002a461e0e400bc470ff9c7c1dcc0c00015230f072005c61000060800a2060000881800010027fce3c0caa2e0460ff38aa0000008013fe71e04551502307f9c550000004009ff38f014b8381183fce2a8000002004ff9c7808541c08c1fe71540000010027fce3c04220e0460ff38aa0000008013fe71e00930502307f9c550000004009ff38f00088281183fce2a8000002004e6187808140c00000000000000010022a8a00053f0c2200000010803c0080111040006441200000000000000004008882000102010000000000000000 else 0x3e0011050013fe70550000002307f9c1f00008080054c140000000000000000f8000404000a208000000000000000043efff3df0088929558ffcffb83000021f6ff9ef82c459caafffe7fdcf806390fb7fcf7c02664a0460ff38aa00000087d3fe73e01332502307f9c5500000043e75d55ff9d7d1dcc0c00015230f0721f3aeaaffce3e8eee461e0fb91878390f9c7c14002004055230f07cc0c000087ce3a0a00182202a918783e606000043e71d0500080101548c3c1f303000021f20c828004888000000000000000010f90001401600c4511f0007447c031c87c6baa3ff3afa3b98180002a461e0e43e35751ff9d7d1dcc0c00015230f0721f1aaa8ffcebe8ee6060000a9187839007d33d3fe71f07773f0fffdcfc3c1c803e19e9ff20003aa9f87ffe63e000e400fff7cff9cfc3ddd8ffce3fa30f072007ff9e78064c14aac7fe71dc180001003ffcf3c00620a0460ff38aa000000801f98e9ff38f83b98180002a461e0e400fcc34f00c1809440c000110300002006ff9e7838555c08f9fe7154e000010037fcf3c0caa2e0460ff38aa000000801bfe79e04551502307f9c55000000400dff3cf010a8381183fce2a8000002006ff9e78024c1408c1fe71540000010037fcf3c002a0a0460ff38aa000000801bfe79e00110502307f9c55000000400c882400222080000000000000000) else if Nat.blt b 18 then (if Nat.blt b 16 then 0x3e028f830002882008401e0110000001f010a83800dff3c2a8000001183fce0f808541c004ff9c1540000008c1fe707c042a0e0027b8e00000000000000003e020503001398600000000000000001f01028180055f142200000010803c00f808140c000a20800000000000000007c03665affbffcfdee0c0001563ff3f3e01b32d7fdffe7ee6060000a9187839f00d996bfef3f3f73030000548c3cfcf806ccb5ff6ff9f9540000008c1fe707c03665aff9dfc7dee0c0001563ff3f3e01b32d7fcefe3ee6060000a9187839f00d986bc0bff3a7b830000558ffce0f806cc35e01b30d28818000220600007c035f52ff9d7c5ddc8c3c037230f073e01a3297fdfbe6ee6060000a9187839f00d194bfe75f1773030000548c3c1cf80688a5ff7ef9bbdc180002ac7fe7e7c03260a003ffcf1ee0c0001563ff383e0193050017fe70f7060000ab1ff9c1f00c7c08003441055230f00cc0c0000f8060c04007e61a28818000220600007c030602000d1041440c000110300003e01332507dbfe7a550000002307f9c1f00801083efdd357b830000558ffcfcf802cc35e06ff9f1540000008c1fe707c00625affb7fcfcaa000000460ff3f3e003105001ffe78550000002307f9c1f001882800bff382a8000001183fce0f8005414004ff9c1540000008c1fe707c00220a0037fcf0aa000000460ff38 else if Nat.blt b 17 then 0x3ff1a229ffcebeaee606000ea9187839ff8d114ffe71f5773030007548c3ffcffc62e06001a2282a918783e60600007fe0330b002ffde0aa000000460ff383e0fb77f7fdffe7eff7e1fffbbfff9f9f07cbbfbfedff3f7fbf0fffddfffcfcf83e1dfdff6001faa9f87ffe63e007e7c1f0efeff94007d54fc3fff31f003f3e0f057707da007aaa7e1fff98f801f9f05c1b7bfed003f553f0fffcc7c00fcf81fdcfdff3bf8fb98180002a461e0e7c0dff3ef027fce8bb83fce2ee0ff383e06ff9f7802cc3408c1fe7154000001f032a8b8009ff382a8000001183fce0f819545c000b30c00000000000000007c0bff7affbffcfdff8ffce3fe3ff3f3e05ffbd7fcefe3eeec7fe71fd187839f02ffcebc0bff3a7fe3ff38ff8ffce0f817dcf5ff7ff9fbdc180002ac7fe7e7c0bce72ff9d7c5dcc0c00015230f073e04ff9d781bfe7c5dc1fe717707f9c1f027fcebc056e1e0460ff38aa000000f813fe75e00b30d02307f9c550000007c09ee3af037fcf8aa000000460ff383e045515001bfe78550000002307f9c1f022a8a8009ff382a8000001183fce0f80edcbdff7ff9fbdc180002ac7fe7e7c074e56ffbf7cddcc0c00015230f073e03a72b7fcebe2ee6060000a9187839f01cb838009ff387fa30f07dd8ffce0f80a7e1c004ff9c175007804cc1fe707c052e0e0027fce0aa000000460ff38 else 0x3ff38f83801798e0aa461e0f98180001ff9c7c1c0075f5477230f07dc8c3c00ffce3e0e003a72a2a918783e60600007fe71f07001d3151548c3c1f30300003ff38f838006bea0ee461e0fb9187801ff9c7c1c003575055230f07cc0c0000ffce3e0e001a6282a918783e60600007fe71f07000d1941548c3c1f30300003ff38f83800688a0aa461e0f98180001ff9c7c1c002405055230f07cc0c0000ffce3a0e001a2282a918783e60600007fe71707000d1141548c3c1f30300003ff38a83800688a0aa461e0f98180001ff98883c00bff787b830007558ffce0ffcc360e001a2282a918783e60600007fe61907000d1141548c3c1f30300003ff30983800688a0aa461e0f98180001ff98201c003445051030007440c0000ffcc008e1f3aeaab9818003aa461e0e7fe60007000d1141440c001d10300003ff21d878017fef0550000002307f9c1ff90ec3c00366580000000000000000ffc8441e00ffffe3dcf8003aafffffe7fe4220f007cbbf1cc7c001d53f0fff3ff20d83800688a0aa461e0f98180001ff906c1c00344500000000000000000ffc8360e000202802100783c40000007fe40007007c33d1cc7c001d53f0fff3ff1bbadffcefebfffc7ffffff1ffff9ff8ddd6ffe77f5f73030000548c3c1cffc6eeb7ff1bbadfff1ffffffc7fffe7fe35753ff9d7d5dcc0c00015230f07) else if Nat.blt b 19 then 0x3ff3afa387cebaaaaa461e0f98180001ff9d7d1c3e3555155230f07cc0c0000ffcebe2fe05e7392a918783e60600007fe75f17f01d3959548c3c1f30300003ff3af8bf8069ca4aa461e0f98180001ff9d7c5fc03465255230f07cc0c0000ffcebe2fe01a2292a918783e60600007fe75f07000d7d41dc8c3c1f7230f003ff3af8380068ca0aa461e0f98180001ff9d315ffe75f5773030007548c3c1cffce88affff8ffbb98f8003aa7e1ffe7fe74457ff9d7d5dcc0c001d5230f073ff3a22bffce3eaee606000ea9187839ff9cfc3c00fff7c7fa30f07dd8ffce0ffce7e1e005ffbc3fd18783eec7fe707fe73f0f002fb9e1548c3c1f30300003ff39f878017c8f0bb461e0f9a1f81c1ff9cfc3c0076e5c55230f07cc0c0000ffce7e1e001fbac2ed18783e687e0007fe73f0f000f9961548c3c1f30300003ff39f878006feb0ee461e0fb9187801ff9cfc3c00377587fa30f07dd8ffce0ffce7e1e001bbac2a918783e60600007fe73f0f000db961548c3c1f30300003ff39f878006ccb0aa461e0f98180001ff9cfc3c003645855230f07cc0c0000ffce3e8e1f3a22aaa918783e606000e7fe71f470f8d5547fe8c3f1f763ffff3ff38f83803e99e8ee7e1e0fb9f87ff9ff9c7c1c00fcc7455230f07cc0c0000ffce3e0e005eeb83fd18783eec7fe707fe71f07002f39c1548c3c1f3030000 else if Nat.blt b 20 then 0x3ff7cf93800e98a8aa461e0f98180001ffbe7c9c0034c5055230f07cc0c0000ffdf3e4e001a2282a918783e60600007fef1f37f00d1149548c3cff30300003ff6ff9ff83e5dfceefffe7ffdf87ff9ffb7fcffc03665a0460ff38aa000000ffdbfe7fe01932d2ab1ff9ff70600007fed0037f07c33d9cc7c00fd53f0fff3ff60017803e19f8e63e007ea9f87ff9ff9ffc3c00366585563ff07ee0c0000ffcf3e0e001a2282a918783e60600007fe77f5fffbffdfdfe8c3c1f763ff3f3ff3bfafffd7fef7ffc7ffffff1ffff9ff9dfd7ffe77f5fffe3ffffff8ffffcffcefebfff3bfafbb918783ee461e0e7fe77f5fff8ddd6fff8ffffffe3ffff3ff3bfafffc6eeb6aa461e0f98180001ff9dfc7fc0fee7e55230f07cc0c0000ffcefe3fe05ffbd3fd18783eec7fe707fe77f1ff00d9969558ffcffb8300003ff3bf8ff806ccb4aa461e0f98180001ff9dfc3c00bff787fa30f07dd8ffce0ffcefe1e001b32c2a918783e60600007fe75f57ffbf7ddddc8c3c1f7230f073ff3afabffcebeaeee461e0fb9187839ff9d7d5ffe75f5773030000548c3c1cffcebeafff3afabaa918783e60600007fe75f57ff9d195d548c3c1f30300073ff3afabffce88aeaa461e0f98180039ff9d7d5ffe3575377230f07dc8c3c1cffcebeafff1aba9aa918783e60600007fe75f57ff8d114f558fffffb8300c7 else 0x4004ff9c7831555408c1fe71540000020027fce3c10aa8a0460ff38aa0000010011104000c44500000000000000000800888200042220000000000000000040007984003155500081e000440000020003cc20000f30888c0f0002303c0010001c01000c5dd45560780019c1fff08000c000006e7e80880000004200f00400051040031555000000000000000020002000001888a0000000000000000100010000008444000000000000000007fff7fffff9ddd7ffffffffffffffff3ff7ffbffffe7ffeeefffe7ffdf87ff9ffbffdfffefff7f7fe3ff3fff8ffcfcffdffeffff3bfafbbb1ff9fff461e0e7fefff7fff8ddd6fff8ffffffe3ffff3ff7ffbfffc6eeb6aac7fe7fdc180001ffbffcffc0bff7a7fe3ff3fff8ffce0ffdffe7fe05f73d2ab1ff9ff70600007fefff3ff01db979558ffcffb8300003ff7ff9ff806feb4eec7fe7ffd187801ffbffcffc03665a5563ff3fee0c0000ffdffe7fe01b32d2a918783e60600007fefdf77ff9d7d5ddc8c3c1f7230f073ff7ef9bf80e9cacaa461e0f98180001ffbf7cdfc03465255230f07cc0c0000ffdf7e5e005ffbc3fd18783eec7fe707fefbf2f002fb9e1548c3c1f30300003ff7df978006ccb0aa461e0f98180001ffbefcbc00364585563ff3fee0c0000ffdf3e4e007e63a2a918783e60600007fef9f27002f31c1548c3c1f3030000) else if Nat.blt b 32 then (if Nat.blt b 26 then (if Nat.blt b 23 then (if Nat.blt b 22 then 0x40097fec7fc1e61719c1fff156078002004bff203f8fba98ce0ffc0ab03c0010025ff901f47d94c6707fe05581e0008012ffc80f87dc263383ff02ac0f00040097fe407c1f61319c1ff8156078002004bff203e0f3098ce0ffc0ab03c0010025ff901f07884c6707ffc5581e1f08012ffc80f83c4263383ff02ac0f00040097fe007f1f34319c1ff8156078002004bff003f0f9818ce0ffc0ab03c0010025ff801f47d90c6707fe05581e0008012ffc00fa3e4863383ff02ac0f00040097fe007c9f20b19c1ff8156078002004bff003e1f7018ce0ffc0ab03c0010025ff801f0fa80c6707fe05581e0008012ffc00f83e4063383ff02ac0f00040097fe007c1e60319c1ff8156078002004bff003e0f1018ce0ffc0ab03c0010025ff801f03880c6707fe05581e0008012e0c00f83c4062303c3008c0f0004009666007c32a020000000000000002004b33003e093010000000000000001002599801f048808000000000000000801277c00f83c4063383ff02ac0f0004009116407c1e6131100018002078002004803003e8d921888000c00103c001002401801f06880c44000600081e000801088800022208000000000000000040084440000100000000000000000002004003003fc99a5aa9c00c011f3fffd002001801fa0042c00e00600038018e80100080007222900070000001c0000 else 0x400c717c7ff9775f55b9e1f067e7fffa006383e3ffcbbafaadcf0f833f3fffd0031c1f1ffe5057c46e787c11b9e1fe8018e0f8ffe2ceaeab73c3e0cfcffff400c707c7fe8671f55b9e1f067e7fffa006382e3c1caaae005cf03822700001003181e1ffe4dd3910e000008781e0e8018c0f0fff2669eab73c3e0cfcffff400c60787fe8010f00b9e1f044e0063a0062aaa0000a2080000000000000001003141d01fe5cd6d56e787c19f9fffe8018a0a8006282a22373c3e08dcf0f8400c4450003911480038000000e0000200622280008882000000000000000010031114000040000000000000000000801880a0007222900070000001c0000400c4050003101400038000000e00002006202800140084001c000000700001003101400080040402e787c113801808013ffd8ff83cc2e3383ffe2ac0f0004009ffec7fc1e61719c1ff8156078002004fff43fe1f7038ce0ffc0ab03c0010027ffa1ff07d81c6707fe05581e0008013ffd0ff83cc0e3383ff02ac0f0004009ffe87fc1e20719c1fff156078002004fff43fe0f1038ce0ffc0ab03c0010027ff901f07984c6707fe05581e0008013ffc00fa3e4863383ff02ac0f0004009ffe007c3ea0319c1ff8156078002004fff003e0f1018ce0ffc0ab03c001002689a1ff06981c44000600081e00080131fc00f83440632803f02240f000) else if Nat.blt b 24 then 0x400dfffc7fc0661708c1fff154000002006fffc3fe0f3038ce0ffc0ab03c0010037ffe1ff07881c6707ffc5581e000801bffe80f83c4263383ffe2ac0f000400dfff007c1e20319c1ff8156078002006ffee3c00e20a0460ff38aa0000010037eff1ff07985c6707ffc5581e000801beef8ff83cc2c22000000040f000400df77c7fc166160000000000000002006f93e3fe0b30b88c0f0f82303c0010037bfe1ff069818210078044000000801bddf0ff83440e3383ffe2ac0f000400de6787fc126060000000000000002006e7e80000c00004200f00880000010035fff1ff07985c6707ffc5581e000801afff0ff83c40e3383ffe2ac0f000400d7ff407d1f65319c1ff8156078002006bffa03e0f3098ce0fff8ab03c0010035ffd01f07984c6707fe05581e000801affe80f83c4263383ffe2ac0f000400d7ff007d1f24319c1ff8156078002006bff803e0f9018ce0ffc0ab03c0010035ffc01f07980c6707fe05581e000801affe00f83c4063383ffe2ac0f000400d7ff007c1e20319c1ff8156078002006b33803e091010000000000000001003511c01f06880c44000600081e0008019fff8fff2eebebbf3ffe2efcffff400cfffc7fe8451f08f9fff154e0063a0067fee3c1caaae047cff38aa7000010033ff71e04551502307f9c550000008019ffb8f00288281183fce2a800000 else if Nat.blt b 25 then 0x41f078a087edff8b5581e0006707fe3a0f83c5043f2ffc1aac0f0c03383fffd07c1e233e097fe55560781c19c1ff8083e0f109006bffa2ab03c000ce0fff841f07884803577d15581e0006707ffc20f83c424012ffc8aac0f0003383ffe107c1e20200dfff05560780019c1ff8083e0f101006bff82ab03c000ce0ffc041f07880802dff895581e0006707fe020f83c404013ffc0aac0f0003383ff0107c1e2020097fe05560780019c1ff8083e0f101004bdf02ab03c000ce0ffc041f07880802577815581e0006707fe020f834404012ddc0aac0f0003383ff0107c1a2020090060402078001100018083e0b101004bf702ab03c000ce0ffc041f04880803599c000000000000000020f824404013ccc00000000000000001003f99e9ffdcbd1b98f80002a7e1e0e801dffbcf0628aa811f3fce2a9c0000400e5dd60031415008f9fe7154e000020072229001c88a4001c0000007000010039114800c4050000e000000380000801bfff8ffe3eeae3383ffe2ac0f000400dfffc7fd1f65719c1fff156078002006fffe3fe8bb2b0460ff38aa0000010037fff1ff0ff85d7707ffc5dc1fe00801bfff8ff83ec2e3383ffe2ac0f000400dfffc7fc1e61719c1fff156078002006fffe3fe0f30b8ce0ffc0ab03c0010037fff1ff0798582307f9c55000000801bfff8ff82cc2c1183fce2a800000 else 0x41f4789cf825ff955581e0706707fe020fa3c4c7c12ffc2aac0f0383383ff0107d1e2520097fe45560781c19c1ff8083e8f121004bff02ab03c000ce0ffc041f44c908025998000000000000000020f8fdd67ff2ffcbaac0f0003383ff0107c7eaa3ff97fe1d560780019c1ff8083e3f501004bff02ab03c000ce0ffc041f17aa087e7ff835581e0006707fe020f8bd5043f2ffc1aac0f0003383ff0107c3fa23e097fe15560780019c1ff8083e1fd01004bff02ab03c000ce0ffc041f0fb8cf825ff955581e0006707fe020f87dc47c12ffc2aac0f0003383ff0107c3ea23e09ffe15560780019c1ff8083e1f511f04bff0aab03c000ce0ffc041f0fa808025ff815581e0006707fe020f83ec24012ffc8aac0f0003383ff0107c1f6020097fe05560780019c1ff8083e0f901004bff02ab03c000ce0ffc041f079848037ffd15581e0006707fe020f83cc2401affe8aac0f0003383ff0107c1e612009ffe45560780019c1ff8083e0f309004bff22ab03c000ce0ffc041f07984802445910081e000440006020f83cc0401affe0aac0f0003383ff0107c1e602009ffe05560780019c1ff8083e0f301004bff02ab03c000ce0ffc041f078acfffdffdf5581e0006707fffa0f83c567ff2ffcbaac0f0f83383fffd07c1e2a3ffb7fe3d560780019c1ff8e83e0f151ffcbff0eab03c000ce0ffc7) else if Nat.blt b 29 then (if Nat.blt b 27 then 0x5e0051050033ff70550000002307f9c20ff7fef7c1022ca847cffffaa70030107f9f3fbffe5df7d77e7fffddf9fffe83fcd9f5ffd0031e11f3fffea9c00c741fe5cd6803141d119f9ffff56e787c20ff2669401000c0847cffffaa70030107f7fbe3ff97fe1d560780019c1ff8083fbd5f1ffd8031f55ffffffb9f00c741fc7dd48025ff915581e0006707fe020fe3e68401affe0aac0f0003383ff0107f1f3420097fe05560780019c1ff8083f3ffc10f8bd5063383ff02ac0f00041f97fe087e5e38319c1ff81560786020fcbff043e3f5418ce0ffc0ab03c00107e5ff821f17aa0c6707fe05581e00083f2f1c10fcbff06ab03c300ce0ffc041f87cc08035ffc15581e0006707fe020fc3e604012ffc0aac0f0003383ff0107d3fe73e0d7ff557707f9c5dc1ff8083e9ff39f04bff2abb83fce2ee0ffc041f4ff9cf825ff955581e0006707fe020fa7fce7c1222ca8460ff38aa00030107d3fa63e097fe15560780019c1ff8083e9fd21004bff02ab03c000ce0ffc041f4fa9cf825ff955581e0706707fe020fa3eca401affe8aac0f0003383ff0107d1f6520097fe45560780019c1ff8083e8f939f04bff2aab03c0e0ce0ffc041f47c908035ffc15581e0006707fe020fa3e484012ffc0aac0f0003383ff0107d1e673e097fe55560781c19c1ff8083e8f179ffdbff3eab03c0e0ce0ffc7 else if Nat.blt b 28 then 0x5ff009818037bbe1550000002307ffc2ff80000c01bddf0aa8000001183ffe17839555c00c705c044e000000b9e070bc1bfffaffa7fceebb83ffe2ee0ff385e0dfffd7fd3fe7719c1fff156078002f06fffebfe1f71b8ce0fff8ab03c0017837ffc41f4fe98c6707fe05581e000bc1beefaffa7fcecaa000000460ff385e0d7ff507d3fe735dc1ff817707f9c2f06bffa83e8f1398ce0fff8ab03c0e17835ffc41f0fa88c6707fe05581e000bc18e2fafff7fefeab73c3e0cfcffff5e0c55550013fe70550000002307f9c2f0628aa8019ffb8aadcf0f833f3ffe17827ffa5ff0fb89c6707fe05581e000bc13ffca0fa7fce6bb83ff02ee0ff385e09ffe107c3ea2319c1ff8156078002f04bff283e9ff39aee0ffc0bb83fce17825ff941f4ff9cc6707fe05581e000bc12ffca0fa7d4e63383ff02ac0f0385e097fe507d1e27319c1ff81560781c2f04bff283e1f7198ce0ffc0ab03c0017825ff841f4fe98c6707fe05581e000bc12ffc20f87f4463383ff02ac0f0005e097fe107c3ee2319c1ff8156078002f04bff083e1f5118ce0ffc0ab03c0017825ff841f07888c6707fe05581e000bc1222ca0fa7fce6aa000300460ff385e09006107c3aa231100018002078002f042aa28009ff382a8000001183fce1782045941feffded54e006008f9fffebc08aa2a0067fee0aa000000460ff38 else 0x5ff47d958037fff15581e0006707ffc2ffa3ec8c013ffd0aac0f0003383ff017fd1e677e0dfffd5560781c19c1fff0bfe3f75bffefffeeab03c000ce0fff85ff0fb8df837fff55581e0006707ffc2ff87dc2c01bfff8aac0f0003383ffe17fc3ee06009ffe85560780019c1ff80bfe1b70b006fffe0aa000000460ff385ff079adfff7fff75581e1f06707fffaff83cc2c01bfff8aac0f0003383ffe17fc1e61600dfffc5560780019c1ff80bfe0f30b006fbbe00103c00088000005ff079858035fff15581e0006707ffc2ff83cc2c01ae0f888c0f0002303c3e17fc1e616009ffec5560780019c1fff0bfe0f30b004fff62ab03c000ce0ffc05ff079858026efb15581e0006707ffc2ff83cc0c01bfff0aac0f0003383ffe17fc1e60600dfff85560780019c1ff80bfe0f303004fff42ab03c000ce0ffc05ff079818025ffa15581e0006707fe02ff83c42c01bfff8aac0f0003383ffe17fc1e20600dfff85560780019c1fff0bfe0d103006f77c2ab03c000ce0fff85ff059858037fff0550000002307f9c2ff82cc2c01bfdf8aac0f0003383ffe17fc1661600df77c0000000000000000bfe0b30b006383e22303c0008c0f0f85ff04981803799e00000000000000002ff824c0c013ccd000000000000000017fc0e61600dfffc5560780019c1fff0bfe0220b006fffe2aa000000460fff8) else if Nat.blt b 30 then 0x5ffe5dd78033fff15df9ffff77e7ffc2fff2eebc019e4f88cfcffffab73c3e17ff9775e00c747c467e7fffd5b9e1f0bffcbbaf006383e233f3fffeadcf0f85ffe5dd78020c1b119f9ffff56e787c2fff2669c018c0f08cfcffffab73c3e17ff7fff7ffdfffdd7707ffc5dc1fff0bffbfffbff8fdd6fff8ffffffe3ffff5ffdfffdffc7eeb719c1fff156078002ffefdfefffffffffffffffffffffffd7ff7eff7ffdfbfdfffffffffffffffebffbf7fbffdddf7ffffffffffffffff5ffc7dd58037fff15581e0006707ffc2ffe3cfeffffffffaadcf0f833f3fffd7ff1675600c707c467e7fffd5b9e1f0bff7ffc70f83c5463383ff1eac0f0005ffb7fe387c3eaa319c1ff8f56078002ffdbff1c3e0f1518ce0ffc7ab03c0017fec018e1fdeaf8fdcf8063aafffffebff4228f0067ffe2aa70031c47cfff85ffa0043803181e11138018e02e787c2ffcfff0c3e3f5518ce0ffc0ab03c0017fe5ff961fc78fcc6707fe05581e1f0bff2ffcb0f83c5663383fffeac0f0f85ff97fe187f7fbe319c1ff8156078002ffcbff0c3e3f5518ce0ffc0ab03c0017fe5ff861f078a8c6707fe3d581e1f0bff200c30fff77d7ee7c031d57fffff5ff4ff9df837fff55dc1fe717707ffc2ffa7fcefc1bfffaaac0f0003383ffe17fd3fe77e0df77d02307f9c55000000bfe9ff3bf04fff6abb83fce2ee0ffc0 else if Nat.blt b 31 then 0x60097fe007c1e20319c1ff8156078003004bbb003e4f905088000000103c001802599801f64c928000000000000000c012ccc00f926414000000000000000600844400009100800000000000000030037fcf3c18aaaa0460ff38aa000001801bfe79e08554502307f9c55000000c00bcc70ffde7e1dcc0c00015230f076004ff9c7839555c08c1fe71540000030027fce3c14aa8e0460ff38aa000001800f98a9fffcfd3b98180002a461e0ec00488040062228000000000000000060024402002111000000000000000003000f9963fffbfaf73030000548c3c1d800788a1fffcfd3b98180002a461e0ec003c450ffde7e1dcc0c00015230f0760004000003911480000000000000002ffffffffffffffffffffffffffffffd7fffffffffdfffdfffffffffffffffebfffffffffefdfeffffffffffffffff5ffffffffff5c1f7bbffffffdeff87faffffffffff377dbfffffffffffffffd7fffffffff079adc6707fffd581e000bffebbef0fefd7e7fffffffffffffff5ffefffffff9f7ff5df9ffff77e7fffafff7feffc19fffaaefcffffbbf3ffe17ffbff7fe0c717d467e7fffd5b9e1f0bffdbfaf006383e233f3fffeadcf0f85ffe7dfffff9f7ff5df9ffff77e7fffafff3efffff8f3fbaefcffffbbf3fffd7ff9f75e00dfffc577e7fffddf9fff0bffce0fffff3effeab73c3fccfcffff else 0x600be66a7fcf3e0ee6060000a918783b005bff303e0f3098ce0ffc0ab03c001802dff881fc7cd0c6707fe05581e000c016ffc40fc3e6063383ff02ac0f000600b7fe207d1f24319c1ff8156078003005bff103e4f9058ce0ffc0ab03c001802dff881f07c80c6707fe05581e000c016ffc40f83c4063383ff02ac0f000600b666207c1220200000000000000030055de73c1caaae047cff38aa7000018029110800040000000000000000000c0140884007222900070000001c0000600a0042003911480038000000e00003005002100140084001c0000007000018027ffb1ff3ff87fff1ffe07fc7fe0ec013ffd0ffbffc9fff8fff03fe3ff076009ffe87fcffe0fffc7ff81ff1ff83b004fff43fe4fb078ce0ffc0ab03c0018027ffa1ff07981c6707fe05581e000c013ffc00f93e4163383ff02ac0f0006009ffe007c1e20319c1ff8156078003004f3343fef9f2773030000548c3c1d802799a1ff3cf83b98180002a461e0ec013ccd0ff926c1c00000000000000060097fe407c9f61b19c1ff8156078003004bff003fcf9a58ce0ffc0ab03c0018025ff801fa7cc2c6707fe05581e000c012ffc00fb3e4963383ff02ac0f00060097fe007cbfa0b19c1ff8156078003004bff003e4fb058ce0ffc0ab03c0018025ff801f27c82c6707fe05581e000c012ffc00f93c4163383ff02ac0f000) else if Nat.blt b 37 then (if Nat.blt b 34 then (if Nat.blt b 33 then 0x600e4452003b19480038000000e000030072229001c9ba4001c0000007000018039114800e4552000e000000380000c01c88a4007222900070000001c0000600e4452003101400038000000e00003007222900140084001c0000007000018039114800040000000000000000000c01c80a4007222900070000001c0000600dfffc7fff7f5ffffffff1fffffffb006fffe3fecfb2f8ce0fff8ab03c0018037fff1ff65d9782307f9c55000000c01bfff8ff9ffc3fff8fffe3fe3ff07600dfffc7fcf7e1eeec7fe71fd18783b006fffe3fe4fb0f8ce0fff8ab03c0018037fff1ff25d8782307f9c55000000c01bfff8ff83cc2e3383ffe2ac0f000600dfff87fc9f60f19c1ff8156078003006fbbe3fe7bf0f73030000548c3c1d8037c9f1fffdfd7fdeff87c3bfffffec01bccf0ffbe7c9dcc0c00015230f07600de6787fcf3e0ee6060000a918783b006f33c3fe49b070000000000000001803789e1fffcfd3b98f80002a7e1e0ec01affe00fb3e4963383ff02ac0f000600d7ff007c9f20b19c1ff8156078003006bff803e0f1018ce0ffc0ab03c0018033ff71e02550702307f9c55000000c018e0f8fff2eebeab73c3e0cfcffff600c4450000910080000000000000003005fff53fe7ff07ffe3ffc0ff8ffc1d802fff981f47d94c6707fe05581e000c017ffc40f83c4063383ff02ac0f000 else 0x600ee65a7839154c0038000000e00003007732d3c1c88a6001c000000700001803b7f5800e5556021e078044380000c01daeac0072aab00070000001c0000600ecfd20039114808781e0110e0000300763a9001c88a4001c000000700001803b194800ec652000e000000380000c01d8ca400722a900070000001c0000600ec652003911480038000000e000030073eeb001caaac005cf000227000018039d55800e5556000e000000380000c01ce8fcfff2eebeab73c3e0cfcffff600e745e7839555c00b9e07044e00003007323d3ffc88a7805cf0f82270031d80399169e0e4553000e000000380000c01cc8a4007e7e908870000043c0f00600e5dd6003955580038000000e000030072eeb001ca8ac047cff38aa7000018039555800edfd6110e000008781e00c01caaac0076bab00070000001c0000600e55560039f7581138000002e780030072aab001ceaac001c0000007000018039555800e5556000e000000380000c01caaac0072a2b00070000001c0000600e5456003977585538000023e7f9c30072a2b001caaac001c0000007000018039515800e5456446e787c11b9e1f0c01c8aa4007322900070000001c0000600e4552003915480038000000e0000300722a9001c88a4001c0000007000018039114800fc652000e000000380000c01c88a400767e908870000043c0f00) else if Nat.blt b 35 then 0x600ffffe7fc9761e08c1fe7154000003007ffff3fe0f30b8ce0fff8ab03c001803ffff9ff0598582307f9c55000000c01ffff4fffffe9fffffff03fffff07600ffffa7ff9f74f19f9ff8156e78003007fff903fcf9a58cfcffc0ab73c001803fff79e0fd7572abfff9c773e0000c01feefcfffefebdcc7c000153f0f07600ff77e7ff9775e0038000000e00003007fb3f3fffbfaffbdff0f877fffffd803fbfe9fffcfd3bb9f87806e7e1e0ec01fccf4fffe7e9dcc7c000153f0f07600fe67a7ff9374e0038000000e00003007f33d3ff60087511f0000447c001d803f99e9ff3cf83b98180002a461e0ec01fccb4f07e3a99447c000111f0000600fcfd2003f1948aa7e1e0198f80003007e7e9001cc8a4043c0f0088700001803f194800fc652288f8000223e0000c01effec0ff3eeb633f3ff02adcf000600f7ff207f9f34b19f9ff8156e78003007bff903e0f1018ce0ffc0ab03c001803d99c81feced2800e000000380000c01ecce40ff26e940070000001c0000600f667207f9334a0038000000e000030077fef3c1caaae047cff38aa700001803bff79e0a1147023e7f9c55380000c01dffbcf00288281183fce2a800000600ef75e7839555c0038000000e0000300773ad3c1c8aa6001c000000700001803b9969e0ecfd3110e000008781e00c01dccb4f0763a980070000001c0000 else if Nat.blt b 36 then 0x61f27c82802dff895581e0006707fe030f93e414012ffc0aac0f0003383ff0187c9f20a00977600020780011000000c3e4d905004b7f00880000004200f0061f26c82802401810081e000440006030f92e414012ffc02a8000001183fc0187c9320a00d66700000000000000000c3e49905005b331000000000000000061f24c828025998000000000000000030f8fdd67ff7ffcffbc3f000778fff1d87c7eaa3ffbffe3fde1f8003bc7ff8ec3e2f5410fdbff16ab03c000ce0ffc061f17aa087e5ff835581e0006707fe030f87d447c17ffc6aac0f0003383ff0187c3ea23e0b7fe35560780019c1ff80c3e1f501005bff12ab03c000ce0ffc061f0fa808025ff815581e0006707fe030f83e404012ffc0aac0f0003383ff0187c1e2a3ffb7fe3d560780019c1ff8ec3e0f101007bff92ab03c000ce0ffc061f07880802fff895581e0006707fe030f83c404016ffc4aac0f0003383ff0187c1e202009ffe05560780019c1ff80c3e0f101004bff02ab03c000ce0ffc061f06880802c01890081e000440006030f824404016ccc40000000000000001803ffff9fffffd7fffffffc7ffffe0ec01ffffcfffefebdddfffce3fbf0f07600ffffe7ff9f75f19f9fff156e78003007ffff3ffcbbaf047cff38aa700001803ffff9ff47d95c6707ffc5581e000c01ffffcff93ec3e3383ffe2ac0f000 else 0x61ff447287fd11cba23e018e88f8063b0ff6769401ecce4001c00000070000187f9f75a00f7ff6556e780019f9ff80c3fcf9a5007fff92ab73c000cfcffc061fe7cd2803dffc955b9e00067e7fe030ff2669401fcce4001c00000070000187f9334a00f6672000e000000380000c3fc99a50072239211f3fffea9c00c061fc7cd0802dff895581e0006707fe030fdd5757ff600c7d57fffffee7c031d87ec018a1ff4cf2fdcf8063aafffffec3f600c50fd80317447c031d11f00c761f97ee087edff8b5581e0006707fe030fb7fcf7c12ffcaaee0ff38bb83ff0187dbfe7be09776502307f9c55000000c3ecf925005bff12ab03c000ce0ffc061f67c928025ff815581e0006707fe030faff5c7ff7ffc7fbc3f000778fff1d87d3fe73e0b7fe757707f9c5dc1ff80c3e9fd31f05bff1aab03c000ce0ffc061f47c90803dffc95581e0006707fe030fa3e484016ffc4aac0f0003383ff0187d1f2420097fe05560780019c1ff80c3e7fd55ffdfff1fef0fc001de3ffc761f3eeaaffefbf8ee6060000a918783b0f97f457c12ffc2aac0f0003383ff0187cbfa0a0097fe05560780019c1ff80c3e4fb0d004bff22ab03c000ce0ffc061f27d828025ff815581e0006707fe030f93e577ff2ffcbaac0f0f83383fffd87c9f20a00f7ff25560780019c1ff80c3e4f905006bff82ab03c000ce0ffc0) else if Nat.blt b 40 then (if Nat.blt b 38 then 0x7e0e4553003b9d680038000000e00003f0722a9801dccb4001c000000700001f839114c00eeeda154e000008f9fe70fc1bfffaffbffcffff8fffe3fe3ff3f7e0df77d7fdbfe7e550000002307f9c3f06f9bebfffffbffbdff0f877fffffdf8315554006ff9e1540000008c1fe70fc16ffc60fa7f4c63383ff02ac0f0007e0b7fe307c3ea2319c1ff8156078003f052aa38009ff382a8000001183fce1f828451c00effde154e000008f9fe70fc140086007776d0aa70000047cff387e09ffe97fcffe2fffc7ff81ff1ff83bf04bff283edff3daee0ffc0bb83fce1f825ff841f0fa88c6707fe05581e000fc12eeca0fb7fcf4aa000000460ff387e085545001bfe78550000002307f9c3f012a838019ffb82a8000001183fce187fffffbfff5df7fffffffffffffffec3fffffdfffaabbf55ffffffb9f00c761fffffeffee7f9feefffffffdf87e3b0ffffff7ff6f3cfddffffffef7fc31d87fffffbffb1167eabffffff73e018ec3fffdfdfffaefbffffffffffffffff61ffeefafffd33cffffffffffffffffb0fff77d7ffe88e7d57fffffee7c031d87ffbbebffb8fe3fbbfffffff7e1f8ec3ffddf5ffdc131f55ffffffb9f00c761ffeefaffec018faaffffffdcf8063b0ffe769401e88e4553f0f07cc7c000187ff3b4a00b00622a9f8783e63e0000c3fe99e50fd8031755ffffffb9f00c7 else if Nat.blt b 39 then 0x7ff27d838037ffe15581e0006707fe03ff93ec1c017ffd4aac0f0003383ff01ffc9f60e009ffe85560780019c1ff80ffe4bb0f006fffe0aa000000460ff387ff24d83803799e00000000000000003ff8fdd6fffffffffbc3f000778ffffdffc7eea7ffbffebfde1f8003bc7ff8effe3f70b006fffe3ef0fc001de3fff87ff1eba9ffffbfeee6060000a918783bff87dc6fc1ffffeaac0f0003383ffe1ffc1e61600ffffe5560780019c1fff0ffe0f30b006fffe2ab03c000ce0fff87ff07981802fffa95581e0006707fe03f07ffffbffdffbfaefcfff8bbf3fce1f83fddfdfffffdfbdcf80002afffe7efc1fcef6ffff7eddcc7c000153f0f077e0fd77f7ffbff7eff7e1fffbbfff9fbf07bffb83e1f7198ce0ffc0ab03c001f83dffcc1fefedac67e7fe055b9e000fc1dffbef077fef8bbf3fce2efcff387e0effdf783bdd7c08f9fe7154e00003f077bafbc1dffbe2a9c000011f3fce1f83b9d6de0ee75b000e000000380000fc1dbfae0077fef0baf03c0267cff387e0ec753003b99680038000000e00003f073abfbffdffbfaadcf0f833f3fffdf839d55c00fffde154e000008f9fe70fc1caaae0077fef0aa70000047cff387e0e5557003bdd780038000000e00003f072aab8015779c2a9c000011f3fce1f839555c004ff9c1540000008c1fe70fc1c8aa600777ed08870000043c0f00 else 0x7ffb19e787fffbfbfffffffffffffffbffd88b3c3fffffdfb9f00c755fffffdffec118e1ffeefafdcf8063aafffffefff602c70fff77d7ee7c031d57fffff7ffb006387ffbfebf73e018eabfffffbffd8031c3ffddf5fb9f00c755fffffdffec018e1ff607aeccf8063a2bfe1fefff600c70fdd5757ee7c031d57fffff7ff7ff9ff837fff5ffc7fe7fff1fffc3ffbffc9c013ffd0ffe3ff07ff8fff01ffdf3e4e00de6782a918783e6060000ffef9f27004f3341548c3c1f30300007ff67d978037fff15581e0006707ffc3ffb3ecbc013ffd8aac0f0003383ff01ffd7fef7ffffffffff1ff9c7fc7fffeffe8fb2b007ffff2ab03c000ce0fff87ff3ffafffffffffffc7fe0fff1ffffbff9ffc5fc13ffd2ffe3ff07ff8fff01ffcffe1e00dfffc7ff1ff83ffc7fff0ffe7ff07006fffc3ff8ffc1ffe3ffc07ff3ff83802fffa9ffc7fe0fff1ffe03ff9ffc1c013ffd0ffe3ff07ff8fff01ffcfbeaffffeffbb98180002a461e0effe7bf0f006fffe1fe8c3c1f763ff387ff3df878037ddf0aa461e0f98180003ff9e7c1c01fccf455230f07cc0c0001ffcf3e0e00de6782a918783e6060000ffe79f07005f3351548c3c1f30300007ff3cf83802799a0aa461e0f98180003ff93ec3c01ffffcaac0f0003383ffe1ffc9f61e00dfffc5560780019c1fff0ffe4fb0f006fffe0aa000000460ff38) else if Nat.blt b 41 then 0x7fff507787fffbfbf7bfe1feeffffffbfffa239c3ffddf5fb9f00c755fffffdfffd114e00fe67a288f8003a23e0000fffcfbfffff3effebbf3fffeefcffff7ffe7dd7803ffff955b9e00067e7ffc3fff3ee9c01ffff4aadcf00033f3ff01fff9c1fffffdffffdeff87fbbfffffefffcbbaf007ffff0aa70000047cff387ffe5dd7803fddf80038000000e00003fff2eebc01fecfcfffffffffffffffdfff9775e00efffe577e7fffddf9fff0fffcbbaf0073a3f233f3fffeadcf0f87ffe4dd3803f99e80038000000e00003fff26e9c01cc8f4043c0f0788700001fff9114e00fc67a398f8003aa7e1ffefffbf7fbfffffffffffffffffffffff7ffbffe387c7eaa3bbc7ff8fde1f8003ffdf7f1c3e7dd5555230f07cc0c0001ffef3f0e003e62a2a918783e6060000fff79f87000f1141548c3c1f30300007ffbbfeffffffffffffffffffffffffbffdddf7fffffffffffffffffffffffdffeeefbfffbbbeffffffffffffffffefff766dfffffffffee7c031d57fffff7ffba26bffffbfeff73e018eabfffffbffdc7f1c3ffddf5ffbf0fc7ddfffffdffee3f8e1fba26aea9f87e3e63e018efff71f87007f33d154fc3c1f31f00007ffb8fc3803789e1bb7e1f8f9aff87c3ffdbff1c3fbfdf18ce0ffc0ab03c001ffedff8e1f1faa8c6707fe05581e000fff660dfffffffffef7fc3fddffffff else if Nat.blt b 42 then 0x7fffffdff83fddfcaafffe7fdcf80003fffffeffc03e65a5563ff3fee0c0001ffffff4e00ffffa7fffff83ffffff80fffff7fffffffffffffffffffffffff7fffeffbffffbfeeee7e1e0fb9f8783bffff7fdffffddf7fffffffffffffffdffffbfefffbafebfbbfffffff7e1f8effffdff7ffdd135f55ffffffb9f00c77fffeffbffc7aea6aa461e0f98180003ffff7edfc1fcef6553f0f07cc7c0001ffffbbeffffeefbfffffffffffffffeffffddf7ffdd575ffffffffffffffff7fffe67bffffbfeff73e018eabfffffbfffeffbc3fffdfdfffffffffffffffdffff7f5e00ffffe3fdf8783eefffe70ffffbfaf007fbbf154fc3c1f31f00007fffdfd78037c9f1bbffffffdeff87c3fffefebc003e65855230f07cc0c0001ffff3fce1ffeefaffdf87e3eefffffeffff9fa7007f33d154fc3c1f31f00007fffcfd3802e89a8aa7e1e0f98f80003fffe7e9c01344d0d57fffffee7c0301ffff3f4e005e6382a918783e6060000ffff9fa7001f3151548c3c1f30300007fffcfd3800788a0aa461e0f98180003fffcbbfffffffffffbf0fffddfffffdfffe19effffeefbffdf87ffeefffffefffee2ffffffffffef7fc3fddffffff7fff707ffffffffff7bfe1feeffffffbfffb03dffffddf7fbdff0ff77fffffdfffd77de1fffefefffffffffffffffefffebbef0ffb83f777ffffffbdff0ff else 0x307c1e2020097fe05560780019c1ff818012ffc00f83c4063383ff02ac0f0007ffffffffffffffffffffffffffffffbfffffffffffffffddffffffef7fc001fffffffffffffffbfdf8783eefffe7efffffffffffff7fffffffffffffffff7fffffffffffc9ffbbffffffdeff87fbffffffffffefbfffffffffffffffffdfffffffffff747feefffffff7bfe1fefffffffffffb83ff77ffffffbdff0ff7fffffffffeeefbffffffffffffffffbfffffffffe3f75bdde3ffffef0fc001ffffffce1f1faa8eef1ffe3f787e000ffffffbff07ffff9fffffcfffffff38
def wireAt (i : Nat) : Nat := Nat.land (Nat.shiftRight (dictChunk (i / 32)) (125 * (i % 32))) 0x1fffffffffffffffffffffffffffffff
def stateWires : Nat → Nat → List Nat | 0, _ => [] | n + 1, ids => wireAt (Nat.land ids 0x7ff) :: stateWires n (Nat.shiftRight ids 11)
def htChunk_7 (_ : Nat) : Nat := 0xce66baa4deb2565e503e9bc028b5680f08c90aa15e09b36f
def stChunk_7 (_ : Nat) : Nat := 0x8c702dcb2474a273b58197c48a9049cb2474a3739d8197248a9049cb2484a9b2ee312374a2f3b58197248b1049cb2374
def htChunk_9 (b : Nat) : Nat := if Nat.blt b 1 then 0x5797a1576fc056e39055cf025551f255072a54d08854189a528774524234519dc54cebca4ca5944ca1854c39484b96024b5cf748c43e4853a4481fa747574246f68346714c45ccd1451d6b442b3a42d52b42881242859641363c4073b73ffb3b3fed643fd6673f9abd3f47753e6e0c3dc4673d861c3abac038178934adce34a46032e99b3297b93227762f8a672b8cde2aaf672a5fc42a0b6c2909a128664927f9d027b92e26ad6e25d56225c80324d4d823ec4f22b06a228270226f5a217088201c271e1f471d756e1d31c81cf4ce1b82201b6cc81b3c4d1b07321a0ef9190c1418fbf318dd71188a101823e9178979172af716e1a1164031163ce71627de1596751523ed149eb11221ec10a70c105d981005e40f6d0c0f69010f4c530e7af50e3aff0e30c40e1a310d93a20d69a80d31640d05fe0c3a9b0b00ab0afe7109e81f09214608b735084c4b079f92079c5b072a9b06f88d05dc9305928604e0e404899a0483f303f6de02d819023c6901de7301c625014dce00be60003020001765 else 0xf699d7ec16d1e5e1b1e51534e22b51df54f4ddee5ddc0cf0db08a1dad37cd6fb75d4ec71d37477d27a83cf7bcaceb7a0cad3a8c6963ec509d2c2c702c26d20bec2aabe7fafbdd8ddbc96a1bc8c61b9fa5ab647cab18102b0261ab017a1af2d34aea914ae7019adbeabab130da738e5a5fef3a4a0cea45fb4a43437a2d3e99f90ff9b8eeb9b4557999e36973d39962f6d9555f4947a1c93a7a38e0beb8cfca48c488087c4de862f6e8368ab834d0f82b7eb827f8d81bd1b814b807d2e7d7cc0ff7a61a77642a6762dd7755ec874bbcd738e526fa2146f28dc6ba78a6ab29f693ab366df8d66390466041e64fcb864998063147561cece60aa466047a360002d5ffdd45fe2415fb3375fab135f65265f0ad05de8d65d53205d1b1a5bc232
def stChunk_9 (b : Nat) : Nat := if Nat.blt b 3 then (if Nat.blt b 1 then 0x838e5981a472e8b075cb30348e5c961e3966068dcb92d3788cd64b90e0586ae5981a372e4b3b60e3032f84496a6d378a66f0702d4c88ce59281ad58bd071cb2372f8b53629c1146e3816a6c536e68dcde2c1c72cc0d239685a9b162092371c0b071cb3034d25c9614b966068f0b92d4d97cc0d1b97f5a3739581972048b071ce30346e5f162c3e172c8dc4dad1b606a5d1b9725a994b26e172136b071cb3034925c960e3966069acbe2ced852c0cb91125838e5981a47338b0fdcb30346e5f1673c1c72cc0cb92c5e852e591b9725844e5981a472e4b536a64ca4806f169bc1c6b26f0702cc372ac0d1b9725 else if Nat.blt b 2 then 0x839049cb2372f8b5365f3034a25f1689d022e43804dac1c72cc0d2817f5a994b27097c136b071cb3034545c9614bd172cc0d1bac1c72cc0d239725852e5981a832e4b1520939646e0956a6c536f08dcde2d4c88ce59239ad5a9b30d83a372e4b15208b9646e3816a645472c920d3ad4d8c4dcd1b9725838e59842502e4b0a60939646e5c960e39b60691cb92c7188cbcd1b8e05a99311c19c12e4b5368745482238162c3966068dca0ad4d986c0d281725a5d0a5cb3032e4b071cfb0346e6cd689b9660691cb92d1374e944b909b5838f49cb30346eb30dcb30346e7cd68db0352c8dcbe2c1c72cc0d281725 else 0xa9b4c1819fd2e4b5362c3e246e4316a64c453e898b92d4d96115208a375838e7181a6b2e4b49e0e3966065f160e396606a24b92ce7852e59819725852ecd81a372e4b5362340a46e38160e3965e691cb92c1c72cc0d1b99f5838e597c237378b53661b034a25c96a6cb988c8dc38ac6a8a90451b8e05886e5981a372f8b5329649190e3816233965da8dcd9ad4d986c0d1f9725a9b192052371c0b53661b034e85c96a6c54824920702d4d8c4de11b9725838e59802373f0b071cb37a46e7cd6a6cbb8a68dc4dac1c72cc21239725a99311c199c136b43a49c541c026d614b956068dcb92c1c72cc1d1b97f5) else if Nat.blt b 5 then (if Nat.blt b 4 then 0x838e5981a372feb0a5cb3034b45c96a644672c8dcd9ac1c72cc0d379725a9b18e072371c0b5320e39b4d66f160e39660e8dcbe2c2972cc0d2397258a8f85cb247136b071cb3034985c96a6cc460ea10b92d4c87ee59449725838e5981a3742ab5326bc1c74294560e38c606940b92c2972cc1d1b972597ce5981a372f8b5326bcc47428dd6a6d2c6067f0b92c1c72cde9239725852e5981a502e4b071cab0346e7dd62a3e172c8dc4bad4c8a8e59239a75a9b071802373cab5362a41546e3816a6c5f8a88dc702cc372cc0d289725852e0d81a372e4b15dcb30346e5c96a65137aa3804dac4672cbe11b9725 else 0x852e6d81a372e4b151cb30346e51d629b9660691cb92ced838c0cb91145a9910dcb2892e4b0a5cb30346e5d1629c1472c8dc122c2972cc0d1b9685a26add28972136b53221b9651499d6a65189b65c84dac1c72cbf91b97c5a9b30dbda372e4b0a605b966068dd6a65189ca5c84dac1c72cc0d1f97c5886e7181a372e4b10dcb2e746e5c962a39660691ca0ac1c72cc0d2d17c5838e59842372feb0a5cb2fe46e5c96a64c470684cb92d4ca273b4be09b5a9944e74172136b3860e30346e5f1661b966068dcb92d4d986de9289725838e5981a47444b071cb30348e5f1614b966068dccf2c2972cc0d1f9725) else if Nat.blt b 6 then 0x838e5581a502e4b536a64c94a26f16a6c578288dc702d4d838ded1b9f759cb071cb3032f8b536623074a05c962c3966068dca12d30906c0cb90e05838e5979a372f8b071cb30246e5f16a651b9ca5f04dad1b606a592397258a8f79cb237136b17a0e39648e5c960e3965ee8dcb92c1c738c0d239725852e5981a472f8b071c630346e5fd60e3966068dcbf2c1c72cc211b97c5a9b15208a3c1c0b119cb2f346e7e1661b966f48dcb92d4d988c0d421725838e1581a472e4b071cb30348e88162bb966068dcbe2c1c824e59241725838e5981a472e6b0a5cb30346e5c96964e16065c8122d4d97314d1b89b5 else 0x1071c6b0346e5f16a6cc4606940bfad4c88ce7d419725838e5983a472e4b53661b034a27cd6354465e68dc702c1c72cc0d1b980585ee5981a372e4b0a5cb3034fa5c9614bb772c8dcb92c978a68dc7009b5886e5965a37378b5362a41146e781614b965ee8dcb92d4ca59380b909b58a8e5981a372a2b5366230646e5c96a6cc46069b8b92d4ca273a47009b5a9b071bd2373eeb071cb3034d65c96233966068dcd9ad4d97cc0d281725986e5981a672e4b5322339f5085c9614b96606984b92d4d8a70151b8e05a9b30d81a372e6b24e2a41146e3816a6d278a66f0702d4c988e0d0189b5
def htChunk_10 (_ : Nat) : Nat := 0xc26d209789a6966b5687f7bc81bd1b7fa4225f65265d5320594a875797a156e39054189a3ce6b533ac2f2f883f2eb697257c111b3c4d1110e50f73930e89c50e7af504e0e4
def stChunk_10 (_ : Nat) : Nat := 0x41c72cc0d359725a9b4b260b032e426d80041c712c0d1b97c50010a5c430346e5c940042972cc0d1b97258a8f99cb2371c026d8004c372cc0d1b9725001071cb30348e5f140041c72cbd1239725001071cb30346e5fd40054c88ce591b9b350010a5cb30348e5c940041c72cc0d1a97c50010a5cb30346a5c940042672cc0d1b9725838ee5cb30346e5f1a14bb972cc0d1b9726001071cb30348e5c940041c72cc0d1b9f65001071cb30346e5e540042972cbf51b9725001071cb3034a05c940054ca59370b909b5
def htChunk_11 (b : Nat) : Nat := if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0x97d7a097af00964a509215709212209205f09176f0916a7090f0609029008f22508e88508e77e08ceac08c10508b82b089de60894e60878ae0864d008506c084e4208490b08455a083fe908250c08198f0809b90805e007f54907c59507a92307a2d9078eeb0770b7073cd707207206fe2706eb2f06d91a06d19e06ceda06c3ab06a3580694bb0679130660860656c1065022064c4406405506378e061dce05ee2f05eb4605e6ef05e62d05ab2905a54d05986c05947b05885705583b05506205438b0542a6052e3f051232050d8e04e0e404e05904c3d0049e690494ed0494a8048789047da20473d60431a304047903ee3703e52d03ddbe03c55c039f28039d68039c1e038d600387b9036843035733034f8a034ce803487803456e03432b0339b70317e003060102a6d2029c92029ab8029aad0283a40266340264a8025ad10221e80200a901fa1201dbdf01b50801b18601893b01634301444b01402f01136200d8f000c9eb00a9f5009ca000943300902800663900519400494b0042a7 else if Nat.blt b 2 then 0x1499d01475ea1474a0146ce114693414472d1445461427b31422521418e71411bd140a3613f5f013c88213b89e13675d132099130ed5130ac512fb7412fab912f92612e40312c05212b72f12b57612b53b129d46129b30128d77127e401277d612734f126fc3126bb01263221228a41209321208c211caae11b6b011ab471177d711741c114c8d113b50112dc01115f310ef3d10e07c10d27b10c47310bc3510b13e1060261056c110498410492f102d851014580ff8540fe8860fddde0faede0f8aa80f86ff0f67880f4bb90f4b260f1c290f133e0eda410ebfaa0eb0e30e80e90e7af50e6cc70e51b20e43790e3b3a0dcb9d0db0f80dae370d8c740d83990d7ebb0d436f0d3ec50d348a0d1df70d09ac0d03b80cfd8e0cf0f70cb29b0c8a670c7f5c0c63c20c40870c20880c0f060c0d670c04df0bf3730bf07f0bd1970b7b3d0b76cd0b63c60b5be70b3e610b3b2f0b1a5b0afbe10aebee0acab10aca430a80870a73b60a69cb0a25580a047109f88609ef2a09eb6509db5709d12509cb80 else 0x2036e12000471fff891fd6981f912b1f7da21f6cca1f3ed11f3b7d1f289f1f1fed1f1ba51f136a1f04b61f04281f02d51efc071ef3971e57cb1e56d61e3bf71e24381e1a3e1e038b1e02031df50e1df1aa1df0e11debd81ddf571d76841d5e2a1d3aaf1d22a91d1fcc1cff5b1cd25d1c80a61c80821c5e191c5dbd1c5ad01bfad81bf76e1befc11bee551bdebe1bc7521bbaf91bb3cf1bb3ae1badd51ba8a71b9ee51b9bcb1b9b4e1b7e6f1b78e21b3c4d1acd5d1ab7ec1ab6ac1ab25c1aaea21a6f0f1a68b51a5be21a40131a3c3f1a36521a28b01a0af819e6e719dde9199e1919991c19698a1953d71932681912bf190af218f4d218ec6518d90018ace01864ee1856af181ea9181e3017ffb917d3ea178be2175ec31752271749a417317a172ed6172e4b1727af16f47a16ce1416cc9f16c6fa16c5c116af5416aad1169534164ecb1641fc1635921629e716191c160f0c16044b15f74615f41815ed211572ce1564d51547ed1534261500aa14fd6d14e96914d8a514cb7f14ad9714a502) else if Nat.blt b 4 then 0x2c86b52c793b2c72272c39532c31742c27872c1f5b2bf7f92bd82f2bce772bcda42bcbb72b8dce2b8ca52b551b2b4aff2b465e2b2f432aa0af2a8fd72a808b2a80752a6bfc2a5aec2a2f6c2a21422a1e612a1b542a097229cfcb29c98429c7a829bb7829b32d29a9e42951de295199293a4f291f71291b01290f3228e6d828dc4e28d14f28ba23288b9f28874928759c28562b284fd928470c2838f028072b27ff3527fc2527cd2a27cd0e278a9427870c27809b277954277603271b1c270ea226f8c626f6e726f07b26dec626d13526cede26b5362691dc2665c12664e72643e82622a0261ebc261722257c11256146254502253ee7253c4f25179b2513c1250e3324d92824cbc924c11424bf5e24498b243c7d242bc924119423d59d23c39023bd2a238cd4238ae223896a234e1a2338132336d422f48322efb222c69422b3c622b0e722a791229da922930b225ca122521f220a8521d1802196aa212e54210e7021042420d97520d41220b9d720b50320b00e209e5520744e205ef620495a else if Nat.blt b 5 then 0x3a97b63a94003a90083a8db43a82473a4b463a1d873a0fee3a0a8039ed0039419e39078d38bf35385fd1382e93382726380bc337e72e37c97637c48e37a6303792e13733973729ad37217a36fd2136e9a536c5d536b28136b07436972a36099735f75d35e3a235dec7356536353a17351f2034fd0034e7ac34cd4634c60a345fce3437183407a833efd933e63c33dc1533d09d33c68f33aa93338da7338939336e7d33663a3332ce3331d83327303314023302c832e02f32b7bf326fac3262993262053243203227763208ce31ff3931f7de31be50319b7f315d9e3148c931316630ec0930e75930cbf630c49930c46b309dc73087683078cf3073673054f73037cf3034593031892ffe7a2fefee2fd0612fbf5c2fb7712fabe12fa87e2fa2c52f9f6d2f818d2f71502f271b2f1c882f1b972f05da2ed4ae2eb6972e93962e52462e46022e42bf2e17632e12c42e0d042e0af92dfb2b2ddd632dd1a42dc58e2db5e42da3022d55dc2d55882d2fd02d099d2ce7a12ce1242c8bc12c8ba52c876e else 0x47429f473686472dea4722424712a5469bff4690e64671ba465b0c465b0846469b46311845f6b845db3945c80a45bff945a43a4575124563f0450a4144f8344474c84464494454f24451594433b1441e10441ba844177c4407ae44018f43fe3e43db2943d8ef43cf19439d7d43821d43803243470d4336ad42efc242c86d4236cc422d2e41e21241d9c341ccff41be5141b77d418bd8417086416e7c4132fd412c7a411087410a8e4103fc40ff1440fc5940fb9040dbb940a04640986b4074a34067b34058ce403a02402e1f40180d3ff55a3fbf033f76683f67613f5be73f26413eff013ee9363ec1e93ea8773e6ecf3e6c3a3e1ef63e079e3dc01b3daf413da7b93da71d3da37d3d88fc3d831c3d79883d78723d70e23d2fb03d2ce23d2b803cdb5a3cd2c33cd15b3cc82d3cc3bf3cc0aa3cb3bc3ca0c03c8f413c8e183c89e23c797d3c75313c4f0f3c475a3c3f793c21173c13e83c0d633bd1173b948f3b42033b34e13b30f53b1c7b3af9b93af1cf3ad6cc3ac8373ac52c3ac3bb3aa315) else if Nat.blt b 9 then (if Nat.blt b 7 then 0x56bf8256b325569cd7569b67567ac25675ab567386566d1e5663b156599456234156225556109256098355f72855e75655b3bd55742855467e55466a552ea25522fc550a1f54d84e54c4aa54a60754262954189a5415e453e6ef53c16e53a879539749535f89533e9d533c02531c6053019052cf2752b29452a1525298ee526c44526002525cd1524937522b8152217751e94651cbfb51b945516b2a5156465145fa5132fc50fb0c50e5a550b0b9509552507d25507618505983505820503f09503d9a503ad54fd2684fcf3c4f8a454f4dca4f26c24f06904ef5884e92a44e4c834e0d1c4de07c4dd9bc4db5c44db1d54d90a84d87cb4d6b384d4cfa4d3f404d19944d12334d0a0c4d04994cca484cc89e4ca56f4c44c04c22784bbea04baf484ba95a4b4d1c4b45644b3b634b31c24b135c4b0a724ab7b54a99c84a99384a86aa4a7abe4a60bd4a37c54a200249f99249b1a749a6bb4999de4999db493bf149257c49239c490eb148bf3348ae7148a1e74806cc48050247ff2847833a476f48 else if Nat.blt b 8 then 0x69cc3969cac76980f8695ec7691bb268ffdf68f43d68b966689ee1685f02685cad6859d568346867f8f867c5cd67967a6789b6676b8f6764de67201e66d074669ca3667540663ff06616c666169c65bd7865a4e1657ac565266b65072465036c64e93c64c68b642d46641dc763dd4c63c5f9637cfc636ae96358f562f7a162c83b626a3e623f5c6236336234fc6230af62298662217462183b620d2262048061f23461b6f1619b2e6180a561583d614c216133746128ac61028260c1e760ac5060844c607ba0606f886036a96007fd5fd3a65fa45d5f8da25f65265f519b5f3d0a5f03f35ed10c5ecadb5eb42d5e73e85e68ec5e63a45e037a5da5025d5be35d595b5d53205d51555cdc405cdc165ccee05c80155c46a05c2c365c1ee05be8255be17b5b7d935b1c7d5b17405b0a5e5b06565adbd75ac5f85ac1a95aa7cd5aa6d25a948e5a859f5a42fb59ea8559c9a759ba17594099593263592f5558fa3b584116581b1e58131a57edf25797a157897e577ec7574f9f57177d56e39056c65d else 0x7cad617c88d17c74a77c66d07c5b6b7c4f3d7c39eb7c34797c164b7c0e117bf0d77be0fa7b7e3b7b338a7af1327acf887a9f6b7a86a27a83577a7a4a7a5e277a56527a52867a51d07a48597a227e7a17a07a04b879e6b779c63979c2d679833e7966fe79656d791ff978fcdf78e2fb78dd2e78dc6c78b33b78b04a78573277f5ca77924e775f9777045776fb4376f21b76e4de76c9fd76500f7642507607cd75ed3675dd8b75bdb375678475546075484a74f4ca74cff974c8597481dc74780b743f9d74117c7403a873c9d3733aa67313d47309b172d0f3729cac72921872751872622672560172266c71da3f7159b3714b59713443712a927116907100607092e6706e91701825700ce86fed076fb97a6fafc66f78b86f402c6ef7496ee7b96ed77e6ed2f36ed0456e96346e45dc6e25696dde286dcd496dbec36da55e6d9aa96d3c0e6d2efc6ce2a26cd8196cb7826c8f6a6c78896c56a86c4ae66bc4a76b7c1d6b1a5d6ada4a6aab506aa4566a30c36a2cd06a253969e3fd69e17a69dade) else if Nat.blt b 11 then (if Nat.blt b 10 then 0x949ad1948831946a499465e2945141943df8943a24940293937de29370a392fa0992a1ba92a13f9246bc91fbe791c72c9188fe91217d90f60a90e9bb9088269063639053b2904cc48feba28fead48f77b48f29788ecdcb8e6f028e5a9b8e51748e28ee8db56b8db1938d80178d499e8d2bd98d151f8d140c8d13c48d125c8cd0e98ccf068c5ed98bd0a68ba1ed8b9df68b9a3e8b4c468b172d8ad0278ac0238aa5ae8a87638a561a8a0ab589fb6789d82989bb3689bb2f89a9c688b512886cfe88293387b92187ab3f876aba8727f7872141870d2986e67f86a36e852bea85231e847b03846f4c846746843fee84325e8356cc833fd483242083076e82fdb682c77d827ff782621d8249898247cf8214fa81bd1b81a7ac8199cd818353814d0d814abb811e928080b08019ea7ff3167fc4527fa4227f85b87f6c177f4c7d7f496f7f42527f39937f32807f31417f2fbb7f0f287f09797ef4057ea7cf7e56be7df6e27ddc6b7d920b7d86547d70af7d08597cefde7ce7e27cdfc47cd4287cb8d9 else 0xae19bfadb85fad8354ad27bface437acb820ac4a95ac3f84ac346dabe254ab15c7aaecdbaaaebbaa97cbaa84abaa51e2aa3352a9bf37a936d9a90ac9a8c429a8be78a896f4a81e53a8124ea7b3cba76c9fa76998a7556ca72e01a71a60a6d7a6a6b884a69274a60b49a5e940a59f35a57622a555c6a5480aa52945a5244ea4ed08a4de71a4c925a4b854a431a4a4244ba403eaa3ec8ca344b8a30c74a3068ba29325a2602da25d1ca24ddea20b32a20455a1f6e6a14eb8a123e3a07455a0591ba0252da020a69f65a99f614d9f56ca9f38469f2c109eb3ab9ea46d9e80e69e22ad9e135e9dfd049deda89d9d059d50949d2ee09cf51b9cf10f9cd3339c16329bfff79bf7a59bb34d9b4e149b4d979ab8e79a28f49a1bd29a106199fd7799b2ba9992f0997fb2994d2c99209e99016e9900bc98f1ec98dac59884959846f39839f59836db97dae297cde397bff697af7b9797cc9789a697107f97085796d37d968a32964e539641e7960c3095dc91955a219500b894f35894e92e94e31594bbaf) else if Nat.blt b 12 then 0xd3c700d3754cd30321d2ec98d26709d25d72d22aced2167dd148a8d031e7d02da1cff009cfa240cf4fe0ce2f6ece20b2cd4533cd44e8cd086bcce56ccc2cc0cbaa9bcb6127cb51c4cb0861cae5f0ca9737ca7f0eca709bca29b4c9a5d9c94af9c91adfc8f98cc8ef5dc8d539c8af25c7f7ecc7f642c7dd5bc6f612c55261c509f0c4ff5bc418fbc39f7dc397d8c38786c363cdc2efd9c29feac29783c2891bc26d20c18dd0c16f93c0c7b3c0c099c09615c091dfc05049c00bb0bff908bf8782bf7fbbbef85dbec434be7de7be08eebde173bd4954bd3ff8bd268cbd2327bd0a9cbcdc08bcdb54bc7d76bba3cabb695cbb1c16bb052fbaadd7ba5349b94aa5b93ad7b90ba4b8cb42b8b9dab8ab26b7a8beb79e90b6dec1b6625cb65993b5c56cb54cecb54576b523c7b4c1fab3e838b332e3b3183cb29da4b294feb25ae0b255f7b25484b1e303b1c46ab19d66b18f9db169f4b14c9db1335cb10beeb0edaeb0441ab03883b00b08aff06dafeb3dafc07baf7534af7423af5260ae2ca4ae2531 else 0xfed5d3fb017bfaf265f825b6f809c5f7ada5f5586ff34a1def35e0ee09e5edbd76ebc93beb7a10ea9a0ce7bc69e7119ae607a7e58851e53ab8e4cb82e32e2fe1ce02e0d720e0c1d1dcf3b5daf8d9dab00eda85cfda7f60da3ccad9ebbfd98c3ad8e693d8833ed838f3d6e92ad685afd6057bd54a92d4642ad45c28
def stChunk_11 (b : Nat) : Nat := if Nat.blt b 25 then (if Nat.blt b 12 then (if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0xa99311952372e428da0e3966068dcd68246a990a5cb2372e425da3f41c60691cb90e06a9b169f4a371c026daa64dc8388dcb909b6838d5581a472e4381aa6cbe58a944b909b6a99311c1a672e426daa648c87e8dcde0e06a990a5cb2502e426daa651b988a7d1b9726a9b0a55d2372e4431aa641c72a8dcfb89b6a9b07181a47338381a0e3966068dcf70246852e5981a9746e5c9aa641c692a29338e06838e5981a372e4151a0e3285748dcbe10c6a9b0fd81a372f8381aa652c9e65c87009b6a9b10d812372e4381aa6c5e8528dcb90e06a9b3115d23f2e426daa642972c8dcbe10c6a992161fa37378381aa6531838e59099726a9b53223267390381aa6c2260691cb90e0697ce59b32512e426daa6cc4606940b909b6 else if Nat.blt b 2 then 0x838e5965a373f06f1aa6c538168dc7009b6838e5981a6b2e417daa6c547c28f07009b6838e5981a832e426d80054ca59370b909b5a9b161f0a371c026daa6cc4606940b902e6a9b07181a372f83bdaa6c1c6f499cfc09b6a990719828a39e381aa64c4742e591b9726a9b53214a3735c431a8dbd156e8dc7009b6a9b5326223f3dc26da89d0172c5c87009b6a9b2f958a512e426daa64dd838945099726838e5981a8a4ce7e1aa641c7b45c8890e06a9b5322a28a326381a0e3966069f4b90246a9b5326223734e5cdaa6c1c606924b90e06a9b07181a6b2f8381a0e3b772c8dcb90246a9b532961fc2e426da0e3166068dcbe0e06a990a5e939646e26daa6d4ca627e4b90a36a99396623962e426daa64c472c8dcb910b6 else 0x838e7181a372e417daa6c46818c0d1b8e06a9b53214a7d2e4431aa641c718940b909b6a99071cb2512e442daa6c1c6008dcb90e06a9b53214a3735a431aa642972cd311b9726838e5981a372e40c9aa6c466069f4d68e06a99071c1a372f826daa6c296068f0b90e06838e5981a472e4041a0e396606a0cb90826a992f9cb2372f826da0e3186068dcbe0e06a990a5cb23734e5c9a31c0b6aa8dc7009b6a9b53214a372e4411aa641c72ca0cd989b6838e5973a372e417daa6d4c9888dcb90a36a994b26e41c2e426daa6cc482c8dcd51726a992f98aa512e426daa6cc46cc8fcb909b6a9b5322023741e381a61b966068dcb90cc6a9b5326223f35a26daa6d4c8528dcf710c68a6e5981a372e4091aa644672c8dd039726) else if Nat.blt b 4 then 0xa99151cb23734e095a14b9672cc0d1b9726a99071cb2472e428da29b5546e5c87009b6a9b5321fa914b4381aa652c9c25c84d8186a99119cb2373665c9aa6c5d8388dcb90e06838e7d81a372e4091aa6cc460e8dcb902e6a9b18e2340b46e381aa652c90f1f87009b6a994b23f1bc1c0155a14b966068dcb90c168a8f858ca371c026daa645472c8f0d38e06a9b5322327d4245c9aa6cc455c8dcb90a36a9b15207a3734e381aa641c742e59289726a9b5320e2673e2431aa6d4c88c8dcfe9ad6838e5981a373e6381aa6cc3606a391b9726838e5981a372f80a5aa6c1c60691cb40e06a9b0718023729e381aa6d4c97c91cb910c6a9b14dbe2373f026daa641c72c8dcbe1366a9b532622682b226daa641c72c8dd0a89b6 else if Nat.blt b 5 then 0xa9b5320e2914b43bdaa6d0d8a8f847009b6a99071cb2372f825daa6d4c88c9f4bb0e06a9b5325f25140626da14b286068dcb910c6a9b11973a3735a401aa6cc45d68dcb90a36a99071cb2514265c9a623836068dcb909b6886e5981a372e426daa6d4c87e8dcde8e06a994b2623964265c9aa6cc45908fcb909b6a9b5322325035a381aa6c1c5748dcbe10c6a9b5326223736828daa64c468c8dcb90a36a994b1cb22b2e426daa6d2c6067f4e09726838ca981a502e4381aa64da83899c9b0e06a99151cb23c3c026daa641c72091cb910c6a9b4a6623032e426daa6c5e8388dcbe0e068c6e5968a372e4091aa6d4ca587f4be09b688cd0981a372e4401aa6d4c8a88f0e08e06a9946e72bd11c026da0e3966068dcbf9726 else 0xa99071cb23734e5f1a0e39660691cbe1726a9b18db9ae046e5c9a5f396606944b909b6a9b125b32373f026daa642972c91cb909b6838e59642373f06f1aa6c3f7f08dcde0e06a9b5326223f40826daa641c72ca293385f6a99071c12512e426d80041c72cc0d281725a9b30d81a373e6381a3a4547c28dc7009b6a99376622372e428daa6d4c9948dcb90a36a9b532622392e428daa6c547c28dcd20e06a994b23f172216381aa6429746e59239726a994b26e9721c026daa6c1c606940b90e06a99119ec34246e381aa6c1c60691cba0e06a9b07581a472e4381aa6c3c6068dcb90e06a9b53214a3d2e4431aa6c547b88f07009b6a9b5320e2673f0419aa6c547c68dc7009b6a9b0a5642372e4431aa6c465ce9f4b91006) else if Nat.blt b 9 then (if Nat.blt b 7 then 0xa990a5cb25a2e426daa6d4c9888dcde05a6a991aa2a2371c0271aa6c298288dc700716a99119cb2372e4209a0e3966068dcbe0c16838e5981a373445c9aa6c547c28dcda8e06a9b071bd2372e4369aa6cc460e8fcb90a36a994b243c771c026daa64e18528dcb909b6a9b5325f2373ee26daa6c547dc8dcf289b6a99071cb2514404d9aa6c546068dcd50e06a9b532232373c06b5a0e396606944b91366a99119a4a372e4411aa641c72c938b909b6a99151cb23728225daa6cc47c88dcb989b6a992f98b2512e426daa6cc47c28dcb989b6838e5981a373f02b1a0e32860691cb90e06a994b23519c1c026daa64c48a8e591e09b6a9b4b17d9fd2e426da14b965da8dcb909b6a9b07181a3c2f8381a0e383606944b909b6 else if Nat.blt b 8 then 0xa9b5325f23b3f026daa6d4c8868dcde10c6a9b2f95a2512e426daa6d4c97c99cf589b6838ccd81a6b2e4381aa6c1c8148dcd38e06a994b26e1721c026daa6c586068dca08e06a9b5326244646e6b9aa6d2788cdcd819726a9b5326223f2e626daa6c547c28dcf01a76a9b532232372e43fdaa6c4d7f099c7009b6a9b5325f26d2e426daa64be630944b909b69af071d3a371c026daa64be71a944b909b6852f85cb2372e426daa6c1c5fc8dcde1046a9b532232372f8401a0e3396068dcde0fb6a99311ea17222426da14b96606ae91b9726a994f63b9721c026da0e39672cc0d1b97c6852e5981ad146e5c9aa6d4c88c8dcb91036a99071cb2372fe26daa6c2a6068dcb90e06838e5981a37440091aa651b838e8d239726 else 0xa991fa2a23c1c026daa6d4c8528dcd990c6a9b5322a24834e381aa64c46608dcb90a36838e31b32673f026daa64466848dcd68e06a99071d1b9648e5f1aa642972c8fcb909b6a99119cb2373f06b5aa6d37838c00b90e06a9b2ce24a371c026daa64c472c8dcb90a36a994b2711fe2e426daa652c91e848b909b6a9b532961c9382381aa6cc46068fcb90826a9b4b1fc1ad1c026daa6c296068dcb910c6a994b1c61fd2e426da0e38d6068dcb90246a9b071642372f8431a2a3e172c8f07009b6a9b151f725c1c026da0e3286068dcbe10c68a6ce581a37378381aa6d4c8868dcb910c6838e5981a472e455daa6d4c97e9b4b909b6a9b5322a23c388381a964e16067f4b909b6a9b31181a3f2e426daa6d4c9888dcbf8a36) else if Nat.blt b 10 then 0xa9b2fa5ba512e426daa64c372c8dcb909b6a9944de8a371c026daa6c1c60691cb90e06a9b07181a6b2e43edaa652c9bc5c87009b6a9b532622502e4431aa6c29606a0cb90e06a9944dc62512e426daa6c63852df11b9726a99071cb2472e4285a0e39660691cb906d6a9b5321fa373fa6f1aa641c718944f71066a991199627d2e4381aa6c548248dc700256838d99982671c026da0e3966f4944b91066a99071cb24744426daa64c3746e591b9726a991199623735a381a0e3966068dcfc1bc6a99071cb2472f826daa642972c8dccf09b6a591f9819fd2e426daa6d4c88c91cd68e06a990a5cb2373825c9a0e3966068dcfc0a06838e59802372e4381aa64466849f4b90e06a591f9611721c026daa6c466068dd091726 else if Nat.blt b 11 then 0xa99119a1a3735c381aa6c487e28dc7009b6a9b5322026720c381aa642962a8dcb910c6a99151cb24728226daa6d4c97c944f789b6a9b0a5be30348e5c9a2341c72cc0d281726a9b5326225b2e428daa6c547c28dc830e06838e5981aba46e5f1a0e3966f48dcb90cc6838e5981ad146e5f1aa6c467c28dcd68e06a9b532622402e426da0e3966068dcf989b6a991aa2a23c34e381aa6d2c5747f4b909b6a9b5326623f2e4209aa641c72c968be09b6a993118aa3f2e426da0e3966068dcb90796838e595d2372f8431aa6c54822f851b8e06a994c6964e12e426daa652c9b65c87009b6001071cb30348e5c960e38c6cc944b91066a9b4b2233033fa5c9aa6cbe606a29289726a9922a2323735a381aa64e18388dcbe09b6 else 0xa99119cb23741a5c9aa641c72c8fcbe09b6a9b071be30346e5fdaa641c7308dcb909b6a9b532962112e4431aa641c692a18de0e06a9b11a15b7c46e5c9aa6c1c6068dcbe10c6a9b532961fd3dc26da3545488cc0d1b8e06a9b072092372f8381a14b965ce8dcb909b6a9b30d81a373f05c9aa64c470661cb909b6a9b14e2341446e381aa64467188dcb91006a9b07180a372e4381aa641c72ca0cb910c6a9b53226a673fa26da0e3966068dcb906e6a99071cda3737817daa6d4c852a10b910c6a992322a23734e381a72cc472cadcb909b6a991fe2a237388381aa652c8f85c87009b6a9b18e05a371c026daa642972ca7d1b9726a9907199a8a4ce381a0e396606940b90e06a991aa2a23c3c026daa641c72c99cfc1066) else if Nat.blt b 18 then (if Nat.blt b 15 then (if Nat.blt b 13 then 0xa9b14df72371c026daa6c54822f711b8e06a990719828a2e4475a0e3b36068dcb90826838fe1c19721c026daa641c72c8dcde05f6a26e5981a8a2e4381a62446654c0d1b9726a99071cb23735a25daa6d4c88c8dce48e06a9b31181a373225c9aa6c1c6f0c011b9726a9b532622802e428daa6c296d28dcb909b6838e5181a372e4381a2339f5ce8dcb91006852e5981a372e4505aa6d4c87e8dcf01bc6a9b5326223f40626da1fb966068dcb90246986e4181a372e4381aa641c72c8dce097c6a610a5cb30346e5c9aa6429746ca11b9726a9b151fd2373fc26daa652c8fc5c8700a36a9b4b1b31fd2e426daa6d4ca58634b910c6a9b532961fd35a26daa6c1c60e8dcbf8e06a9b1197f2372e4411aa6cbe6068dcb902e6 else if Nat.blt b 14 then 0xa9b53226a673c026daa652c8f25c87009b6a993122339646e6b5aa652c9c2944b909b6a591f9fe1721c026daa6c1c6e6c0d239726a9b11df82371c026daa646a8a8f591b8e06a9b4b1641fd2e426da14b966068dcb910c6a9b31230a3738a5c9aa64c462c8fcb909b6a9b12a232374245c9aa6d4ca59118e48e06852ee5cb30346e5c9aa644372c8dcb910c6852e5981a372f8091aa6471838a29338e06a9b15203a7f1c026da14b9657a8dcb909b6a994b2791721c026da623966068fcb909b6a9b071802373f0381aa6c1c6f48dcf98e06838cc16425a378381aa6c465748dcb91006838e99cb2673f026daa6cd07c68dc7009b6a9b532652402e426daa6c1c6cc944f71066a9b5320e2513e6419a0e39660691cb91146 else 0x838e5981a8a2e43e5aa6c436068dcbe0e06a9b5322323735a401aa6c1c6068dcfa9bb6a99312352372e428daa652c9245c870046688d071cb30348e5c9aa6d4c87e91cde0e06a9b11976a37366381aa641c73e8dcb90976a9b4b1fd19c1c026daa64c471a8fcb909b6838e5981a372e4545a0e3a372cae9239726927151f0a371c026da354547c28f07009b6838e5973a372f826da0e3966068dcb902b6a9b532232373dc401aa641c7a28987009b688cecdb9b0346e5c9aa6c465ce8dcd68e06986e59b52372e426da2c41c72cc0d1b9726a9b30dbe30346e5c9a0e396606944b911a6a9b3120e30346e5fdaa64ed8385c89b1156a990a58b2372e4431aa64c488ce593e9726a9b532961fe3885c9aa644668a8dcd98e06) else if Nat.blt b 16 then 0x838e7181a373783edaa6d4c83891cde0ef6a9b5321fa5a378381a62396606a7d1b9726a994b1cb1872f826daa6c545608dcf009b6a9b07181a653ea26da6d41c72cc0d239726a9b071b4a372f826daa6cbe6f4944b909b6a9922a1fa37378381aa6c548248f07009b6a9b0a55a2372e4431a0e3966068dcbe1416a993aa4c9721c026da0e3966069ad1b9726838cc181a472e4381aa647188c8dcb91006838e5981a472e4381aa6c547f08dcd38e06a990a58c2372e4431aa6c63816dcd1b89b6a9b1515823734e381a2f41c72c8dcb90246a9b5322327d2e4401aa6d4c9868dcb910b6a9b53221a6746e431a0e39657491cb909b6a9b5325f2742e4419a0e38c606944b91066a9b532962043fa26daa64466c0d091b9726 else if Nat.blt b 17 then 0x838e5981a372f8431aa6d2c606848b909b6a9b119642372e4401aa6cc45d68dcd709b6838e59b32472e426daa6d4ca587f4b989b6a99071cb24735a26daa652c91e704b90e06838ee5cb30346e5f1aa6c465a28dcb40e068c702dcb2371c026daa651372c9987009b6a991c60e25c378381a0e3966068dcb903e6838cc181a5a378381aa644673e8dcb90836a991fa2323735a381aa6c4657a8dcd68e06a99071c19fd2e426daa6d4c996944b90816a9b5322327d338381aa6d4c84491cb910c6a99071cb2473dc26da0e3966068dcbe03f6a9b14db9a372e426daa65139da5c87009b6a9b0fdf0a37378381aa64c488ce7d1b9726a99119a4a862e4381aa652c9065c87009b69db07181972224091a0e396584a29289726 else 0xa9b5320e2672c4431aa6d4c9888fcf789b600153661b034a25c960e3966068dcb90976a9936a0e2512e44d9aa6c4d7c299c7009b6a9b5322a237414381aa6c1c5f08dcde0e06838e5981a502e426da2a3ee72c8dc7009b6a993b60e17222826daa6d4c8389acbe10c6a9b07205a371c02b1aa651b9ca7e0b909b6a9b5321fa3f378381aa6cc360691cb90e069db071cb30348e5c9a9647e606704b90e06927151ee2371c026daa6d378a65c87009b6a993118c29f46e5c9aa6d4c97c99cfc09b6838e5981a3c2e4091aa6cc496e8fcb909b6838e5981b0346e5f1aa6c3f5908dcde0ef6a9b5320e25a3783bdaa642972c8dcba09b6a9b4b1819fd2e426daa652c8fc5f07009b6838e5981a373e25c9aa6cc45848dcb90a36) else if Nat.blt b 21 then (if Nat.blt b 19 then 0xa9b532232373ca6b5aa6ccd7d28dc7009b6838e5981a502e40b9aa645472c8dca389b68d5151f2a371c026daa6d4c8a88dcfe9a76a99071cfa472e426daa6c1c6f48dcfc1bc6838e59642472e426da0e35546e5c8700ac6a9b3122330346e5fdaa6d4c97c944b91066a9b53214a3c2e4431aa6c2c6068dcb90e06a9b5325f4544e826daa6d4c8c88dcd18e06988c615a2372e626daa6c4680e8dd039726a9b071be2373f02b1aa6d27852c0cb90e06852e5981a372e413daa6d4c87ea451b8e06852e5981a373785c9aa641c72c8dcd98976a9b30e0e3034a25c9aa644672c8dce48e06a9b07181a513dc419aa6d4c88c8dcd69046a9b071b52373e6431a14b966068dcb90016a9b5322327f40e5c9aa644372c8dcde1726 else if Nat.blt b 20 then 0x988e595a23f2e426daa6d4c88c8dd041ad6a99119cb27d2e4401a1ec1c72cc0d1b9726a9b5321e2372e4431aa6d2c7be7f4b909b6838e5983a372e40b9aa64df97c944b909b6a99119cb23735a401aa6d4c88c8dcd99006a9b0fd81a373783bdaa6d4ca58704d68e06a9b5322a23c3be26da233965ce8dcd68e06a99071952502e4431aa6d4c88c8dcb99006a993121fb9646e6f1aa6cc460691cb90096852e5981a372e41f1aa64297368dcb909b6a9b31183a372e428da0e396606a291b9f36a993122339646e6cdaa6c548108dc7009b6838ce981a372f8381a354536068dc7009b6a9944e709fd2e426daa644372c8dcb907c6a994b18a9fd2e426daa64296968dcb90e06a99071c82512e4419a6244672cc0d1b9726 else 0xa9b532962033fa26daa643f72c968de0e06838e5981a472e40d9aa6d27838c0cbe0e06838e5981a372f813daa642972c8dcb909b6a9b151f728a46e381a0e3966068dcde17c6838e8dcb30348e5c9aa64be718944f709b6a9b07181a892e4381aa6c536f08dcb909b6988ca981a372e40b9aa652c9c25c84d8246a26e9d1b9721c026daa6c6382702d1b8e06a9b4fe623034a25c9aa6c1c6069acb90ef6a99071cb27a4a25c9aa6d4c9868dcf990c6a9b5326225d2e426daa652c8ff1507009b6a99071cda5a3783bdaa6429746e591b9726a9944dcb2372f826daa6cc46068dcd51726a9b4b1ffbf81c026da0e3966068dcb90316a9946e7a9721c026daa6d4c87e8dcde1006a9b152092373c069daa6d4c83891cba10c6) else if Nat.blt b 23 then (if Nat.blt b 22 then 0xa9b10d81a372e43edaa64ca87ee591b9bc6a9b15d81a372e4381a14b7c650c0d1b9726a58e59819fd2e426daa142972cc0d1b9726a990a5cb2262e426da0e41272c8dcb90246852e59572372e426daa6c1c6f8ae91b97c6a991fa1fa37378381aa6c465f08dcb90e06a9b15207a371c026daa652c91f118b90e06838e5981a472e41c5aa6d2c894848b909b6a99071cb24744026da0e39660691cb909b697ce31b32512e426daa6d4c8a88dcf01a76a9b53214a374285c9aa65139b499c7009b6a591f9819721c0119a3541c60691cb90e06838e5981a372e40cdaa641c72c91cb989b6a9b2f981a512e4091aa643f660968de0e06a9b07179a9146e381aa652c8d07f4b909b6a9b53261a372e428da0e3966068dcbe1726 else 0xa994b1c69fd2e426da0e330606a29338e06a990fdcb29146e381aa64546848dcd38e06a994b2409721c026daa645472c8dcfc1a76a9b07181a672e4369aa6d4c88c8dcd70e06a991199523735a381aa6d4c988a10b909b6a9b07181a373ee369aa641c72c99cfc1366a99071c6a472e426daa6c547c28dcfe89b6a9b5329b1fd2e426daa6d4c89a99ce20e06838e5962a472e426daa6cc3606944b90e06a591f95d1721c026daa643f72c8dcb90976a99071c2a472e426daa652c62c7f4b909b6a9b532962002e426daa6d4ca587f8b909b6838e5981a372f81f1aa641c7368dcbe09b6a99311c19f92e426daa641c70699cfc09b6a9938e4e9721c026daa6c4b7fe8dc7009b6a992f9cb2673f026da9647e88cc0cb90e06) else if Nat.blt b 24 then 0xa370a5cb30346e5c9aa6d4c9888fcb98a36853051cb30346e5c9aa643f72c8dcde02c6a9b5321fa373ca6f1aa64f488cd08b90e06a99071cb23744426da9647e6cc5c87009b6a994b23f1ad1c026daa6c29606940b90e06a99071c19c12e4381aa6c1c6068dcd990c6a9b07181a372e6331aa6d4c988a00d709b6a9b11a05b736068ddaa641c72c8dcbf8a36a9b5322323735a381aa6c547c28dc700976a9b53263a671c026daa6d4c87e8dce60e06a994b23f1ee1c026daa643f660a451b8e068a7051cb2371c026daa651372c9451009b69db071d32201c026daa652c6307f4b909b6a9b5321fa37378411aa641c660a28bc0e06a9b0a55d2372f8431a89b96606944b909b6838f45cb30346e091aa64d58a88f0f009b6 else 0xa9b07181a3742a381aa6d2c606a29091726838e59812372e425daa6d2c96e7f4b909b6a9b532684be4e826daa6c1c7d08dc7009b6a994b2421721c026daa6c1c8148dc7009b6a9b0a583a372e4381a62396606a6d1b9726a9b4fd81a374245c9aa6c547c28dcf009b6a9b2f981a372f8381aa6c1c606a0cd98e06a994b26ea512e426daa6d4c9888fcb910668d51515a2371c026da233736aac0d1b9726a9b5320e2502fe431a2340b72cc0d1b8e06a9b11975a3735c381a14b2860691cb90e0688ce5981a372e4401a14b9660699d1b9726a9b151f0a3734e381aa6c547d88dc7009b6838e59572372f826da6239660e8dcb90a36a9b532622372f828daa6cc460e8dcde9726a9922a2a23734e381aa6d4c852a0cb910c6) else if Nat.blt b 37 then (if Nat.blt b 31 then (if Nat.blt b 28 then (if Nat.blt b 26 then 0xa9910dcb2373f06f1a2a3e172c8dcfc09b6a9937e6223f2e426daa6c53828a291b8e06988e5981a372e40b9aa6d4c838a24b90ef6a9b2f9fc2512e426daa6c296068dcb90c56a9b4a20e0e01361c5aa64c37208dcb910c6a9b1195a2372e4401aa6d3fa58c0cfe9726a9b31181a372fe0b9aa6cc45de8dcb90a36a9b5322323740e6b5aa6d4c988908b989b6a9b15180237282381a0e39660699cb90cc6838c9181a472e4381aa6d4ca587f4f789b6a991198c2372e4401aa6c468008dcb91006a9b5320ea373783bda5f38c606944b909b6a9b0a5f12372e4431aa6d4c88c9f4b90e26a990fd94237378381aa6c1c6068dcfe97c6a9b5322323735a389a9647e5905c87009b6852e5957a372e426daa6d4c87e8dd041bc6 else if Nat.blt b 27 then 0xa99119cb23735c381aa6c1c6f8c0d1b97c6a990fd9828a4ce381aa6cc46068fcb90246a9b0a581a472e4381aa6c547c28dc860246a99071c199c1c026daa641c7a28dc8a89b6a9b11a05af346e381aa643f72ca29338e06a9b151ee2373c026da0e32860691cbe0e06a59201819721c026da0e39660699d1b97c6a991aa2a23c1c026da964e16065c87009b6852d0981a372e4381a14b966068dcfc1726a9b5329d9a732c381aa652c72c7f8b909b6a9b532622672e442daa6c1c606930b90e06a990a5cb2472f826daa641c736a29338ef6a9910da12372e4381aa6c547b88dcd38e068a8f91cb2373f026da8dc1c72cc0d1b97c6a993b6623832e426daa641c7188dcbf89b68a8f85a12371c026daa6c645e68dca08e06 else 0xa9b5321fa37378381a0e38c6f4944b91066a990719828a4ce3bdaa6c1c6068dcbf8e06a9b5322a23734e401a0e39660691d239726a9b0a581a5a2e4381aa641c7a29448909b6838e5981a372e458daa6d4ca587f4d21726838e3181a373f06f1a0e3966068dcfc02c68e31522330346e381aa6c608a88dc7009b6a99071cb28a4ce3bdaa6d4c88c8dcd98e06a9b5320e2372f842da9647e6065c87009b6a9b07209a371c01c5aa6c1c6068dcf017c6838d65802372e4381a14c1c72cc0d239726a9b30d81a512e426daa652c8fc5cc7009b6a9b07181a4e2e4381aa651b9cc5c87009b6a9b53214a672ae43180042972cc0d239725a9b31164a372e428da0e32a6068dcbf8e06a994b2479721c026da0e39656891cb909b6) else if Nat.blt b 29 then 0xa9b53221a9146e381aa652c988e590189b6a99071c62673f0419aa6c1c6cc8dcbf89b6a993aa4d1721c026daa6d2c7f07f4e09726a991fa2a23734e381aa6c296068fcb90e06a9b31181a372e442daa65139da5c88a89b6a9b07181a372e437daa651b52c91cb909b6852e59be30346e5c9aa6c547c28dce08e06838e5981a8a48e5c9aa6cc45748dcb90a36838e5981a372e4589aa641c746944b911a6838e5981a372e4185a0e39660691cb91586a9b071b9a372e42b1aa6c1c6068dcbe0c56a9b0a581a372f8431aa642972c8dcde0556a9911a0e39646e6cd80041c72cc0d1b97f5838ff4b91121c026da14b9656e8dcb909b6a99119a2a832e4381aa6d4c8868dcbe10c60015322339646e6cd6a6d4c88c8f0b91006 else if Nat.blt b 30 then 0x838e5981a8a4e85c9a0e3966068dcfc0456987071cb30346e5c9aa6c546068f0d38e06a591f9ef9721c026daa6d4c8a88dcd39046a994c2419721c026da623a77068dcb909b600130dcb30346e5c9698c1c72cc0d451726a9b4b1ef99c1c026daa6c295fc8dcb90e06a9b5321fa3740e6f1aa6cc46cc8dcb90a36a9b5326223735a28daa6d3b7c26587009b6a9b30d81a372e4381aa6c547c28dcdd8e06a591dd819721c026daa6c3f56a8dcde0e06a9b3115a23f2e428daa641c66099c830e06001071cb30348e5f16a6d4c9888dcf70a36852e5981a9a46e5c9aa64e5852e58b909b6a9b11981a3740e5c9aa6c638168dc700246a9b5326223735c28daa6c5480ac0d1b8e06a9b0a581a3733c381aa641c66299c830e06 else 0xa9b311fc23f2e426daa6c296068dcb91006a99071cb2472e4281a0e3966068dcd99726838e59642372e4209aa6d4c83899cdb0ef6852e5981a472e4381a0e3a7706944b909b6a9b2e62330346e5c9a14b9657491cb909b6a9b5322a2373ca69daa6c537de8dc7009b6a9b10d81a372e43bdaa651372c7f4b909b6a993b60e22026c381aa64668a88dc7009b6a994b2481721c026daa652c8d06707009b6a9b10d73a372e4381a6242972cc0d1b9726a9b14d802372e4381aa6c546068f0f009b6838ca581a373f06f1aa652c9c2814b909b6a991199da372e4381aa6c1c6dcc0d1b97c6a9b119b9b0346e5c9aa6d3060661cb90e06a9b10d81a6b2e4381aa645872c8dca109b6a9b07179a37378381a0e3b36068dcb90246) else if Nat.blt b 34 then (if Nat.blt b 32 then 0xa9944e76a512e426daa6d4c8848dcde0e06a99119cb2502e41f1a9fcc472cc0d1b9726a9b07157a373783bdaa644672cd811b9726a9922a2a44646e381aa653072c630b909b6a9b532232514225c9a0e38c60691cb90e06a9b0a581a37338381a9647e7f07f4b909b6a992f9a12512e426daa64436668dcb910c6a990fd98237378381a3f4547c28dc7009b6a994da3f1721c026daa6d4c9868dcfb89b6a9b5322a23741069daa643f72c8dcde0e06a9b5320e2512e8419aa64ae8385c88909b6852e59612372e426daa6c297f08dcb910c6838e5981a9a46e5f1aa64e5838e58be09b6a9b0fd57a37378381aa6d4c89a99cef89b688d071cb30346e5fdaa65139b4944b909b6a59385fc1fd2e426daa6d4ca587f4b91066 else if Nat.blt b 33 then 0xa99071c2a372e426daa6c538289847009b6a994b248c7e2e4381aa6d4c87ea1cde0e06a9b4b1819fd2e4091aa6c465e68dcb90e068d5151f0a373c026daa6cc46068dcb90a36a994b26e2372e426daa64e18388dcc009b6a9b11979a37378381a9fc1c72cc0d289726838e5981a372e4209aa6d4c98e944b909b6a993ae4c9721c026da0e39660691cbe0e06a9b151f0a5f1c026daa6c548148dcd38e06a9b0715ea372fe431aa651b706944b909b6a9b31183a372e626da0e3966069c5239726838e0d81a372e4091aa6c547f48f07009b6a9b53221a8a4ce381aa6d4c8a88f0ff09b6a99071caa502e426daa6cc36da8dcb909b6a59311cb3035145c9a2c41c72cc0d1b97c6a9910dcb2372e425daa641c650944b91066 else 0xa9944e709721c026da0e41272c8dcb902568ff151fd2371c026da9fd2c8fcc0cb90e06a9945dcb2472e426daa6d4c9888fcb90976a994b23f1ef1c026daa642972c8e0b909b6a9b311bda372e442daa6c538288dc700246a9b5322a23734e381a3f41c6068dcbe0e06838d5581a372f8381aa641c72c920d39726a9b07181a513e6331aa648f88c8dce48e06a9b53261a372e626daa6c548248dcf009b6a9b5325f25133a26daa6d4c838a28fc0ee6a9b5320e2373ee42daa6d4c83894509a036a9b4de0e2f3378381aa64466849f4d68e06a9b08981a372f8381aa64d7988e0d1b89b6a990714fa262e4381a0e3965848dcbe09b6a9b1520923734e381aa64e5988c60b909b6a9b5326223736628da0e3966068dcc397c6) else if Nat.blt b 35 then 0xa9b2f973a512e426daa6c546068dca38e06a99071cb2372f828daa644672c8dd069ad6a9935e0e3a146e381aa6c547c28dcf389b6a9930dcb2672e426daa64d58a88f07009b6838e5981a472e4449aa6d4c9888dcf790b6838e5965a3737817daa65138fc5c87009b6a994b248c772e4381a0e3966068dcb90286852e5981a472e426daa641c72a91cb909b6a9b532232672ae401a14b286068dcb90e06838e5981a372f8041aa644672c91cb907c6852e5981a372f85c9aa6d4c988a10b90a36a9b5325f25135e26daa6513746944b909b6a9b311fda3738a5c9aa651372c99cfc09b6a9b5322a23738c381aa649e66099c7009b6a9946e6d9721c026daa64c462a8dcb90a36a9b5322a2373c06a9a2a41c72cc0d239726 else if Nat.blt b 36 then 0x838e5981a472e4091aa641c72c8dcd685f6a9b071bc2f346e6f1aa6c296068dcb90f96a992fa402512e426daa64c4746a6d1b9726a99119a4a3735a381aa6d4c838944f790b6a994b23f1a42e4381aa6d4c8a88e4f009b6a9b31181a3f2e626daa641c746e59359726852e5981a372e455da38c547dc8dc7009b6a9b5326223740628daa641c64891cb910c6a9944dcb1c12e4381aa6d4c8a88dd039a76a99071cda8a4da5c9a0e3966068dcbf89b6838e5981a372f80b1a0e3a672c91cb909b6a9b5322a23934e381aa6c1c6f8c0d1b9b36a9b18a29c1446e381aa6d4c9891511b9aa6a990fdcb28a4a25c9aa641c72c9d0b91066a9b18d68a472e4381aa644672c8dcd989b6a99311c1a8a2e426daa6d4c97c940b909b6 else 0xa9b11973a7d35a381aa6d4c88c99cd58e06a9b53214a472e4431a14b966068dcb906d6a9b4b1fc1fd2e426daa641c65091cbe10c68a8f99cb2371c026daa64d58388dcbe09b6a994b2431721c026daa642968a8dcb910c6a9b0fdb32671c026daa64c462c8dcb90a36a9b3062330346e5c9aa6d4c8868dcde0e0688cd0981a7d2e4381aa6c547c28dc7009b6a9b14d81a9146e381aa6c4b7d28dc7009b6a99119cfa3741a5c9aa6d4c97c944ce09b6a992f9c62673f026daa64c46848fcb909b6a9b07181a373f0339aa64c472c8dcb98a36a9b311fda3733a26daa641c72c9acb909b6a9b071702372d0381aa6c1d6068dcbe0e06a9b5325f2742b426daa6c436068dcb910c6a9b07181a9146e3edaa6c1c6cc9d0f709b6) else if Nat.blt b 43 then (if Nat.blt b 40 then (if Nat.blt b 38 then 0xa990a5a1a372e4431aa652c8f05c87009b6a993562a2373c069da9641c72cc0d239726a9944dcb19c1c026daa6c547b88dc7009b6a9b151f0a391c026daa6c1c6cc944f709b6a9b0720730346e381aa6c1c606940b90c16a9946a719721c026daa6c4680e8dcd68e06a9b0a5f0a372e4431a233425ce8dcb910068d5151582371c026daa641c72c944b91066a9b3115a2372e428daa6d2c7f05d87009b6a9b5322327f35a381aa6d4c988a04b909b6a99071cb28a2e43d1a14c1c72cc0d1b9726a99071cfa372e417daa6d4c9888dcde8566a993118c2372e428da61b966068dcb909b6838d1581a3736638180042972cc0d1b9725a9b15223303478381aa6d4c9889b8b909b6a9b07181a472e6381aa6c295da8dcb910c6 else if Nat.blt b 39 then 0xa9946e72b5f2e426daa6d4c8a8970f289b6a9b2f981a513785c9aa651852c8dcb909b6a9b2f9b4a512e426daa6c1c6068dcf990c6a992f9942512e426da0e33960691cb90e06a9b2f9b32512e4419aa6d4c838968be10c6852d5d81a372e4381aa6c538288dc7d89b68d9151f22371c026daa6d4c9888f0b90a36838e5981a372e417daa64e59365c87009b6a9b5325f2513dc419aa6cc36f48dcb90e06838e5981a3737817da0e35466099c7009b6a994b23f17220c381aa6c466068dce48e06a9b532961fd382671aa6d4c986944b91066a9b5325f2512e826daa6c1c6068dcbe0e06a9b119bc2f346e5c9aa6d4c83891cbe10c6a99151cb2372a226daa652c91e7247009b6838e5981a472e4001aa6c296068dcb90ec6 else 0xa994b23e9721c026daa652c9c27f4ce09b6a9b5326223f33826da6ac547c28dcf009b6a9b0fd81a5a378381aa6c1c6d4944f989b6a994b23f9721c026da9647e6065c8700246a9b07181a372fc381aa6c1c6cc99c7b09b6a9b53214a373783bdaa6d4c87e8dd001bc6a99119cb25146e6b5aa6d4ca59150e20e06a9b0fd6429146e381a14b306068dcb90e06a9b11981a3735a401a14b966068dcb90e06a992fa35a512e426daa6c5488d0491b8e06a58e59819872e4091a113966068dcb90246a58fe1cb1fd2e426daa65318fc5c86289b6a9b5320e2673f042da2a3e472c8dc7009b6a9b0a581a372fe381aa6cc45ce8fcb909b683902dcb30346e091aa65187068dcb909b6838fe1cb2472e426daa6c535a28dcde0e06) else if Nat.blt b 41 then 0xa9b12a23237392381aa6c465748dcd68e06a99119cfa7d2e4401a0e3966069c51b9726a994b1c19fd2e426daa652c6847f4b909b6a99071cb23730026da2341c72cc0d1b97c6838e5981a472e40a5a0e3a372cae91b97c6a99071cb2472e44d9a0e3966068dcb40246a994b23f1fd33826daa64c488cd0d1b9726a9b135fd2671c026daa6c1c606968de0ef6988f45cb2b746e26daa6d2c982c0cb909b6a990bdcb2372e426daa641c70691cb909b6a9b071642373783edaa6c1c6e6c0d1b97c6852e5981a372e4111a0e396606a29100e06a990a5cb27d2e426daa644672c8dd089726a9b0716429146e3bdaa6ccc838c0d1b97f6a9b07181a37366401aa651372c8acb909b6a9b07181a472e43bdaa6d4c83899d099f86 else if Nat.blt b 42 then 0xa9b07181a373783eda0e3966068dcc11726a9b5320e2372fe419aa64dd97c944b909b6a99151cb237388381aa6d4c988a0cb90a36a9b5326223738c5c9aa65136be8dcb909b6a9944e779721c026daa6c466cc8dcd68e06a9944dcb2512e44d9a61b96606a291b9726a994b23f3d92e4381aa641c53e944b91126a03071cb2661c026da0e3966068dcba0246a9b53261a513e626daa64e5988f45cb09b6a9944dc1a512e426da0e396606a29269726a9b2f981a512e4419a0e35546e5a07009b6a9b5322a44646e81da6d41c72cc0d1b97c6852e59642372e426daa6c3f606a451b8e06838e5965a372f826daa6c295e68dcb90e06a99071cb2472f8431aa64c453e8dcb91126a9b0a5812372e4381aa6cbe55c944b909b6 else 0xa9931235a3f2e426da623185688fcb909b6852e5981a372e4209aa6c548248dc7009b6a9b15181a373c069daa65139b65c87009b6838e6d81a372e4091aa6c1c6068dcfb8e06852e5981a372e41c5aa6c536068dcfa89b6a990a5cb23744026daa643f7188dcde0e06a9b5326223738a5c9aa641c73e8dcbe09b6a9b1196423735a381a354296068dcb90e06a990a5cb2372e626daa64466588dcb91006a9b151f42371c026daa141c67299c7009b6838e5979a373f026da354547c28dc7009b6a9b14d81a37378381a964e17f05c87009b6838e5981a472e4305aa644668a8dcb910069891198c30346e5c9aa6d4ca587f4ce89b6a9b4b1fc17220026daa6d4c8528dcba10c6a9b5322325135a305a76c1c72cc0d1b97c6) else if Nat.blt b 46 then (if Nat.blt b 44 then 0x838d551b9bc1c01c5aa6d4c838a28bc0ef6a9b11981a3735a381aa652c9007f4b909b6a9b071b32673d626daa6c638168dcde0e06838e8dcb30346e5f1a0e396606ae9239726838e5981ad148e5c9aa6c1c82891c700716a9b11981a3735c381aa652c9c27e0b909b6a99071cb29f4a05c9aa6d4c99299c7009b68d5151ee2371c026da0e3966068dcb90246a9b4b1739fd2e426daa6cc47c88dcd51726a9b5322a237354381aa64546928dcd38e06a99311cb2502e426daa6c548228dca08e06a99071cb2482e426da41c296068dcb90e06a992f9982512e426daa642970a8dcb909b6a992f9cb2512e426daa6d4c87e8dcde0ea6a9b5322a2373c028daa6c467c28dcb91006a9b532622502fe26da29c146728dc7009b6 else if Nat.blt b 45 then 0xa9b0fd64237378381a963f872c6707009b6a993766223f2e426daa644673e8dcd68e06a99071cb2373e626daa642968c8dcb910c6a993a20e3832e426daa644672c8dcbf87c6a9b53265a3735a381a2a3e16488dc7009b6838d1581a832e4381aa6c547c28dc700a36a9b4b2251c91c026daa641c7448dcb90976a99071c6a372f826daa6d4c87e944de0c16a994b1a11c12e4381aa6d4ca58714ce8e06852e5981a373185c9aa6c1c6da8dcfb89b6a9b07181a37366381aa652c8fc704ce0e06a9b532964c433a26daa6d4c87e9f4de0e06a9930dc82512e426daa6d2c7f66747009b6a9b4b22f1fd2e426daa6cc455c8fcb909b6a9b532961fd33826daa6d4c88c8dd091726a994b1cb2112e426daa6d4c8528dcb910c6 else 0xa9b0a60730346e381aa644662c8dcd68e06838e5981a472f8091aa6d2c6067f4de1726a9b311fc2372e428daa652c6507f4b909b6a9b5322a23c348381aa643f72c8dcbe09b6838c9181a372f8381aa6c2955e8dcb910c6a9b071b7a673f026daa6d4c8a8908d50e06a9b5321fa8a4ce3bdaa652c900714b90e068530a5cb30346e5c9aa652c989200b909b6a59201fd9721c026daa6d4ca6c800b909b6838e4181a373e6381aa6d4c8a88dcf009c6a991fa232372e4401aa6c4657a8dcb91006a99071cb2832e4155aa6d4ca586f0c90e06a9910dcb26746e26daa6c1c5908dcde0ef6a9b07181a742e4331aa6c468168dc700716a9b071bd2372f8381aa6c1c6068dcbe8e06a9b532961a7338381a2a3e16928dc7009b6) else if Nat.blt b 48 then (if Nat.blt b 47 then 0x9ab151f0a371c026daa6cbe6f4944b91066a99071cb2372f8249a0e396606a5d1b9726a9b071b32673f026daa641c746a29100e06a9b07181a512e4369aa6d4ca58704ce0e06a9b5320e26720c3bdaa6c547c28dc7009c6a9b532962142e40c9aa6d4c87299c7009b6a9b31181a372e4369a233965ce8dcb91006a9b5321fa6720c381aa652c9e6848b909b6838e595a2372f826daa644372c8dcde05f6a9b5325f2372fe26daa6d4c85291cbe10c6a9b5320e2513783b580041c72cc0d359725a994b2623963825c9a0e39660691cb90cc6a9b151eea371c026daa6cbe584944b909b6a9946d4ba372e426daa641c736968de0e06a99071cb237378545aa6c1c6068e0be0e06838e5981a764a25c9aa641c72c9acbe09b6 else 0xa9b2f229a371c026daa652c8d27f4b909b6838cc181a373783bdaa64ec9325c87009b6a9b5322c237284431a0e3966068dcde0ef6a9910d99a37378381aa6d4c992944b909b6838e5981a472e41f1aa64c48d48fcb909b6a994b26e9fd2e426da9647e5ce5c87009b6a9b53261a502e426daa644672c8dcb90836a99119952372e4401aa6c4d7be99c7009b6a9b5322a25134e305aa652c8f45c87009b6838e5981a472e413da0e39660691cde17268a8f85cb25146e26daa641c73e8dcd989b6a9944dcb2472e426daa6c546cc8dcd38e06a9b151fd237388381aa651b7a2a7d1b8e06a9b15202be146e381aa6d2c55c7f4b909b6a99071e939646e26daa641c72c8dcb90976838e5981a8a46e5f1aa6c465cc8dcb90e06) else if Nat.blt b 49 then 0x8a8f858aa371c026daa6c1c6e6c0d419726a991518b23734e381aa6c1c816c011b8e06a9b3115a2372e628daa6c5480e8dc7009b6a9b10d81a37378381aa6c4b7d48dc7009b6a9b1462330346e381aa6d4c88c8dd091c96a9b07181a512f8305a14b966068dcb90246a9b532232374105c9a14ba672c8dcb909b6a37071cb30348e5c9a0e3336068dcbe0e068a90a5cb30346e5c9aa65137a85c87009b6a9b3125c23f2e426daa6d4c88c8dd031726a9b532232372e4411aa642972c8dcb91066a9b0a581a372e43eda0e39655c91cb909b6a9b53221a3735a381aa652c72c7f4b909b6a9b11975a372e4401aa641c72c8a8b909b6a9b532622512e442daa652c65c7f4b909b6838e5981a372e451daa6c2957491cb910c6 else 0x2a6d4c9988dcb908369890d9cb30346e5c9aa6c1c60c8dcb90e06a9b5322c23734e381a14b285748dcb910c6a991c62a25c1c026da2a3fa72c8dc7009b6838e99cb25144026da14b966068dcb90006
def htChunk_12 (b : Nat) : Nat := if Nat.blt b 1 then 0xa29325a2602da0252d9576a7943a24938c7692ba3491217d9088358ba1ed8aacee89fb678721418356cc82c77d82498981bd1b7ff3167f2fbb7e99587d70af7cad617a5fe0782a1b76c9fd759cba7275186f78b86e25696dcd496d652b6d2efc6b7acc67cc55678490614c2160c1e75e68ec5c40f6590b61573617569b6755e75655742853c16e531c60522b81516ee54fec494e1c264e10d84c5c5f4c35d14a7abe48bf3346981f45a43a44f947442f684336ad4331a642fb4b423cbe418df9410a8e3fa1bc3e1ef63dc01b3d2b803d0f343cc0aa38080b37a630371e8c36099734731a32aff53022ad2fb7712e8c052d2fd02d2d432c680b2aa0af2a2f6c2a1b5429a9e42964f427ff352791fa258ba422c6941f7bd81ecf2b1e6a311df1aa1b3c4d1a68b51a40131864ee1856af17522716cc9f164ecb152fab14ad971411bd12a008129b301228a410492f1014ab0f1c290f1bec0eabe50e77590d8d8b0d83990d7ebb09bc4b075db406fe2705ee2f05123204576c03456e016343014b87 else 0xf12dbce7bc69e32e2fda3ccad9a6a5d838f3d3e5f9d0e871ca29b4c7dd5bc612b8b3e838b3ab51b0edaeb08c83af7423af5260aeaeddad8354aa51e2a936d9a5e940a4c925a39002
def stChunk_12 (b : Nat) : Nat := if Nat.blt b 2 then (if Nat.blt b 1 then 0x20e39660691cb92800a9930dcb2372e426d80054d838c0d239721c0c0020e3966068dcfc1bc60015320e39648e5f04db000a99119a127d2e438180054c88cd091b9ad1c0c002a64c472c8dcb90a360010a5cb30346e734b93000a9b31181a3f2e426d80054da993111f973136c002a641c72c8dcb908c60015320e39646e5fc4db000a99119cb2372e420980041c650c0d239721c0c002a6c1c6068dcfb0e0600153214b9648e5c84db0009f5071cb30348e5c980041c6068dcb911b1c0c002a6c1c6068dcbc8e0600153614afd46e5c8703000a994b26e9721c026d80054d838c0d281721c0c002a642972c8dcb90946001532964822e43804db000a9b071802372e438180054da993111b972146c002a6c547c28f07009b60015362a3e12663804db000a99396623962e426d80041c72cc0d1b9720a8c0020e39660691cb91286 else 0x1536a652c3fc5c84db000a9b5322a23734e37180041c72cc0d23972136c002a6d4c8a88dcf01a76001071cb30346e5f0b93000838e5981ade48e5c980054c852e591b972136c0020e3966068dd1417260015366230746e5c851b000838e597ea372e40918004c488ce5981a372e4c002a641c72c8dcb908f600153614b0346a5c8703000a9b532232342e440180054da58c0cfe972136c002a6c266068dcb90e0600153289ced2e43804db000947071cb30348e5c980041c72cc0d1b972046c0020e39660691cb90e06001536a64464fa5c8803000838e595d2472e426d80054da991191b9ad200c002a641c72c91cb809b6001536232e746e6b4703000838ee9cb30346e5f180041c64ec0d1b9721c0c002a6d4c88c8dce48e06001536232e546e5c870354c838f5dcb2372e4381c0041c72cc0d1b9cd2f8c002a6c638168dc7009b6) else if Nat.blt b 3 then 0x15360e30346e7d869b000852e5981a372e44a180054d838b051b9bc1c0c002a6c466e6c0d1b97260015360e2f346e6f0703000a9b30d81a372e438180041c72cc0d1a972048d5322a3cf72c8dc7009b70015360e30348c5c8703000a9b07181a372fe38180054da991191b9b31c0c0029647e6065c87009b60015329648f2e43804db000a9b0a581a472e438180054c8d51511e0e0136c002a641c7128dcbe09b6001535f0b0d46e3804db000852e5981a372e4491a0e3b972cc0d1b972048e002a6c547c28dc6e09b60015320e38846e5f04db000a9b151f0a373c026d80054d8a8f851b9a71c0c002a652c8f65c87009b6001536a644646e6b4703000838ef1cb30348e5c980054da98fd91b9ad1c0c002a6d4c88c8dcd70e06001536a630d46e69c703000a990a5c42372e426d80054c852e591b972114c002a6d4c9848dcb90a36 else if Nat.blt b 4 then 0x11aa2a3e146e3804db000a9b14d81a3737838180054d838c0d1b9bc1f6c002a6c1c6068dcb90d460015329647f2e43804db000a99071cb2372e422d80054d838c0d1b97c17ec00214b966068dcb90e06001536a652c3fa26c3bb000838e5981a372e417d800535838e5981a472e4c002a6c1c6068dcbe0e060015362a3dc46e3804db000a9b3115a2372e428d800429838e5981a372e4c002a64c46308dcb90a3600000214b966068dcb92800a9b4b1fc1fd2e426d80054d8a8f851b8e0136c002a6d4c9888fcb789b60015320e3964d65c84db000838e5981a472e409180054ca58c88fe972136c002a6c1c6068dcbe0c060010a59430346e5c87030009f50a5cb30346e5c980054da991511b9a71c0c002a6c548248dcd38e06001536232f346e5c8703000a9b31181a372e428d80054d838c0d239701c0c0020e3966068dcb90826 else 0x14d614b966068dcb93000a9b15203a371c026d80042972cc0d1b972048c002a6d4c88c8dcb91046838f99cb2372e43804db800a994b1cb1fd2e426d80054d852c0d1b9701c0c002a6c1c5fe8dcb90e060015320e39646e5c84bb000a9b532961c133838180054d850c0d1b9721c0c002a641c72c8dcf989b6001071cb30346e5c869b000a9b07181a3736638180041c710c0d1b972048c002a6d4ca587f4ce09b6001536a644646e848b93000838e5981a4739a5c980054d88cc0d1b9ad1c0c0020e3966068dcb90246001536a645446e6a8703000a9b152092371c026d80054da993111b9c52e4c00214b96606b791b9726
def htChunk_13 (b : Nat) : Nat := if Nat.blt b 13 then (if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0x52f460525f405219405123205033504f38304dad104da9004d74e04c9b204b3d9049c32048bd00484c80470d7046a59045f98045f60045c010454d6045428044fd0044dd404497c044751043b5f043205042dd80429c304290b04272b0425c3041240041154040f0903e31f03e1cd03dc4f03bef903bd0403a72f039be2038da0036d9c03456e034051033bb1033a70033a5303395c0335f0031178030b0b02f37802ee2602ea3902e82302e18402d5ef02bad502ac9c02a12e02a02c0280860275ea02759e0273f7024f5e024d800249f40246f102462e02403d023d4e022101021ebd021ba6020fec0209c70200a901dfcd01d2e501c5c701c35701c0b9019f3d0195630185210182b601780101779e01762c017188016343015ecd015e970157ef0146e401424e01416c0135ce0134a7010a500101ad00fa4700efbb00d48700cc4000bcaf00b8ce00af3c00a74d00a45f009d5c009cdc009c9f009a4c00958e00849c00778f006e8e00696e0067090050a4004fb700346d0033ab000f62 else if Nat.blt b 2 then 0x9b1260988a909865a09828709777c096be70950800937900935220921d1091d9a091a530915430910ab08fc4c08f5fd08f36108ed6708e40b08dd5408cf7b08a68808a5c20899c608968608947e088ba0088b5a0884850881400878cb0870c8086ec7086a0a0868a108686b086775085c240858fd0857750838b5082b0a081a5507ffe707f25207ef3507d6fa07d27207cd9f07c5df07c59507c56707ba2607b5ff07aff907a8fe079347077fad0760ef0756780744a60743af073a10073564073551071d1307180607102d070f7307065d07058906fe2706f89106f71f06e9fb06e2e506da3306cc4306c0b906ace906a1d006a152069bd606983006868f06755f066b870650ab06477106414c063d3606333706246c062438062331061c94061c7e0614450610d8060c53060a3b05ee9d05ee2f05dc1c05d63805d56405c8c005ae58059f61059cc7059881059368058eda058bc9058a39057cd9056ca20568c505646805644c0559790557e50553e8054d4c0548b5053b54053b1b053089 else 0xf921e0f85050f66880f4d4a0f4b5e0f37130f31810f1c290f181e0f13470f074b0f06d50eed620eec4c0eea7e0ee78b0ee72e0ed9e70ed4bf0ed24c0ea53b0e9d530e8e6e0e8dfb0e8dac0e8ac50e85180e62380e4f7f0e4ca30e4baa0e3f910e3bc60e1fef0e17040de8fa0de7590dd24a0db4f50db4a90d87850d83990d813d0d7ebb0d63910d4cc60d4aa30cfd8e0cf5d00cf56c0cecd50cebbc0cdf410cd8b50cd33f0ccf8a0ccbdd0cca410cca1a0cc7ba0c96db0c96b90c8fd80c8f070c85520c78660c75430c6cce0c6ba00c64e10c5d630c57070c555a0c2f600c24ac0c12420c12400c11310bf6e30bf19e0befd90bd5ea0bc9760bc7360bc2f60bbf910bbcbc0ba41b0b8c9d0b80b40b68630b550c0b4e640b4a2a0b444d0b3d6d0b3b2f0b18600b160a0b02510af9ad0af5220af4f10af4450ae7cf0acc8e0ac9b10ac5910ab9850aae040aa3af0aa2000a93fe0a8dd40a7f030a678c0a51370a36850a2dd70a0ec90a0a1f09f78109f3cb09ee4f09eda409e51d09cda309b363) else if Nat.blt b 4 then 0x1500c71500aa14ee1414e14b14d78614c5a714bda614ad9714a9e7149462148fc81455cc144e68144aef1443af1435f21432e41411bd140d1e14013313fe3113fbd013efee13ef6613ee6e13e3bb13d92213d15313c71a13bbe613b64713b11a13a789139f201399f8136b541348bf1344a5133db0133306132c42131ead130a1c13012b12f91a12e7c412dce912d58f12d2fd12c00c12b82f12ae3a12a9d0129b301294b112883b12855312839f12806c127d381268981266081228a4121ef9121c3a1215a2120e8b12085711f6bd11e61911dfeb11df4111dc3f11c4c111c41811b90111b190119ef6119bac1188d811793a117715116c6811674011650b1161b8112f0a112c6a1126d01125e4111db3111421110cf810f49110dc3010d33a10cac410c84510c7a510b5fc10ada310a263109b7c1098e8107b931077e2105a5e104c5f104a7e1049f910495210492f10268b10225d1020ea1012031010ee100dfd100dbc1008ad0fdb5b0fc8390fbffb0fbcc40fb7090fa3bf0f9e7d0f9645 else if Nat.blt b 5 then 0x1aed241acf561acb181ab9ae1ab63a1ab19b1ab09f1aa3091a9f911a968a1a930a1a85be1a79451a68b51a65821a552a1a53351a47601a47421a40131a3a4a1a13ff1a12961a0ee21a050819f9ac19e94519ab861974a0196da3196c7b19675b1957b11953fd194e03193ee7193017191cf518fcea18f32a18d0cb18bf8318a622189ce21871c0186e43186a7c1867e71864ee185c891856af1852ee185291185202184bee18350d182fd2181e4a17f89817f02617ed5017ed1917e8ba17d70117d6c317d66f17d26f17caa717b83717b3431768b4175a7517592d175800175227174bd717425f173af01734ce1728f117226f171fa4171ce4170ead16f8b516de8b16cd0e16cc9f16985a169525168fa8168d521684cc1662bf164ecb164718162d0e16275b160b0c160a1016044b15fd6f15fc0c15ef7615e29415d80415d7c215d2fd15d2ec15cb4f15ca4415c98715c53815b7f915b31a15ac5c15aa61159e2f15969815883e15762b1559f3155291151c1f150d11150b0b150a3c150378 else 0x20b3e620b0c2209e8c209a70208f3e208cc7208387207e5420729f205334205313203787202de32016d12012362007691ff6e11ff54c1fea6c1fe91d1fd73c1fca1a1fc4bf1facbb1fa1851fa09f1f9b6b1f654e1f60401f54e41f3ed11f3aa71f32c61f2d491f28361f21561f11a11f040d1efc0c1eddb11ecf2b1ead991ea9be1ea7cd1e98ef1e808b1e73ab1e6ed71e63dd1e5b361e58291e42e81e3a931e1f6b1e1d941e11181e029e1df75d1df1aa1de9871dbeec1db3321da8b81da5151d98d21d94031d8d991d87811d7bd51d70301d5a9c1d4c791d4aff1d45401d42eb1d3fdd1d10b11d084e1cf5511ce4b11cd8c11cba801cb5f61c98ff1c84d31c6f4d1c6e921c61f01c52151c43301c3eba1c37031c34ae1c2fd81c2c3b1c2a251c13771c11bc1bda411bd7721bd6231bbfd01bb7521bb5b71bad061b9df61b87db1b7f2f1b7c2a1b7bb11b76a61b73171b61df1b61551b5c0a1b5a491b49111b3c4d1b3a381b2b361b2a4d1b262d1b1a211b15041afe9e1afb341af4dc1af387) else if Nat.blt b 9 then (if Nat.blt b 7 then 0x26cf4726ce6226c2f826bfc626b9b726a2d6267fac2679c926710d26693c26602e2654a42651b8264c1d264b8d264b37262f432622c5261dec260cf8260bf5260baa25f5af25f44125c7ba25c45f25c32125c11c25b32d25b10225a6c92597cd25964c2588dd2568e32568ad255447254475253d992533f42528c82527cb252643250ae425069124f06424e78c24e35224d8e724d4f024a8f72499ba24989a248de4248b09247e4f24650c246256245e332448c82445ec244136243d042425cc2425bc241a432411f92405b424019c23dac123d92c23d78723d0f623bf73238c1d23818e237fbb23761f236a5a2365722364572362912361f323603c235afd234f2d234d56233813231d62230fe023091123014c23008022ec6422dabd22cd9522cbce22c69422a9cb22a84a22a5d522850b225cff2246b52246222240a7223d3e223bd9222a6f222247221abf220ec6220e9e21f37821e0da21dae321c130219c082194fc218d0621888221804a211bd62114152112bb20e14a20dc2f20b6d0 else if Nat.blt b 8 then 0x2c75d72c72582c72272c6d302c5cb32c43462c418f2c1a522c16082bece32be1992bd93d2bd59f2bbe8a2b98d32b8b342b7a5d2b77a22b73ae2b736f2b68842b65952b56632b482f2b39ce2b2c932b21e72b113b2b10772b0c292affd62af8682ad8892ad00f2ace902ac6e52ac32e2ac1672abb152ab6752ab4462ab4432aac352aa0af2a95702a90b92a906b2a8edf2a8a8d2a6dcc2a5fb82a5d792a4ec52a45952a3c5d2a350e2a2f6c2a22ce2a1fa42a1b542a19da2a18322a03b729eb4829ea3f29e0d029d40829b93129b87a29a9e429a475299f13299452298f1f298d07295eb229496b2944de291f1a2911fa290c2529099728f24428e99528e5c328d0d828bf3e28bed128b0f428a42d2874f5286cac283f9d283c3b28328b281918280f1927ff3527f46a27ec0027e2d027de7327d99427d15927ceb527c95027c84427c34527bde927bb1127b64527ace6279aef279a2a277eac2762102759f127539f27512d2747b6270fd226ffeb26f92426f42326f01d26edee26d2d226d0f0 else 0x326a00325c633257213254fa3247aa3240a53240233238623236943227a33221cc320fb732008231f83c31e16331d75531d6db31cd8c31cad531be17319655319589318d0431862d31824731777431665f31639a3163733160c631539e315035314d1e314231313e64310c94310bce310b5c31080a30fbd930d8da30c8b230c1d330bc4330bb3a3095643080523074d530730e306164305a3b3053903045d43042ab3037cf30354b302fad3026a330255b30057e3002212fff402ffdee2fe0372fd2792fd0e32fd0612fcccf2fb7712f7ff62f7b9a2f6de12f40de2f381f2f2e082f11892f02402f01882ee4e92ee0a32ed51c2ecd622ecb512ec3222eb6c72eac442ea3332e9b2f2e7e302e569d2e4d822e413c2e3a322e35822e28fb2e28492e204e2e1dd82e1d1e2e06dc2dc24c2db91e2da4092d8ca52d87c42d7c892d76492d71452d65b52d5c0e2d52012d3ec32d38892d2fd02d2aa52d12692ced342cddce2cd6862ccfe92cbf672cb93b2c9cb92c8e822c8ac12c79502c76492c7640) else if Nat.blt b 11 then (if Nat.blt b 10 then 0x38994d388e3938833638668838507c3831f5382911380fdc38051a37f4f037f36d37e45237e35337d6cd37b0f037a63037a107379dc03780f4376a58374b1a373d56373c35373a613738c43728323718933713f9370f8936d80f36cd3c36c16136c06b3696a73681ca367e823672f5366d863668dd36668f36375d36213b361b6c361240360cec36099736089b3605ac35e81a35e20735dd2c35c9e635c99b35c10735bde035b47335b33835ab6b35a5e4359e183585623576b13576663561b6355e8935511c35498335417a353c163539573536c235356e353286351c09350d5d350cbc350b4d35099334e28d34ddae34d68234d5ac34c56c34b5c134a64634a49034a22e34a0243478df346e1b346c553468fc345cf93459303457053456b534371834332a342a773412c7340aca3406c433f23a33e00e33d10c33b68f33b3d9337888336e7d33642b33620d3361e83358743344ed333d3f332bd8330a8b32fcd132e12932df0c32b061329df2329c75328cff3284f13280a7327dc4327b5b else 0x3eca7d3eca5b3ec4623e99123e8ea43e6b273e5f673e5cab3e2e773e2bf53e22523e1ef63e11123e0eb93e091c3def283dea5a3dd1e13dcfe33dcb0c3dc20d3dc01b3dbf653dac3d3da3043d835c3d7fea3d6f363d63843d463e3d2b803d22bc3d21f23d18893d12533d11103d0d563d0d503d01fa3cfd553cf9df3ce6c43cd6f33cd51c3cc0aa3cab3b3ca6443ca19c3c999b3c86e23c7bbd3c42353c3f1d3c3b573c2f463c21093c1f9b3c12303bfdca3bf0543befa23bef153bee893bee203be1ae3bddcb3bd2573bc4703bb3cf3baed33b9f8c3b8d2f3b7aa43b60f13b53c83b51c53b4a023b47973b367d3b318d3b30f53b2bcf3b17083af7e93af60b3ae9843acebb3ac9c83ac25f3aad9c3aa15d3a952e3a655d3a4da03a45e23a44153a39a43a34d03a2f9f3a08e339e49639c6ae39c56139b2fc399c91399b7c3998f83993ce39917a397fb6397dd4397d4d395f9239552039496739317439214d38fbd738f86c38e6f438dffa38d07c38cb7e38b9ff38b3a338b09238a2de38a18f) else if Nat.blt b 12 then 0x461efd461abc45feb445e08a45da7d45cbbe45c0c745b78245a93d45a72345a44f45a43a45954d459422457f84457b374578744577ee456df945540a4536484515c74515494506734502f94500c044fef644f89544f2c844e5cc44dfc044d7b444cc5444c61e44c3bf44ae0844a972449d7d449c67448ad54484d1447b46447a28446d8244410f44307a442b8e441dcc4414e0440fbb4405c443f2a843e0a243cf7543bc6343b8a143acb1439b7a43941d438a7f43708d43609b4336ad4328294307a64302c042fac842eb0b42c1ce42b20842a3064272b0426e49424170423a3d42217a4214f041fb1341ed8541ca0441c43641beec4192b1413bf1412a0d4116d2410a8e41048340dfdd40cffb40c17e40c0bc40bb4340b61640a615407f5a4079e240757e4072424068b1406809405d0c405cca403953403315402f794013393fe26a3fde083fd9593fd55f3fca793fa8d33f9f5b3f9ddb3f9db33f9c313f95733f655a3f504b3f3b503f34c33f2a5a3f1bd33f19193efa563ef9203ee64e else 0x4dfec04d86a34d83584d7f034d7c8a4d6c3a4d640e4d59064d28564d247d4d23eb4d185e4d12154d0ccd4ce44b4cd58d4cd3474cccb74ccabb4cc8a34cab134ca5de4c8fe24c8c8d4c8b914c865e4c7c7a4c6f164c60c24c250c4c22244c215b4c137e4c0ea24c0a874bfd9c4bfd7b4bfd494bc7644bb8d64b9bc34b8bb54b85204b77a44b74a24b66f24b32704b1d774b10454b08204af0194ae6e64adcd34ac2664aa3ce4a9b9b4a95574a8e804a7b434a7abe4a72d64a492a4a44604a3dbb4a0c8a4a065549feb749e03849d07649c99549b81249b0e1497aa4496e3c495908493cd4493117492ff0492b0b491159490caf490a4f4908104906f049024248eb8f48d82148d2f548d12548c21c48bf3348b52248a82a4879934833a6482f68480c68480c6147ef2947b27347aca247abd14792874774f2474b87473fd9471a9d470ed3470a9246fc1546f82246f5ad46d0cc46c48046b08546ae9c46a57c468ea3468ab84685a8468151467e444672dc466d884650674631b046285d462608) else if Nat.blt b 20 then (if Nat.blt b 16 then (if Nat.blt b 14 then 0x53d6e453d54053cc0a53c3a853c16e53c15a53bfff53b40753adc953a4a5538a9853875e5371c2535f89535d57535b96534052533dca5335e35335b6532dfc532ba753203c531c6053199553155253134052f3c152e7db52e38152d93952d28352ccfd52c51f52b30a527ee8526309525a12524679523cc5522b8151eefa51eeeb51ddcf51d87851cdeb51b02851ae0751ad1851916b51802d517b42517925517649515bda5158125152205151e2514cfd514576513c655132c751239f511316510fd851071250fd8150f00e50e83750da7e50cfc150cacc50b6f050b18f50b17850a31f509e175080a2507706506ef05061a750530a504cd350386c5036c2502f225026eb5017135016a55014675013ff5013cc5004474ff6e74ff41e4fe6a44fe5284fc8174f99184f87314f6c364f66084f5db24f5af24f5a864f586f4f54d04f4e414f4c744f24fe4f23734f0d6b4f06224f02094ef9ae4eeb8a4ee9e84eba354e9b8b4e97c54e958a4e89974e69b84e65d74e40594e310d4e10d84e08d1 else if Nat.blt b 15 then 0x5b8bba5b68bc5b64005b639b5b5fe75b5caa5b4c865b2da05b24355b0dd35aa2685a9fba5a8c685a81595a6f1e5a57075a56bd5a4b495a45435a31115a131a59f2ff59e0cf59df2059d5b459c57659c37b59af60599a175991c35989655976f85975aa597056596b65596aeb595e1959486b5934575916ed591543590b6158ffec58f00c58c8e458c02a58b32f58b22a589e65587bbb5860a7585b215854235849e85847ef58331b582df75818a6580fed57fbe657ea3957e04657c9e457ba1f57a5da579de6579c215794c057903c577ea9576fd7576e5157639b574f86574d085719c15718b95716e05708c556f1b856c39b56bf8256be4e56b6dc569cb9569b67567e8a5665305662a556512656415d563ece563aae561141560b8d55efd655ea1555e85855e75655c7b8558d9855742855496355402b5534d7552cf055261b551a6f5508e854fc1b54fc1854cbd054c7bf5460de545dce542ff35426c254242d5422955421c9541d4854159d5413685409d554062a53efa553e24e53de54 else 0x6335096321e2631fd363150d62f0f962e11262dad862d8a062d42f62c8a862c3eb62c26d62c0f862a611629ff16293aa62728a6271ad62710b6261dd6256836215af62008b61fb6761f76661e1ff61dfcf61cc9e61a537619eef619e786174cc61744e615e1d614c2161356e6119fb610ed86103da60e5db60d0f360d05960c62a60c1e760bdb660a2c46092b5608fc66086f46080e260788e6073b4605ef5605e3d605955604b9960402c60347f6032f6603157600e296006486005085ff1745fe35a5fdb485fce505fc7de5fc1825fb5f55fad3d5fa3c25fa3535f88125f7fc25f734e5f55785f45d85f43e55f2d835f27da5f1fd55f14b55ee7395eda605eb0cb5ea24a5e9a9b5e97415e779c5e75c05e68ec5e55b85e40af5e32955e15275e146f5dbbb45daa0a5da1ab5d516d5d33805d07e45cf6de5ced3d5cb97e5cb8255cb4635cb21d5caf075ca5e65c9c6f5c9ac25c8aff5c58105c38bf5c33a95c2f015c226e5c10945c036a5bfb015bf5a15bcc525bc6ea5bb8b25bae215b9156) else if Nat.blt b 18 then (if Nat.blt b 17 then 0x6c61ac6c59826c3fd46c3c836c36eb6c36386c256b6c234d6c194f6c11bc6bfe1a6bf13d6bee2a6bebd56bab1f6ba1dc6b93236b8f906b89346b5f656b50a96b4d326b32006b18766b0eb56afe286abe5e6ab6736aa3456a8e3c6a800e6a7fe36a4b6e6a49146a312d6a243d69e9a769e7f769bafe69b5b869a92269a1306975df695dcb694b3c6946ef6928ff690cd268e7c368e54068d02f68cf8e68c2e668b81468b77f68aff068ab39688a216889166886e36884be686afa68628d6862606854356853ca684ed968474c682d09682a806812c56805eb67e4d767e17c67dc6e67c5cd67b37b679770678b796788aa676601674e2467201e671ae366fcbe66f37a66df4966ddc166b1e466785a666e276666456666096640de6619566613a965f1e465949f6579066555716548b665213964fd4764b6c464b4fa64b14464b0f964a2a6649884647e8b647ab464464264318c64247c6417086415376414a364041763faf763f2d563ed8c63ddda63d81263c63763c5bc63c16963bfab637ffd else 0x758bb27576c7755b127553d5753b05753427752890752488750b9374ceb274be5b74b61474ae2774ab0574a69f7479797477c5746ab6746904745367744a6b74347474341e7430b57412fc73f5b173bc1e73ab0373986a739441737f7a737bd1737169736ed3732e8f731c8773154273071b72e98c72e1d672d8c772d24972b01e72ac4d72a4ab729ede727bd872751872721e726eb7725e5272513772370c7217f371dd9c71d6f671d62971d53671c55b71ba4371b32c71ac0071a9c671a378719fd171947e7182fa7178ea715d99714e98713b9d71315971240e70e99770b08370831a707f9c7066667049247037447000946fe01f6fca576fc2b16f99266f78fc6f78b86f78126f67586f62d96f5dc86f58056f532c6f2fcb6f09596ef98b6eed666ee4a96ed7ab6ebe896e63766e3c366e359a6e30b46e25696e18da6e0cb96df0116deb7f6dcd496d90f56d59866d39f46d2efc6d14eb6d13c06d080c6cde0e6cda0d6cd6686cd21a6ccb1a6cbeee6cac436c95836c94456c93ee6c6e33) else if Nat.blt b 19 then 0x7d713e7d70af7d68c77d46cf7d25eb7d050d7d00657cdd5d7cc7fd7cbaf07cad617ca4c17c9f6d7c935e7c74757c73227c13397c05ea7bf25b7bcee47bb1277b98707b751d7b68387b410e7b3bb47b31ae7b27d97b269a7b1e197b0f3f7afc977afc1b7afb1c7ae9367abf667abba87ab8ee7ab7f57a9ddc7a8bff7a7e0d7a73e77a64a37a60c27a47b27a35847a2ceb7a27057a184f79efe179d01f79c7c379ad9279a47579a22b799fbb7996bd7990aa798fd9798fc4798176797e107977cc796bea7962dc7961ed79553c794b82792b22791b6679162c790aae79052c78f0db78cda878c9ff78aadc78a83c7873d0786789782cec782a1b7825897823bf781de57809b378048678007677fcf277f26477ee5577ed3277eb2677e03277d45f77d23577c10d779bde779b57778a8c778619777907775cba775608775543770ab177000476fa4076efaf76cdc876c9fd76c73b76a7597683ab766178764232762bbd75ff2975ff0975f9f675f33d75db6d75ca6075c5dd75ba3475b166758c90 else 0x86222d86220c85fcae85e83f85ce3a85bbae85b97985b92685b80685a90485a3aa85820f8571078570dd856da0856c08855c8785519085477d85459284f3c784bb0984a96884925a846e7f84612e8456658434a184325e842f50842eca8419b48418e28403d383f7f783f76483e2e083db2583d8c883d1c183ca0483bf9383bd0783bc8783a49083a33e839663837c438375d5835b44835abf8356cc8353eb831df2831a6683148a8309f182f9d182f49b82ef2782c77d82ae9482ab1282a24082781f826e5f826e338249898224df8213c781f0c281bd1b818b12816b23815f79814b95811ba881183381126b80fd7880f82b80afe58094d58091aa8080b080583c8050c0803ce2803a1d8029de8013a080138e8010557ffd647ff3167fc2c97fa9027f437d7f3ed27f33367f32807f2fbb7f28397f1dd17f1ca87f1c8a7f118b7f084d7efe247ef6aa7ed8a47ec0607eb1387ea8c87e7f0f7e7ce17e63567e53237e39db7e34117dff397dff2d7de4b27ddb8b7dd0927daeb37dacea7d8b25) else if Nat.blt b 23 then (if Nat.blt b 21 then 0x91e2db91adeb917fc69167e1913db5912df8912c3091217d91159491081290f40990f17490eb3f90c6d490be9590aff2904b4890218b8fae758fac5f8fa5c78f9d4a8f9a9b8f8bec8f746f8f69688f67b98f5ac48f57788f3c9a8f21a38f06c68ef9a98ee9988ed4b78ed2ea8ea0798e91708e79168e75388e2aa78e0b888e06b08dcebb8dc8938da37b8d92958d8d358d766e8d70128d61018d5b528d4e018d38308d203a8d12df8cf8018ceec58cd3e48c891b8c6de18c4c378c3c268c2fb88c2b478c0e628c0dfc8bc0d38ba1ed8b8c688b89868b88f18b51568b41888b2ff48b12e98ae9b48ac0018ab4028aa8768aa5b38aa1e98aa1908a86638a788e8a1af389fb6789e86489e35f89d9dd89bb3689a04a894c25892ae188d78988d4f288ca9a88bef588bc4f888d8f886e58885836884ada882e2e882ba3880bfa87f90f87e8fb87e0a487d27e87b8d88798ba87792e876cd487639a8732b58721418720eb87140786f16a86e67f86e53a86dbaf86a9428692cc866e8086497c862a0a else if Nat.blt b 22 then 0x9ca2099c5a399c44d39c3bcb9be78f9be3649bdc469bc5609b7e8d9b70899b65ba9b63339b607e9b33449b325e9ae9609aa81e9a9bca9a84ea9a43f69a43bc9a34a79a30e99a019a99e36199bf7a99aca6999712998230997d84995fc99941dc992e07992418991f989915ae99001e98dd9598da6e989e6f9899b9988f30988c5c98823c987a5a98357c98090a9803ca97f74497f5b297e73797de8b97c29e97b193979d719791ea9754a29750dd97501d972bb2972879971ff8970a2d96d44d96b63f96abcb9692aa968d4f967a499677a9964dea964ae196308a961c54961622960daf95fc6895f96a95efab95ed5695e7a895c6dd95c2df95a8f895924195828295814c9580719557c1955006954486953b28950ff694fdec94e05794ddb994bbb89475de945893943a24942f2e942a9493dff993dbfa93d0dd93c1089396c0936ded9365c893643b935e4b93496393451f9321979314f99311ea92ca0192bb2e92b51292a8dc92a081929b30925b619243d2922bdf922a529207b691fbfb else 0xaadad8aaa639aa9e28aa97d5aa8e59aa79bbaa5cffaa5298aa51e2aa413baa396faa1c4ea9f4f8a9c32da9b750a9b443a9a5e2a94666a936d9a8ef17a8e91ba8aeb1a8ab26a87701a875efa84723a8186da81056a7e651a7d296a7a13aa77aa4a76c9fa75323a74a8ba7484ea7374ba71507a6fec5a6f3a2a6de62a6b112a6a37ca698e5a68b5ea68333a66c07a65916a64ebca63975a62e7da60bbaa5f0dca5e940a5d387a5a874a5a736a59544a58f00a58641a52c32a4fb97a4e716a4c925a4c239a4bb34a499baa47d41a47227a453a6a41302a3f24aa3f229a3c0a0a3a169a39d87a38951a36a8fa369a1a36359a3297fa2c4bda2c1b6a2bb69a2b9efa2b0f4a29eaea29325a28c4ba26fe3a2602da25750a24468a21f01a21529a20a51a1ff29a16bfea10465a06f87a0561fa0361fa0252d9fe2109fd6e59fcf119f900a9f90089f65809f612c9f5ee99f5ec49f3e2d9ef2379e9c949e87a99e7f169e558f9e31be9e1bb59e00c19dec069ddba29d99159d561c9d52909d4af39cd45c) else if Nat.blt b 25 then (if Nat.blt b 24 then 0xb84a52b83096b80e3cb7dbb4b7b281b7ab13b79e9db77f43b75f35b73789b6f73bb6ea4eb6d101b68c08b67e3cb66b83b66772b66563b6574eb62eb9b60630b6050ab5f71fb5d7d2b590cdb54cecb54214b51b64b4eda5b4e1dcb4d792b4cccab4b261b48d74b48acdb4457eb43ed0b40426b3e838b3d920b3d680b3d18eb39b74b39765b37626b37589b327f5b3262bb2b638b2b565b26846b25b8eb25950b2018cb1beddb1a16ab199c2b159beb145a8b11983b10be9b10607b101c5b0f62eb0edaeb0ce11b0c29cb0bdfab097d3b07e85b07d45b073d4b05cc2b03d34b00c06afdd13afb4deafa84daf947caf8999af898faf7423af5713af5260af2f93af147caee9caaedca5aed78daea24cae8db6ae8496ae746bae5eddae5ad7ae5877ae4a46ae26c1ae2531ae159fadf854add7caadcc26ada6a8ada492ad969cad8354ad7e54ad67b7ad39d8ad3324ad2adead2212ad1658ad055bad0413acde10ac9866ac6dfaac5a79ac260eac0f94abb38fab434aab3b5cab1631aaedbeaae43d else 0xce3326ce062bcd81cfcd4146ccc1acccb5cbcc937bcc1982cbd030cbaa14cba2c3cb8342caffe2cad701cab618caa506ca9a72ca98cdca884bca8166ca7b74ca2f1eca29b4c9d4efc9c7cec96e60c93285c92573c91488c8e7bdc8af25c85c8ec8479ec82186c80f88c7eca0c7e1c2c7dd5bc79f2ec71737c6e5d6c68f5fc67366c64e01c5f430c5eea8c5d5fec59dc5c5922bc56623c542d6c534c5c4ffc0c4b15ac4a6d9c48906c3e2dbc39296c38d3bc37779c376e9c34c9ac30f71c2f883c2edefc2b87cc22a63c1d52dc1bf6cc1a24ec198fdc13604c1107ac0e2dec0d413c07f6ec03694c00144bff99cbfdbc9bf8bb2bf80babf4835bf46ecbf2629bee7dfbeb6c2be77d2be6b78be5370be5319bdd2c8bda3eebd8993bd3f8bbd3780bcdf6ebccb79bccabebc7b24bc2ab9bbf4b7bbef63bba039bb8ed0bb875ebb554dbaf747baf5c3badf07ba5bf3ba477eba46ccba392cba2981b9f673b9f4d0b9f309b9b644b95a5cb95695b91c5fb8f7b8b8e7d6b8ab26b86627b865c4b854ce) else if Nat.blt b 26 then 0xf3cff6f28b5cf0a9b4f069c9ef7d71ee20d5edd7a9ed2aa6ed0c5ded020fecef04ec3a7eeb2c4aeafa8aeac01beab26bea1ffae91e7ae8f9a4e8c6cbe8596be80be0e7fc31e7bc69e79d55e78553e730cbe72297e6fc27e69034e5f684e5cc41e5a25ce50683e5016ae4ce65e4baa9e4b6bce45446e43891e42b46e3ff48e3bdb2e35368e32e2fe2f169e2e8f0e2d0b9e2712be253b6e1c568e1a746e18a30e162e7e15845e14031e123c4e05740dfe1a7dec70adead96de664cde4b31de3a63dd9b72dd99f7dd1a1fdca612dc38abdc31e3dc188fdbdfeadb9f10db472cdb20dbdace7ddaba4eda3ccad9f7a5d9a6a5d98d3cd94355d93cb3d9323ed8df28d83b11d838f3d83261d82f95d82029d81387d7fbe1d6b9f8d6b73fd5cbdcd5c79fd53bdcd4fd06d4f489d4735fd44986d43e3ad40f6fd3d057d3ae15d38682d33ae2d32fd4d31ef5d30997d2735fd26c13d23509d216e6d2045fd15513d02589cfc3f1cf743ecf5d1bcf510ccf4acdceed40cebca7ceb5f4ce86b9ce5eadce3e0e else 0xfe57f3fddf0efda7d3fbeee4fa9455fa9277f9a4e3f8a70cf74d59f641e3
def stChunk_13 (b : Nat) : Nat := if Nat.blt b 52 then (if Nat.blt b 26 then (if Nat.blt b 13 then (if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0xa9b5320e2373c05c851bc1c718d991b9ee1c026de0e3305908dcde1721c0f536a64c44a08dcb909b7a9b07181a8a46e5c877bd4da990711b9b321826de0e3966068f0b90e0136f5360e2b046e5c87009c7a9b5320e2372e63304dbd4c9151191b9a02e4381ea6c496cc8dcb90e0136f536a641c46e5c8a390c7a9b07181a373783bc2abd4d838c0d1b9ee1c0091ea6c1c6f8c0d1b972058f5320e39646e5c88209b7a9b071b32373d65c84dbd4c838ca11b9721d826dea6c53606984b90e0136f071cb2c846e6f0b90e07a990714b2372e44544dbd4d838b9d1b9bc1c0155ea6c1c606a2928972198f5326229646e5c88909b7a9b071612372e4430123d4c8ff1511b9891c026dea6c1c6068dcb90e00a8f5323541c47e5c87009b7a9b071f3a372e43804dbd4c87ee6d1b9721de26dea641c6548dcb90e0136f536a643f4785c87009b7 else if Nat.blt b 2 then 0x838df1942372e426c14bd4da993111b97328c26dea6c4b5488dcb90e0136f5360e2c24b45c87009b7a9b1362330346e5c8703d4c838e4128a372e426dea6d4c9888dcb910b1c0f5328dc2972c8dcb909b7a9b5320e2373784002abd4c838cd51b9721c026dea6c1c6068dcb90fb048f5320e3164785c87009b7a9b07181a3735a380123d4da4f07205b031c026dea6d4c8528dcb90e012ee002a6c295748dcb910c6a9b532232372e438049bc1c72cc0d1b9721c02b1ea6c1c6cc99cab8e0136f536a643b46e5c88009b7a9b18d692372e43804dbd4d838c0d1ba073785c9ea6c547f08dca08e0136f536a64be46e6a0b90e07a9b5326223f2e45104dbd4d88cb211b9721c01f1ea6d4c838945099f92e4f5360e30346e5c8860827a9b151582372823804db800838e5981a372e4151aa646a8388dce09721c0f536a64294a05c87009b7 else 0xa990a5cb26746e5c84dbd4d838c0d419721c026dea64d68388dcf2972136f53631c1c5c08dcb90e07a9b5320fa373d65c84dbd4d838f7d1b9a42e4381e0e36666e8dcb90e0136f0715ba372e44487009b7a9b5320e2802e44004dbd4c838e591b9e52e426de2a41c72cc0d1b972048f536a641c4785c87789b700153272cc472c5c84db54da991191ba0d2e4401ea6d4ca586fcb90e0136f536a652c97c944b909b7a99071c62513dc3044dbd4da990711b9aa2e4381ea6c1c60699cdb1721c0f5366230346e5c8a309b7a9b0a60e2ba46e5c8863d4d988c0d692372e426de0e318606a291b9721c0f536622e746e5c84d8097a9b5320e2372e43804dbd4d838c0d452673f0381ea6d4c9888fcb90a3136f5320e39646e5c89b1157a9b071b3a372e43804dbd4d838c0d3e9721c0091ea6d4c8388dcd990c104f5320e39646e5c8830247) else if Nat.blt b 4 then 0xa9b07181a372e638051bd4c838c611e1721c026dea6c1c5ce8dcb90e00bee002a6c547c28f07009b6a9b5320fa672ae3804dbd4c838cc12d1bc1c0155ea6d4ca58620b90e0136f5360eaaf46e5c87009b7838e5981a8a46e5c814bcc4630c0d1b972136025e0e38c6cc944b90c1136f53661b0346e5c8700cc7a9b07181a372e4430173d4da992f928972136001ea6d4ca586f0c38e00aaf5320e39646e5c87309b7a99071c6a373de3804dbd4c8d51511e1721c026dea6c536068dcb90e0048f5320e2964a25c88909b7a9b5322323740e5c8703d4c9cb3120e3962e426dea641c72c968de0e00aaf071a130346e5c8700887a9b07165a373f06f0703d4c8e31520e2371c026dea6c1c6069acb90e00bef5326231846e5cc4d80978e7071fc2372e43804dbd4c852ca1239721c026dea644672c8dcb9100136f5360e3034a25c8608247 else if Nat.blt b 5 then 0xa9b071b9b0346e6f0b93d4ca5923cdf1721c026de14b966068dcb909b048f5320e3965068dcb909b7a9b5326245447e5c84dbd27838d55819721c026dc0054da993111b972146d536a652c3fa5c84d88e7a990fd982372e43bc4dbd4d838c0d1b9721c00c9ea6c1c606bcd1b9bc1c0f5360e30446e5c87009c7a990a5942372e4430123d4c988e594da372e426dea6c1c60691cb90e0020f5360e37c6068dcbe1727a9b071572372e43804dbd4d98907183a372e426dea6d4ca7e8dd09172136f5360e3035065c8700827a990719828a4b45c8703d4c934c591b9721c026dea6d4c83899d1b904136f536a64be46e5f07009b7a9b5321da373383804dbd4c88ce591b9720f8091ea6d4c8528dcd39721c0f53298c1c7068dcb909b7a9b07181a372e43bc2fbd4da99071419b31c026dea6cc45688dcb989b012f5321fb9646e5c87789b7 else 0xa99071a12372e438051bd4da993111b9722b826dea641c72c8dcfc172146f5362330346e6f8b90e07a9b53214a373c05c84dbd4c838d7d1b97222426dea6d4c8a88dcd394c1c0e002a6c1c6008dcb90e06a9b5326241c46e5c851bd4c9df070b91121c026dea6d4c88c8dcb9100100f5320eb3046e5c87009b7a993860e2372e426c0c3d4da990711b97220017dea64688388dcd21721c0f536a641c46e8547009b7a9b0716123f2e43804dbd4c8fd0711b9bc1c0155ea6c5e838a291b9721c0f536a652c3fa5c84d8557a9b5329628a3fa5c84dbd4c838e592897226c449e0e3a36068dcb90e0088f536a652c514848b909b7a99071cb2372e83804dbd4d8a8f851b8e018226dea641d72c8dcb90e0136f5360e2b44785c87009b7a991fa1da372e43804dbd4da9907128972216381ea6d4c97c8ecb90e0136f5362a41c7c28f07009b7) else if Nat.blt b 9 then (if Nat.blt b 7 then 0xa99071922472e43804dbd4ca26e591b9721c026dea6d4c87e8dcde1bc1c0f536a641c48e5c8700a37a99085cb2372e43804dbd4da994b1339fe2e426dea6d4c83899d1b9e5136f071c63664ce5c87009b7a99119cb23735a5c8703d4da993111b99c136025ea6d4c87e8dcb90e0140f071fc3964a28dcb909b7a9b07181a372e4418703c1c650abd1b9721c026dea641c72c8dcf71061c0f53614b0346e5c8700c17a9b5322327d46e6b4703c1c72cc0d1b972224091ea6d4c8a90711b9f820cf5320e3964b85c87009b7a9b5321fa3737838000bd4d838c0d1b9721b426dea6c1c5848dce09721c0f536a641c46e7f4be09b7a9b532684be4a25c84dbd4da993111b9c53145c9ea6d4c8a90a51b972218f536a641c46e5cc830e07a99071cb2673f03044dbd4d838c0d1b97c1c00a5ea6d4c83899cad8e0136f071cb2c246e5c84d8207 else if Nat.blt b 8 then 0xa9b071f72373785c8703d4da990711b9721c426de0e3966d28dcb90e0136f536a652c3fc624b909b7a9b5322a23c3c03804dbc1c74ce591b972136091e0e3966cc8dcb91061c0f536a652c30e5c8858e07a990719829e46e5c8703c1c7f0e311b9721c026dea64c4838e591ba132e4f53272c1c2e44487009b7838e5981a372e4380503d4da994fe961fd2e426dea6c635a28dcb90e0048f5326247e46e5c84d8097a9b5321fa373785c8703d4d838bad1b9721c026dea6d4c9888dcbf89b05cf536a644650a8dcb91007a9b532622372e426c403c6a838b9d1b9721c026dea641c72c8dd15972136f5363241c6008dcb90e07a9b072012372a83804dbd4da4f11a0e3032e4381ea6d4c87e8dcde0e009ef5320e3964ce5c86609b7a9b07181a373fa704b93d4da991511b9a71c0095ea6d4ca634b0fe972136f5320e39646e7c8b909b7 else 0x15360e2ba46e5f086354da990711b9bc1de005ea6d4ca587e4b90e0136f5320e33346e5c88605f7a9b5320e23740e5c84dbd4c838c391b9721c026dea64c472c8fcb909b012f536a641c4a284cb90e07a9b07181a373783802c3d4d838fb91b9bc29e381ea6c466068dcb90e00f8f536a641c4725c87009b7a9b5321ba372e43804dbd4d838c0d70a372e4381ea6d428388dcb90e0158f536a6446838a00b90e07838cc181a373785c8703d4c988e591b9721360b9ea6c436068dcb90e0136f536a652c98884cb90e07a991aa0e2372e44004dbd4c991071cb2372e426dea6d4c88c8dcb98e00f8f536a643f46e6f0a78e07a9b53214a372e43144dbd4da990713f9a72e4381ea6c5e8388dcb90e008ef071cb30346e6f0b90e07a9b5321fa6746e3bc4dbd4c838c911b972218091ea6c1c56a8dcb90e0136f536a641c51499c700557) else if Nat.blt b 11 then (if Nat.blt b 10 then 0xa9b5320e2373983802abd4c838e594fa372e40b9ea6c1c606a291e1721c0f5360e37c46e5c84d8297a99071cb2372e44504dbc1c650ad91b9721c026de0e3e16488dcb90e0136f5360e3e146e5c8700a37a9b5320e2862e43804dbd4d838ab91b9721c426dea6d4c8a88dcfe941136f536314536068dcb90e07a9b5320e28a46e5c8823d4c88ce591b9ad1c01f1ea6c1c606a28b90e91c0f5326239653ea591b9727a990719829146e3802abd4da993111b9f92e428dea6d4ca588dcfe9c12e4f5329647e7a65c87009b7838e5981a372e4090123d4da990712d1721c028dea6c1c5688dcb90f6136f5320e396456898b909b7a9b5320e2673d23804dbd4ca37071cb2372f826dea651372c898b90e0136f536a641c46e5c8860257a9b07203a3734e5c8703d4c838e5948a371c0155ea6d4c8388dcbe0e012ef5326ec1c46e5c87009b7 else 0xa993760e2262e43804dbd4da990a5239721c026dea6c1c5908dcfc1bc1c0f3120e3965848dcb909b7a991aa0e2373383804dbd4d838b111b9721c026dea6c1c606a351b9721c0f536a641c51499c7005f7a9b072032372e43804db800a994b26e9721c026da0e3396068dcb90e00c6e002a6c1c606940b90e06a99071942472f83804dbd4c838e5933a372f826dea6d2c7f0fd4b90e0136e002a6d4c83899cfc1066a9b5322326746e6b4703d4d838ac51b97220c381ea64296848dcb90e0136f53214b4546e5c87009b7a9b5320e2373be5c84dbd4c989119cb28a46e5c9ea64e48d5070b90e0136f53214b9646e7e0b909b7a9b5321fa373783803e3d4da990711c172218091e0e41472c8dc7009b0e2f5360e2cb46e5c88605f7a9907195a372e43804dbd4c88ce593e9721c01f1ea6d4ca6d0fd338e0136f5360e36e46e5c86489b7) else if Nat.blt b 12 then 0xa9b5322328a46e5c8803d4da993111f98a2e426dea6d4c8a88dca68e0136f5360e30346e7e0700ac7838e5981a372f826c123c1c72cadd4fa372e4381e0e3425ce8dcd68e0136e002a642972c91cb909b6a9b532624544783804dbd4ca93071cb2372e426dea641c7a0c591b8e0136f536a641c5148dcf29727a990718aa372e4418703d4d852bb51b9721c026dea641c6548dcbf8e0136f5320e3964ce5c8830e07a9b532622672e43144dbd4c838ca11b97c218091ea6cc45d68dcb909b100f5320e39646e644b909b7a9b07183a3f2e43804dbd4c838e591b9bc0aa0b1ea6d4c8388dcd397c1c0f532964dd8385c87009b7a591f9fc2372e43804dbd4d838c0d2397c2e4381ea64698388dcb90e0136f536a652c3825c8700137a9b2f981a512e43804dbd4c838e6d1b9721c026de0e3966068dcb902400af536a64c447e5c84d8247 else 0xa9b071b7a373f05c84dbd4da993111f972136015e0e3966068dcb90e00a8f5322341c72ca29289727a99071c1a5146e5c84dbd4d838b091b97220026dea6d4c87ea291b9721def5360e30346e5cc700247a9b071b52372e43804dbd4c838cbd1b9721d426dea641c65c8dcb90e0136f0720939646e5c87009b7a992f9cb25146e5c84dbd4da990711b9e02f826de0e38c6068dcf70e0136e0020e32860691cb90e06a990a60e39648e5c84dbd4da990fd1b9bc1de155ea652c988e0d1b972136f536a641c47e5c8700a37a99071a1a372e438051bd4c8d90711b9aa2e4381ea6c548248dcd39411c0f5320e39646e804b909b7a9b53265a372e43803e3d4da99071271721c026dea6d4c8a88dca08e012ef5323641c46e5c87009b7838d0973a7d2e43804dbd4da991191b972200155ea6d4c9888dcce98a136f536a642946e5c8860247) else if Nat.blt b 19 then (if Nat.blt b 16 then (if Nat.blt b 14 then 0xa9b5329fc4646e5c8803c2b838e5981a372e426dea6c297c28dcb90e0136f5322339f46e5c87007c7838e5981a372e43304dbd4d838abd1b9721c026dea6d4c9972f928972136f5320e3964a28dcb91367a9b0720a2372e4380563d4c88cc551b9721c01f1ea6c29606ae91b9721c0f53614b035a28dcb90e07a99071c62373f05c84dbd4da990711b97f1c026dea6c1c6cc99cf70e0136f536a64204725c87009b7a99071cb24748e5c84dbd4da990a52d1721c026dea64be7188dcb90e0136f5320e39646e5c8b189b7a9b0a55d2372e4430703d4c838d093e97220026dea6d4c83a8dcde0e00aaf536a644646e5c8700827a99071c62373f06f04dbd4c838e591b9f81360b1ea641c61e8dcb90e0136f53238c5488c8dc7009b7a9b07181a372f838060bd4d838c0d23972218091ea641c6848dcd6900136f5320e39946e5c87009b7 else if Nat.blt b 15 then 0xa9b4b1819fd30e5c84dbc1c72caf51b9721360b9ea641c72c8dcd51721c0f532964dd3f25c87009b7a99071cb2372e43804dbd4da990711b97c18a26dea6d4ca6d0fd451721c0f5322341c72c8dcb90827a9b11981af346e5c8703d4da990a51b97c21826dea6d4c8a88dcd39411c0f5320e38c46e5c89b0e07a9b12dfaa372e43804dbd4ca36f511b9721c026dea641c660a29289721c0f5360e3e95748dc7009b7a9b4b1611872e43804dbd4d838b21451721c01b5ea6d4c8a88f0c38e0136f536112c246e5c87009b7a99396623962e43804db800a99071cb2372fe26daa6c1c6e28dcb90e0136f5360e30346e5c8700aa79c307181a373fa5c84dbd4da990711b9f820c015ea641c72cd7d4fa372e4f5320e33146e5c87009b7a99071cb2372e438c4dbd4d838fe11b9ee1c026dc0054c88ce591b972104d536a642946e5c8860057 else 0xa9b071b325e2e43804db800a9b53221a372e4431aa641c72ca2923972136f5362341c6008dcb90e07838f45cb30346e3804dbd4da991511b9e028226dea641c72c8dcb9162136e002a6cc46068fcb909b6a9b07158a373d65c84dbd4c9cb071cb29f2e4381ea6d4c83899cf40e0136f536a641c46e780b909c7a9b071fc27d2e43804dbd4d8c715181a37378381ea641c6508dcde0e00aaf5320e39646e5c84d8617a99071cb2472e45604db800a9b5326223f2e626da3541c6068f0b90e0136f5360e30348e5c8ab8e07a994b20e3834a25c84dbd4c9c50711b9fe2e426dea6d4c97c9d0b90c1136f53247c1c46e848b909b7a99071982372e43804dbd4da990711b9c9382381ea6d4ca58944fe972136f536a64c488c8dcb90a37a9b53263a372e43bc4dbd4c9ad0711b9721c026de0e38c606944b90c1136f5320e38c46e7f4b909b7) else if Nat.blt b 17 then 0xa9b2fa2330346e5c8703d4c838d091b97c1c026dea6d4c8870711b972218f5320e39646e7e0be09b700153614b0346e5c886354d8951191b9be2e4381ea6d4c8a1071338e0136f071cb2ae46e5c87009b7a9b07200a372e43804dbc7e838c0d1b9fd2e426dea6d4c8388dd05972048f5360e3f84a25c86089b7838e99cb2672e43804dbd4d838ac5339571c026dea652c9c28dcfe972136f536a642947e5c87009b7a9b532622372e442c4dbd4d98907181a3f2e426dea6d4c88c8dcfc1ad1c0f536a64c447e8dcb909b7a9b5320e2372e437c4dbd4da994b0fe972136025ea6c1c606a28b91601c0f5360e30346e6f4b98e07a9922a0e27f2e43804dbd4c838cc11b9721c0209ea6d4c9888dcb90e0146f536a64c48388fcb989b7a9b07181a373fa6704dbd4d838c0d451992e4381ea641c7468dd100e0136f1fa0e2c246e5c87009b7 else if Nat.blt b 18 then 0xa9b071f4b6646e3804dbd4c8ff0711e1721c026dea6d4c88c8dd03972136f071cb30346e5c8120007838e599430346e5c8123d4da99071239f82e4431ea6c1c6068dcfc1bc1c0f536a641c48e5f07009b7a993120e39646e5c851bd4da990fd1b97220c381c0054c88cd093e9721c0d536a641c478690b90e07a991522334246e5c8703d4d838c0d1b9721c0279ea6cc46068dcde172012f5365f2ba46e5c87009b7a9b53214a3733c3804dbd4d838ad11b97219826dea6d4c8a88dcd390c1c0f53614c1c6068dcb910c7a99071afb2846e5c84dbd4da99071211aa2e4381e4541c80e8dcb90e0136e002a64466848dcd68e06a99311942372e426c04bc1c660ab91b9721c026dea6c1c6068dcfc0e0140f536a641c4845c87009b7a9b4b22a3f82e43804dbd4c9ab0711b9a72e4381c0054c988e591b972146d5320e39644c5c87009b7 else 0xa9b5320e25b2e43804dbd4c87ee591b9bc2e4381e0e3965d68dcb90e0136f5360e36946e5c8858e07a99311cb2372e426c403d4ca591f91b9fd2e426dea6d4ca593111f972136f5320e3d16308dc7009b7a9b5320e2372f8430123d4da990e51b9721c026dea6c1c816c0d702371c0f5360e30348e5c87006d7a9b11a0e30346e7f4b93c1c648b9d1b9721c026de0e339606984b90e0136f5360e2e746e5c8700a37001071cb30346e7e0de354c88d071a127d2e4381c0054c838e592397c136d071cb30346e5c8830e07a9b31181a372e43144dbd4da994b11b9fd33826dea6d4c8a88dcd38e0124f5360e4145148dc700717838c5581a372e4380123d4c9ab0711b9e02e426dea6c1c6f4944b91061c0f5326f41c46e5c87009b7838ce981a372e43804dbd4da994b2622742e426dea64e6838e58b90e0136f5322341c6848dcd68e07) else if Nat.blt b 22 then (if Nat.blt b 20 then 0xa9b119f72372e43803e3d4c9892011b98a2e426dea6c1c6068dcf98e0136f5320e33051499c700557a9b5320e2372e441877bd4da990712d17c1c026dea6d4c97c8dcf70e0136f5322a34246e5047009b7a9b0715d2372f8430703d4c838e311b9a72e4381ea6d4c8388dcb90e014af5322a39646e7e0a089b7a9931235a372e426c04b800a9930dcb2372e426daa6c1c6dc8dcb909b052f53298c1c72ca28b909b7988c615a2372e426c04bc1c630c0d1b9721c028dea6d4c9888fcb909b000e002a6c1c60691cb90e06a9b5320e2372ea3804dbd4c838e59452671c0155ea6d4c8388dcb9100146f5323545446e3804d8097a9b5320e2512e4418663d4c87ecc11b9bc2e4381ea641c72c8dcb90e2136f5320e31846e5cc700a37a99071cb25146e69cb93d4d838ae91b9fd2e426dea6d4c9868dcb90e0136f5320e31646e5c8830e07 else if Nat.blt b 21 then 0xa9b5325f23735a3804dbd4d838c0d451721c01b5e0e3966068dcb90cf136f5329647e2e43804d8187a9b5322a2472823804dbd4c86ecc11b9721c026dea6c1c824a291b9721c0f5329647e2e43804d8137a9916214b9646e5c84dbd4da990a51b972218001ea641c72ca293a172136f5320e39646e7e04d8457a9b5320e2372e4430663c1c6aac0d1b9721c0221ea652c72c7e4b90e0136f53261c1c72c8dcb909b7a9b11a0e3034a05c8703d4d838c0d1b9b82e4381ea6c1c7be99cab8e0136f5320e39646e81cb909b7a9b071f0a372f83804db800001071cb30348e5c96a6d4c8a88f0d38e0136f53268c1c72c8dca209b788ce5981a372e43803e3d4c838e591c9721c026dea643772c8dcb90e0136f5362241c6068dcb90e07a9b07181aba46e5f0703d4d838de91b9721c0331ea641c72c8dcb90ec136f5360e3035a28dcbe0e07 else 0xa9b0720630346e3804dbd4da4f071819721c026dea6d4c88c8dcb90ef0f8f5360e3e95908dc7009b7a9b0715a2372e4418703c1c7f0e591b972136091ea6c1c6068dcb90e00dcf536a645446e504860247a9b5320e2374225c8863d4c838ca51b9f82e426dea6d4c8868dcb90ef136f5320e39646e77cb909b7a9931214b9646e5c84dbd4d88cc0d692372e4381ea6d4c8388dcfe9ee136f536a64464a28dcb91007a9b07181a7d35a3804dbd4c838ca51b9f837826dea641c72ca18b90e0136f536a64be4fa5c87009b7838d5581ae046e5c8703d4d838d991b9f82e426dea641c6308dcb91061c0f536a641c4ce7e0830e07a99071c62373c05c84dbd4da994b0c39721c028dea644662c8dcb90e00f8f536a653030e5c87009b7a9938e3f41c2e43804dbd4d838c0d2897218a26dea6d4c8869acb90e0136f5365f36646e5c87009b7) else if Nat.blt b 24 then (if Nat.blt b 23 then 0xa9b5320e23741e3802bbd4da991512d1411c026de0e32857491cb90e0136f5320e39646e6ccb909b78c7071cb30346e5c8123d4da990711f97c1c026dea6c6383902d1b8e0136f536a641c4fa7f4b909b7a99071ebb9646e5c8703d4da99332232372e4401ea6d4c88c8dcb9100012f536a641c4fa848b909b7a9b14d81a372e43ec4dbd4c852e59239721c026dea647e8388dcb90e0146f5360e36646e7f4b909b7a9b0715ea372e438051bc1c65eb211b9721c026dea6d4c8388dcfe9ad136f536a641c4a2778b909b7a9b5320e2373783802abd4d852b9d1b9721c026dea6d4c97c944b90c1136f536a643f4ce8dcde0e07a9b071fca372e43804dbd4da9907141972218381c0054d8c702d1b8e0136d536a65313f25c84d8097a993566241c46e5c84dbd4c9a70711b9721c026dea6d4c8388dcce0e0146f536a641c478780d39727 else 0xa9b07181af25145c8703d4c852e591b9872e426de0e3285748dcb910c048f5361fb0346e5c8700247a9b532622372e426c04bd4da993020e2373f026de0e3fb72c9451b972136f5322341c72c8dcbf89b7a99071cb23f2e438051bd4d88cad11b9721c01f1ea6c1c5748dcd39721c0f5360e2e15688dcb90e07a9b5321fa672ae3804dbd4c838e591b972136245ea6d4c8388dce097c1c0f071cb30346e7acb909b7a990a5cb2372e4430123c1c684c0d1b97220026dea6d4ca587f4b915b136f5360e30346e5c88605f7a9b5321ba6746e3804dbd4da990a51b97220026dea6c547c28dca08e0136f536a641f46e7e0b909b7a9b5320e2802e43804dbd4d88d07183a372e4381ea6c1c5848dcba0e0136f536a64c446e5ccb90a37a9b4b1819be2e43804dbd4d838f851b9721c0271c0054d838c0d1b97c218d536a644646e834b90e07) else if Nat.blt b 25 then 0xa9b071f6a372e43804db800a9b53223237392381a0e3166068dcb90e0048f5320e3877068dcb909b7838ca1612372e43804dbd4d83cc0d1b9721c026dea6d4c83899c778e8136f071cb2af46e5c87009b7a9b071fc2372e63804dbd4c838e5928a472e426dea641c62c99cab8e0136f536a641c46e6f07005f7a9b5320e27d2ec3804dbd4d838ac11b9731c026dea6d4ca5931128972136f5360e2e746e6b48009b7a9b0715d2373c05c84dbd4da990711b9ad1c025dea6c4d7be8dcb90e0136f5365f2c846e5c87009b7a9b5325f2672e43804dbd4da990711b972218369ea6d4c9a33111f972136f5322339646e5c8700827a9b07181a8a2e4584703d4d838c0d1b9ba2e4381ea641c62c8dcf5972136f536a652c8a87f4b909b7a9b11a0e30346e780b93d4d838ab91b9bc1c0155e0e3966d48dcb90e0136f5320e34b46e5c87009b7 else 0xa9b53226a673123804dbd4c9b50711b9171c026dea6cc46068fcb90e0136f5320e39648e5c84d8097a992161fa372e43804dbd4da990711b9ee34e381ea646a8388dd0e172136f5362a3e146e4307009b7a9b5322341c46e724703d4c838e591b97223c26dea6d4c83899cab8ef136f5360e3035148dcb90da7a9b5322a23f2823804dbd4da993111f9731c026dea641c73699d1b8e0136f5322a41c72c8dcb90977a9b5320e2373525c8703d4c838e31239721c026dea646c838908b90e0136f536a642946e6707009b7a991920e39646e7e04dbc6a8390491b9721c026dea641c7b0d091b8e0136e002a641c72c8dcde05f69ab071f0a372e43804dbd4da990711f9721c0271ea6d4c8388dcb910c0a6f536a641c46e5c8858e07a9b5320e237398538703c1c660abd1b9721c026de31c1c6aa8dcb90e0136f5327941c46e5c87009b7) else if Nat.blt b 39 then (if Nat.blt b 32 then (if Nat.blt b 29 then (if Nat.blt b 27 then 0xa9b5320e2373dc7804dbd4da9931140172136201ea6d4c8a89fcd00e0136f53614b0346e5c8860e07a9b071b323734e5c8703d4c838c61339571c026dea6d4c8388dcd69a71c0f5360e37c46e5c8700ac7a994b2623965145c84dbd4d838d99702372e4381ea645472c8dcf0141136f5360e3fa46e710b90e07a9b151f0a371c026c493d4c838e59339e81c026dea6458838e591b97c136f53614aba46e5c88609b7a99071c62372e4430123d4da990711b9fe3885c9ea6d4c8a88dcd39721c0f5360e4057c28dcb90e07a993860e25146e5c84dbd4da991511b9c1282381e3f41c7f88dcb90e0136f5322341c6928dcb90e07a9b53221a372e4430703d4ca7f311cb2372e426dea6d4c8768dcb90e2136f53614b0346e5f0700247838e5981a372e426c2a3d4da991511b9a71c013dea6d4c9888dcb90a30acf5320e3a372ca29289727 else if Nat.blt b 28 then 0xa99071c626746e7e04dbd4da990fd1b9f8378381ea64718388dcd39721c0f5362a40746e6807009b7a99071c625a2e43804dbd4c838e8dcb2372e4209ea641c72c9c523972136f536a64c488c9f4b90e07a9b071bd2373785c8703d4c838ca11b97222a26dea6d4c8388dcff19c136f53245c1c46e5c87009b7a9b0715a2672ae3804dbd4da990711ba07378155ea646a8388dcb90e0136f5326241c72c8dcbe09b7838f85cb25146e5c84dbd4c838e1d28a372e426dea641c7068dcb909b048f5326239647e8dcb909b7a9b5321ba373783802abd4da7f07181a372e4369ea6d4c8388f0b91061c0f536a64c488c8dcd68e07a9b0a581b0346e5c8703d4da991511b9a729e381ea6d4c8389f4d39721c0f5360e3625748dcb909b7a99311cb2372e438051bc1c630c0d1b9721c0091ea6c1c5d6a00b90e0136f5320e3964b4944b909b7 else 0xa9b2be0e3e146e5c84db800a9b11973a3735a381aa6d4c98907123972218f071a12ba46e5c87009b7a9b5320e26736c3802abc1c72cb151b972136151ea6d4c8388dcb91071c0f536a641c46e84cb90e07838e595d2373f05c84dbc1c72cc0d1b9f8378381ea6d4c8388dcd29721c0f5363241c5fc8dcb90e07a9b07181a372e4544703d4c838e592397c1c026dea6c547b88dca08e0136f07197b0346e5c87009b7a9907198a6746e3804dbc1c72cc0d1b972052091ea6d4c8389f4f0172136f071982b646e5c87009b7a9b07173a372f83804dbd4d838c0d1b9721c00ade0e3e17188dcb90e0136f536a641c4a269cb90c17a9b071b32373c05c84dbd4d986da91b9721c026dea6d4c8388dcf01ad136f5324941c46e5c870046788d071a130346e5c8703d4c838e59211721c026de2341c72cc0d1b9f82e4f5362c41c6068dcb90e07) else if Nat.blt b 30 then 0xa99071cb25147e5c84dbd4d838c011b9721c026dea647e8388dcf1172136f0718aab046e5c87009b7a99071d1b9646e5c8173800a9b5322323735a401aa6c1c60691cb90e01c0f5320e39b46e6f0700557a9b5322323735a61c703d4d88d07173a7d2e4381ea6420838e591b9f8136f5362f41c46e5c8700247a9b532961fd2e426c123d4da990712d1721d426dea6c1c57491cb90e0136f5320e32446e5d07009b7a990719826746e3804dbd4d88d07173a3735a381e3541c55c8dcb90e0136f536232eb46e5c8700807a99071cd2372e43804dbd4da993111b97214626dea6c1c606a28b90f91c0f536a653b32c5047009b7838e5965a373f05c84dbd4d838f851e1a72e4381ea6c5488cb9d1b9721c0f536a64c44725c84d8097a994fe0e3964a25c84dbd4da990713395f1c026dea641c72c8dcb909b104f53214b9646e5c84d8107 else if Nat.blt b 31 then 0xa9b071702c846e5c8703d4d838fbd1b8e01361c5ea641c7189451b97220cf5326245472c8dca089b7a9b5326223f2e426c013d4c988e594b2372e426dea6531a58e58c3972136f536a64544784f87009b7a9b5322341c46e6b4803d4d838c0d28a372e4331ea64ec8385c8700b2136e0020e39660691cb90e06a9b0715d2372e4430123d4da992f91b9731c026dea6c1c6068dcbe1411c0f536a652c3fa628b909b7a9b5320e2372e43ac4dbd4d965151f0a371c026dea6c1c7c28f0f0172136f53621b0346e5c87005f7a9b07181a6b46e5c8703d4c9070711b9721c026dea6d4c9888dcb90a3104f532964466848dcb90e07001536a64464fa5c880354da4f071b9b032e426dea6d4c8a91191b972200e0020e39657491cb909b6a9b5322327d30e5c8703d4c838e6d452372e4381ea641c72c9451b99d136f5320e39646e61cbe09b7 else 0xa9b071612372e438055bc1c72cc0d451721c01b5c0054da990fd2d1bc1c0d5320e39646e5c84d82a7a994b20e3304ce3804dbd4ca591f9451721c026dea6c1c606984b90e0158f5320e38c46e704b90e07a99071942372e438051bd4da990751c1721c026dea6d4c88c8dcd01721c0f536a64c3514944b909b7a9b15173a372823804dbd4da99071341571c026dea652c8fc5c87009b11cf5360e2c2514944b90e07a9b11a0e3034b45c8703d4d848c0d1b9721c026dea641c6848dcf70e0136f536a643f46e6f0c78e07a9b5322341c4fe5c8703d4c838e591b97219c26dea641c72c8dcfc1ee136f5320e39646e5c84d82e7a9b5322341c4fa5c8803d4d97cc0d1b9721c026dea6d4ca59071099721c0f5325f39646e7b87009b7a9b532112372f83804dbd4c838e311f9721c026dea6d4c97d1511b9f8136f5320e3964a28dce09727) else if Nat.blt b 35 then (if Nat.blt b 33 then 0xa9b071b32472e43804dbd4d838ae91b97c21826dea6d4c8388dcf710c048f071cb2b746e5c87009b7838e5981a8a46e5c8663d4da993111f972146025e0e3965908dcb909b042f071c830346e5c87009b7a99265a12372e43804dbd4da990fe0e25a378381ea6c1c6068dce099c1c0f5360e30346e7f4b909b7a991fa0e2372f83804dbd4c838d093e9721c026dea6d4c9888dcb90a305cf5320e3964fa7e0b909b7a9b07157a373783802ab800a9944e769721c026daa641c7368dcb909b030f536a641c46e6b8860247838d99a12372e43804dbd4da99071289f319826dea641c6848dcd68e0136f071cb36646e7e0b909b7a9b11a0e40746e5c8703d4c838e591b9f835a26dea6c1c5848dcb90e0136f53247c1c46e704b90e0797ce59b32372e43804dbd4d838c0d1b972198025ea64c471a8dcb90c5136f5360e2ba4b45c87009b7 else if Nat.blt b 34 then 0xa9b5322a41c4783804dbc1c630ad11b9721c028dc0054da990712d1bc1ded5362341c6068fcb90e07001536963033fa5c84db54da990711b9ad218091ea6454838e5923972136f5320e3966988dcb90247a99071982373783802abd4d838c0d1e1721c0091ea6d4c9888dcf4972136f5320e3304b48dcde0e07a9b07181b0346e5f0703d4c838ca11c1721c026dea641c72c8dcd3972048f5320e3424a25c86089b7a9b5320e2372e4410123d4ca7f4b23f1721c026dea6c5488cfb91b8e0136f536a642946e5d07009b7a990719623735a3804dbd4d838c0d1b9f12e4381ea6c1c6068dcbe10c1c0f5320e39646e6f0700557a992f9cb2512e43044dbd4d838fed2897218226dea6d2c8946f8b90e0136f1fa0e30346e704b90e07a9944e76c1c2e43804dbd4ca634b23f1721c026dea646a8388e4b90e0136f5360e37946e5c87009b7 else 0xa9946de8a9646e3804dbd4da992fa0e2673f026dea6d2c5f661cb90e0136f5360e30346e5c8700977838cd973a372e43804dbd4c852e591b97c2e426dea6d4c8a9119452671c0f5362a3e146e3804d84f7a9b151f0a373783804dbd4d838ae91f9721c026dea6d2c838c0cfe972136f5324541c46e6b47009b7a9b53296237382670703d4d838f851b9ee1c026dea6d4ca588dd09172136f5360e2b146e7e0b909b7a9b071b12c846e5c84dbd4d838c0d281721c026de3441c7f08dcb90e0136f5320e38d4a25c86289b7a9b5320e28a4ce7e0863d4c8d50711b9df2e426dc0054da992f9339f8136d5320e39646e840b905f7a9b2f958a372e43804dbd4c9bb0711ba132e4381e2a3e172c8dca08e0136f536a641c4fa5c8860247a99071cb2802e43804dbd4da994b1099f92e4381ea6d4c838968f70e0136f536a641c4ce7e08309b7) else if Nat.blt b 37 then (if Nat.blt b 36 then 0xa9b0a581a373785c8703d4c838e59282372e426dea6c1c606be91b9721c0f536a644646e5c8800247a9b0fdfc2372e43804dbd4ca370714fa372e4381e0e3965ce9451b972136f0719430346e5f0b90e07a9b5320e2373663804bbd4c97cc551b9721c026dea64be72c99cb90e0136f071cb3966068dcb90247a9b53261a372e4430663d4d838f851b9ad1c026dea647e8a88dca08e0136f536a641c4e255c7009b7a9b0715d2373825c8703d4c852ca11b9721c026dea6c5c8a8f851b8e0136f5362a3e446e5c87009b7a9b5320e26b2e44302fbd4c988cc11b972136025ea6c1c6cc99d1b9f8136f5329647e46e704b90e07838ecd81a372e43804dbd4d838d992d1721c026dea6d4c8868dcde1721c0f5362a3e146e5c87009b7838e5981a372e4304123d4da990712d1ad1c026dea641c72c8dcbe09b020f5320e3966be8dcb909b7 else 0x1536a64be4a25c883341c62cac11b9721c026dea6c5b5468dcb90e0136f536a641c4a28dcf71067a9b11a0e2fe46e5c8703d4da994b2961fd2e426dea6c1c7d68dcd39721c0f536a64c447e5c86089b7a9b071642472e43804dbd4c838e593397226c381ea641c72c91cb9112136f536a645488c8dcb91047001536a643f5228dc70354c9cb071cb1721c026de0e38c5ce8dcb90e0136f5320e39646e5c8858e07a99071952372e438051bd4c88ce591b9721c0201ea6c1c5848dcb90e2136f0719430348e5c87009b7a994b20e3305145c8703d4da9907123972218041ea6d4c838a0cb910c104f5320e3964b08dcfc09b7a99071cfa373f05c84dbc1c684b211b9721c026dea641c72c8dcde0e00bef53614b0346e5c87004f7a99071c1a672e43804dbc1c72cb211b9f82e426dea6c1c7c29f4b90e0136f532964c472c944b909b7) else if Nat.blt b 38 then 0xa9b5320e2373dc704703d4da994b0fe972136001e3541c55e8dcb90e0136f536a64be838944b91067a9b151f0a371c026c3e3d4c838e592897223826dea6d4c8528dcb910c182f536964c46d28dcb909b78d51520e30346e3804dbd4c8dd0711b9721c026dea6cc488cc0d1b9721c0f5320e38c46e5c88009b7a99119cb2372e426c413d4c8a8e591b9a72e4381ea6c1c606940b90e005cf536a644646e5c8800057a9b071f8a371c026c353d4d838de91b97220c381ea6c1c606a28b90ec1c0f536a641c46e6f0a70e07a99071d0b9646e5c8703d4da994b0c61721c026de0e3286068dcb910c048f5360e30746e5c87009b7a9b5321fc1c5228dc703d4d86eb091b9721c026dea641c62a8dcfe972136f536a645446e51c7009b7a9b07181a613785c8703d4d838c0d1ba102e40b1e0e3f862c8dcb90e0136f5360e30346e69cb90e07 else 0xa99071cb28a46e5c8763d4d838c0d452373e6381ea642972c8dcb9157136f532964804a25c87009b7a9b0a581ad646e5c8703d4c8d51511b9a7282381ea6c1c5fc8dcb9104136f0719cb0346e5c87d89b7a9b5326244646e6cc703d4c838e8dcb2472e4091ea652c72c944c3972136f5360e30346e780b909b7a9b5320e2372e438051b800989119cb30346e5c9aa6c46838bed1b9721c0f5360e41646e6a8b90e07a9b532622373de3144dbd4ca26e591b97222a26dea6d4c9888dcb909b0b4f5360e36647e5c87009b7a9b53221a372e43803e3d4c838e593a2372b426dea6d4c97c8dcfc09b00af5360e41646e5c87009b7a9b5320e23f35a3804dbd4d838c0d451902e4381ea6c1c7f08dcb90ef136f536a641c46e5c87009f7a9b4b1819892e43804dbd4d857071be2372e426dea6d4c8388dcf0173136f5320e39646e5f04d82c7) else if Nat.blt b 45 then (if Nat.blt b 42 then (if Nat.blt b 40 then 0xa9b4b18199c30e3804dbd4c988c611f9721c026dea6d2c7f6628b90e0136f071cfae746e5c88009b7a9b5325f2374063804dbd4c838e591ba132e4381ea646a8a88dcf0141136f3120e3965748dcb909b7a9b071efa373fa5c84dbd4c8ff071339571c026dea6d4c83a8dcbe0e0136f536a641c4d05647009b7a9b53221a372e44304dbd4da990712899d18226dea641c72c91cb909b048e002a6cc460e8dcb90a36a9b5325f2512e45044dbc1c816d5581a371c026dea641c72c9451b99c136f536a641c4ce690ab8e07a9b07181a372e4380163d4ca58e30c39721c026dea6c546068f0a08e0136f0718c2b046e5c87009b7a9b0720a2611c026c38bd4d838b212d1721c026dea64227188dcb90e0136f3122341c72cc0d1b9727a9b5326243f46e6f0703d4d838d991b9c12e4381ea6c296068dcb90e00f8f536a641c46e704d68e07 else if Nat.blt b 41 then 0xa99071cb2472e426c02bd4c88cd093e9721c026dea6d4c97c944b909b006f53270c1c46e5c84d8247a9b532961c53145c8703d4da9915133a3734e381ea6d4c838944f78c5136f536a641c4e87e0b91067a9944dcb2512e44484dbd4d988ad11f9721c026de76c1c74c5c8890e0136f536a64464fa5c8800e07a9b0f60e30346e5c8703c1c72cae9239721c026dea641c6928dcb90e0136f536a652c8a8704b90e07a9b49e0e3035145c8703d4d8a8f711b9721c026dea6d4c97c944b915a136f5326239646e5c85189b7a9b07183a372e4380173d4c8ff1520e2371c026dea6d4c8388e0b90e0136f53614b0346e5c88609b7a9b5320e2373f03384dbd4da994b26218a2e426dea6d4c838944e0972182f071922ae46e5c87009b7a9b071572372e438051bd4d98907183a372e428dea641c7188dcce0e0136f14d9cb0346e5c87009b7 else 0xa9b5326223737815404bd4c838e5942a372e426de0e3966068dcfc172136f536a642946e5c87009b7a9b5325f2512e44304dbc1c72cc0d1b9721361bde0e3e172c8dcb909b048f2f9cb30346e5c87009b7a9b0716423f2e43804dbc7e838c0d1b9721c0119ea641c6848dcb98e0136f5320e31546e69cb90e07838e5981ad146e5c8123c1c72cc0d1b9f837826dea641c72c8dcfc173136f5360e2b246e5c87009b700153214ba372c8dcb9354da58c0d451be2e4381ea6d4c9890711b973136f5360e41446e380388247a9b07181a372f838000bd4c8d10711b9fd2e426dea6d4c838944b90fe136f1fa0e30346e6707009b7a99071c12372e43804dbd4d838c0d329681c026dea6cc4838c0d452512e4f536a641c46e80cfe89b7a9b4fd81a3737c5c8703d4c838e593a17222426dea641c72c8dcbe17c136f53694c1c6065c87009b7) else if Nat.blt b 43 then 0x838e5981a372e44d8703d4c838d151b9b31c026dea6d4ca591191b972200f3120e3966cc8dcb909b7a9907197a372f03804dbd4c838c551b9e02e426dea6d4c8388dcb91061b4f071cb2c246e5c87009b7a9b4b15d1872e43804dbd4c838c591b9f82e426dea6d4c87e8dcfe972136f536112ba46e5c87009b700153214b9646e5c84db54da991522323c1c026dea6c1c5ce8dcf70e0136f5325f31646e5c87009b7a9b5322a2373c05184dbd4da99071239731c026dea648f88d0711b9721c0f5322339646e680b90e07a9b071f7a372aa3804dbd4c853071d1b9646e5c9ea6c1c6068dcbe1721c0f536a652c8387247009b7a99071cb2374407e04dbd4d838bad1b9721c028dea6d4c989135338e0136f071c1b0346e5c87009b7838d0981a372e43804dbd4da990712397c2e4431e0e3456068dcb90e0136f5320e3d572c8dc7009b7 else if Nat.blt b 44 then 0xa9b5322a41c46e780d3bd4da990711ba002e426dea6d4c8388dcff172136f5360e30346e5c8860247a9b07173a7d2e43804dbd4d852ab91b9721c026dea6c1c5748dcce0e0136f536a644646e5c88000078fd11a0e30346e5c8703d4c838e591b972218151e2341c6aac0d1b9721c0e0020e39660691cb909b6838ecdb9b0346e5c84dbd4ca591f91b99c1c026dea6c1c5ce8dcd68e0136f536a644d46e690b90e07a9b5320e2392e438051bc1c72cc0d1b9fd2e426de0e32c6068dcb90e0136f53214c1c72c8dcb909b7989071cb30346e5c8223800a9b5322a2373c069daa641c6488dcb90ec136f5360e30348e5c8700717838cc1612372e43804dbd4d838dd51b9721c026dea64c4838e593e972136f5320e39646e8809b0e07a9b11a0e30346e670703d4da990711b9ae20026dc0041c72cc0d1b97c2e4d5360e30348e5c87009b7 else 0xa9b07181a5a2e43804dbd4d838f851b9731c026dea6d4c87e8dcb90e012ef5320e39646e704b90247a9b5320e27f2e43804dbcda838e991b9721c026dea6d4c8448dcf70e0136f536a641c4fa5c88009b7a991520e3964783804dbd4da990712817218226dea6c1c5ce944b90c1136f536a64c446e5c8a289b7a9b5320e25a2e63804dbd4da991191b9721b41f1e4541c6068dcb90e0136f5360e36646e5c88009b7a992f98c2372e43804dbd4c838e412897219826dea6d4c89a99cc38e0136f536a64465005c8700807a9b5325f2673f03804dbd4c838e351b9f82e426dea6d4c88c8dcd69571c0f5325f38d46e5c87009b7a9b071be2372e433c4dbd4da990712d1bc1de381e3f41c5748dcb90e0136f536963033fa5c87009b7a9b07176a373663804dbd4d838fe91b9721c026dea6d42852c0d1b9721c0f5320e31646e7f4b909b7) else if Nat.blt b 48 then (if Nat.blt b 46 then 0xa992020e2512e43044dbd4c838f50b91121c026dea6c1c5688dcfe972136f5320e34950c5c87009b7989071cb2c846e5c84dbd4c8fd0711b9ee1c026dea6d4c8c90711b9e5136f53631c1c6f88dcb90247a994b20e39648e5c84dbd4c838e593a1e82e426dea6d4c9891511b946136f5360e30346e5f08609b7a9b5329641c3fc5c84dbd4da58d98c39721c026dea641c6308dcfe972136f5360e30747e5c8700a378a8f85cb2372e43804dbd4d83901d1b9721c026dea641c72ca29289720aaf53240c1c46e5c87009b7a9b5322a2373885c8703d4ca58e591b9fd2e426dc0054da994b0ff172136d5360e3f846e728b90e07a99071a62372e4380443d4d838f911b9731c026dea6c1c5608f0b90e0136f5320e39646e5c88a89b7a9b07162a472e43804dbd4d97cad11b9721c026dea6c1c7be8dcf0172136f536a645446e52c7009b7 else if Nat.blt b 47 then 0xa9b07181a3f2e43804dbd4c9331f91b9721c026dea6d4c8388dcbf8e0146f536a64c446e5c8518557838e59612372e43b04dbd4d838b451b9681c026dea6d4c988a291b972146f071cb3035c08dcb90e07a994c60e39646e5c84dbd4c838e592897222426dea6c1c7dc8dcd39721c0f5360e3034a27e4b909b7a9b5322341c46e6b8703d4da990711f9731c026de3f41c6cc8dcb90e0136f5320e31548e5c87009b7a991fa0e23735a3804dbd4c838e591b972104155ea641c7188dcba0e0136f5326246a46e5c84d8097a9b5320e2513f05c8833d4da990713e99c1c026dea6d4c87e8dcd39721c0f5320e39648e5c84d8007a9b11a0e30346e5a0703d4da992f92897220c381ea6d4c8389d0ad0c1136f5323441c46e780b909b7a9b53214a372e43b04dbd4d838d991b99c1c026dc0054da991191b9ae1c0d1aa2a3e146e5047009b7 else 0xa991fa0e2512e43044dbd4c838e591b9bc13617dea641c72c8dcb90e013ef5326239646e628b909b7a9b07181a373825c8703d4c838c591b9a72e4381ea641c72c95cb90e0136f5320e3964e88dcb909b7a9b532232373923804dbd4ca591f8b915b1c026dea641c72c9d4b90e0136e002a6d4c88c8dcd68e06a99071c62373dc418703d4c838c551b972218091e6239656ea591b972136f5360e2c846e5c88009b7a9b532622374265c804bd4da990fd1b9e02e426de6244672cc0d1b9721c0f536a641c4a26706089b7838e59bd2372e4418703d4c838e8dcb2372e417dea6c1c6f8c0d23972048f53289b964a28dcb909b7a99071c62673f03044dbc1c72cc1d1b9721c026dea6d4c8388dcbe0e0136f53658c1c46e780b909b7a9b5320e2373d65c8833d4d838c0d1b99d1c026dea6c1c5d48dcb90e0136f5320e33051499d1b8e07) else if Nat.blt b 50 then (if Nat.blt b 49 then 0x838f858aa372e43804dbd4c8d51511b9a72e4381ea6c1c5848dcde0e00aaf536a652c4a27e4b909b7838e3181a373785c8703d4da58b20c39721c026dea641c65a8dcb90e0136f5320e3154b45c87009b7a9b5329dc5446e69c703d4da991922323735a381ea6d4c8388dcd39721def071c636646e5c8830e07a9b31183a372e438051bd4da190715d1721c026dea6cbe606a291b9721c0f5365bc1c46e7e0b909b7a994b23f4542e43804dbd4d838d99338e0136155ea6cbe96e8dcb90e0136f536a64468388dcd68e07a99071cb2372e426c2fbd4da994c6622372e428de0e3966069451b9bc2e4f5320e39653e8dcb90247a9b151f0a6746e3804dbd4d8a90491b9411c026de0e3966068dcf0172136f5320e39646e5c8700a37a994b20e38746e5c84dbd4d85305181a372e4381ea65137188dcb90e0136f536a643f46e6f07002c7 else 0xa9b07181a8346e5c8703d4ca593863f1721c026dea641c6608e0b90e0136f5360e2b446e69cb90e07a9b07203a3740e5c84dbd4d8a9071f0a3734e381ea6c1d5748dcb90e0136f536a641c50a5c86089b7a9b5322a2372823804dbd4c838e8d942372e4091ea641c72c8e0b90e0136f5360e3035148dcfe9727a99071cb2373923804dbd4da992f91e1721c026dea6d2c838c0ce09721c0f5360e2c846e6707009b7a9b5320e23735a4104dbd4d838bf91b9721c026dea652c838e593a172136f5360e3035148dd091727a99071c62512e441860bd4da99119339571c01f1ea6d4c97c944b909b09ef5320e31846e69cb90e07a9b5326223f46e5c851bd4da992f91b9ef1c026dc0054d8a8f851b9a71c0d536a64be4a26f0b909b7a9b07181a8c4785c8703d4da990713fa072e426dea6d42838c0d1b97c1c0f536a641c46e7cc8609b7) else if Nat.blt b 51 then 0x989071cb30346e5c84dbd4da7d49e0e3032e4381e0e3965748dcbe172136f5320e34246e7447009b7a9b5320e2402e43804dbd4da19071b31721c026dea641c62a8fcb90e0136f5369641c584a28b90e07a9b0715a2373c05c84dbd4ca58e58c3972136091ea6c54838f851b9e0136f5326241c72c8dcb989b7a9b5320e23c3fa5c84dbd4c844e591b972136091ea6c1c6d28dcb909b048f536a644646e6b4d18e07a99071cb25246e5c84dbd4d838bed1b9721c026dea6c54824c0d1b8e0136f071cb30346e5c8a08247a993966239652c5c84dbd4d852abd1b9721c026dea6446852e591b972136f5363241c6068dca78e07a990a5d1b9646e5c8703d4c838c611b9e02e426dea6d4c8528dcbf8e0136e002a6c547c28dcf009b6a9b5320e2374165c812bd4d838c091b9721c025dea6c46838c0d2e1721c0f5323545446e3804d8027 else 0xa9b5321fa372e4430123d4c8e30711b9e52e426de0e39660691cb90e0136f3120e3966068dcb90827a9b5320e2673f03144dbd4da994c214a372e4431e0e3966069451b9720a8f5329647e8fc5c87009b7a9b07181a8a2f05c8703d4da991511b9e034e381ea641c6328dcfc172136f536a64be4a25c84d87c7a9b5322327d2e44004dbd4d98911981a372e40b9ea6c4c5468dcb90e0136f5320e31546e704b90e07a993560e2372e43804dbc1c650ae91b9721c026dea64296608dcb90e0136f5360e3034ca5c87009b7a9b5320e2372f83b04dbd4c838e313397220c381e0e3966068dcbe1721c0f536a644646e6b48009b7a9b07181a672e4380663d4d838b9d1b9731c026dea6d4c83896cb90e0146f5320e3964a27a0b909b7a993120e39646e8804dbd4c852e591b9721c026dea6c1c606a3d1b9721c0f5362a2ae46e5047009b7) else if Nat.blt b 78 then (if Nat.blt b 65 then (if Nat.blt b 58 then (if Nat.blt b 55 then (if Nat.blt b 53 then 0xa99071cb25146e5c84dbd4d8a8c0d1b9a01c026dea6c547c88dcfc0e0136f536a645488ca18b90e07a9b0720a30346e5f0703d4c88ce7d1b972200381ea6c1c8248f0d39721c0f071fd39646e5c87009b7a9b071642372d03804dbd4ca59311cb2372e426dea6d4c87e968de0e0136f5360e3625688dcb909b7a9b5326224246e5c84dbd4c838e591b9fe2e426dea641c70661cb90e0136f536a641c4a45c86189b7a994b23f1721c026c123d4d8a8f851b8e0136089e0e3966068dcb910c048f5360e30346e83cb90e07a9b532961fd2e43044dbd4da990a51b972282431ea641c69299d1b8e0136f5320e31648e5c87009b7a9b532962053fa5c84dbc68838f851b9721c026de0e3965ce8dcd68e0136f0718c30346e5cc7009b7a9b5322a2372863804dbd4da990711b97320026de0e3b972cc0d1b972048f5325f38c4a28dcb909b7 else if Nat.blt b 54 then 0xa9b07164a372e43804dbd4c838e311b9721c026dea6d2c60661cb90e0136f071cb3034ce8dcfc09b7a9b5320e2392e43804e3c1c72cc0d2d1721c026dea6c296068dcfc1721c0f5360e2bb46e69cb90e07a9b5320e2512e83044dbd4da991512e14f1c026dea6d4c8a88dcc98e0136f5323941c46e5c87009b7a9b5322323735a6b4703d4da990fd1b9bc2ae381ea6c3f7c28dcb90e0136f536a652c3fc5c87009b7a9b532961872e63804dbd4d838d991b9ee20c381ea6d4c97ca3928972136f5360e30346e5c8800827a9b53214a472f83804dbd4c9890718c2372e426dea641c7188dcb90e3136f536a641c46e7cc830e0790107181a372e43804dbd4c838e591b9ad20026dea6c1c6cc8dcb90e015cf5320e39646e7e04d8597a9b5326641c46e5fc4dbd4da990711b9b320026de0e39c6068dcb90fb136f536a641c48e5c87789b7 else 0xa9b53214a372e4430863d4da993122a23734e381ea6d4c838968de0ef136f0719430346e5c8700447a9b07181a373383804dbd4da990711e1a72e4381ea6d4c838944f7106182f5320e3284fa5c87009b7001532354544783804db54da9931128a372e428dea641c62c968b90e0136f5360e3035148dcf01727838d39612372e43804dbc1c6ccca11b9721c026dea6471838970b90e0136f5368641c5905c87009b7a9b53214a372f8430123d4da9907128a033f226de0e330606968b90e0136f53247c1c46e5c87009b7838d095a2372e43804dbd4da993111f97221826de0e3965688dcfc172136f536a64544725047009b7a9b07181a372e43784dbd4c852e591b972136111ea6c1c60699d1b97c1c0f5320e3965148807009b7a9b3120e2b446e5c84dbd4c838e591b9f82f026dea6d4c88c9f4d69721c0f536a641c46e70cb90e07) else if Nat.blt b 56 then 0xa9b5329b18f2e43804dbd4d838f851b9721de26de0e3966068dcb911a1c0f5360e30746e5c87004770015329648f2e43804db54c838ca12897218226dea6c1c6cc944b9106182f536a64c446e5c8518097838e31572372e43804dbd4da85071338e01361c5ea6d4c8389d0b90c1136f536a644688c8dcd68e07a9b5322a2373be5044db800a9b071be30346e5f1aa6c3f5908dcb90ef136f5329648046e5c87009b7838ca581a373785c8703d4da990712d1721de26dea646a8a90711e0e0136f5329641c72c944b909b78fd07181a372e43804dbd4da990711ba093c05c9ea652c9c28dcb90e0136e002a6c2960691cb90e06a993320e39646e5c8413d4c838c611b972218091e2341c654c0d1b9721c0f5360e2c8514968b90e07a9b5322a2862823804dbd4c838e5928a262e426dea6c1c6069f4de1721c0f5360e30346e644b90e07 else if Nat.blt b 57 then 0xa9b5320e2673dc418703d4ca591fa3b9721c026dc0054da991191b9b31c0d5362341c6068dcb90e07838f858c2372e43804db800a591f9819721c026daa641c692a291b9721c0f536a643f46e704b90e07a9b0720a2371f626c38bc1c72cc0d1f9721c026dea6c1c6068dcfc0e0058f5360e2ab46e5c87009b7a9b0717c2372e43804dbd4da991193e9ad1c01f1ea64f78385c8890e0136f5329648f8385c87009b7a9b12a0e2373825c8703c1c73eb9d1b9721c026dea6c1c606944de172182f536a64be4e899cb909b7a9b0a60e30348e5c8703d4c838e5938a372e426dea6c1c5688dcb910c048f536a64c4838944b91067838c5573a372e43804dbd4da990711e1e02e426dea6d4c8388dcfe9a42e4f5360e37c6068dcb905f7a9b4ee2a3e146e3804dbd4d896b451b9721c026dea6d4c838944b90c3136f5322341c72c8dcbe09b7 else 0xa9b07165a372e43804dbc1c72cc0d452373f05c9ea6d4c89a99c9f0e0136f5322341c72c9f4b90e07a9b5320e23f2e43bc4dbc1c650b211b9721c026dea6c538288dc7009b0e2f5320e3964d48dcb909b7a9b071b32672e4418703d4c838c591b9c12e4381ea6d4c97c9451b9ee136f536a64be4a25c88309b7a9b4b1fc19c2e43804dbd4da990a51b9bc1c0155ea6d4c83891cb910c1c0f536a64468388dcd98e07a9b0715d2372e43804db800a9b5321fa37378381aa6d4c8388dcb910c106f5326d41c72c8dcbe09b7a9b0715d2372e438055b800a9b07181a372fe381a9647e838c0cb90e0136f536a645446e69cc38e07a9b1860e23738a5c8703d4da990fd48a371c026dea641c62c8fcb90e0136f5360e30351499c700717a9b5322a23741669c703c1c718c0d1b97220c381ea641c73e8dcb9100136f5322a44672c8dcde0e07) else if Nat.blt b 61 then (if Nat.blt b 59 then 0x8d507181a373c05c84dbd4c8d50711b9721c028dea641c72c8dcb90e0138f071cb2fe46e5c87009b7a990718aa373383804dbd4da993120e2373de26dea6c635a28dcde1721c0f53261b965148dcb909b7a9b5320e28a2e43802f3d4c8a8f3dcb2371c026dea6c1c60691cb90e00aaf5320e38d47e5c87009b7838e596128a46e5c8703d4d838fe11b9fd3825c9ea641c7188dcb90ec136f071cb30346e5c84d8307a9b5320e2373825c877bd4da992fa5f2512e426dea6d4c988a011b972136f536a646487e8dcde0e07a99071cb2372e826c123d4c83ae591b972136091ea651b52c8dcfc172136f5360e30348e5c8ac0e07a9b071fc2372e4418703d4c88cd091b9722001f1ea6cbe6f48dcb90e0136f071ab30346e5c87009b7a9b0720928c46e5c8703d4c838e591b9831c026dea6d4c87f0711b9bc1c0f1aa0e30346e69cb90e07 else if Nat.blt b 60 then 0xa994b23fa672e43804dbc1c72cbed1b9721c026dea6c1c5688dce09721c0f536a643746e5c87509b7a991c20e2372e43804dbd4c9db071cb2372f826de0e3966068dcb9024002f5327441c72c8dcb909b7a99071cb2373045c84dbd4ca591f8b90e0136001ea6d4c9888dcb9144146f536a641c46e7f4c009b7a99071cb2372f826c223d4da994b2622031c026dea6c1c6068dcb90e013af536a641c46e6f07005c7a990718c2373825c8703d4da990711b9ee1c026dea6d4c8748dcb90e0136f5360e40046e704b90e07a9b53265a372e438040bd4c838d091e1721c026de3241c72cc0d1b9721c0f5362a3e146e7807009b7a99071cb23c3f05c84dbd4da990711b9f821026dea652ca591f8b90e0136f536a641c5228dc7789b7a9b07181a3736e5c8703d4d896f6d1b9721c026dea6c296f8c0d1b9721c0f5360e2c85228dc700557 else 0xa9b5320e2673f03a44dbd4d83ac0d1b9721c026dea6c1c6068dcb90e004cf536a641c51464cb90e07a99071cb2472e43044dbd4c8e30711b9721c026dea64c488cc611b972136f5360e3df46e6707009b7a9b5325f2743f05c84dbd4d838c0d1b97c1c01e5ea6d4c89b071338e0136f536a641c46e780d21727a994b23f9892e43804dbd4d87ec0d1b9721de26dea64f4838d08b90e0136f536a641c4785c8860247a9907194a372e43804dbd4d88d08181a372e4381e0e396606a7d1b9721c0f536a643f46e6f0d18e07a9b5320e27d2e43804dbd4da991194423735a381ea6d27838c0cb90e0048f536a641c46e7c4b910c7a99071cb2373c65c84dbc1c72cc0d1b9bc2e4091ea6d4c9888dcb90a3146f5360e3034b46f0700557a99071cb2373f045c4dbd4d838c0d451721c0239ea6d4c8388dcd68e0136f536963df30e5c87009b7) else if Nat.blt b 63 then (if Nat.blt b 62 then 0xa992420e2372e43804dbd4c8d10711b99c1c026dea6d4c8528dcde172218f071922c246e5c87009b7a9b071612372e438051bd4da99071339661c026dea6c58852c0d1b9721c0f07205b966068dc7009b7a990a5cb2372e426c4dbd4d838c0d452742e4381ea6cc48a8f851b8e0136f53661c1c6068dcb90e07a9b07181a373dc418703d4d838bad1b9ae1c026dea6c1c606970b90e0136f071cb30346e5c88009b7a991aa14a372e43804dbd4da990a51b972218005ea6c1c7c28f0b90e0136f536a645446e69cd38e07a9b0715727d2e43804dbd4c9ab1511b9e028226dea641c736968b90ef136f536a64c447e5c84d84f7838c5973a372e43804dbd4da993111f9bc2e426dea652c8d061cb90e0136e002a6cc36068dcb90e06a990a5cb2372e426c1b3d4c9b50711b97226c381ea6d4c87e8dcb9100136f536624465688dcb909b7 else 0xa9b0716423737838038bd2c72cc0cc39721c026dc0054d88cdcd81a372e4d536a64544788dcd38e07a9b53268c4646e6f0703d4c852e591b972136209ea6c1c7f099cab8e0136f5321fb304b45c87009b7a9b07181a373785cc703c1c650c0d1b9721c026dea6d4c9a08dca08e0136e002a6c1c5e68dcde0e06a9b5320e2373f05c8833d4da991511b9e034e26dea6c1c6068dcb48e0136f5360e2ca46e5c8830e07a9b5320e27e2e43804dbc1c72cdbd1b9721c026dea6d4c97c8dcb91061c0f5320e31853e8dcb90e07a9b071572512e43044dbc1c72cc0d1b9720f8091ea641c7368dcb909b048f536a641c46e7dc7009b7a990fdcb25a2e43804dbd4c838ca11b9731c026dea6d4c8388dcfc1bc20cf536232e75a28dcb90e07838e5981a372f85c84dbd4da991611b9421c026de0e38c55e8dcb90e0136f5365bc1c4a27e4b909b7) else if Nat.blt b 64 then 0xa9b532622372e426c053d4c9070a51b9721c026dea6c547c28dcc38e0136f5360e30346e5c8700a67a9b5322a23c46e7804dbd4d838b211b9721c0209ea6d4c9888fcb909b0f8f5320e39046e5c8830e07a9b5320e27d2e43884dbd4d838c0d48a371c0155ea6c1c6f8c0d1b97c1c0f5360e3034a25c8830c179c3071fc2373fa5c84dbd4da993111b97c136025ea6d4c838a28b90ee1c0f5323f43f46e5c87009b7a994b18b1872e43804dbd4da99312232372e4431ea641c72ca291b9720bef536a641c47e7bc7009b7a9b11a0e3736068dcb93d4c838c591b9721c02edea6d4c838a451b8e0124f53614aba48e5c87009b7a9b5320e2373dc3b04dbd4d838c0d1e0e01361c5ea641c72ce1d1b972136f536a641c47a5c87009b7a9b532232374246f8b93d4da990713a15718826de0e3185ce8dcb90e0136f536a64465148dce48e07 else 0xa991fa0e2372e43bc4dbd4da991191b9fd2e41f1ea6c295848dcb90e0136f5320e39646e5c84d8247a9b071fc2373fa6704dbd4ca58e34c39721c026dea6d4c87e99d2d0e0136f5320eb1546e5c87009b7a9b12a2341c46e5c8703c6b838c0d1b9721c026dea6c296068dcc39721c0f536a644687e8dcde0e07a99071982372e43a84dbd4d88d07181a372fe381e0e38c56c8dcb90e0136f0719cb0346e5c8700ac7a9b53214a372e44303e3d4c852e591b9721360b9ea6c1c6068dcb90e0122f536233034fa5c87007c7a99311cb2372e428c04bd4c8d50711b9cf1c026dea6d4c838a291b9f3218f5320e39646e5c87509b7a9b5320e2374183804dbd4da990711e1c12e4381ea641c62c8dcce0e0136f5326543f72c8dcb909b7a99071d1b9646e5c8123d4da994b0c39721de26dea6d4c8388dd039ad136f5320e39646e69cb90257) else if Nat.blt b 71 then (if Nat.blt b 68 then (if Nat.blt b 66 then 0x8e9071f0a372e43804dbd4c838e5913172136091ea641c72c9e91b9721c0f5365b41c7f08dcb909b7a9b5325f2373d65c84dbd4c87f071cb237378381e0e32a6068dcb90e0136f5360e30348e5c8700097a9b5329618a2e43804dbd4d8bd0711b9cc2e4381ea641c6308dcb90e0174e002a643f6608dcde0e06a9b071f0a373485c8703cc496f071cb2372e426dea6d4c87e8dcb9104136f53626bf846e5c87009b7a9b53214a8e46e5c8863d4c838e8dcb2372f826dc0054c87ee591b9bc1c0d536a64be4a27e0b909b7a9b0a5b72ba46e5c84dbd4d838f8d1b9721c026dea641c6308dcce0e0136f53289b964ce5c87009b7a9b532622372e427004bd4da99312232832e4381ea64ed989070b9112136f53686c1c7c25c87009b7a9b07181a672e4418703d4d838c0d28a472e4381ea6d4c88c8dcd70e0136f1fa0e3f846e7f4b909b7 else if Nat.blt b 67 then 0xa9b3120e30346e5f0703cbe718d991b9721c026dea6c1c6068dcb88e0136f5369641c5f6a28b90e07a994b24447e2e43804dbd4da993111b972146015ea6cbe6068dcb90e0048f5360e303514944b90e07a9b3115a2372e65c84dbd4c838e591b9ae1c026dea641c72ca28b90e00bcf5369fc1c5f68dcb90e07a9b11973a372e44003e3d4d86eb211b9721c026dea6d2c988c0d451721c0f071cb30346e5a07009b7a9b1620e30346e5f0703d4da9910d1b9721c025dea643f838cc11b9bc1c0f5325f38c46e7b87009b7838df19430346e5c8123d4ca5946e769721c026de3f41c5688dcb90e0136f536a641c4ce8dc7509b7a9b07205af346e3804dbd42838e5981a372e4091ea651b988a591b972136f536a644646e6b47009b7a9b532232502e43803e3d4c91b0711b9721c0109ea6d3f988c0d1b9721c0f5323541c46e5f07009b7 else 0x838ce581a373785c8703d4c838e311b9bc1c0155ea6d3f838c0d289721c0f5325f38c4a25c86089b7a990a5cb2373185c84dbd4da991511b9a72ae381e0e3966cc8dcb90e0136f53272cc472c8dcb909b7a9b0a581a372e4380083d4c838e591b97226c331ea6c1c6068dcfc1bc00af536a641c46e6cc7009b7a9b07173a372e4380563d4d838dbd452372e4381ea6d4c87ea292d1721c0f5362a3e146e69c7009b7a9b5320e2673fa55c4dbd4da990711b9e12e426dea641c66099c700b5136f536a641c4e25787009b7a9b1120e3f846e5c8703d4c838e593d2262e4381ea6d4c87e968de0e00aaf5360e30346e6a8b90e07a9b07205b035148dc703d4c838ccd33a371c026dea641c68a8dcb910c104f071cb2b447e5c87009b7838e595ba5146e5c84dbc1c718d991b9f82e426dea6d4c87e8dcf2972136f5360e3034e291cb90e07) else if Nat.blt b 69 then 0x838d5581a8a46e5c8703d4da990711b9bc1d4155ea6cc4838c0d1b972146f5320e3304a25c86089b7a9b5322a23734e4f8703d4d838b0d1b9721c026dea6d4c88c8dcf01720f8f53214b9646e5c8a109b7001536232f346e5c870354c838e592897218226dea6c1c7c28dcf01a72e4f5362a3e14788dc7009b7a9b07181a3730e5f0703800a9b31181a372e428daa6c1c82702d81a371c0f5320e3455065c87009b7a990719827d2e43804db800838e5981a372e4209aa6c1c6068dcde0e00f4f5320e3964968dcb909b7a9b5322323735a380173d4c8d51511b9411c026de0e39b5908dcb90e0136f071cb30346e5c8700447a9b071572372e63804dbc1c6cccc11b9721c026dea6c1c5da8dcb910c104f5360e2ba46e5f0860247a99151cb23729e3804dbd4c838e593e9721c026de0e32a6068dcb90e005cf5323541c46e5c87009c7 else if Nat.blt b 70 then 0xa9b5322a237354518703d4c838e811b9721c010dea641c62ca791b9721c0f536a644646e5c8a09007a9b5322a2373123804dbd4da991511b9461c026dea641c6848dcb91061c0f5323f41c4785c87009b7a9b072092371c026c38bc1c72caf91b9721c026dea6c466e6c0d1b9721c0f5362a41c8248dcd38e07a9b5320ea372e43bc4dbd4da990711e19c1c026de89b966068dcb90e0136f5360e36e5748dcbe09b7a993960e3964a25c84dbd4c97ce31339721c026dea6c1c5628dcb90e0136f0720a3966068dcb90247838d3d5a2372e43804dbd4da9907148a3729e381c0054d8a90491b9a71c0d5326241c7468dcb90447a9b071f725c2e43804dbd4c83ee591b9721c026dea6d4c838a291b9721d4f5320e39646e7e06209b7a9b4fe9630330e5c8703d4d88d07179a372e4381ea6d4c838a292d1721def1fa0e3035148dcb90e07 else 0xa9b07165a8a46e5c8703d4d98911981a372e4025ea6c1c60e8dcb90e0048f3760e30346e5c87009b7a9b072092372e438012bd4d8a8fbdf0a371c026dea6c1c6ee8dcb909b040f0718b30346e6f0b90e07a9b07181a3740e5c84dbd4c989119cb2372e4431ea6d4c8388dcde104124f536a641c4e85c86609b7a9b07181a392e43804dbd4da9931146a3f2e426de0e3305908dcb90e0136e002a6d4c8a88dcd38e06a99071cb2372e426c20bd4da990712397220c381ea652c8fc5c8a40e0136f53238c1c4ce8dc7009b7a990719828a2e43805abd4da991351b9fd2e426dea6d428388dcb40e0136f536623e446e5c8a309b7838e59642372e43804dbd4da99071451781c0155ea6d4c8388dcfc0c6136f0719430348e5c8700247a9b53214a372e44302c3d4c838ccd452372e4381ea6cc488cc0d28a372e4f071cb3034ce8dcb90247) else if Nat.blt b 74 then (if Nat.blt b 72 then 0xa9b532232372e4430803d4da990a533a372e4431ea6c1c7be8dcb90e0136f5360e30346e5f0700107a9b5322a41c46e7804dbd4c838ccd1b9bc1c017de0e38d6d28dcb90e0136f5327841c46e5c87009b7a9b0a581a372f85c8703d4da991911b9411c0249ea6c1c6068dcef972136f536a64be4a25c86289b7a9b532964543123804dbd4c838c991b9721c026dea652c8fc5c8700c1136f536a64c446e62cb909b7a9b07181a8a46e5a0703d4d988ae91b972136025e0e31555c8dcb90e0136f071cb2af46e5c84d8247a9b5322327d2e438009bd4d838c0d431721c026dea6d4c83899cf0157136f5360e30346e6f0b90ef7a99119a12372e43803e3d4c88ce591b9f82e41f1ea6d4c8388fcb90cc136f53221b9646e7e0b909b7a9b5320e23741e3802abd4c838ca11b9721de26dea6d4c8a90711b9a71c0f5362a41c60691cb90e07 else if Nat.blt b 73 then 0x838e5981a373785c814bd01838e591b9721c026de3641c6068dcb90e0136f5360e30346e5c8628247a990719da372e43804dbd4da990713e9bc1c0155ea646a8388f0f0172136f536a64c446e5c84d8147a9b071b9b0346e5c84dbd4da990711f9731c028dea6d4c989119472372e4f5323641c46e5cc7009b7a9b2f9b32512e43044dbd4c988c611f972136025e0e3966068dcb90f9136e00214b286068dcb90e06a9b1215d2372e43804dbd4c8530a5cb2372e426dea6d4c8768dcd68e0136f532964dd46e5c87009b7a9b071be30346e5f04dbc1c736c0d1b9721c026dea6c1c8208dcd21721c0f53614b0348e5c87009b7a9b5320e28035c3804dbd4c88ccb11b9721c01f1ea6d4c83899d1b9f820cf0719c30346e5c87009b7a9b5320e25a2e4418703d4da99071339f93f026dea641c7208dcf98e0136f536a641c5228dc778557 else 0xa9b311b32372e426c04bd4d97307181a372e426dea6c1c6068dcbe0e0058f536a64c446e6b44d809797ce3181a372e43804dbc6a88d07181a372e4381ea6d4c87ea29289721c0f5360e41446e5a07009b7a9b5320e2513783042abd4da990711b9a4338381ea6c547c28dcab8e0136f5328da9f52c8dcb90e07a9b532232373663804dbd4c9a3071cb2372e426dea641c660a28b90e009ef536a641c4765c87009f7a990719825a3785c8703d4ca591f8e99721c026dea641c6488dcbe0e0136f071cb30746e5c8700a37a9b5320e2372f838051bd4d838c1d1b9bd2e4381e0e3a672c8dcfc172136f5323fc1c46e710b90e07a9b5322a28a46e53c703d4d988ad11f972136025ea6d4c9888dcf709b012f536a645446e69cd18e07a9907194a373783802abd4da990711ba031c026dea6d4c98699cb90e0136f0a60e3286068dcb90e07) else if Nat.blt b 76 then (if Nat.blt b 75 then 0xa9b5325f25130e5c84dbd4c8a9071cb2373f026dea6c546068dcd39411c0f4060e39644c5c87009b7838e31612372e43804dbd4da991351b9e02e426de0e396606a6d1b9721c0f5365f3664ce5c87009b7a99071cb2372e63804dbc1c684c0d1b9721c0091ea6d37838c0cb90e0136f5366741c46e5c87009b7838e5981a373f05c8123c1c72cc0d1b9721c626dea6d4c88c8dcd98e0104f536a643f46e5c87009b78d50715d2372e43804dbd4da990711f97220c381ea6d4c83899cb910c198f5323f41c46e690b90e07a99071cb2472f826c123d4d9630711b9721c026dea6d4ca587f4b909b09ef536a643f46e6f07009b7a990718aa392e43804dbd4d8bd0711b9bc2e4381e0e38c6068dcfc172136f5320e39a46e5c87509b7a991fe0e2373383804dbd4da994b0fe9bc2e426dea6c1c6068dcbf8e0136f5360e2aa46e5c87009b7 else 0xa9b15225be146e3804db800a99071cb26b2e426daa6d4c838944f717220cf5360e2c246e5c87509b7a9921a0e2372e43804dbd4da5912a0e1721c026dea6d4c8388dcde0ef136f536a64c447e7e0b909b7a9b071642373783802abd4da9907133957218091c0041c72cc0d23972048d5362a30346e780a089b7a9b5322a23728238051bc1c72cc0d1b9721c0209ea6d4c8389acb90e0136f5320e39648e5c86609b7a9b071be2372e426c183d4c98b071cb2372e426dea6d4c9888dcb910c05cf5360e37a46e83cb90e07a9b07181a472e4380123d4da990fd1b9721c0209ea641c72c8dd100e0136f5365f3f846e5c87009b7a9b532622372e426c293d4da994b20e2031c026dea641c6608dcb98e0136f071cb30346e5c87009b7838e5981a3737838038bd4d8a8f851b93e1c026dea6d4c8388e0be0e0136f5320e3964ec944b909b7) else if Nat.blt b 77 then 0x838e5981a372e4380173d4c838c611b9721c026dea6c1c80e9fcb90e0136f5360e3e14ce55c7009b7001536a644346e6f0703000a9b151f0a371c026da3541c6cc8dcb90e0136f5360e40046e5c87009b7a9b311642372e426c04bd4da993111b9721b426dea646a8388dcd68e0136f5360e3034b45c8700247a9922a2a41c46e3804dbd4da990711b9721de209ea6c54838bf91b9bc1c0f071cb2c546e5c87009b7a9907192a372e43804dbd4da9907128a112e426dea641c7188dcb9115136f1fa0e3f846e704b90e07a990718c2372e438c4dbd4da990711b99c1e226dea6c1c60691cb90e000af536a642946e7e0b910c7a9b07181a372fe380173d4d838c0d45a372e4381ea6d4ca587f4b909b0f8f536a653b31255c7009b7a9b5320e2422e63804dbd4c8d50711b9ee1c026dea6c1c7f08dcfe972136f536a641c46e5c87789b7 else 0x8d5071f0a3c2e43804dbd4da59072001721c026dea6c1c5ce8dcb91061c0e002a64c46308dcb90a36a9b532622372e426c093d4da99152232373c026dea64f68385c8700b4136e0000042972cc0d1b9725a9b53214c1c48e5c8863d4ca58e59131721c026dea64c4838e591b97220cf53661b0346e5c87009b7a991aa0e2512e43044dbd4d838da11e1721c026dea6c3f56a8dcb90e0136f5369641c7f07f4b909b7a9b5321fa8a4ce3802abd4d838c0d1b97c218091ea64ed838e0cb90e0136f5369641c590a28b90e07001536a642948e5c886354da991522323734e381ea6c1c5688dcb90e0136f536a64438388dcde0e07a9b1520e3e146e3804dbd4d838ad11b9721c02adea6d4c88c8dcb9104124f071cb2b746e5c84d8247a99151a4a372823804dbcd5838c0d1b9e02e426dc0054da58fe0fe972136d5324cc6a46e5c87009b7) else if Nat.blt b 91 then (if Nat.blt b 84 then (if Nat.blt b 81 then (if Nat.blt b 79 then 0xa9b5320e2372e4418803d4d838c091b9721c026dea6d4c97c8dcfc172136f536a141c46e6f0700717a9b532622372e428c013d4d838c0d1b9721ee26dea641c72ca5d1b972136f536a141c46e5c8700ab7a9b5320ea372e4380503c6a838c0d1b9721c0109ea641c7188dcb90e013ef5360e30346e5f0ab8e07a9b07179a373783804dbd4d8b4a8d1b9721c026dea6d4c87e8dcde1721def53289b9630e5c87009b7a99071c627446e5c84dbd4d838c0d1b972218331ea6c1c6068fcb90e0048e002a6cc45688dcb90a36a993120e31846e5c851bd4d838c0d23a372e4381e0e3966f8c0d1b972048f5360e41446e380560717a99071cb25146e5c851bd4da99071289721b426de0e38c6f48dcb91061c0f532623cf72c8dcb909b70010a60e3966068dcb9354c838f451b9121c026dea6c46838de91b9721c0f5360e37b46e5c87009b7 else if Nat.blt b 80 then 0xa9b5320e2372e4588863d4c838d093e9ad1c026dea6cbe606944b90c1136f5360e2c24fa5c87009b7a9b0720923c2e43804dbc1c7bee591b9721c026dea64e18388dcfe9c12e4f5320e39646e7e04d8057a9b135f0a372e43804dbc29650ae91b9721c026dea6d4c8388dce11721c0f5320e3a346e5c88d0e07838e5981a9a46e5c8123d4c9cb071cb172136091ea6c1c7ee8dcb90e0136f5366230746e5c8518097a9b5321ba372e43bc4dbd4da990711b9bc1c0249ea6d4c83891cf98e0136f536232e746e5c87007c7a9b5322a24228c3804dbd4c838e591b97c136155ea641c72ca291b97c136f5360e3f846e69cb90e07a9b0715823734e5c8703d4d9890715a2372e428dea6d4c838a29338ef0aaf5360e2c946e5c8700a370015320e3964a25c883354d838bcd1b9721c026dea6c466e6c0d1b972136f5320e3164725c87009b7 else 0xa9b5320e23c2e43804dbd4da991511b9511c026dea641c72c8dcbe09b0bef5362f41c46e7f4e09727a9b31181a372e426c04bd4d838c0d1b97c1c01b5e6241c74ce591b972136f5360e2b44725c87009b7a9b1520e3dc46e3804dbd4c838e592397213613dea6d4c86e8dcbc0e0136f5320e39648e6f0b909b7a9b5320e2374125c8703d4da993111b973136025ea6c1c60691cb90e0000f5360e2fe46e5c8700247a9b19181a373405c8703d4d838b092897218226dea648f8388dce48e0136f536a6446838a0cb90e070015362a3dc46e3804db54c838c611c9721c026dea6c205688dcb90e0136f5360e30351e984b90e070015360e3664a27b84db54d838d991b97221a381ea6d4ca587f4e09872e4f5320e32846e7407009b7a9b07181a8a46e5c8703d4da5907181a472e4381ea6d4ca5861cb91061c0f5360e2b046e780b909b7) else if Nat.blt b 82 then 0x838fe1a12372e43804dbd4d8a907181a8a4ce381e0e3f872c8dcfc172136f536a641c46e828b90e07001071cb30346e5c82fb41c72cae923972136091e0e396606a28b91121c0f536a641c46e7f4bb09b7a991fa232372e43803e3d4d88caf51b9721c01f1ea6c1c8288dcde0e00e2f536a641c4ce418700557a9b13a0e3035145c8703c1c6a4c591b9721c026dea6c1c7de8dc7009b0e0f5321fb3046e6f07009b7a9b07181a372e43802fbcc4838e5981a372e4091ea641c72c8dd02972136f536a644646e6707007c7a9b5326223f2e43144dbd4d838c0d1b9bc1c017dc0054d838c0d1b97c1c0d5360e2ba46e5c8700a37a990a5c62372e43804dbd4d988c0d1b972104025c0054da990712397c218d5365f3034ce5c87009b7a9b5320e2372fe3044dbd4d87eabd1b9721c026de0e3b96068dcb90e0088f536963f833861c7009b7 else if Nat.blt b 83 then 0xa9b5320e26738855c703d4d838d991b9721c028dea6c1c7f08dcb910c048f536a641c46e6b4700a379bb2de0e2372e43804dbd4c838cc11b9721de26dea6d2c96e7e4b90e0136f536a64c48528dcb910c78d507181a372e43804dbc1c7f0cb11b9721c026dea641c6608dcde0ef136f536a645446e6847009b7a993460e3964ce8dc4dbd4c838e3128a372e426dea641c72ca591b97c136f536a641c46e6d8b90ea7a99071922373dc3804dbd4da990711b9ee1c028dea641c72c8dcde0ef136f5360e30346e5c8800247a9b5326244646e7e0de3d4da991091b9721c026dea641c6628dcb90ef136f5362a4467c28dc7009b7a9b5320e2671c026c253d4da990713395720026dea6c1c5748e0b90e0136f5360e2af46e5c87789b7a9b071be2372d03804dbd4c838e59239721361f1ea6c5488cbf91b9721c0f536a644346e840b90e07 else 0xa9b5322341c46e5fc863d4c988c611b9721c028dea6c1c6069acfc1721c0f53289cda46e5c87009b7a9b3120e30346e6cc703d4c838cc11b9781c026dea6c1c8108dcb90e0136e00214b966068dcb90e06a990719a2372e43804dbd4d88cbcd1b9721c026dea652c838e3128972136f5360e30346e670700247838cc181a6746e3804dbd4c838e591b972136065ea6d4c9888fcc3972136f5366230346e5c85189b7a9b07181a372e4420703d4c9a90711b9721c026dea6cc4568a911b972136f071d3b8346e5c87009b7a9b071bd2512e441860bd4da991511b9411c0271ea6d4c8528dcb910c106f5369630330e5c8700247a9b532662372e420804bd4c988c551b972136025ea641c72c8dcb9147136f536a652c988a38b909b7a9b4b1fc1fd2e43804dbc6a838f951b9721c026dea6d4c8388dcfe9a72e4f5320e39646e834d689b7) else if Nat.blt b 87 then (if Nat.blt b 85 then 0xa99071c1a373f05c84dbd4c97cd091b9721c026dea64be72c8dcfc172136e002a652c8fe5c87009b6a994b23f1fd30e5c84dbd4da993114017221826dea6c1c5848dcb98e0136f5369bc1c5e65c87009b7a9b18d702d146e5c8703d4c838e591b97c136025ea641c72c944b91061c0f536a64cc88c8dcd68e07a993562a2372823804dbd4da994b0fe99c30e26dea6d4c986944b90cc136f5360e37a4ce5c8830e07838d0974a372e43804dbd4d838dcd81a8a46e5c9ea6cc45688fd1b972136f536a641c46e5d0830e07a9b5320e23737853c703d4d988ad11b9721c028dea6d4c88c8dcb90e0124f536a641c4ce8dc7789b7988e5981a9646e5c84dbd4da994b21fa671c026dea6c548248dcd38e0136f5320e34946e6b47009b7853071cb30346e5c8703d4da991191b9bc1c0249ea64c46308fd1b972136f5320e3964a28dcbe09b7 else if Nat.blt b 86 then 0xa9b071f728a46e5c8703cb7838e591b9721c026dea6c1c6068dcb90e015af536a652c988a28b910c7838e5981a373783802abd4c8a8e5928a3728226dea6d4ca58704b90e00f8f5360e3664a27b87009b7a9b071fda373fa5c84dbd4c838ca11b97220c381ea6c1c7f08dce09721c0f53289ced46e5c87009b7a9915214b9646e5c84dbd4da994b20e2671de26dea6d4c83899cf88e0136f5320e39646e7e0b91367a9b07181a372e4434703d4da994fe622372e4431ea6d4c87e8dcde1a01c0f536a64be48e5c87009b7a9b5326223740626c04bd4c9db070b91121c026dea641c6848dcb9116136f5320e32f4b45c87009b7a9b5322a23734e3804dbd4da990fd2d237378381ea652c8ff070b90e0136f071a13034fa5c87009b7a9b53214a7d2e43804dbd4c838e7d1ba0d2e426dea6d4c88c8dd089721c0f536a641c46e5dc7009b7 else 0xa9b5320e27f35a3804dbd4da9931d1b9721c026dea6d4c83891cbe10c1c0f536a64be4ce8dcfc09b7a9b5325f25a2e43804dbd4da990711b9bc1de155ea6c1c5748dcbe0e0136f532354548388dcf009b7a9b07181a373725c8703d4d838dc11b972136081ea651b7068dcb90e0136f53693c46606b44b90e07a9b071ff2372e43804dbd4da9911933a372e4401ea641c72091cb90e0136f5320e33246e7b87009b7a9907199a372f83804dbd4da990711b9801c026dea6d4ca587f4fc172136f5362341c6068dcbe0e07a9b5320e2373c069cb93d4d8a907181a3c1c026dea651b52c8dcb90e0136f536a641c46e7f4e29727a9b07173a7d35a3804dbd4c88ce591b9722001f1ea6d4c97c944b909b102f5362a3fa46e5c87009b7a9b5320e2673563804dbc1c660c0d1b9bc1c0155ea64898388dcb90e0136f5327741c2e43805a89b7) else if Nat.blt b 89 then (if Nat.blt b 88 then 0xa990a5d1b9646e5c8123d4d8a911981a37282381ea6c1c590984b90e0136f5362a4036068dc7009b7a99071962372ec3804dbd4d838c1d1b9731c026dea6c1c7c28dcfe972136f5328dc1c72c91cb909b7a99071cb2373f06104dbd4d838b211b9b62e4381ea641c72c8e0b909b048f071cb2cb46e5c84d85f7a9b5320e2373be690b93d4d838df11b9bc2e40a5ea6d4c9888dcb9146136f5360e4005148dcb90e07a9b5322a23c3c05044dbd4ca36a59131721c026dea6c1c80e8dcd68e0136f4b20e396606a28b90e07a99071afb1646e5c84dbd4c852e591b97222426dea6d4c97e968b90e0136f0718c2b746e5c87009b7a993118b2372e426c04bd4d8c70651b9721c026de14b286068dcb90e0136f536a641c46e5c8860827a9b5320e2671c026c2bbd3f838e5981a372e4381ea6c1c6068dcbe0e01c0f5369f41c6068dcb90e07 else 0xa9944dd1a372e43804dbc46838d0973a372e4381ea6c59838c0d1b9721c0f536a641c46e848e09727a9b312232ed46e5c8703d4c88cca91b9721c01f1c0054d838c0d1b9bc1f6d5360e3785e68dcb909b7a9b5320e2372e43684dbd4da990712897c18226de0e39660691cb909b048f536a641c50a5c86389b7a9b5322a4464fa5c8703d4ca591f8b90e013613dea64e5838c60b90e0136f0719430346e5c8700247a994b23f1bc2e43804dbd4c838ca1339571c026de0e3966068dcbe172048f5360e37c46e6f0700717a9b07173a5e2e43804dbd4c989119a2a372e4381ea642972c8dcb909b048f5360e30346e7cc700cc7a993560e23c3c05c84dbd4d838c0d1b9721c028dea6c1c6cc8dcbe0e0136f536964c47f05c87009b7a9b1515d2372823804dbd4da992f91f9721c026dea641c6bec611b972136f536a641c46e84d018e07) else if Nat.blt b 90 then 0xa9b07181a3736c5c8703d4c838e6d452372e43bdea64c497ce591b972136f5360e3e146e780b909b7a9b3120e3fb46e5c84dbd4d838bed3e9721c026de0e3966068dcb9157048f536624b746e5c84d8097a9b5320e2373825d8703c1c72cae928a372e426dea652c8fc5c87009b0f8f1aa2a41c7c28dc7009b7a9b5320e2472e43144dbd4d8a707181a37378381e3f41c7f08dcb90e0136f536a642948e5c88609b7a9b532622373f06a8b93c46838e5981a5146e5c9ea6c1c7c28dcd39721c0f5360e37b46e5c8858e07a9b071572372e4418703d4d838fb11b9721c026dea6c1c7f08dcce0e0136e002354547c28dc7009b6838cd95d2372e43804dbd4da990a51b97c2e4431c0054d8a6c0d1b9bc1c0d5362a36646e5047009b7a99071cb26d4b45c84dbd4da992f91b9af1c026dea6d4c8868dcde0e0136f5360e2f346e7e07009b7 else 0x15325f3964a25c84db54da992f91b97220026dea6c1c6068dcf009b0e2f5320e3964a28dcf709b7838d1576a372e43804dbd4c838e592897220c26dea643f660a291b9721c0f5362a41c8248dc7009b7a9b5329618b2e43804dbd4d988da51b97218a26dea6c1c6068dcff172136f536a644646e81cde1727a990719424746e5c8863d4da993111b97228228dea641c68491cb90e0136f5321fb965148dcb90e07a99071cb2473f05c84dbd4d988ad11b97214626dea64c4838e591b97226cf532623d472c8dcb909b7838c59612372e43804db800a9b152092371c026daa6d4c9890711b9c52e4f5365f2e746e5c87009b7a9b151f0a3c2823804dbd4d838c0d309bc1c01c5ea6c1c6068dcd38e00e2f5360e3fb46e714b90e07a993118c2372e428c4dbd4d838c0d1b9721f2091ea641c62a8dcb90e0146e002a6d4c9888dce29726) else if Nat.blt b 98 then (if Nat.blt b 94 then (if Nat.blt b 92 then 0xa991fa0e2373b45c8703d4c9c30711b9fd2e426de0e3335968dcb90e0136f071f239646e7e0b909b7a9b071b4a512e43144dbd4c989071cb2372e425dea641c660a291b9721def5320e38c4fa5c87009b7001071cb30346e5c812354da991520e237354381ea642972c8dcb909b000f5360e30346e7ccb90e07a99071cb2372f826c02bd4c838d092d1721c026dea641c72ca291b9721def5320e31646e5c88a89b7a99071cb25a3f05c84dbd4da990711b9e03825c9c0054da991511b9aa1c0d5329642972c8dcb909b7a9b5320e2672ae3804dbc1c72cc0d1b9720da091ea641c72c9451b9ad136f5325f41c72c944b909b7a9b5320e2373de42c703d4d838c0d3f9721c026dea6c1c6069f4b9100136f5360e30346e5c8700897a9b53214a372e455c863d4c838c551c1721c026dea641c72c8dcf6172136f5320e396514944b910c7 else if Nat.blt b 93 then 0x8fd17a0e2373825c8703d4d838ae91b9ee1c026dc0054da990a51b972218d5320e34247e5c87009b7a99071cb23f3f05c84dbd4c989071a1a372e426dea652c988e5933972136f5360e36a46e5c8830e07a993860e2263fa5c84dbc1c72cc0d3a2372e426dc0054d88cc0d1b9ad1c0d536a643f4ce3806089b7a9b532622373805c84dbd4da991511b9fe31226dea6d4c8388dcb910012ef5362341c6068dcf70e07a9938e0e3162e43804dbd4c838e311b9f818826dea641c72c8dcc6972136f5360e3e146e5c8860247a9b07181a372f83804dbd4ca591f8e09872e4381ea641c746a6d1b9721c0f53693c1c6066f0b90e07a9b532322373403802abd4d838c0d1f9731c026de0e3306068dcb90e00c6f5360e30357491cb90e07a9b4320e3f82e43804dbd4da990fd4526746e381ea6d4c8389d0f70c1136f5360e2ba48e5c8860e07 else 0x15360e30346e6cc70354d8a711981a372e4381ea643f6928dcb90e0136f5320e34346e5c8860247a9b11a0e3034a25c860bd4da994b20e1fd33826dea6d4c8388dcd3972200f5320e39646e5c8830e07a9b5322341c46e848b93d4da990fd1c1721c026dea6c608388dcb90e0136f071d539646e5c87009b7a9b5320e23741e3802e3d4c838cc51b97220c381e0e38c5908dcb90e0136f5360e2ba46e6b47009b7a9b07181a373783ec703800a9b532961fd33826daa641c73e9f4b9100136e002a6d4c88c8dd091726a9b53214c1c46e5c8863d4d8a911981a3729e381ea6c63816b451b8e0136f5320e38c46e7e0b91067a9b532622422e45184dbd4c838e7d28a372e426dea6c46838c0d1b9ad1c0f071cb30346e5c84d85f7a9b5320e28a4ce8dc77bd4da991511b9a31c026dea6c1c60699cb38e0136f311cb2b446e5c84d8097) else if Nat.blt b 96 then (if Nat.blt b 95 then 0x9ab07181a372e43804dbd4d852c0d239721c0091ea6c1c6cc8dcd68e0136f5360e3e146e704b90e07a9b532622372e426c41bc2972cc0d1b9721c026dc0054c838e591b9f3136d5320e31546e5f07009b7a99071a42372e43804dbd4c8fd0711b9d81c026dea6d4c88c8dcb90e011af536a641c4a25c86389b7a9b071bd28a46e5c8703d4d838ad11b9721c028dea6c1c6cc8dcf70e0136f536a641c5025c87009b7a9b5326223f3f25c84dbd4da993111f9722b226dea641c6308dcb90e0146f46d5ba9646e5c87009b7a9b532232372e440041bd4da991520e23740e26dea6c535a28dcb90e0136f536a644646e5fc7007c7a58fe1cb1872e43804dbd4d8a8c0d1b9411c026dea647e8388dcbb0e0136f5320e33046e5c8830e07a9b18a0e30346e5c8703d4c838e591b9fd3825c9ea6c1c6068dcb90ec048f1520e3966068dcde0e07 else 0xa99071c62372e63804dbd4da990fd1b9bc1c0091e6241c630c0d1b972136f536a64be46e7b8830e07a9b532622373425c84dbc1c72cda91b97219826dea6c1c5ce91cb90e0136f536a641c46e6f08605f7838e99cb2372e43804dbd2c988e5981a372e426de0e3966068dcb909b05af53666aa346e5c87009b7a992f9cb2512e43804dbd4da990711b97220825dea6d4c838944d68c1136f071a12e746e5c87009b7a9b53214a372e43bc4dbd4da9907d1b9ee1c026dea6c3f838b211b9bc1c0f5360e4056068dcb90e07a9b532232373445c8703d4c9890d9cb2372e426de0e396606984b90e0136f071a8b4246e5c87009b7a9b5320e23741e7e0833800a9b0fd64237378381aa6d4ca58670c48e0136f536a641c4a27b86089b7a9944e76b962e43804dbd4ca58e592898a2e426dea6d4c9988dcb9080048f5323541c46e690b90e07) else if Nat.blt b 97 then 0xa9b5320e2473383804dbd4da990891b972218091ea6d4c8388dcf29a72e4f5360e3035148dce48e07a9b3120e2bd46e5c84dbd4d838c0d1e1e02e426dea6d4c8388f0b90e0146f53623ae746e5c87009b7a9b5320e2373783bc123d4c838e3528a372e426dea641c72ca29289720a8f536a64c446e5cc518097a9b07173a5a2e43804dbd4d838ac11b9721c026de0e3306068dcb90e0048f5329638330e5c87009b7a994b1a11872e43804dbd4d838c0d1e1a72e4381ea652c72c7e0c3972136f5320e32c46e5c88009b7a990718b23739e3804dbd4d97cc0d1b9bc2e4381e0e3966068dcb90e0048f23e0e30346e5c87009b7a992f9942372e43804dbd4d838af11b9721c026de0e3596068dcb90e0136f53270cc48388dcb909b70015360e2c846e6f077b54d838f851b9bb2e4381ea641c72c944b91361c0f5322a31546e5047009b7 else 0xa9b5329643f46e6f0703d4d99707181a372e4381ea6c1c6068dcf70e0136f5320e39646e5c84d8327a9b07181a3a2e43804dbd4d840ac11b9721c026de3f41c7c28dcb90e0136f5362a446828c0d1b8e07a9b11a0e2ed46e5c8703d4c838e5923a372e4431ea64c472c8dcb90c5136f5360e36a46e7cc7009b7a9b5320e25a3383804dbd4da99071339621c026de0e3f872c5c8890e0136f071cb2e746e5c84d8207a9b071822372e43804dbd4d852c0d1b9721c0155ea6c1c5ce8fcb90e0136f5360e30360691cb90e07a993562a41c46e7804dbd4d838c0d23972218381ea6d4c88c8dd091721c0f536a641c4ce3b47009b7a9b53221a8a46e5c8703d4da59071fc1721c026dea641c62c8dcbe0e0136f536a641c5125c8700977a994b23f1f82e43804dbd4da990a51b972218381ea641c746a28b91121c0f5325f46b46e5c87009b7) else if Nat.blt b 101 then (if Nat.blt b 99 then 0x91f12a0e2372e43804dbd4da990f11b9721c026dea6c1c5908dcde0ef1c0f5322341c6868dcb90e07a994b1cb1be2e43804db800a9b532961c1338381aa643765e8dcb90e0136f5360e3e146e5a07009b7a9b5320e2382e4380503cc4838e5973a372e426dea6c1c5688dcb90e0138f5323544646e5c87007c7a9b2f9572372e43804dbd4d838b212d1bc2e4381ea64546308dca08e0136f0718aaba46e5c87009b7a9b5320e2373fa5c84dbd4c838c611b9721c0271ea6c536068dcde0e0136f5360e30348e8dcbe0e07a99071cb2372e43284dbd4c838e592897218a26dea6d4c8388f0ff172136f536a641c47e6707009b7838e59642372e426c123d4d838c0d1b9721f626dea6c1c6068dcd68e0136f5320e38c46e7e04d8057a9b5320e27d2e63804dbd4c838e591b9f31c026dea64e18388dce09721c0f53631c0b6068dc7009b7 else if Nat.blt b 100 then 0xa9b5320e2373c05c84dbc7f838fe91b9721c026dea641c72c8dd1009b048f071dca9a46e5c87009b7a9b0a581a5146e5c8703d4da991191b9ad1c0305ea64c472c8fcb90e0136f536a645446e6a87009b7a993120e39646e6704dbd4c838e311b9721de26dea64dd97c8dcb90e0136f5320e39e46e5c87009b7a99071e8b966be8dc4dbd4da990fd1b9721d426de0e3426068dcde1721c0f536a644646e5c8ab9007a9b07158a512e43044dbc1c72cc0d1b9f83785c9ea641c62a8dcd68e0136f536a64c446e7ecb909b7a9b53261a8a46e5c8863d4c838a7d1b972224381c0054c838e591b97212ed536a641c46e6f0700577a9b071612372e4418703d4d838c0d1b9721c009dea65137068dcb90e0136f5320e31546e7b87009b7a9944dcb2373f05c84dbd4da994b20e1c1338381c0054d838d99339f8136d536a642346e5c87009b7 else 0xa9b07181a37366380413d4da990fd2897218226dea6c1c5ea8dcb90e0136f071cb3034fa5c87009b7838ce5642372e43804dbc1c76ee591b9721c026dea641c68a8dcb90e0136f5360e30346e6cc7009b7a992f9cb2372e43804dbd4d838fed1b9721c026dea6d4c8408dcd39721c0f25e0e30346e5c87009b7838c615d2372e43804dbd4d87ed991b9721c026dea6d4c8528dcb910c104f5362f41c46e6707009b7a9b532232374245c84dbd4c97ce311b9f82e426de0e3966068dcc21721c0f5320e38c4a25c8830e07a9b18e05a372e43804dbd4da58c0cc51721c026dea6c1c6068dce619c1c0f536a64544785047009b7a991be0e2372e43804dbd4da990711b9c62e4381ea6d4c8388f0b90e0138f53616c1c6068dcb90e07a9b5320e2472e443060bd4d852c0d1b9721c0025ea6d4c838944fd972136f5360e2b14ce5c87009b7) else if Nat.blt b 103 then (if Nat.blt b 102 then 0xa9b53214a373185c8863c1c672c0d1b9bc1c01c5ea6c54838c0d1b9e0136f5360e2ba4785c87009b7a9b532961922e43804dbd4c986e411b9721c026dea6c1c5908dcb90ef136f536a64c4838945099727a9b5320e2672ae3804fbd4da9911a0e2372e4411ea6c1c568944b90c1136f18dcb2d146e5c87009b7838e5981a372e411014b800a9b532232372e4411aa6d4c83899ccb8e0136f071f339646e5c87009b7a9b4b20e3035225c8703d4ca59071cb1fd2e426dea6c546068dcc48e0136f5360e3e146e5c87009b7a9b5325f2744a25c84dbc29650c0d1b9721c0091c0054ca58e58fe972136d5320e3965148dcb90547a9b0fd642373783804dbc1c6ccc611b9721c026dea6c1c6cc99cfc0e0136f536a645446e690a08e07a9b5320e2372e4430123c1c684ab91b9721c026dea6d4c97c944b909b0aaf5320e3964a28f0b909b7 else 0xa9b5321fa9146e5c8703d4d838c0d452672e4381ea6d4c88c8dcbe0e00f8f536a641c46e5cc7789b7a9b0a581a372e438002bd4da9910d1b97c1c026dea6c465da8dcb90e0104f0a60e3966068dcb90247a9b53214a372e4430403d4c838e6d2d1721c026dea641c72c8dcb9151136f5320e39646e5c84d82b70010a5cb30346e5c812341c686bad1b9721c026dea6d4c8388ecb91061c0f5322c41c72c8dcb909b7a9b5320e2672bc3804dbd4c88cd151b9721c0209ea6d4c85299cab8e0136f5360e3664785c87009b7a99071942372e43805d3d4d838c0d452512e4305ea6c1c606a29339651c0f5323541c46e764b90e07a9b071ee2372e43804dbd4da994b20e19d1c026de0e396606a28b90e009ef536a644688c8dcb91007a9b07181a3737859c703c6a838fe11b9721c026dea6d4c83899d1b8e012ef53289b965145c87009b7) else if Nat.blt b 104 then 0xa9b5326244646e5c8403d4da7707181a8a2e4381ea6c1c6068f0b90e0136f536a645446e69c700027a99312233a372c8dcb93d4da5917a0e1721c026dea6d4c83891cb910c198f5360e2ae46e6707009b7a99071cb2372e426c4bbd4d97cb091b9721c026dea641c72c944fc972136f071cb3034ec8dcb90e07a9b5320e2472f8430123d4c9c3071131721c026dea651b838f451b8e0136f1a20e3df46e5c87009b7a9b5321c2372e43804dbc1c62cac51b9721c026dea6d4c8448dcb90e0136f5362a41c80e8dc7009b7a99071cb2372f826c1fbd4da990a614a372e4431ea64e18388dcb90e0136e002a6c5480e8dc7009b6a994b1cb1fd2e43804dbd4c995071cda372e426dea6c1c6cc8dcb90f6136f0718c30346e5c87009b7a99071a5a372e43804bbd4c838e591b97c28226dea6d4c838944b90ed136f536a64548388dcff09b7 else 0x2a6d4c9928dcb90e0136f5360e3ed46e704b90e07838e59612373f05c84dbd4da9933214a372e4431ea6d4c9888fcb909b012f536a64548389d06089b7838c595a2372e43804dbd4c8d5071239721c026dea6d4c88c8dcde1ad1c0f536a64c44b45c84d8097
def htChunk_14 (b : Nat) : Nat := if Nat.blt b 2 then (if Nat.blt b 1 then 0x1c2a251c04c81b2cbb1af4dc1ab09f1a6f041a40131a373219c28319be991999c9198360196c7b18d1b618b462184b7d181e4a17df2517c93417c2f317976d1768b4175a7517520817448516fd0d16a748168d5216471815ef7615ac5c15a6401594ed15529114f77914ef0c14c5a714aff214abe814284413ee6e13854e135f761348bf130a1c1302c812faf512f63f127d381268981239a611e61911b190119ef6119390116c68112c6a11212110f5ba10c467107b931012030fca790fbcc40fbc4b0faa1c0f67f50e6ee90e4ca30e1fef0e1fb20e15bf0dedba0cdf410c555a0b3d6d0b160a0af9ad0adecf0ac9b10ac5910ab9850a854009ee4f09b1180988a9096873091fb508f36108ed6708cf7b08c01108bec608b2af08a6f7086a0a08301c07fc4f07fb0707f48307f25207e28d07d7c707be4d0768e207625706f8910645e405ee2f05ab3f058eda048fca03ec5303bbf503395c02e82302845c022bc002295e020fb601b1b001624001426b0139de006709004f4d004e760033ab else 0x3befa23bd2573bc4703b67553b2f303b24373b17083aa01e3a47d83983d9397dd4397a933950e338f86c37f3e137b0f0374b1a373626372832370bd1362252361240360cec359e183585bf350d5d34d5ac34a0243456b533caf633771b33742e33642b334f4f332daa32511231f18531cd8c31c20431895f31639a31503530a049306cbc30697a3005a22fd2792fab292f597c2ece2b2ecd452e22b62e06dc2db9632d71452d5c0e2d363d2cd6862cd46c2c9cb92c500a2c31092c28902c282d2be1992bb3742b9ec92b6bd12b67f62b482f2b2c932ac1672a9d032a96e72a7b832a68b129c97a291f1a28d0d82868ba28637c28328b27d15927c65e27c11626ff062695c0268dfe264b8d25581525462924a8f7242d9623ebb323a0b423636423014c22f6ff22ed5922d40c22cfe42286f1226876221abf21e50b21897e210d6b209b25208f3e203b7b203726200f9a1fc4bf1fa1851f2d161f181f1ee6cf1ebc741e73b41e5c341e14771d94031d53171d4ec61d3ce11d011f1cb6511c6f4d) else if Nat.blt b 3 then 0x5e59ef5dd6495d33805d0c055c9ac25c58d55c33a95c2f085bd0535bae215ba00f5b44bc5a57395a4b495a32575988b75967f6588452582d5757a5da5795305732e456c39b560d3b560b8d55f73e55c7b8553c7855246454159d53b407535ad7533dca5335b6532dfc526309525a12523b5151e554519f4c517b4251652d513c6551273051071250fd81502f224ffdbc4fe5284f8e004f586f4ec84b4eb1a04e3f4b4e36384e09574deea14d742f4d67134d46124cd3474cccb74ca1cc4c250c4c137e4b73e84b6fb74b38754b316f4b08204b00ba4a9f214a97f04a6c224a010049e7f0497aa4495559490a4f4869c147ea95478ab04781f0473b9e46ae9c46a57c466d8845f32745da7d45b78245b07d45a43a45336044fef644cc5444a3eb4484d14481e5447b464451f344307a43fd0d43e2b24364b041beec40c0bc4079e2406809403f824039533f07da3efa563ec4623e8ea43e1baf3e091c3dcb0c3dc4723d7fd03d6a713d54443d22bc3cfd553cc0aa3c92183c2f463c12fa3c06c2 else if Nat.blt b 4 then 0x9380d2937cca92b512912ebf9120b19108ca90611c8ee9888e9bbc8e91708e2aa78db8fa8da37b8d21828c96638b6ad58af1f98ac8688aa5b38a0f9b89fb6789b0b489788a88ca9a887a3f886e58880fd487f3b187d27e8692cc86878f85459284e88d84660e842f5083f7f783c70a83b2c0831df2824e1e8116478050c0803a1d801f087f437d7f2fbb7f1dd17ddb067dacea7d8b257ce6687cd6937c74757c2ef77bb1277b751d7b27d97afb1c7a94fa7a8bff7a2ceb79043578aadc77eb2677560876e49675ccd4755b12753b057523f4749c277469047412fc73dc5d737f7a730f5a727bd8727518720a4471d629715d99714e987114ca70c68670bc18706f40700aa16fca576f61346cde0e6cd6686c94456c8fab6c373c6c256b6bf13d6b90126b50f06ad1856a024b69b5b869b26c6886e367f53167e4d7677721667da46654b7655571653ef565333a63cc51635e676303a66271ad6226ea6208bf61080c60d56960d05960bdb660788e5fc69f5f33b25f14b55eaa855ea8105e9391 else 0xfa9455f6ae88f0a9b4ec9d99e8f9a4e7fc31e72297e5bfe8e50683e327b5e2d4dce29462dcf649dc188fdbf89dd9d28fd99a81d9323ed4d844d499b1d40f6fd3ae15d38682d3300ad2d9d0d014c7cf5d1bce3326cc24c9ca4d98ca2dcbca0604c9a63dc6abe0c5922bc447f8c40a6ac39296c38d3bc28c97c22a63c08462be5370bdec55bc29f9badf07ba9e8ab9b644b9a4e3b7efefb77ea3b75f35b6f320b66b83b5d012b5abd2b5252cb4d1d5b3b861b37589b327f5b30de4b2af17b26846b1ce45b159beb073d4af4873aec425aeb815ae02beacde10ac845cac314babd5b6abce4eab81b2aaad58aaa639aa51e2a9e8b3a74fd9a72adaa6d5d8a65ee2a64296a624dda5498ba4c239a47d41a369a1a2f0d8a2c1b6a29eaea28633a27f38a25e64a0d45ba0c4039fd6e59f5ec49e31be9e31819dfab69dec069c8c789c32129bec5d9bddde9ba5f09ba4069b325e9969f998da6e98c12a98133997ebcc97c29e979d719678cf96162295fa1e9582829557c19447ff93d05e939e05938c76
def stChunk_14 (b : Nat) : Nat := if Nat.blt b 10 then (if Nat.blt b 5 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0xa991fe0e2372e443c7009b8001536a641c46a5c07009b70015360e2b846e5c87009b7001071cb2fd46e5c87009b70015360e30346e5c8830e070015320e32146e5c87009b7001536a641c46e5bc700a370015360e30346e3804d8757001536a641c2e44b46b09b70015360e2a546e5c87009b7001536a64c48388dcb90a370010719fb0346e5c87009b7000002a6d4c9888dcb90a36001536a641c3fa5c89089b70015360e2ae46e5c87009b7001536a641c46e5c86b89b7001536a641c47e5c86689b70015360e30346e76cb90e07001536a641c46e6a8b90e07001536a641c46e5c87009b70015360e303514750b90e07001536a641c5148dc7005b7001536a64464685c87007c70015360e3035b48dcb90e070015360e30346e5c87007b7001536a641c46e5b47009970015360e2f046e5c87009b70015320e31346e5c87009b70015360e30346e5c87005470015360e30348e5c8940e070015320e39646e5c84d83d70015320e32a46e5c87009b7 else 0x1071c8b0346e5c87009b7001536a641c2e44c47009b70015329647e5bc5c87009b70015360e3035048dcb90e070015320e39b46e5c87009b7001536a642948e5c87009b70015367d41c60691cb90e070015360e30346e5c87009070015320e31c46e5c87009b7001536a641c46e77cb909b7001536a641c50c5c87009b70015326ec1c46e5c87009b7001536a652c3f25c87009b7001536a641c46e81cb909b70015320e39646e5c89789b70015362330346e5c87007c7001536a641c4725c87009b7001536a643746e5c87009b7001536a641c4c85c87009b7001071cb30346e6f0b90e070015360e2c846e5c8700867001536a641c46e5c87109b70015329647e2e44407009b700153214b9646e5c89209b7001536a643f46e6f0b90e070015360e2eb46e5c87009b7001536a64c446e5c84d8807001536a642946e5c87009470015320e38e46e5c87009b70015360e2ba46a5c87009b7001536a641c4b25c87009b700153289b9646e5c87009b7) else if Nat.blt b 3 then 0x1536a641c48a5c87009b7001536a64c446e5c8700a37001536a641c46e5c86b09b7001536a641c46e5c8700b07001536a645446e780a089b70015360e37646e5c87009b7001536a652c31c5c87009b70015320e38146e5c87009b70015320e33046e5c87009b7001536a645475a8dcd38e070015360e2fd5148dcb90e070015320e39646e5c87009b7001536a645446e69ca08e070015360e30346e5c87008670015320e39646e5c86589b70015360e30346e5c87289b70015320e33146e5c87009b70015320e39646e5c87189b7001536a641c48c5c87009b70015360e2af46e5c87009b70015320e38c46e7e0b909b7001536a641c46e5fc7009b70015360e2ac46e5c87009b70015325f38c46e5c87009b7001536a644646e5c87008270015360e3034aa8dcde0e070015320e39646e5c88709b70015320e31a46e5c87009b70015360e36a46e5c87009b7001536a641c47e5c8700a370015360e30346e5c86c89b70015323641c46e5c87009b7 else if Nat.blt b 4 then 0x15365f36646e5c87009b7001536a641c3a85c8830e070015360e30346e6f07007370015320e39646e5c87609b7001536a64be46e7b87009b70015320e39646e5c84d81e7000002a6c1c60691cb90e06001536a630d46e5047009b70014d60e3966068dcb902470015320e39646e8c8b909b70015360e2a646e5c87009b70015320e38846e5c87009b7001536a64c346e5c87009b70015329c41c72c944b909b7001536a641c46e5c86c09b70015320e33d46e5c87009b70015326ac1c46e780b909b7001536a64c49468dcb90a370015320e38c46e5c8700997001071cb2a546e5c87009b70015360e35e6068dcb90e070015360e30346e7e0de0e07001536a641c48e5f07009b70015329647e7785c87009b70015320e39646a5c84d82470015360e3035268dcb90e07001536a645446e5046e09b7001536a641c4845c87009b70015320e39644c5c87009b7001071cb2ae46e5c87009b7001536a64c447e8dcb909b7001536a643e46e5c87009b7 else 0x1536a641c46e5c8858e07001536a643f46e54c7009b70015320e34046e5c87009b70015320e39646e808b909b700153214b9646e5c89409b70015360e36646e5c8700997001536a643f46e5c8700867001536a652c988944b909b700153688c466068dcb90e070015360e36546e5c87009b7001536a641c46e7b8700997001536a641c46e5c89e0e07001536a64c446e5c84d8097001536a644646e5c8901007001536a641c46e5c8830d070015360e30346e6c8b90e070015362a3e146e5047009b7001536a641c5005c87009b70015360e3034a88dc7009b70015369641c75c5c87009b7838ee5cb30346e5c87009b80015320e38946e5c87009b70015360e30346e6f0b50e07001536a641c45e5c87009b7001536a641c3825c8908e0700153693c1c6065c87009b70015320e39646e5c86889b70010719130346e5c87009b70015320e38b46e5c87009b70015360e2b346e5c87009b70015360e30346a5c87009b70015360e36646e7e0b909b7) else if Nat.blt b 7 then (if Nat.blt b 6 then 0x1536a644646e680b90e07001536a644646e6b4940e070015320e33c46e5c87009b70015360e30346e5c87002370015323f41c2e44847009b70015320e39646e5c84d82e70015365f30346e5c87009b70015326239652c8dcb909b7001536a641c3384847009b7001536a641c46e5c8828e07001536a645446e69c898e070015360e36346e5c87009b7001536a641c46e5c8700a270015360e2ba48e5c87009b7001536a64c446e5c85189b7001536a641c48e5c07009b70013fa0e3966068dcb909b70015320e39646e5c84d8827001536a641c46e84cb90e07001536a649688c8dcb91007001536a64c45bc8dcb90a370015320e39646e734b908b70015360e3ba6068dcbe0e07001536a644646e5c89b8e070015323541c46e5c87009b70015320e39646e5c86b09b70015360e30346e5c8700af7001536a645446e69cb90e070015360e3af46e5c87009b7001536a652c8385c89e0e07001536a64c45b68fcb909b7001071cb30346e5c8700867 else 0x153272c1c72c5c87009b70015320e3424685c87009b7001536a641c46e5f06009b70015320e39646e5c84a02470015360e3034d88dcb90e0700153214b2846e5c87009b70015320e31f46e5c87009b70015360e30346e5c87009970015362a3e146e5c87009b70015320e3966be8dcb909b70015327d42972c8dcb909b7001536a643f46e3804d83970015360e2f646e5c87009b70015320e39646e5c89809b7001536a64548388f07009b7001536a64c47788dcb90a370015360e3a546e5c87009b70015360e30346e604b90e070015360e30346e5c86a89b70015320e31746e5c87009b7001071cb2b746e5c87009b7001536a641a46e5c8700a370015360e30346e7f4b909b70015320e3424fa5c87009b70015360e3035c68dcb90e070015320e34246e6b47009b700153252c1c72c8dcfc09b70015360e2c246e5c87009b7a9b50a9641c6065c87009b800153651c1c60691cb90e07001071cb36b46e5c86809b7001071d739646e5c87009b7) else if Nat.blt b 8 then 0x1071a130346e5c87009b7001071cb30346e7e0b909b7001536a642946e5c87009b70015360e2cc46e5c87009b70015360e30346e5c8700987001536a641c46e5407009b7001536a64c48388dcb989b7001536a641c46e5b47009b70015320e39646e5c86689b7001536a64fa88c8dcd68e070015320e34946e5c87009b70015360e3ae46e5c89e0e07001536233096068dcb90e07001536a641c4705c87009b70015360e30346e5c86e09b70015320e39648e5c84d82470015360e30346e5c87002c70015362a3e146e44c7009b70015360e2c84b45c87009b70015360e30346e8a0b90e070015360e2fd46e5c87002470015360e30346e780b909b7001536a641c46e5c8700a37001536a641c46e5c87009f70015360e2e546e5c87009b7001536624466068dcb90e070015360e37a46e5c8830e070015360e30746e5c87009b70015360e30346e69cb90e07001536a641c46e3bc4d83970015360e30346e3804d87770015360e3c946e5c87009b7 else if Nat.blt b 9 then 0x153298c1c72c8dcb909b70015360e2e74685c87009b70015320e3964a25c88909b70015323dc1c46e5c87009b7001536a641c47e5cc7009b70015360e3bc60691cb90e07001536a641c4605c87009b70015360e2fc46e5c87009b70015360e40746e5c87009b70015320e39646e5c88a89b70015360e3034b45c87009b7001536a641c4fe5c87009b7001536a641c4fa5c8700607001536a641c4fa5c88009b70015360e3034f28dcb90e070015360e3fa46e5c87009b7001536a641c46e7f8b909b70015360e2e74fa5c87009b70015320e39246e5c87009b70015360e2e746e6b47009b700153214c1c72c8dcb909b7001071cb30346e734b902470015320e31046e5c87009b7001536a641c4c65c87009b70015320e39646e5c86409b70015360e30348e5c87009b7001071cb2c246e5c87009b7000002a642972c8dcb909b60015360e30346e5bc7009b70015360e30346e5f0b90e070015360e3035bc91cb90e070015360e30346e5c8850e07 else 0x13120e3966068dcb909b70015320e34746e5c87009b70015360e3034f68dcb90e070015360e30c6068dcb90e070015365641c6068dcb90e070015360e2fb46e5c87009b70015320e39646e5b47009b7001536a64fa87e8dcde0e070015360e3646068dcb909b70015328441c72c8dcb909b70015360e2ad46e5c87009b70015320e39d46e5c87009b7001536a645446e5047009b7001536a641c4665c87009b70015360e2fe46e5c87009b7001536a64547988dcd38e070015323541c46e3804d87370015360e2f946e5c87009b70015360e30348e890b90e070015360e30344e5c87009b7001536a64468388dcd68e070015320e39646e5c84d85f70015320e39646e5c8700a370015360e2c84625c87009b70015360e30346e704b90e070015320e3964e88dcb909b70015329ac1c72c91cb909b7000002a6d4c88c8dcd68e060015360e30346e5c8700627001536a641c46e5f07009b70015360e30347e5c87009b700153233c1c46e5c87009b7) else if Nat.blt b 15 then (if Nat.blt b 12 then (if Nat.blt b 11 then 0x1536a641c4b45c87789b70015329641c72c944b909b70011fa0e30346e5c87009b70015360e30346e6707009b7001536a641c47869cb90e07001536a641c46e5c89e8e070015320e39646e5c84d81d7001536a641c34e5c8998e0700153247c1c46e5c87009b7001536a641c46e5c87209b70015366241c5688dcb909b70015360e3c946e5c89e0e070015320e38c46e5c87009b70015369630330e5c87009b70015326241c6308dcb909b70015320e39646e5c87c09b70015320e3964a28dcb909b7001536a641c46e6b07009b7001532964c472c8dcb909b70015320e31b46e5c87009b700153251c2972c8dcb909b70015360e30346e3804d85b70015360e3662e44b47009b7001071cb30346e8a4b909b70015360e3035c48dcb90e070015362341a6068dcb90e070015320e39646e86cb909b7001536a641c46e5c86e89b70015326ac1c46e5c87009b7001071942ba46e5c87009b70015320e33e46e5c87009b700153214b9646e5c87009b7 else 0x15360e3e12e44cc7009b70015320e31246e5c87009b700153238c1c46e5c87009b7001536a641c46e5c8668a370015320e32946e5c87009b700153654c1c5fa8dcb90e07001536a641c4fa5c87009b7001536a64c246e5c84d8097001071cb3034f68dcb90e07001536a641c46e6b47009b70015360e3034a68dc7009b70015360e30346a5c87002470015362341c5d88dcb90e07001536a641c46e7b87009b70015320e3964f85c87009b70015320e39746e5c87009b70015360e2c746e5c87009b7001536a645446e69c940e070015320e38c46e5c84d81e70015360e2cb46e5c87009b7001536a64a388c8dcd68e070015360e2cc5148dcb90e070015360e2ba46e5c87009b7001536a641c46e5c07009b70015320e39f46e5c88009b7001536a641c4785c86e09b70015362341c6068dcb90e07001536a641c2e44cc6e09b70015362a3e17988dc7009b7001536a641c478780b909b7001536a64c446e5c8518097001536a641c3c05c89989b7) else if Nat.blt b 13 then 0x15320e38846e5c84d8247001536a641c2e44b87009b70015320e39646e5c8450247001536a643146e5c87009b70015360e303514944b90e070015320e39648e734b909b7001536a644646e6b47009b70015360e30346e770b90e07001536a652c3145c87009b7001536a64465bc8dcd68e0700153214bbc72c8dcb909b7001536a64fa8a88dcd38e070015320e39646e5c84d82470015362a3e146e4a07009b70015320e32346e5c87009b70015320e38a46e5c87009b7001071c9b0346e5c87009b70015320e31e46e5c87009b7001536a64c488c8dcb910c7001536a641c4685c87009b7001536a641c4625c87789b7001536a650a88c8dcb910070015320e31446e5c87009b70010719430346e5c87009b7001536a641c46e7e0b91067001536a64be46e5c8830e070010719faf146e5c87009b7001071cb30346e5c87006070015360e3e14785c87009b7001536a643f4625c87009b7001536a64c447e5c85b89b700153214b965bc8dcb909b7 else if Nat.blt b 14 then 0x15360e3736068dcb909b70015360e2a846e5c87009b70010718e30346e5c87009b70015360e3df46e5c87009b7001536a64548388dcf009b70015329341c72c8dcb909b70015320e37f46e5c87009b70010718aaae46e5c87009b70015322334246e5c87007c70015360e2a946e5c87009b7001536a64548388dcd38e070015367d4547c28dc7009b7001071982c846e5c87009b7000002a6d4c8a88dcd38e060015360e30346e5c87001b7001071cb2c846e5c87009b7001536a645446e6247009b7001536a645446e5187009b7001536a641c46e698b90e07001536a641c46e87c7009b7001536a62d046e7f4b909b70015320e39646e5c86909b70015360e30346e5f0940e070015360e2b146e5c87009b7001536a64467788dcd68e070015323545446e5047009b7001071cb30346e5c87004470015320e3964fa5c87009b70015366241c6d68dcb909b70015320e32046e5c87009b7001071cb36646e5c87009b7001536a641c46e6cc7009b7 else 0x1536a641c46e790b909b7001536a64a38a88dcd38e070015360e2f346e5c87009b7001536a64be46e7e0b909b70015360e30b6068dcb90e070015360e3f846e3804d87770015360e30348e8dcb90e07001071cb30346e5c84d81e7001536a642846e5c87009b70015360e2b446e5c87009b70015362a41c7c28dc7009b70015360e3a846e5c87009b70015320e31846e5c87009b7000002a6c547c28dc7009b60015360e40046e5c87009b70015367d41c6068dcbe0e070015360e3f846e7f4b909b7001536a641c46e5c87789b70015360e2c646e5c87009b70015360e30346e5c86b09b7001536a641c4d65c87009b7001536a65439888fcb909b70015360e30348e5c87002470015320e39646e8807009b7001071cb30346e5c87009b70015322a41c72c8dcfc09b700153213c1c72c8dcb909b70015320e39646e5cc7009b7001536a643f46e5c87009b70015360e3035145c8968e0700153268c1c72c8dcb909b7001536a641c46e80c7009b7) else if Nat.blt b 17 then (if Nat.blt b 16 then 0x1536a641c46e5c87e89b70015360e36646e5b47009b7001536a644646e5c87009270015360e30346e5b07009b700153651c547c28dc7009b70015360e30346e5c8700a77001071cb30346e5c8940247001536a642946e5c07009b7001536a641c46e3804305b70015320e33046e5c87789b70011aa0e30346e5c87009b70015360e3e046e5c87009b70015320e38c4a28dcb909b70015320e34a6228dcb90e070015360e3af2e44b87009b70015360e3f846e5c87009870015360e2c146e5c87009b70015360e30346e71cb90e070015360e30346e5c87005f7001536a64be46e5c8700997000002a6c1c6068dcbe0e060015369ac1c60691cb90e070015320e39646e5c84d81c7001536a641c4785c87009b70015360e30346e5c89e0e070015366230346e5c84d8097001536a641c2e44cc7009b70015320e39646e5c84d82f7001536a64c446e5cc4d80970015360e3035148dcb90e070015360e2ee46e5c87009b7001536232e746e5c87007c7 else 0x153619c1c6068dcb90e07001536a641c46e3804d87670015320e31d46e5c87009b7001536a641c46e5c86d09b70010719430346e5c870024700153214b9646e5c84d82470013ea0e3966068dcb90247001536a641c46e5c86d89b70015360e30346e5c8700a37001536a641c46e66c7009b7001536a64547788dcd38e0700153651c1c6068dcbe0e0700153267c1c72c8dcb909b70015329632230e5c87009b70015360e36b46e5c87009b7001536a64c446e5c8a309b70015320e38646e5c87009b70015360e2ba46e5f07009b700153236c1c46e5c87009b7001071a82a546e5c87009b7001536a641c46e5c87089b7001536a641c46e780d397270015328da9646e5c87009b70015323f2d046e5c87009b70015360e3f846e704b90e07001536a641c46e7f4b9098700153276c1c2e44487009b7001536a645446e69c7009b7001536a64545bc8dcd38e07001071d4b9646e5c87009b70015320e34146e5c87009b7000002a641c72c8dcb908b6) else if Nat.blt b 18 then 0x1536a652c30e3804d87770015362a30346e5047009b70015320e39646e5c8830e070015362341c5e28dcb90e07001536a641c2e44c87009b7001536a641c47e5bc7009b700153614b0346e890b90e070015360e30346e5f07009b7001536a641c46e3c04d85b70015329ac2972c8dcb909b70015325ac1c72c8dcb909b70015360e3035bc8dcbe0e070015320e34446e5c87009b70015360e3035b091cb90e0700153270c1c46e7f4b909b70000020e3966068dcb902460015360e2ba46e5c07009b70015360e2b446e5c86689b7001071cb35346e5c87009b70015360e3034f68dcb90d370015360e3e146e5c86e09b70015320e31846e5c86689b70015360e3b046e5c87009b70015360e3034c65c87009b70015360e30346e6d8b90e070015360e3e146e780b909b70011fa0e3f846e5c87009b70015320e39646e5c87008b70015360e3e146e69cb90e070015360e3f846e6707009b70015368f4466068dcb90e070015360e30346e5b47009b7 else if Nat.blt b 19 then 0x15360e2bf46e5c87009b70015360e3035145c8908e07001536a641c46e7f4b909b70015360e2f146e5c87009b7001536a641c4ac8dc7009b70015360e30346e5c87d89b70015360e30346e6b47009b7001536a643f46e5c87008470015360e30346e7b87009b70015327f41c72c8dcb909b70015369641c7f05c87009b70015360e30346e5c07009b70015320e33046e5c87008670015360e2b046e5c87009b7001536a652c8389507009b7001071cb30346e5c87002470015360e30346e5c8700bc70015320e3967008dcb909b70015360e30346e5c8700877001071d339646e5c87009b7001536a644646e5c8941007001071a12e746e5c87009b70015360e36c46e5c86b09b70015360e30346e8787009b70015360e30346e5c86e89b700153655c1c6068dcb90e070015360e3bc6068dcbe0e070015360e2b446e5c8700a370015360e36646e7b87009b7a99071e7b9646e5c87009b80015360e30346e5c8700d370015320e31846e5c8700a37 else 0x1536a64c447e5c84d80970015320e39646e5c87e09b70015360e3034785c87009b70015320e39646e7e0e709b7001536a642246e5c87009b700153270c1c46e5c87009b70010718c30346e5c87009b7001536a641c46e5c8700b970015360e30351499cb90e070015320e39646e5c87d09b7001536a64a388c8dcb910070015362341c5fa8dcb90e070015360e2a746e5c87009b70015360e2c846e5c87789b70015320e39646e3804d87770015320e38f46e5c87009b70015360e2e846e5c87009b70015360e3e146e5c87009b70015360e2c246e5c8700867001536a641a47e5c87009b70015320e34546e5c87009b70015325f39646e5c87009b70015360e3fb46e5c87009b70015360e3032e44b87009b70015360e2c046e5c87009b7001536a641c46e5c86e09b7001536a64544785047009b7001536a641c46e780b909b7001071cb3035bc8dcb902470015360e2b946e5c87009b70015360e2cc46e6f0b90e070015360e3034685c87009b7
def htChunk_15 (b : Nat) : Nat := if Nat.blt b 8 then (if Nat.blt b 4 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0x7c90507be3f0793d6079371079289078f2007748e07724f0770d7076251074d8f073c5b073a1007136d0703ad07037307015206f89106e45f06d46306bf4b06b2cb06a061069b94067c660679a00675f906550e064bec06486c06392a061d59061bcc0615f806063b06002b05f18305ee2f05ea7505d06f05c97205c6c0059f2a058eda058940058758055e570547ef05149e05101904d94204c5d804b4fd049cb60483c2047f76047f56047aa5045bc3045bab045204044063043a3f04344f042e9a041172040d00040a7f03fa1b03f28503db1403ce1903abb9034dd703395c032c3d032af103160602e82302e5ae02d33002b03102af45029fa80294a502916602600a0252ec02396a023131022aab0225d90224d9021aff020a9102091502021701fbb101b14601adc5018e47018ab50184f701844c017705013e7c013b61011e6a01076000faf200f58500f44400ea9a00e98700df4500de0c00dbda00db7500ab5d00948b009443007188006c9b0067090055ed0037e60033ab002e1e else 0xf06b30eec040ecf990ec4c50e86800e74620e68c60e4f240e4ca30e43e10e1fef0e170d0e16cf0e0d760e06ad0dffc70dead90de2000ddcc80dd6120daf8e0da45d0da1190d96b10d90ed0d8bfd0d82770d7a3f0d6dee0d57400d4f700d09df0d09180d08900cf5a80cf2ff0cf20c0cecc00ce2e30ce15e0cdf410ccff60cc00d0c7f280c6cce0c555a0c508c0c49bd0c41a50c206c0c1ff90c1c0c0c17e80c17670c0f1f0c05520bf4680bdc7b0bdb5a0bd4130bd3500bc3e70bc1c20bc17b0b7af80b74730b5c410b3d6d0b3bfb0b37740b2a6a0b25d30b160a0b09880b04770af9ad0ae0150aca970ac9b10ac6bc0ac5910ac0670ab9850ab5cc0a988e0a5a2f0a51db0a47b50a3ba50a170509fe3309fd3d09f8b709ef1909ee4f09d9dd09d07609b36309919a0988a909810a09746c093a4b091ebd0916ff08f36108f11708ed6708cfde08cf7b08cf0b08cd9f08c8ba08a4df08981f088fb9088292086cba086a0a08679d0855a1084e28082be50825c708216308105c07f25207e92c) else if Nat.blt b 3 then 0x16b6be16b45c168d5216833a167ad416638f165cf3165015164718161c3e1601ff1600d615f01615d00915ac5c15a6ed1584151579d1156aac156830155f0e155291150e76150be314eae614e45e14de7314c5a714b50c14b32a14a64e149da6148fc8147b661454f2145321143ea014147e14037b13fff713f1da13ee6e13c49913c16c13a96c1363c7135d9d1358031348bf1348a71341ab1339b81336aa133292131eac130a1c12f23a12edf312bec012bdae12a2e612a175127d381276ca127031126898125751124c851240041237fa1236cc122d3f12162811f35611e61911d12a11ce4611c6fa11ba7c11b19011a03c119ef6119d041192f6116c6811615d115c54113ea8113865112c6a112b481125281119681114d011135110fa8310e07b10cc3a10cb4710a0a7109e13108cd11082c7107d00107b93106b0610635c1057a41037c51029aa1012030fe17b0fdc2b0fce160fbcc40fb9c20f96450f845c0f6f090f615d0f5a9b0f4e440f424c0f371d0f2a510f19040f0d3a0f0c73 else 0x1ee6cf1ed8cf1ed4b71ecde91ebc281e5d0e1e51131e4d751e429c1e3a931e2f2f1e251c1e20291e1d941e189c1e15671e15311e0e491df9431dd7861dcc371dc5fc1d94031d40571d34871d2e9d1d1a141d194e1cfb1c1cf9dd1cf3e21cdfc41cbb3c1ca99b1ca1e41c96261c935b1c89371c73f61c705c1c6f4d1c5f421c43a31c2a251c14771c11bc1bf8fe1bf7811bd4821bd3e81bd28d1bd1301bc1e11bbcdd1bbb011bad131bab401b9b721b97501b7c2a1b6daa1b61cc1b38871b16681af4dc1ae7201adea11adc2e1ad8681ac3dc1ac1ef1abac21ab0cc1ab09f1a8ba11a76dd1a5e0f1a59071a505e1a40131a3d731a33f11a2efc19fd0419f8a21991461989841972ea196f8b196c7b1958f0194cde194a3819307a18ed0b18d48018d0cb1878661858a81857671846da1833dd181e4a17fbb317f52717f21717e07617c3c017abb9178e8e178aec1781e8177a2e1768b4175b9f175aa1175a75174900173f101736be172b4c16ff5f16fe9016f9a216f90e16cfe116ce6d16bc41) else if Nat.blt b 6 then (if Nat.blt b 5 then 0x27a50c27977d278c692782ac276ee42755ef27474127450c27436327365127314f2727d02724c927222c271cde27143f27033f2701a926f81626e23926d27b269df02676f9265dd9264b8d264a42261c0525ef5125b35925ada6258372254efd2533092509d424f88c24d4d824be8d24b94724a8f72483ab247fd0247ac324686d242c8e242a18242a0924046b23f15623eb5223eb4923e0c123997823917823853f23661c23252123166523097a23014c22ffb722f43d22e75f22e29c22cb9222bcf122bac322ad21223bd92239eb2232f1222796221b18221abf21d66021d19221cf3521ccfa21c13021b915219cdf2199a0217a12216bb621699821446d2136f8212be32115f220e8ad20e5c420e41220d39820cf2120cbde20b4b7208f3e207f2b2074192066d9205f052044092037be201153200cad2003c11ff4081fd8811fd6321fd4931fd0551fd0301fcfa51fc4bf1fbb371fb4881fa1851f874d1f821a1f72c91f5fe21f5b461f27f61f1a971f18c61f0b2f1efcaa1efaa71ee73b else 0x31673a31639a315719315035313434310f9b3108cc30f54f30ec9c30c63e30964c307163306739305764300f222ffaac2ff5b62ff3a02fe7642fd2792fce0c2fa43a2f7be62f7bc92f5f382f40de2f39112f34442f28ab2ed9442ebfab2e9b2f2e85c92e7f602e75372e72622e70252e700a2e08642e06dc2de5652de3352dc71e2db9142daf022dac5a2d81f62d7c322d72662d71452d6abc2d5c0e2d4c462d2efb2d0f862d0c592cf3f72cebfb2cd6862cd0f82cbfde2cbdd22cb3492cad552ca7cf2ca7072c9cb92c96d62c78582c500a2c42892c36f52c2b582c1db72c07562c05ec2bfac72bec632be1992bd3af2bcbc92bc13b2bc0cf2b99a52b482f2b3f3d2b3a982b2c932b278f2af9882ae08c2ad4fb2ac1672a95702a8b1a2a56bb2a1f052a0ebb29fd1a29fc2e29fc2829db3a29caab29ca9529bedb298bf3295f9e293629293227291f1a290c2529077d28ef0e28d0d828b62928aa392890cd287ba72860ec28352d28328b28123e27efdd27de4027d9f727d15927cea827bb3d) else if Nat.blt b 7 then 0x3ab3b33aac913aa3523a9b503a96b83a939e3a90a53a7fdd3a63053a58df3a4dc83a3a433a32fc3a0bdc3a065d39f9d239b7d0399812397dd4396018393d6a392b533922223914ba3902c83902bc38f86c38ee3838e89d38e5a338af2f3891103857a2384d8c3849c738481c383afa382b0c37ed0537b85837b11837b0f037a952379e6a3796ed374fad374e98374b1a374135373bd0373721372832371e143719ff37174e36e43f36d11736b4b6368c5a3684ba365321363153362b683628f83617bf361240360cec35ecc535c43135bb84359e1835859035821c35819c3569613564513559d835448e353376351f323519e335186d350d5d34ee0934e86f34ddcd34d5ac34b3a534a024349c73349bb334657c3456b5344c95343856342eb1342a9d33fda633d54033d4bd33af83339780338fc633642b333f3633366a333035332630330af03308f632f4ac32ee9832d7ee32b6d5329ee6326dfc325e64325b8c3248a1322cee321cde3218d331fe6431fe1731d68631cd8c31846d317f21 else 0x45a57845a43a45a3b7456ee04569024565a5451e8245124544fef644fde044e6e944e45044dd6c44dcbb44cc5444cb0b44c93544bb48448aa04484d1447b46444eb34432bd44307a44207743f01043bfad438ddc4356ba433bc44336d443138142bc67427cbd42796f425a254230d2421c0942147341f52b41eb8041d03141c59441beec41a86141a85641a7fc419d2d41965b41894d417e8141720f416968415d78414a17414536411d3c41192040ebe840c0bc40b49740ad5d40a83c4098a84096774079e240680940561f403fa7403ef540395340298b4021aa401a98400a0b3ff7bd3fd39c3fbd3a3fb4e73fa3c23f9e393f9dac3f7efb3f0d383f05eb3efa563ef4653ec4623ec3223ec0163e99123e8ea43e7edc3e623c3e5ed33e5e4e3e3b613e21813e21613e091c3df3f93dcb0c3d84d33d70223d2fbb3d2c063d22bc3cfd553ce6c43cd5a73cced23cc0aa3cb1703c83b03c2f463bfe283befa23bd2573bc4703bb3743babeb3b680e3b17083b13ae3afe793ae1913ad61d3ab3c0) else if Nat.blt b 12 then (if Nat.blt b 10 then (if Nat.blt b 9 then 0x5207e351fc4651df5651d94351d14c51c8bf51bc57518663517dd8517b4251718b514c84514293513c6551230551071250fd8150b1d650adfb50addf50a5f25084bb5080ca5062d1504c8550368d502f22501c305002ef4ff3d44fe5284f9dd04f9db54f88d84f840b4f7f624f586f4f48aa4ee8ee4ee0d84eb7554e821d4e5c814e5c354e1b7b4de4624d9a054d90e74d78194d2f6e4d182f4cd3474cccb74cc3084c83554c6f7f4c67d44c4b264c41444c288b4c250c4c137e4c039b4bf5034bde564b72dc4b4ed74b36b94b28d24b12da4b11744b08204aee134aeb4f4ae7954ac8324ac6434aa4324a8f7b4a85064a845e4a7b6a4a71f24a6c4c4a6ab84a65ff4a5f0a4a140b49a64849826f497e1f497aa449795e494ed4494589491ba74910ac490a4f48bf9548b9bc48a4ff487ca548714e485ee148152847b33a47a2564792634758ba471d3d4711f146d94246b43246ae9c46ab0346a57c469513468d15466d8846630246467e46388b46379846138d45e3f545da7d45b78245a942 else 0x5f14b55ef5765ebcd15e31495e1d035ddb2c5dd7db5dc84c5d3e0b5d3df05d33805cfa6c5cd7b95ccb175cc1275cb8835cb8255cae6f5c9ac25c95065c55335c33a95c23e15c07f45bae215b77e05b740b5b22195b21c65b08cf5b04ce5afec75afa385ae1eb5ae0245abd625ab4935a9e175a923a5a7cf25a62535a4b495a2dc35a2a625a27fb5a164159d66259a023598793593d85591f4459154359093358fae358f6f258ef9558c3a258bc8a588b695880c1581ab357fcb457c9e457b85557b5f057a5da577142575dc85757e957395e5708c556d21a56c5b356c39b56bf8256b25c56972c5679455646fe562bb5561fab561f93560b8d55f4c955c7b855b26555a89155a79a556f41554cd4554785551be454be6954b6b55493b6548df1548113546692546358545bc1542cc154159d540c6953f05d53e93353dfa853b407539d48538a98533dca533ae85335b6532dfc5327f3531c3a52e21a52c97152bbe352ae47527ef2526309525a12524c1c52397c522cfd522387521d5b520898) else if Nat.blt b 11 then 0x6cac016c94456c847d6c54af6c51406c3d806c256b6c05546bf9bd6bf2396bf13d6be0d16bc6026b9b626b7d966b45f56b413e6b3ab16b06026a82e46a3c2d6a39f76a180b6a103f69bc3469b5b869afab69a7f3699145698b7769690b691aa168f07a68ef3968bd266886e3684ff0683a6d682e6d67fcf867e4d767e19f67d5a667afad67a37b678de7674395672d866711f866ffee66e2d366e1eb66b71e66b63d669b366671e8667115666a0466579466272f6606d765fbe965de0765bc20659118656fef65557165542b6546a2651fdd651fac64f9c564a6bf6476606459376440d863fecb63c5bc63aadc637c0f6379ff637234634ebc63339563186962a8e8629a186283c36271ad625ce261cc1a619d026190666182f0617bbb6174d161631161523f612fb261127260d05960c41960bdb660b90060a0d460a0c760788e606b7460457f602c5e60129e6008055fd25c5fcf775fc5c85fc1e95fac595faaae5f93845f62035f61d65f5b505f4cc55f41935f3d765f2c4b5f172c5f1691 else 0x7b61c47b374d7b27d97afb907afb1c7ab4ff7aac8d7a8bff7a84497a2ceb7a1f1e7a11e07a063a79eb6e79e71979c74279a22b798fc57984a8796488795d3f7959d479436379049d78f7fb78efe278e79a78cb8978aadc78aa61787b94784d3977eb2677cb0e77b84577af1e778af0777eb3777651775608774efc774c457739b57696b0763b3e761d2775ff4775dfe175d9d775d18e75ab1f759e4175775d755f82755b12755978754377753cbb753b05751d5e75199774f96574f69874e8f974bb2474b9d37492267412fc73ee0b73a370737f7a736f6773687d73572d733895732a1e73079f72daf272be70729142727bd87275187267fb7258fa71d62971d60f7199ea719580717a36716114715d99714e9871497071419871381c710f3d70d5c270bcbc70aef87060e8703ab1702ff87022187018267001276fca576fba066f91036f83df6f1c326ec82a6ec6776ebf596e79d66e5bcb6e58f16e18da6dff5e6de8706dd4276d83d06d2a2c6d0c9f6ceda26cde0e6cd6686ccf006cbab2) else if Nat.blt b 14 then (if Nat.blt b 13 then 0x8a66e68a5f938a5f7e8a54528a47cc8a43e78a1ce389ff9889fb6789d4fc89c036898a488978ba893922890be588dce088dc3088cdd488ca9a88ba42886e5888381a8828dc88100f880f3e87e5cd87d27e87c53b87b49c87b3ad877f908759b9872069870fc086ecc186ea7f86daaf8692cc864ff486271c85dca685d87785bf5b85b9a785b92685ad89859c5c859880855190854592851e8d85025984ef9b84e1b784bd3184bcec84b8f884704f843e5c84379a842f508405fc83f7f783d2c483ad2e83a05f839c34831df2828bba825572825478821e2c820db781d7bc8193f18180b9816733815b2280c18480af14809f4480633f8053ec8050c0804ddf803a1d803854801cdb8002d08001757fe78f7fc6e27faba77f772c7f6b317f437d7f39bb7f2fbb7f1dd17e92437e90ca7e90677e87ef7e66a47e1a5a7dda0a7dd2e17dc9427dc4707dbf8a7dbc0b7dacea7d8b257d7d3c7d52ef7d42947d00657cc7fd7c948c7c74757bda387bc4db7bb56f7bb1277ba5cc7b76ed7b76e87b751d else 0x9aea859ae5369a84a89a81dd9a7fb69a73079a5c599a5a509a47f39a40bf9a3aa69a376e9a1ed69a1cdc99971299921c9978c1993c5a98f98198f44b98dd9598dd6f98da6e98cb2698c32198ba9c98b9eb98b05898a7d398a19097d2ba97c29e97bb1297a095979d7197407c970f3c96f5a596ec3d96d0a196adbe9662239639ed96162296008295dd839584bc958282957b6f9571d39557c19555bd951d8895002e9490cb9475f0942d1793bf7493659a935c59933ea092f99592ca0192b51292a8dc92521291fcf991b2ac91a5d1913eb8913d70911e0f90859c904e3a903f6b90297a8ffac88fe74c8fd7208fc6eb8fbdf28fb9118fb5228f6b838f3a918f178e8f03e38eb9588ea7238e9f698e96598e93608e91708e7b148e6b7f8e33e48e2aa78e0dcd8e0a8c8dc6338da37b8d26a18d14988d07ee8d00f58cef878ce3c18ccc598cc1878cbdab8ca06b8c98618c763f8c64c78c145e8be3e68bb3588b95998b4ffd8b0a8d8af89e8acea78aa5b38a902e8a8c3b8a85d38a77cd8a6900) else if Nat.blt b 15 then 0xae4034ae3f63ae3dcbae2531ad8eebad885cad7747ad5d1ead5ac4ad1d6dad0491acde10acc7a2ac1118abc192ab7e16ab5c49ab5a95ab59d1aaea3eaabd5daaa639aa96c0aa8747aa51e2aa42d0a9d39fa9b9e8a9b909a9aa3da98aa7a98747a97d81a97575a94e93a93d35a9048ca8fb74a8eb3ca8e91ba8e28ba8d2c1a8bef9a842dca83439a8283ba81bafa7c59aa7a0cfa78fefa764cda73e0da7296ea72700a70e6ca6d73ea661caa5e232a52587a4d779a4c239a48973a47d41a4403ea41f68a4021da37d27a369a1a3511ea33bb6a2f106a2c466a2c1b6a2bbf1a2aa3ba29eaea2460da22f2ca1d64ba1a0d9a13cb2a0e08ca0af98a0ad25a0904aa083d4a080c7a078aba06dcea03566a00a129fd6e59fbe389faaa69f8b639f5ec49f3c209f2c299ef2fa9eb8b19e948c9e94039e93d09e8e2d9e83ef9e83599e357f9e31be9e0b8e9dec069dab009da05a9d990b9d35849d0f949cf2349cb7ce9c78179c66769c5bd49c51f29c500d9c3cc09c2d0e9be5f39b4f799b325e9af382 else if Nat.blt b 16 then 0xc78cb1c77a94c6fa72c6c878c69c8dc6961dc68b7bc6761ec5eb5ec5922bc57c9ec514ddc50f50c4a2aec44951c39296c38d3bc36721c333b6c30088c2d952c2c96ec2bba2c2416dc22a63c22673c1ce60c1b206c18089c0dd52c09c10bfbe97bf9fc1bf534bbf4d0bbf495cbee786bebdddbea4cdbe93f5be7fd7be7ac2be5ce1be5370be4b6abe397fbde513bda4bdbd8993bd6cbebd5d4cbc8ae0bc85a3bbe73dbb9b35bb882bbb6a98baea7ebadf07bacb54bab14bba92cfba8d61ba8b81ba0a9bb9e2dfb9bdc6b9b644b98245b96defb96639b933bab8bd6fb88d15b862b7b75f35b75af8b7368db72504b70b4ab709ffb6dac6b6c808b6882fb66c5bb66b83b6627ab5acaab597bbb56f67b551feb53afab51b64b46ff6b45f76b43930b3e2c7b3e1a3b3ae4ab3761db37589b327f5b30de4b2f927b27826b26e67b26846b26420b23e24b1ec48b1d497b159beb0f430b0a850b0798db0784db073d4b04560b03d31b01203b009cdafb241af3b47af2f93aec870ae9d5dae8c23ae832d else 0xfed681fca943fb9eb7fa9455f7de86f6dbe8f65a6df16f5ef0a9b4f010eced4258ebf395eb1604ea0406e9b992e9afd3e99fcde8f9a4e81581e7fc31e72297e61e5ae570f6e50683e39f9fe198cfe13f43e0b829e06c3ce012c5def64ade7734de68d7dd8674dd7dcbdd0f01dce157dc98eddc188fda3ca0d9a6fdd9323ed920b2d8d2f4d8ce43d8168dd7be92d6cfcfd6b9f8d69b99d62a77d60bced54aefd5209cd4f68dd4c261d4b877d46fb8d46397d40f6fd3ae15d38682d3567dd31000d2f6f8d2f35ed24c17d2385dd1e69ad19337d07b18d0677dd01987cffb5fcf83c5cf5d1bcf3d88cf1e26cec05fce9448ce3326cd6bf5cd0e7fcc50e4cb9ee9cb601ccadde5ca39b9ca2184ca021ec9ac6ec97a5cc902adc83d11c8247cc7f446
def stChunk_15 (b : Nat) : Nat := if Nat.blt b 33 then (if Nat.blt b 16 then (if Nat.blt b 8 then (if Nat.blt b 4 then (if Nat.blt b 2 then (if Nat.blt b 1 then 0xa9b5322a41c46e56c7009b8a9b5325f28a46e5c87009b8a99071cb25146e5c84d84f8a9b5321da3730e5c87009b8a99071cb25146e6f0b909b8a99071cb2372e43a47009b8a9b5320e23735a3804d8928a9b5320e2372e4418700248a9b07205b0346e5c87009b8a9b5321fa372e43806089b8a9b0715a2372e4380518098a9b5322341c46e794b909b8838ce581a372e43804d8718a991aa0e2373c05c87009b8a9b5320e23737e5c87009b8a9b5325f41c4a28dcb909b8a9b5320e2372e43804d80c8a99071a633046e5c87009b8a9b532624c446e5c84d8098a9b5320e2373825c87009b8a9b5320e2512e43044d8038a9b5320e27d2e44307009b8a9b5320e2372e442c700c58a9b07181a372e43804d8788a9b5320e2372e43804d87f8a993122339646e5c87009b8a9b071b32372e44307009b80015360e30346e5c8700547a9b5320e23735a4307009b8a993aa0e38c46e5c87009b80015320e32a46e5c87009b7a990718c2372e4380518098 else 0xa9b5329641c3825c87009b8a99071962372e43804d8138a9b5320e2372e4418700058a9b5320e28a46e848b909b8a99071cb31646e5c87009b8a9b5320e41c46e5c87009b8a9b07181a8a46e5c8700298a9923e0e23737c5c87009b8a9b5320e28c4785c87009b8a990718b2372e43806089b8001536a641c46e6a8b90e07a9b5320e2372e43804d8818a9b532232372e44007009b8a9b53214a6746e5c87009b8001536a641c46e5c87009b7838e59cb30346e5c87009b8a99071c62372e43804d84f8a99071c62373785c87009b8a99071cb2372e43804d82c8a9b5320e2373ca5c87009b8a9b5320e2373105c87009b8a9b1520e30346e5c8700248a9b5320e2512e44306089b8a99071a12372e43804d8188838e5981a372e43806089b8a99071a12372e43804d8138a9b5320e23737861c700558a9b5320fa372e43804d8038a9b5322a41c4ce55c7009b8a9b07181a372e459c7009b8a9b071642372e45047009b8a99071cb23c46e5c87009b8) else if Nat.blt b 3 then 0xa9b5320e2373f05c8700a38a9b5320e26746e7f8b909b8a9b5320e23c2e43806189b8a9b07181a374206f0b90e08a99071cb25146e5c84d87c8000002a6d4c9888dcb90a36a99071cb2372e45044d8248a9b5320e2672ae3804d8488a993120e39646e5c84d8368a9b5320e26736c55c7009b8a9b5323241c46e53c7009b80015360e2ae46e5c87009b7a99071cb2372e43804d8068a993120e3a372c8dcb909b8a9b5320e2372e43a84d84f8a9b5322341c4b85c87009b8a9b0a581a372e43804d8248a9b5320e28346e5c87009b8a9b07181a372e44004d87c8a9b07173ae746e5c87009b8a9b071642372e43804d85e8a9b5320e2372e43bc6089b8a9b5323241c46e5c87009b8a9b5320e2672e43804d8038a9b5326223730e5c84d8098a9b5321ba372e455c7009b8a99071c828a46e5c87009b8a9b532232372e43803e0248a9b5320e2373fa5c84d8558a9b5320e28a46e7f4b909b8a9b071be30346e7e0b909b8a9b5321fa372e43bc7009b8 else 0xa99071cb2372e43804d8648a9b0715d2372e43804d8018a9b11a0e30346e5c87004f8a99071cb2372f85c87009b8a9b5320e2372e43bc7789b8a9b5320e2672e43806609b8a9b5320e2373e45c87009b8a9b071fd2373125c87009b8a9b11a0e30346e6f0b90e08a9b0715a2372e43806089b8a9926e3541c46e5c87009b8a9b5320e2373fc624b909b8001536a641c4ce56c7009b7a99071c62372e43804d87c8a9b071fc25146e5c87009b8a9b5320e2372e43804d87d8a99071cb31846e5c87009b8001536a64c48388dcb90a37a9b532232372e43803e0058a9911a0e32846e5c87009b8a9b5320e23c2e43804d8028a99071cb2372e44007009b8a9b5320e2373be5c8ab89b8a993123541c46e5c87009b8a9b07181ac846e5c87009b8a9b5320e2373625c87009b8a9b07181a372e43804d8728a990718c2372e43806089b8a9b071fd26746e5c87009b8a9b5320e2673f03806089b8a9b071612372e43804d8208a9b071642372e44307009b8) else if Nat.blt b 6 then (if Nat.blt b 5 then 0xa9b5320e2372e44004d89b8001536a641c51499c700557a9b532622372e43804d82e8001536a641c46e5c87109b7a991fa0e3d346e5c87009b8a9944e0e39646e5c87009b8a9b5326441c46e5c87009b8a990718b2372e43804d8198a9b11a0e30346e5c8a78e08001536a643f46e6f0b90e07a9b5320e23746e5c8830e080015360e2eb46e5c87009b7a9b5320e2373f25c87009b8001536a64c446e5c84d8807a9b5320e2372e45647009b8a9b5320e2373be5c89f09b8a9b071fc2372e43804d8098a9b071582372e43804d8098a9b11981ad146e5c87009b8a9b0715d2372e43804d84f8a993120e39646e5c84d8828a9b0715d2373785c87009b800153289b9646e5c87009b7a99071cb25146e5c84d8548a99071942372e43807009b8a9b071b9b035a28dcb909b8a9b5320e28a2f05c87009b8a9b07173a372e43804d89b8a9b5320e2372e44087009b8a9b5326244646e5c84d82e80015360e30346e5c8830e07a9b07181a8a4ce5c87009b8 else 0xa9b5320e23734e680b90e08a9b5320e23735c5c87009b8a9b07181a372e45047009b80015326ec1c46e5c87009b7a9b5320e2372e44004d8828a9b5320e23734e5c8700558a99071cb2372e45807009b8a9b5320e28a46e69cb90e08001536a652c3f25c87009b7a9b5325f2373f05c86089b8a9b071fc3f546e5c87009b8001536a641c46e81cb909b7a9b07181a372e45a07009b8a990718b29546e5c87009b80015362330346e5c87007c7a9b07181a372e4380120248001536a641c4725c87009b7a9b5320e2372e65047009b8001536a643746e5c87009b7a9b5321041c46e5c87009b8a9b5321fa372e43804d80a8a9b5320e2672ae3804d8248a99071d1a372e44487009b8a9b5320e2512e4418700c18a991aa0e23730e5c87009b8a9b4b1fc23730e5c87009b8a9b071642372e43804d8668a99071cb2372e44304d8248a9b5326223f2e43804d8098a9b5320e23741e5c87009b8001071cb30346e6f0b90e07a9b5326241c46e5c84d8808) else if Nat.blt b 7 then 0xa99071cb2744ce8dcb909b8a99071cb2372e43804d8458a9b5320e28a46e5c8748e08a9b5320e2373c05c84d8558a9b53268c1c46e5c88609b8a9b3120e2c246e5c87009b8a9b5320e2672ae3804d8058a9b5320e28a46e780b909b8001536a641c46e77cb909b7a9b0715d2372e43804d87c8a9b5320e2372e4430400248a9b5320e2373dc5c87009b80015360e37c46e5c84d8297001536a641c50c5c87009b7a9b5320e26746e5f07009b8a9b5320e28a2e44307004f8a9b5329641c46e5c8830e08a9b5329641c3f25c87009b8838e5981ad146e5c87009b8a9b5320e2373825c8700138a99071cfa372e44004d87c8a9b5320e2373dc3804d84f8a99151cb2372e45047009b8a9b5329641c46e5c86d09b8a9b5320e2373dc6f07009b8a9b532624465148dcb90e08a9b5320e2373885c87009b8a9b11a0e30346e5c87007c8a9b53214a373f05c87009b8a9b5321bc1c46e5c87009b8a9b3120e30346e7e0b909b8a9b5320e2373d65c84d8058 else 0xa9b532964c446e7e0b909b8a9b53226c1c4ce5c87009b8a99071cb2372e44687009b8a9b5320e2372e43804d8158a9b5320e27d37c5c87009b8a9b07181a6146e5c87009b8a9b5322a2372e453c7009b8a9b07181a372f83804d82480015320e39b46e5c87009b7a9907194a373785c87009b8001536a642948e5c87009b7a9b532a4c1c46e5c87009b8a9911a0e32a46e5c87009b8a9b071f0a372e45547009b8a9b07181a372e43804d85e8a9b5320e27d2e43804d84f8a9b07181a372e43804d8038a9b5320e23735a5c87009b8a9b5320e27d3785c87009b8a9b5320e2373225c87009b8a99071982372e455c7009b8a9b07181a8a46e5c8700c18a9b5320e2373783802a82c8a992363541c46e5c87009b8a9b071b32372e43804d84f8a9b5320e2372e4418700008a99071942372e43804d8448a9b5320e23735a3804d84f8a9b071b32373785c87009b8a9b5320e2373786b47009b8a9b07181a372e4380120058a99071cb2372e455c7009b8) else if Nat.blt b 12 then (if Nat.blt b 10 then (if Nat.blt b 9 then 0xa9b3360e36646e5c87009b8a9b5322a26746e5047009b8a9b5322341c46e5c87009b8a9b53214c1c46e5c8860248a9b07181a372e43804d8928a9b0716123730e5c87009b8a991c60e2372e453c7009b8a9b5320e24748e5c87009b80015360e36a46e5c87009b7a9b5320e2372e458c7009b8a9b532232372e43803e0008a9b5320e2373dc3804d87c8a9b52a0e30346e5c87009b8a9b5320e2373f03804d82c8001536a641c47e5c8700a37a9b5320e2672e45947009b8a9b5320e23c2e43806089b8a9b07181b0346e5c87009b80015323641c46e5c87009b7a9b5322341c514944b90e08001536a642946e5c8860247a9b5320e2512e43044d84f8a9b07181a372e44307009b8a9b5320e2513785c86089b8a9b5320e2374205c87009b8a9b5325f25146e5c87009b8a9b5322a41c46e7e08609b8a99071cb2372e44f87009b8a9b53214c1c48e5c87009b8a9b5329644646e5c87007c8a9b5320e2372e43804d87e8a9b5320e2374025c87009b8 else 0xa9b071642372e43804d80180015320e39646e5c87189b7a990718aa372e45047009b8a9b5320e2372e43807009b8a9b5320e27d2e43804d87c8a9b5320e2372e43b47009b8a9b5322341c46e5c8700828a9b5320e237428704b90e08a9b5326041c46e5c87009b8a9b5320e24746e5c88602480015360e2af46e5c87009b7a9b071b32372e43804d87c8a9b53298c1c46e5c86289b8a9b5320e26746e55c7009b8a9b5320e23735a3804d87c80015320e38c46e7e0b909b7a993120e3966be8dcb909b8001536a641c46e5fc7009b7a9b5320e29146e5c87005e8a9b5320e25146e7f4b909b80015325f38c46e5c87009b7a9b07181a373fa61cb909b8a9b5326641c46e7e0b909b8a99071cb2373825c87009b8a9b5320e2372e43804d85d8001536a644646e5c8700827a9b5320e2373f05c86209b8a993760e2373f25c87009b8a9b0ae0e30346e5c87009b8a99071c62372e44187009b8a9b5325f2372e43804d8098a9b07181a372e43806609b8) else if Nat.blt b 11 then 0x1536a641c4ce7a07009b7a9b3120e37c6068dcb909b8a9b07181a372e43805609b8a990720e39646e5c87009b8a9b1520e3f846e5c87009b8a9b5322a41c46e69ca08e08a9b5320e2472e43804d8558a9b50a2341c6068dcb90e08a9b5320e28a48e5c87009b80015320e33046e5c87009b7a9b5320e2512e43044d87c8a9b5320e2372e45887009b8a9b071642372e45c87009b8a9b07173a372e43804d8138a9b072093e146e5c87009b8a9b5320e2373fa5c84d80980015320e39646e5c87009b7a9b18e0e37c46e5c87009b8a9b071642372e43804d84f8a9b5320e2372e43804d8618a9b5320e2472e45607009b8a9b07173a372e43804d8688a9b071642373785c87009b8001536a645446e69ca08e07a99071a1a372e43804d8808a9b07158a372e43804d8038a99071a128a46e5c87009b8a991aa0e23734e5c87009b8a9b0715ea372e43804d82e8a99071cb28a46e7e0b909b80015320e33146e5c87009b7a992fa0e38c46e5c87009b8 else 0xa9b5326241c47e8dcb909b8a99071cb2373f05c84d85f8001536a641c4845c87009b7a99071c638c46e5c87009b8a9b07181a3b46e5c87009b8a9b071fc2373285c87009b8a9b5326241c46e5c8700a38a99071cb2372e426c1200180015320e39644c5c87009b7a9b5320e237378580700558a9b5322a23732c5047009b8a9b5320e2373ba5c87009b8a9b071efa372e45047009b8a9b5322a41c46e780a089b8001536a64c447e8dcb909b7a9b5326241c4e88dcb909b8a9b4b20e30346e5c8700248a9b5320e2372e44302a8248a9946e0e3964a28dcb909b8a9b5320e28a46e5c8860248a9b5320e25246e780b909b8001536a64c446e5c8700a37a9b5320e2372e44004d8138a991aa0e23c46e5c87009b8a9b07181a915148dcb90e08a991920e39646e5c87009b8a9b07181a372e4380560718001536a645446e780a089b7a99071c625146e5c86089b8a9b5320e23741c5c87009b8a9b532962373fa61cb909b8a9b5320e23736e5c87009b8) else if Nat.blt b 14 then (if Nat.blt b 13 then 0x1536a641c46e5f0860247a9b5320e25146e69cb90e08a99071c626746e5c87009b8a9b1360e30346e5c87009b8a9b5320e2373f05c8a209b8a9b532622372e43804d88080015326ac1c46e780b909b7a9b5320e23737855c700558a9b071612372e43804d8108a9b071f0a372e43804d8558a9b071f0a8a46e5c87009b8a99071942372e43804d8358a99071d038c46e5c87009b8a9b5322342046e5c87009b8a9b07181ad15148dcb90e08a9b071642372e43804d87c8a9b0fd642372e43804d85580015360e30346e7e0de0e07a99071cb29f46e5c87009b8a9b5320e25a2e43804d8558001536a641c48e5f07009b7a9b5320e28a4b45c87009b8a9b532961872e43804d8138a99071cb2674a28dcb909b8a9b5320e25a4b45c87009b8a993ae3541c46e5c87009b8a99071cb2373785c84d8248a9922a0e2373405c87009b8a9b5320e28e4a25c86089b8a9b5320e25a3783804d8558a9b07181a372e4380120008a9b5320e28a2e43804d88e8 else 0x15320e39646e5c87609b7a9b53265c1c46e5c8830e08a9b5320e2373205c87009b8a9b5320e2744ce5c86089b8a9b071642372e43bc4d8558a9946a0e38c46e5c87009b8a9b5321fa372e45047009b8a9b5322323735a5c87009b8a9b5322c42946e5c87009b8001536a64be46e7b87009b7a9b5320e28a4e85c87009b8a9b53261c1c46e5c87009b8a9b5320e23740e5c87009b8a9b5320e2373dc4187009b8a9b532622372e455c4d8098000002a6c1c60691cb90e06a9b5320e23734e5c8700098a9b5320e25146e780b909b8a9b53268c1c46e5107009b8a9b5320e23730e5c8700a38a9b5320e2372e43b07009b8a991fa0e2372e43804d8188a9b5322a2373f05047009b8a9b5320e28846e5c87009b8a991fa0e2372e43804d8138001536a64c346e5c87009b7a9b53298c1c5145c87009b8a9b07181a372e45947009b8a9b5320e23741a5c88009b8a99071cb2373f25c87009b8a9b5320e2372e43887009b8a991a20e2372e45047009b8) else if Nat.blt b 15 then 0xa9b5320e2373825c8700558a9b5320e28a46e704b90e08a9b532964c446e5c86289b8a99071a134246e5c87009b8a9b07181a372e43804d84f8a9b5325f45446e5c87009b8a9b071fc2372e43804d8248a9b07181a373785c87009b80015360e36646e7e0b909b7a9b5320e2372e65c87009b8a9b5320e2373be5c87009b80015365f36646e5c87009b7a9b5326242946e5c87009b80015360e3035145c87006d7a9b5320e2373c05c84d8098a9b5320e2372e63804d84f8a9b5320e2373785cc7009b8a99071942372e43804d89b8a9b071b32372e44187009b8a9b071be2372e43804d8298a9b07181a372e43804d8018838e5981a372e45047009b8a9b5325f41c46e7b87009b8a9b5320e23f2e43804d8558a99071cb29d46e5c87009b8a9b5320e28a47e5c87009b8a9b07181a372e43805009b8001536a641c46e5c8860cc7a9b5320e2373fa5c8a009b8a99071cb2372e426c3e0248a9b11a0e4146068dcb90e08a990820e39646e5c87009b8 else 0x838ee5cb30346e5c87009b8a9b071582372e43804d8058a9b5321fa372e44307009b8a9b5322a41c46e7f4b909b8a9b071bd2372e43806089b8a9b5320e27d4fa5c87009b8a9b5329dc5446e5047009b8a9b43e0e3f846e5c87009b8a99071cb23735a5c87009b8001536a641c46e6f0700557a9b5329641c3205c87009b8a9b5320e2373665c87009b8a9b5320e2372e45047789b8001536a64be4a25c86089b7a9b5320e2372e43805309b8a9b18e0e30346e5c8700248a9b0715d26746e5c87009b8a99071cb2372e43804d8408a9b5320e25146e7b86089b8a9b5320e27d46e6b47009b8a9b5320e29146e3804d8558a9b5320e2512e44186089b800153693c1c6065c87009b7a993b60e3962e44487009b8a9b2fa0e36646e5c87009b8a9b5320e25146e5c86289b8a9b07181a3737c5c87009b8a9b11a0e3034ce8dcb90e08a9b07181a372e45c87009b8a9b07181a373785c8700718a9b5320e2372e44004d8808a99071cb2373dc5c87009b8) else if Nat.blt b 24 then (if Nat.blt b 20 then (if Nat.blt b 18 then (if Nat.blt b 17 then 0xa9b5329641c4a25c86289b8a9b071f7ac246e5c87009b8a9b5320e28a4ce5c87005e8a9b5329623737c5c87009b8a9b5320e2912e45807009b8a9b5320e2372e63804d87c8a99071a125146e5c87009b8a991aa0e2372e455c7009b8a9b5321fa372e43804d8928a99071cb25146e7e0b909b8a990718c2372e45047009b8a9b5323241c46e6f0700558a9b5326241c4a28dcb909b8a9b07181a372e63804d8098a9b5320e23f47e5c87009b8838e5981a372e44307009b80015362a3e146e5047009b7a99071cb2374205c87009b8a9b53214a3730e5c87009b8001536a641c5005c87009b7a9b071fda5146e5c87009b8a9b5322341c46e5fc7009b8a9b071b325146e5c86089b8a990718b2372e43804d8038a9946dcb29646e5c87009b8a9b5325f41c4a25c86089b8a9b5320e2372e43804d8918a9b5322327d2e43804d87c8a9b07181a373d65c87009b8a9b071fc2372e43804d8058a9b53214a372e4430700248a9b5320e28546e5c88009b8 else 0xa990718aa372e43804d8018a9b5320e25146e5c8860248a99071cb2372e43807009b8001536a641c46e6f07005f7a991aa0e2372e44f87009b8a9b5320e2372e44307789b8a99071cb26746e55c7009b8a99071cb23735a3804d87c8001536a652c988944b909b7a99071a12372e43804d8098a9911a0e33046e5c87009b8a9b5320e28a4ce5c8860e08a99071cb2372e438c7009b8001536a64be4ce5c87009b7a99071cb2373f05c84d8098a9b5320e26746e7b87009b8a9b5326241c46e5c84d8098a99071942372e43804d82a8a99071922372e43804d8108a9b5320e2672e44187009b8a9b5320e25148e5c87009b8a9b5320e2372e43804d8568a9911a0e39646e5c87009b8a99071c62373f05c87009b8a9b5320e25146e714b90e08a9b0715a2372e45047009b8a990718b2372e44307009b8a9b07181a372e43804d87c8a9b1520e3e146e5047009b8a9b0fd81a372e43804d8558a9b5320e2374203804d8588001536a64c446e5c84d8097) else if Nat.blt b 19 then 0xa9b071f0a5146e5c87009b8a9b5320e2674a25c86089b8a9b0715a2372e44307009b8a994c66241c72c8dcb909b8a9b5325f2372e43804d8248a9b5320e28a4a25c87009b8001536a645446e69cb90e07a9b5326641c46e5c8860248a9b5320e2372e4430120098a99071a632846e5c8700248a99071cb25846e5c87009b8a9b532964c45145c87009b8a9b07181a372e43bc4d8558a9b5322a2373c05047009b8a9936a0e39646e5c87009b8a9b07173a8a46e5c87009b8a9b5322c41c46e5f07009b8a990718c2372e44307009b8a9b071fc23746e5c87009b8a9b5320e2743f05c86089b8a9b5322a2373125c87009b8a9b5320e27d4ce5c87009b8a9b5329fcc446e5c87009b8a9b532964c4838944b909b8a9b071b326746e5c87009b8a9b5320e2472e43804d8098001536a641c46e5c8858e07a9b5320e26746e6b47009b8a993120e39646e5c84d8558a9b5320e2373c05c8a209b8a993120e3965148dcb909b8a9b5325f41c4ce5c87009b8 else 0xa9b07173a372e43804d8698a99071952372e43804d82e8a9b5320e2373f05c84d8058a993560e2373c05c87009b8a9b5322a41c46e780b909b8a991aa0e41c46e5c87009b8a9b5325f2372e43804d8058a9b071fc2372e45507009b8a9b5329fc1c4a25c87009b8a9b5320e2372e43804d8828a9b4b20e3f846e5c87009b8a9b07181a8a46e5c8a08e08a9b5320e2372e4418700c18a9b532961872e43804d88e8a9b53214a372e43804d8108a9b5320e26847e5c87009b8a9b5320e2373fa5c84d8248a9b5320e2373f06f04d8058a9b071f0a372e43804d8098a9b07162a372e43804d8548a9b0715d2373f05c87009b8a9b07181a372e4380148248a9b532622373f25c84d8098a9b071612372e455c7009b80015323541c46e5c87009b7a99071d1b9646e5c8700448a9b5320e2373545c87009b8a9907199a373f05c87009b8a9b5322a41c46e69cb90e08a9b5320e2372e44004d8558a9b5320e27148e5c87009b8a9b5326241c46e5f07009b8) else if Nat.blt b 22 then (if Nat.blt b 21 then 0xa9b5320e2374065c87009b8a991fa0e2372e43804d8558a991fa0e28a46e5c87009b8a9b5320e25146e704b90e08a9b532232372e43806087c8a9b5326241c46e5c85189b8a9b5326245446e5047009b8a9b07181a3738261cb90e08a9b53298d2c30e5c87009b8a9b5320e2373fa5c84d8058a9b5320e23c2e45047009b8a9b07181af346e5c87009b8a9b5320e28a46e6707009b80015360e2ba48e5c87009b70015320e3304ce8dc7009b7a9b5320e25146e6747009b8a9b5320e23730e5f07009b8001536a64c446e5c85189b7a993660e38c46e5c87009b8a993b60e39646e5c87009b8a9b5321041c46e7e07009b8a9b071fc2372e43804d8008a990719825a2e43804d8558a9b5320e2372f84307002480015320e39646e5c84d8827a99071cfa372e43804d87c8a990718b23b46e5c87009b8a9b532961872e43804d8558a99071cb2372e43804d8448001536a641c46e84cb90e07a990718aa372e43804d87c8a99071cb25a2e43804d8558 else 0xa9b071642372e43804d8218a99071cb26746e5c84d82480015360e2c246e5c87009b7a9b5322341c5148dcb90e08a9b5320e2674b43804d8558a9b50a9641c6065c87009b8a9b5320e27d3f05c87009b8a9b2fa0e30346e5c87009b8a9b5325f23746e5c87009b8a9b5322341c46e6f0700558a9b12a0e23737c5c87009b8a9b1960e30346e5c87009b8a994b276c1c72c5c87009b8a9b5322341c46e5c87008e8001536a644646e680b90e07a9b071b32373f05c87009b8a993120e39652c8dcb909b8a9b5320e2373825c8700098a9b5320e2373f05c84d80d8a9b07181b035148dcb90e080015320e39646e5c84d82e7a99071cb2373205c87009b8a9b07181a8a46e5c8860e080015365f30346e5c87009b7a9b5321fa372e43804d8018a9b071612372e43804d86d8a9b5320e2372e4430700cc8a9b07181a372e44187009b80015326239652c8dcb909b70015360e2ba46e5c8860247a9b5320e23e46e5c87009b8a9b5329fd2c30e5c87009b8) else if Nat.blt b 23 then 0xa9b5320e2372e43bc4d8018a9b5322a41c48e5c87009b8a9b07181a5146e5c86089b8a9b5326244646e5c84d8098a990718b2372e45c87009b8a9b5320e23746e7f4b909b8a990718b2372e43804d84f8001071cb2b746e5c87009b7a990718b2373785c87009b8a9b5320e26732c5c87009b8a9b5320e2513f05c86089b8a9b5320e2374267e4b90e08a9b071bd36646e5c87009b8a9b11981a372e43804d87c8a9b5325f2512e43806089b8a9b5321fa372e453c7009b8a9b5320e23c2e44307009b80015360e30346e7f4b909b7a9b5322a23730e5047009b80015320e3424fa5c87009b7a991520e34246e5c87009b8a991520e39646e7e0b909b8a9b5329623738261cb90e08a990718b2372e43805009b8838e5981a372e43804d84f8a9b5322341c46e680b90e080015320e34246e6b47009b7838e5981a373785c87009b8a99071cb2372e65c87009b8a99071942472e43804d8248a9b5320e2373305c87009b8a9b532624464a28dcb909b8 else 0xa99071cb2373f05c88909b80015362a3e146e5c87009b7a993120e38c46e5c87009b80015320e3966be8dcb909b7838e5981a372e43804d87c8a990718c2372e43804d84f8a9b5320e2372e43804d8138838e31b32372e43806089b8a990718c2373785c87009b8a9b5325f2372e43804d8008a990714b2372e44487009b8a9b5320e23734e5c8700058a9b07181a372e4380608248a9b5320e2372f83804d8108a9b53214a372f85c87009b8a9b5320e2672ae3806089b8a9b5322a41c46e5c8860248a9b532622372e43804d8098a9b53296446838a28b90e08001536a64548388f07009b7a9b5320e2372e455c700a38a9b5320e2373c05c84d8248a9b532964be46e5c87009b8a99071c62373dc3806089b8a9b5320e2372e455c7009f80015320e33046e6f0700557a9b5320e2374205c87005f8a9b5320e2373785c87789b8a990ee0e39646e5c87009b8a9b5320e2373d65c86089b88d507181a372e45047009b80015320e39646e6f0700557) else if Nat.blt b 28 then (if Nat.blt b 26 then (if Nat.blt b 25 then 0xa990719424746e5c87009b8a99071cb2372e438c4d8368a99071cb25146e61cb909b8a9b532684be46e5c87009b8a9b071572372e43804d8138a9b5320e2372e43bc4d87c8a9b5321fa372e43bc4d855800153272c1c72c5c87009b7a9b07181a373125c87009b8a9b5320e2373825c8a70e08a9b07181a372e45187009b8a9b5320e28a4b45c8700558a9b5320e2373fa5c84d8008a9b07173a372e43804d8098a9b5320e23f2e43805189b8a9b5320e25146e5c88009b8a990a60e32846e5c87009b8a99071cb2372e44d8890e08a9b5320e2372e43144d8248a9b1520e3e146e5c87009b8a9b5320e2373185c87009b8a9b5320e2372f05c87009b8a990718b2372e43804d87c8a9b5320e2373c05c84d8058a9b0715a2372e43804d84f8a9b07181a6746e5c87009b8a9b5320e2373485c8a08e08a993326241c72c8dcb909b8a9b5322a41c4b45c87009b800153214b2846e5c87009b7a9b071642373f05c87009b8a9b532964c44a25c87009b8 else 0xa9b3122341c6068dcb90e080015360e30346e780b909b7001536a641c46e5c8700a37a9b5322a23734e5047009b8a9b5320e28a46e5c8760e08a99071cb29b46e5c87009b8001536a641c46e5c87009f7a9b53214a372e455c7009b8a9b5320e25a2e43804d8488a99071a12372e43804d8248a9b4b20e3034ce5c87009b8a99071cb2373f05c84d8248a9b0715a2372e63804d8098a9b5320e23741a5c87009b8a9b071b82c246e5c87009b8a9b5329625130e5c87009b8a99071cb28a4a25c87009b8a9b07181a8a46e5c8b28e08001536624466068dcb90e07a9b5320e2373785c87005e8838c6181a372e43804d8098a99071cb2372e43804d83680015360e37a46e5c8830e07a9b5320e2372e44004d80980015360e30746e5c87009b7a9b5320ea372e43804d8558a99071d1b9646e5c87009b8a9b5320e2372f83804d82c80015360e30346e69cb90e07a990718c2372e63804d8098a992020e25146e5c87009b8a991aa2341c46e5c87009b8) else if Nat.blt b 27 then 0xa9b5320e2373c069cb91418a9b07181a373785c8700558a9b5320e2373383804d8098a9b5322a41c5228dc7009b8a9b5322a23c46e5047009b8a9b5320e2372e4430120248a99071cb2373f05c84d8058a9b18e2a30346e5c87009b8a99071942372e43804d85580015320e39648e5c84d8247a9b5320e2372e43884d8138a9b5320e23738a628b90e08a99071cb2372e43804d8828a991fa0e25146e5c87009b8a9b07181a3732c5c87009b80015360e30346e5c87002c7a9b5320e2914ce55c7009b8a9b5320e2372e45707009b8a9b5322a41c46e704b90e080015360e2c84b45c87009b78fd07181a3730e5c87009b8a9b5320e2374285c87009b8a9b5320e41c46e5c8700a38a9b532961872e43804d8098a99071982372e43804d89b8a9b5320e2472e43804d8248a99071c62672e43806089b8a9b5320e25146e6707009b8a9b07181a3733861c7009b8a9b5320e2372e45787009b8a99071cb2372e43804d89b8a9b5322a41c47e5c87009b8 else 0xa9b0715d23730e5c87009b8a99071cb2372e43804d82e8a9b071f0a372e43804d8248a9b5326241c46e7b87009b8a9b5320e23c2e43804d84f8a9b5321dc1c5148dcb90e08a9b5320e2373de5c87009b8a9b11a0e2c246e5c87009b8a994b23f23730e5c87009b8a9b07181aba46e5c8700248a9b07181ad146e5c8700248a9b5320e2373f05cc7009b8a99071cb2372e45907009b8a9b5320e25a2e43804d8248a9b532622372e65c84d8098a9b0715d2372e4430700248a9b11a0e30346e61cb90e08a9b5329623733861c7009b80015320e34946e5c87009b7a85071cb30346e5c87009b8a9b5320e2472e43804d8058a9911a0e39646e5c84d82e8a9936a0e3964ce8dc7009b8a991fa0e2372e43804d8098a9b5320e2372fe3804d82e8a9b5320e28b46e5c87009b8001536a641c4705c87009b7a9b5320e2372e43804d8808a993120e39646e5c8a209b8a9b07181a8a46e6f8b90e08a9b5322a26746e6247009b8a9b07181a37378680b90e08) else if Nat.blt b 30 then (if Nat.blt b 29 then 0xa9b5320e2373dc61c7009b8a9b5320e24746e5c87009b8a9b53265cbe46e5c87009b80015360e2e746e6b47009b7a9b53268c1c46e5c870097800153214c1c72c8dcb909b7a9b071b72ba46e5c87009b8a993122a41c72c8dcb909b8a9b5320e2372e4430700548a9b071f0a372e43804d80580015360e30348e5c87009b7001071cb2c246e5c87009b70015320e31646e7e0b909b7a9b07181a373fa5c87009b8a9b53214c1c46e5c87009b8000002a642972c8dcb909b6a9b071bd30346e5c87009b8a9b5326241c4fa5c87009b80015360e30346e5f0b90e07a9b5326241c46e6b47009b8001071a130346e5c87009b7001071cb30346e7e0b909b7001536a642946e5c87009b7a9b5320e2372f84304d8248a9b5320e2373c05c84d8008a9b5329dc1c32c5c87009b8001536a64c48388dcb989b7a99071cb23f2e43804d8098a9b5320e23c2e45c87009b8a9b5320e28546e5c87009b8a9b07181a373f05c87009b8a9b5320e2372e4430120058 else 0xa9b5320e28a4a25c87005580015360e3034b45c87009b7001536a641c4fe5c87009b7a9b071f8aba46e5c87009b8a994b20e38346e5c87009b8a994b20e34246e5c87009b8001536a641c4fa5c88009b7a9b5322a41c46e5c88009b8a994b20e39646e7e0b909b8a9b532962373fa5c87009b8a9b34a0e30346e5c87009b8838e3181a372e43806089b8a9b07181a8e5148dcb90e08a9b5320e23733a6287009b8a9b071b323730e5c87009b8a9b5320e23f3145c87009b8a9b5320e23735a61c7009b8a9b4ee0e30346e5c87009b8a9b5320e23b2e455c7009b8a9b53268a372e45187009b8a9b5320e2672e43806289b80015360e3fa46e5c87009b7a9b07181a8a2e43804d86d8001536a641c46e7f8b909b7a991aa0e2372e43804d8428a9b5320e2372f855c7009b80015360e30346e5c88602470015360e2e74fa5c87009b7a9b1520e2e746e5c87009b8a9b071b7a372e43a47009b8a9b5320e2372e44306609b8a9b5320e23f2e43804d8248) else if Nat.blt b 31 then 0xa9b5320e2472e43804d8008a9b532322373405c87009b8838e5981a6746e5c87009b8a9b5329645430e5c87009b8a99071982372e43804d8188a9b0715d2372e43804d8108a9b071fc2372e43806089b8a9b5320e2373825c8700058a9b5320e2373405c87009b8a9b5320e2372e4380500018a9b3120e2c846e5c87009b80015360e40746e5c87009b7a993120e39646e5c88909b8a9b5320e25130e5c86089b8a9b5320e2372e43804d8558a99071cb2372e43804d8598a9b5320e28a46e5c87009b8a99071a12372e43804d8008a9b5321fa6746e5c87009b8a9b5329641c48e5c87009b8a99071cb2372e43804d8138a9b5322a2373f05187009b8a9b071b32672e43806089b8a9b5320e2743d05c87009b8a9b5320e2373783804d8558a9b5320e2372e43bc4d8588a9b5320e2372e43804d88e80015320e39646e5c88a89b7a99071cb35f46e5c87009b8a37071cb30346e5c87009b8a9b5320e2372e4504830e08839051cb30346e5c87009b8 else if Nat.blt b 32 then 0xa993120e39646e5c84d8248000002a6d4c88c8dcd68e06a9b5320e2373dc3804d8108a9b07173a372e43804d8898a9b5322a2372824f87009b8a9b0716423730e5c87009b8a9b5320e2373783804d85f8a9b071f0a373c05c8a089b8001536a641c46e5f07009b7a9b5320e2373785c8a78e08a9b5329641c5145c87009b8a9b532622373145c87009b8a9b532622372e426c410098a9b5320e26746e5c87789b80015360e30347e5c87009b7a9b50a0e3035148dcb90e08a9b5329641c4b45c87009b8a9b5320e27446e5c87009b8a991fa2a41c46e5c87009b800153298c1c72c8dcb909b70015320e3964a25c88909b7a9b071572372e43804d8558a9b5320e2372e4430120008001536a641c47e5cc7009b7a9b5329fc1c46e5c87009b8a9b5322341c46e5c8700a38a9b5322a41c46e6707009b8a990718b26746e5c87009b8a9b071f0a3734e5c8a08e08a9b5322a2372ae5047009b8a9b5320e2372e4418700038a9b5320e2372e4380410558 else 0xa9b5320e2512e43044d81080015360e2fe46e5c87009b7a9b5320e28a2e4430748e08a993460e39646e7e0b909b8a99071cb2372e45247009b8a9b0ee0e2c246e5c87009b8a9b07181a372e43806289b8a9b5320e2372e44004d8248838c5981a372e43804d8058a9b5321fa373785c8700558a9b0715a26746e5c87009b8a9b532232372e44307007c8a9b5320e28c46e69cb90e08a9b071b32372e43804d8108a9b5322a41c51499c7009b8a9b5320e23746e704b90e08a9b07173a372e43804d8248001536a64468388dcd68e07a9b071f0a372e43804d80080015320e39646e5c84d85f7a990718c26746e5c87009b8a99071cb28a2e44487009b80015320e39646e5c8700a37a9b5326241c46e7e0a209b8a9b5320e2372e4418700cc8a9b5320e26d46e5c87789b8a9b5320e29246e5c87009b8a9b5320e25a2e43804d8008a9b5320e2372e442c7009b80015360e30346e704b90e070015320e3964e88dcb909b7a9b5320e2372e43804d85f8) else if Nat.blt b 50 then (if Nat.blt b 41 then (if Nat.blt b 37 then (if Nat.blt b 35 then (if Nat.blt b 34 then 0xa9b5321da372e43804d8138a9b5320e2513d05c87009b8a9b5320e2372e44207009b8838e5981a373f05c87009b8a9b53214a372e43807009b8a991fa3f41c46e5c87009b8a9b5320e2373785c87785580015360e2fb46e5c87009b7a992020e2373145c87009b8a9b5320e2373d65c84d8038a9b5320e2372e44004d8058a99071c62372e455c7009b8a9b5322341c46e6d8b90e08a9b5320e2373f05c86089b8a9b532961872e43804d8248a9b5322a41c46e5047009b8a9b5320e2373bc5c87009b8a9b5326241c46e5cc7009b8838c615a2372e43804d8098a9b5320e23734e5c8700028a9b532112372e43804d8248a9b5320e23f2e43804d8008a9b5325f2372e43806089b8a9b5320e25246e5c87009b8a99071cb25146e5c8ab89b8a9b5322a41c46e5c88209b8a9b5320e2672ae5047009b8001536a645446e5047009b7a9b5321ba372e43804d8558a99071cb2372e43804d8808a99071cb23730e5c84d8248a9b5329641c47e5c87009b8 else 0xa9b5320e27d2e44007009b8a9b11a0e30346e5c8ab8e08a9b5320e2372e65c8700a38a9b071612372e43804d89b8001532964c472c8dcb909b7a991fa0e2372e43804d8058a9b5320e25146e5c87009b8a9b5321fa3731e5c87009b8a9b07181a3730e5c87009b8a99071cb24746e5c87009b8a9b07181b0346e5c8700248a9b532964c446e5c87009b8a9b5320e23730e5cc7009b8a9b07181a8a4ce8dcb90e08a9b5320e2373f05c87789b8a9b5320e2672ae4307009b8a9b0715d2372e44304d8248a990a60e39646e5c87009b8a9b532961872e43804d80580015326ac1c46e5c87009b7001071942ba46e5c87009b7a991aa0e23c2e45047009b8a9b5320e26b3f05c87009b8a9b5320e2373d65c88609b8a9b07181a5146e5c8700548a990718b2373f05c87009b8a9b5326241c46e6cc7009b8a9b5320e2672ae3804d85e800153214b9646e5c87009b70013120e3966068dcb909b7a9b0720a3035148dcb90e08a9b5320e2373383804d8248) else if Nat.blt b 36 then 0xa9b4b20e30330e5c87009b8a9b5329623730e5c87009b8a9b5320e2372e44187004f8a99071cb25a46e5c87009b8a9b53227c1c46e5c87009b8a9b5320e28e46e5c8700548a9b5320e2373785c8830e08a991ae0e2372e45107009b8a99071cb2373783804d855800153247c1c46e5c87009b7a9b4b20e2e746e5c87009b8a99071cb2372e43804d88e8a9b5320e23c3125c87009b80015366241c5688dcb909b7a9b5320e2373f45c87009b80015320e38c46e5c87009b70015369630330e5c87009b7a9b5326641c46e5c87009b8a9b5320e2372e43804d8098a99071cb2372e426c120108a9b07157a372e43804d8558a9b0715d2372e455c7009b8a9b5320e2372e43806209b8a994b26241c72c8dcb909b8a9b07181a672e43806089b8a9b5320e2373f05e07009b80015326241c6308dcb909b7a9b5320e2674785c87009b8a9b53226a372e45047009b8a9b07181a6746e7e07009b80015320e3964a28dcb909b7a9b5320e2672e43a47009b8 else 0xa994fe0e39646e5c87009b8a9b5320e2372e44004d8008a9b5320e2372f83807009b8a9b5320e2372e4380518568a991fa0e23746e5c87009b8001536a641c478780b909b7a9b5320e2373dc55c7009b8838e59be30346e5c87009b8a994c60e39646e5c87009b8a99071cb2512e44487009b8001536a64c446e5c8518097a9b5320e2373725c87009b8001536a641c4e85c86089b7001536a641c4b45c87789b7a9b5322341c46e7e0b910c80015329641c72c944b909b70011fa0e30346e5c87009b7a9b5320e27146e5c87009b8a9b5329641c46e5c88009b8a9b5322341c46e5f07009b8a9b1520e30346e6f0b90e08a9b07173a372e43804d8008a99071982372e43804d8558a990719825a46e5c87009b80015360e30346e6707009b7001536a641c47869cb90e07a99071cb2373405c87009b8a9b5329641c4a25c87009b8a991520e32846e5c87009b8a99071982373783804d8558a9b5326641c46e5c8700828a99071cb2372e43804d8558) else if Nat.blt b 39 then (if Nat.blt b 38 then 0xa9b07181a372e43804d83080015360e2cb46e5c87009b7a9b532102372e43804d8098a9b5322a44646e5047009b8a9b5320e2372e83804d8248a9b07181a3734e5c87009b8001536a641c48e5c8860e07a9b11a0e41c6068dcb90e08a9b5320e26746e3804d85580015360e2ba46e5c87009b7000002a6d4c87e8dcde0e06a9b5329641c46e6707009b8a9b532961872e43804d8008a9b53226c1c4ce55c7009b8838e5981a9a46e5c87009b8a99071cb23f46e5c87009b8a9b07181a372e43804d8108a9b5320e2372e44187007c80015320e39f46e5c88009b7a9b5320e27d2e455c7009b80015362341c6068dcb90e07a990718aa3730e5c87009b8a9b5326241c46e7e04d8058a9b5320e2802e43804d8808a9b5320e23735a55c7009b8a9b5329652c30e5c87009b8a994b20e3965145c87009b8a99071cb27446e5c87009b8a9b5326241c46e5c8518098a9b532232372e43803e04f8a9b532232373785c87007c8a991aa0e2372e43804d8188 else 0xa9b5320e2372e456c7009b8a9b5320e23f2e43804d8028a99071cb29646e5c87009b8a9b071612372e43804d8138a9b07181a373f05c87005f8a99071c62373dc5c87009b8a9b5320e26737855c7009b8a9b5326243f46e5c87009b8a99071942372e43804d8248001536a641c46e7b87009b7a9b07181a372e43804d82c8a9b5320e28a46e5c8860cc8a9b5320e2373045c87009b8a9b5329641c4ce3804d8558a9b5320ea372e43804d8058a99071cb2372f85c84d8248a9b07181a3c46e5c87009b8a9b5320e2672e45807009b8a9b5320e2373e63806609b8001536a641c5145c87005e7a9b07181a372e43a47009b8a993466241c72c8dcb909b8a9b532232372e43803e07c8a9b5320e2372e43805189b8a9b5320e2372e45007009b8a993c60e39646e5c87009b8a9b5320e2392e43804d8098a9b5320e2372e43804f89b8a9b53261a8a46e5c87009b8a9b5320e2373383804d8008001536a643f8388dcde0e07a9b071bd2372e44187009b8) else if Nat.blt b 40 then 0x15360e3e14785c87009b7a9b5320e2672ae3804d87c8a994b26239646e5c87009b8a9b07181a372e44007009b8a9b5321fa3730e5c87009b8a9b5326241c46e5c87789b8a9b5320e23f2e4380518098a9911a0e3964a28dcb909b8a9b5320e41c4fa5c87009b8a9b5320e23737868070055800153238c1c46e5c87009b7a9b5320e2373783802a8558a9b5320e2372e43804d8508a9b5320e25a46e6f0700558a9b50a0e37c46e5c87009b8a9b5320e41c46e6b47009b8001536a644d83899c7009b7a9b07181a372e43805000580015320e32946e5c87009b7a99071c6a372e43806289b8a9b5320e2472e43806089b8001536a641c4fa5c87009b7a9b5322a41c46e5c87009b8a9b5322cc1c46e5c87009b8001536a641c46e6b47009b7989071cb30346e5c87009b8a9b071582372e45047009b8a99071a12372e43806089b8a9b07181a372e4380278248a9b5320e2373fe5c87009b8a99071cb2373f05c86089b8a9b07181a373785c8700248 else 0xa9b5320e28a2e455c7004f8a9b5320e23741e7b87009b8a9b53298cc446e5c84d8098a993320e39646e5c87009b80010719430346e5c87009b7a9b5329641c5145c8700558001536a641c46e7e0b91067a99071cb29846e5c87009b8a9936a0e3964a28dcb909b8a9b3120e2b446e5c87009b8001536a64be46e5c8830e07a99071c62372e43807009b8a9926e0e31846e5c87009b8a990718b23730e5c87009b8a9b53214a372e43804d8828a9b5329641c5145c87008e8a9b071642372e43804d86d8a9b5320e2372e43804d8488a9b5320e23736c5c87009b8a9b5320e26746e7e06089b8a9b5320e25a2e43806089b8a9b071fc2372e44307009b8a993120e31846e5c87009b8a9b07181a372e43803e0248a9b5320e2373fa670b909b8a9b071be3035148dcb90e08a9b5320e2373d25c87009b8a9b5329fc1c46e5c87008e8a9b5326228a46e5c84d8098a99071e8b9646e5c87009b8a992720e31646e5c87009b8a99071cb2372e455c4d8248) else if Nat.blt b 45 then (if Nat.blt b 43 then (if Nat.blt b 42 then 0xa9b5322a41c50c5c87009b8a99071cfa372e44007009b80015320e39646e5c84d8247a9b4b20e36946e5c87009b8a993b60e3964a28dcb909b8a9b5320e2373e65c87009b8a994b20e32846e5c87009b8a991aa0e28a46e5c87009b8a9b11a0e2ba46e5c87009b8a99071cb25146e5c84d8448a9b5320e2372e43804d8248a9b0715a23730e5c87009b8a9b5320e23f2e43806089b80015320e3a372c8dcb90247a9b11a2341c6068dcb90e08a9b532624468388dcb910c8a9b5320e23c3c05c87009b8a9b5326223f46e5c84d8098a9b5320e2372e43806309b8a990718c23730e5c87009b8a9b532622372e4380518098a9b07181a372e45807009b8a994b20e3964a25c87009b8a9b5320e23734e5c8700258001536a64c488c8dcb910c7a994b1cb23730e5c87009b8a9946e6d41c46e5c87009b8a9b071fc2373fa61cb909b8a9b5320e2372e45287009b8a9b5325f41c46e5c8830e08a9b07181a372e44304d8248a9b5320e28a46e5c87005f8 else 0xa991da0e32846e5c87009b8a9b5329641c3145c87009b8a9b07181a373825c87009b8001536a644646e6b47009b7a9b5320e2373d05c87009b8a9b5320e2373f05c88609b8a9b5322341c46e7b87009b8a99071cb2372e45107009b8001536a652c3145c87009b7a9b5320e2372f83804d89b8a9b5060e2e746e5c87009b8a9b5320e2373f06f08609b8a992223f41c46e5c87009b8a9b50a0e30346e5c8700248a9b5320e2673f25c87009b8a9b5320e27d35a5c87009b8a9b071b72b446e5c87009b8a9b071572372e43804d8248a9b3120e3035148dcb90e08a9b5320e2372e43804d8058a99071982372e43804d8638a9b5320e2373f05c84d8038a9b3125bc1c46e5c87009b8a9946e76c1c46e5c87009b8a9b5325f2372e43804d8038a99071942372e43804d8008a990719432846e5c87009b8a9b5320e2373fa5c8a089b8a9b5320e2373de3806289b8a9b5320e2372e43804d85a8a9944dcb2372e44487009b8a9b4b20e30346e6f0b90e08) else if Nat.blt b 44 then 0xa9b071fc2373785c87009b80015320e3964fa5c87009b7a991520e39646e5c87009b8a9b07173a372e43806089b8a993620e39646e5c87009b8a9b5320e2372e43804d8118001071cb36646e5c87009b7a9b5320e2372e43b04d8248a991520e39646e6f07009b8a993120e39672c8dcb909b8001536a641c46e6cc7009b7a99071c82372e43806609b8a9b5320e23746e5c87009b8a9b5322341c4a25c86089b8a99071cb2672e455c7009b8a993120e39646e5c86089b8a9b532622373f05c8a309b8a9b53214a373185c87009b8a9b5320e27d35a3804d87c8a9b07181a8a46e61cb90e08a9b5322326746e5c87007c8a9b5320e2373fa5c88609b8a9b5322a44646e53c7009b8a9b0720923734e5c8a08e08a9b5322841c46e5c87009b80015360e303514944b90e07a9b5320e2373dc3807009b8a9b11a0e36646e5c87009b8a9b5322341c46e6b47009b8a9b07158a372e455c7009b8a9b5320e2372e45347009b8a9b5326241c4785c87009b8 else 0xa99071982372e43804d8488a99071cb2372e44487009b8a9b07181a373f25c87009b8a9b5320e2372e43804d8008a9b5320e2674ce55c7009b8a9b532961872e43806089b8a9b5320e2373f05c8830e08a991fa0e2372e45207009b8a9b5320e2372e45147009b80015360e2b146e5c87009b7a993860e39646e5c87009b8a9b53214a472e43804d8248a9b5320e25a2e43806109b8a9b071efa372e455c7009b8a9b5320e2373c05c8a089b8a9b0720a30346e5c8700248a9b5320e2392e43804d8058a990719828a46e5c8700558a9b5320e2373f03806209b8a9b532664c446e5c84d80980015320e3964a25c86089b7a9b5320e2372e44006089b8a991aa2a41c46e5047009b8a99071cb28a46e5c8700558a9b5320e2373345c87009b8a991520e33046e5c87009b8a9b5320e23734e5c8a08e08a990718b31646e5c87009b80015323545446e5047009b7001071cb30346e5c8700447a9b071fc2372e43804d84f8a9b5320e23c30e5c87009b8) else if Nat.blt b 47 then (if Nat.blt b 46 then 0xa9b5320e28a46e5c8700a38a99071cb2372e43804d8248a9b5329645483899c7009b80015322334246e5c87007c7a9b5321fa372e455c7009b8a9b5320e23946e5c87009b8001536a64548388dcd38e07a9b5326841c46e5c87009b8a9b5329641c4ce56c7009b8a9b07157a372e43804d8248a9911a0e39646e5c84d8248a99071d1b9646e5c8700248a9b071572372e43804d8008a9b5320e2373c05c88609b8a9b5320e2884fa5c87009b8a9b5320e28a4ce8dc700558001071982c846e5c87009b7000002a6d4c8a88dcd38e06a9b5322a41c46e6247009b8a9b5322a41c46e5187009b8001071cb2c846e5c87009b7a9b5326244646e5c8860e08a9907197a372e43804d84f8a9b5320e2373383806089b8a99071cb25146e5c84d8368a9b5320e26731255c7009b8001536a645446e6247009b7001536a645446e5187009b7a9b071efa372e44f87009b8a9b5322a41c4ce8dc7009b8a99071d1b964a28dcb909b8a9b071fc2372e43804d87c8 else 0x1536a641c46e80c7009b7a9b5320e237382670b90e08a9b5320e2382e43804d8558a9b5320e2374246f8b909b8a9b5320e23c4785c87009b8a9b5320e28a46e7247009b8a9b5322a41c46e6f07005580015360e3736068dcb909b7a9b5320e2372e4504860248a9b5320e2372e455c7789b8a9b07181a374205c87009b8a9b532622372e428c4d8098a9b07173ad146e5c87009b8a9b5320e2372e43bc7409b8a99071cb2373145c87009b8a9b07157a372e43804d8058a9b5329642046e5c87009b8a9b07181a372e43e47009b8a9b53214c2946e5c87009b8838e595ba9646e5c87009b8a9b5320e2373f05107009b8a99071982372e43804d82480015360e3df46e5c87009b7a9b5320e23734861cb90e08a9b532622372e45104d8098a9b5320e23c34e5c87009b8001536a64548388dcf009b7a9911a0e34246e5c87007c8a9b5325f2372e43804d84f8a9b5320e2671c03044d8558a9b5325f2373785c87009b8838e5981a372e455c7009b8) else if Nat.blt b 48 then 0xa9b5320e2372e4430860248a9b5321fc1c46e5c87009b8001071cb30346e5c87009b7a993960e39652c5c87009b80015322a41c72c8dcfc09b7a9b53220c1c46e5c87009b8a9b5321fc1c46e6f07009b80015320e39646e5cc7009b7a9b53214a372e43804d8558001536a643f46e5c87009b7a9b07181a7d2e43804d87c8a9b0715a2372e455c7009b8a9b071fc23738261cb90e08a9b5320e2472e44307009b8a9b5326241c46e5c8860828a9b071f0a372e45047009b8001536a643f46e6f07009b7a9b5320e2372e63807009b8838e5981a372e43804d86d8a9b07181a373f05c8700248a991522339646e5c87009b8a9b5325f2372e43804d87c8a9b5320e2373d45c87009b8a990718c2372e455c7009b8a9b5320e2673f055c7009b8a9b5320e23f46e5c8700a38a99071cb35f52c8dcb909b8a9b5320e2472f83804d824800153268c1c72c8dcb909b7a9b11a0e30346e5c87009b8a9b5326241c46e5c88609b8a99071a12372e43805a09b8 else if Nat.blt b 49 then 0xa9b07181a5a2e43804d8558000002a6c547c28dc7009b60015360e40046e5c87009b7a9b12e0e2b446e5c87009b8a9b5320e23735a3804d89b8a9b5320e2373825c8a08e08a9b5320e2373dc418700c18a992760e32846e5c87009b8a9b5322a4464ce8dc7009b8a9b071f0a372e44307009b8a9b5320e2374067e47009b8a9b5320e28c46e5c87009b8a9b5320e2372e43804d85c8a9b5329dc1c4ce55c7009b8a9b53265c1c46e5c87009b80015360e3f846e7f4b909b7001536a641c46e5c87789b7a99071cb2512e43806089b8a9b07181a372e44304d8298a9b5320e25a2e44307009b8001536a641c46e6f07789b70015360e2c846e6f0700557a9b07181a372823804d8718001536a641c4d65c87009b7a9b5320e25a2e43804d85e8a991d60e33046e5c87009b8838e595d2372e43804d84480015360e30348e5c8700247a990718b2372e43805989b8a99071cb2372e43804d80d8a9b5320e2472e43806609b80015320e39646e8807009b7 else 0xa9b5320e28a46e5f07009b8a9b5320e2373f05c88309b8a9b5322ac1c46e5c87009b80015360e30348e8dcb90e07a9b5320e23c2e455c7009b8a9b50a0e2372e43804d86d8a9b071fc26746e5c87009b8a9b071be30346e5c8700248a9b5320e25146e5c8700a38a9b07181a372e43b07009b8a99071a1a372e44307009b8a9b5326225146e628b909b8a99071982372e43804d8008a9b0720e2b446e5c87009b8a99071cb2372e43804d8008a99071cb32846e5c87009b8a9b07181a373785c8700c18a9b5326241c46e5c8830e08a9b07181a8a46e5c8ab8e080015360e2b446e5c87009b7a990720e31846e5c87009b80015362a41c7c28dc7009b7a9b5320e24746e5f07009b8a994b20e33046e5c87009b8a99071942372e43806089b8a9b071b32372e4418700c18a99071cb2372e439c7009b8a9b5320e23734e5c8a78e08a9b5320e2373783802a8248a994b20e39646e5c87009b8a9b5320e24246e5c87009b80015320e31846e5c87009b7) else if Nat.blt b 58 then (if Nat.blt b 54 then (if Nat.blt b 52 then (if Nat.blt b 51 then 0xa9b5320e25a2e45947009b8a9b5320e2472e43804d84f8a9b5320e2473785c87009b8a99071cb2372e426c1b0248a9b5322323730e5c87007c80015360e3035148dcb90e07a9b11a0e2e746e5c87007c8a99071cb2373f05c8b909b8a99071a12372e43804d84f8a9b1520e2c246e5c87009b8a99071cb2373f05c84d84f8a99071a12373785c87009b80015320e39646e7e04d8057a9b532662372e43804d8808a99071cb2373f06f0b909b8a9b5320e2672e4418700c18001536a641c46e6f0700927001536232e746e5c87007c7a991fa0e2373385c87009b8a9b5325f41c46e7e0b909b8a9b07181a8a46e5c87006d8a9b071642372e43804d8718a9b5325f4be46e5c87009b8a9b5320e2373f03804d8058a9b5320e23c2e44f87009b8a9b2ca0e3e146e5c87009b8a9b07181a372e65c87009b8a9b5320e2372e43804d85180015360e2f346e5c87009b7a9b5320e28a46e7e0b910c8001536a64be46e7e0b909b7a9b5320e2372e4380518098 else 0xa9b5320e25a2e43804d84f8a99071cb2372e43804d8168a991520e39646e7e07009b8a9b5320e27d2e43804d8138a99071cb2372e43804d8348a9b5320e25a3785c87009b8a99071a12372e43804d87c8a99071cb2373f05c84d87c8000002a6c1c6068dcbe0e06a9b5320e41c4785c87009b8a9b53216c1c46e5c87009b8a9b53214a372e43804d8098a9b3120e30346e5c84d8098a9b5326241c4ce55c7009b8a9b0717da372e43804d88e8a9b5326241c46e5cc4d8098a993120e39646e5c88609b8a9b11a0e3ee46e5c87009b8001536a641c4785c87009b7a9b5320e2392e43804d80280015366230346e5c84d8097a99071cb2372e426c4d8248a9b5322a28a46e5047009b8a9b5322343f46e5c87009b8a993460e39646e5c87009b8a9b07181a9146e6f0b90e08001536a64c446e5cc4d8097a9b53214a5146e5c87009b8a9b5320e2372e4430120018a9b3120e3034a28dcb909b8a990719429546e5c87009b88fd071fc23730e5c87009b8) else if Nat.blt b 53 then 0x11aa0e30346e5c87009b7a9b071612372e43804d8248a9b5320e23741a6b47009b8a9b532961872e44307009b80015320e38c4a28dcb909b7a9911a0e31846e5c87009b8a9b5326241c51c8dcb909b8a99071cb2373085c87009b8a9b11a0e40046e5c87009b8a9b5320e2372e43bc7009b8a9b5320e26746e7f4b909b8a9b53268c1c4ce8dc7009b8a99071cb25146e5c88a89b8a9b532964c446e5c84d8098a9b071572372e43806089b8a9b07181a8a4a25c87009b8a9b5320e2372f85c88609b8a9b5320e2373783bc7009b8a9b5320e2372e4380518a38a991fa0e2372e45047009b8a9b5320e2373783802a8008a9b5320e2372e44308009b8a9b5320e2472e43804d87c8a9b5322341c51499cb90e08a9b532964c44a28dcb909b8a9b5320e25a2e45c87009b80015360e30346e5c87005f7a9b0715d2472e43804d8248838e5981a372e43807009b8a9b07181ad146e6f0b90e08a9b5320e2373986707009b8a9b5329641c46e6f0700558 else 0x1536a641c4ce8dc7789b7a9b5320e2372e43a84d8558a9b0715d24746e5c87009b8a99071cb2372e43804d8658a9b5320e2372e43b06089b8a9b07181a3c2e45047009b8a99071cb2372e43804d8028a9b5320e2373fa670c389b8a994c60e3964a28dcb909b8a9b5320e2373826f8b90e08a9b5320e2373663804d8828a9923e0e28a46e5c87009b8a9b5320e28e46e5c8860248a9b43e0e2c246e5c87009b8a9b17a0e30346e5c87009b8a99071c62372e43804d8558a9b5326244d46e5c87009b8838e5981a372e43804d8448a9b0715a2372e43807009b8a9b07181a373f05c84d8058a9b5320e23733a5c87009b8a993da0e34246e5c87009b8a9b07181a372e4418700c18a9b5320e23f2e43804d84f8a9b5320e25a2e43804d87c8a9b5321fa5a2e43804d8558a9b5320e23f3785c87009b8a99071cb28a4a28dcb909b80015320e33046e5c87789b7a9b0715d2372e43804d86a8a9b5320e2372e451c7009b8a9b11a0e2b446e5c87009b8) else if Nat.blt b 56 then (if Nat.blt b 55 then 0xa990718c2372e43804d8428a9b5320e2373fa7f4b909b80015328da9646e5c87009b7a9b5322a2372823804d8098a9b07173a372e43804d84f8a99119a12372e43804d87c8a9b07173a373785c87009b8a9b5320e2372e43804e0098a9b5322341c4785c87009b8a9b5322a41c46e69c7009b8a99071a127d46e5c87009b80015360e3f846e704b90e07a993120e39646e5c84d84f8a993120e39646e6f0b909b8a9b5320e26746e780b909b800153276c1c2e44487009b7a9b5322a25146e5047009b8a9b0715d28a46e5c87009b8001536a645446e69c7009b7a9b53268cc446e5c84d8098a99071cb2373f03804d8058a9b5322a42946e5c87009b8a9b5329641c5225c87009b8a9b11a0e3035148dcb90e08a9b5320e2854fa5c87009b8a9b5322341c46e5c8700928a9936a0e39646e3804d8368a9b5325f2373f05c87009b8a990a5942372e43804d8248a9b5320e23f2e43804d87c8001536a641c46e6f0a78e07001536a644646e5c8700927 else 0xa9b532961872e43804d84f8a99071cb28a2e43804d84f8a9b071b32372e43804d8558a9b5320e2372e452c7009b8a993aa3f41c46e5c87009b8a9b071b328a46e5c87009b8a9b5320e28a46e6b47009b8a99071cb2372e43806089b8a9b5320e2372e44302c0248a993120e39646e5c84d87c8a9b07181a372f05c87009b8a9b5320e27d2e43804d88e8a993be0e39646e5c87009b8a9b5322a2373405c87009b8001536a641c46e5c8860827a9b5322a2373786807009b8a9946e0e39646e7e0b909b8a9b5320e2373f05c8700978a9b5320e28a46e7b87009b8a9b5320e2372e43804d8258001536a641c46e6f0778557a9b071b32a346e5c87009b80015360e2ba46e5f07009b7a9b4b20e2c246e5c87009b8a99071c62373f05c86089b8a990718c2372e65c87009b8a9b5320e2372e44004d84f8a9b5322a41c4788dc7009b8a9946e0e29646e5c87009b8a9907199a372e43804d85f8a9b31181a372e43804d8098001536a641c46e780d39727) else if Nat.blt b 57 then 0xa990a60e39646e5c84d8248a9b5329da373125c87009b8a9b071fc23730e5c87009b8a9b5322341c46e5c8700a08a9b07181b0346e6f0b90e08838e5981a372e43804d8718a9b07181a472e43804d8248a9b071642a346e5c87009b8a9b532622372e426c048028a9b07181a3736c5c8ab8e08a9b07181a373785c8860e0800153214b9646e5c84d8247a9b5320e26746e5c88602480015360e30346e5c8700a37a99071cb25146e5c84d8098a9b07181a372f85c8700248a99071942372e44307009b8a9b53214a372e43804d8248a9b5321fa372e43804d89b8a9b5320e2382e43804d8058a9b5320e2373385c87009b8a9b5320e2512e43044d8558a9b5320e28a4a25c86089b8a9b5320e28a4ce5947009b8a990719833046e5c87009b8a9b5320e2373383804d84f8a9b5326241c46e5c8a309b8a9b5320e2373786707009b8a99071cb2514a28dcb909b8a9b07173a372e43804d87c8001536a64c446e5c8a309b7a9b5320e27d2e43804d8558 else 0xa99071a12373f05c87009b8a99071cb2373f07e0b909b8a9b5320e2372e45047009b80011fa0e3f846e5c87009b7a9b07181a6746e3804d8718a9b2f9b32372e43806089b8a9911a0e39646e5c8860e08a9b0715d25146e5c87009b80015360e3e146e69cb90e07a9b1922a41c6068dcb90e08a9b5320e2672ae55c7009b80015360e3f846e6707009b7a9b1520e2fe46e5c87009b8a9b5329841c46e5c87009b8a9b5320e23846e5c87009b8a99071cb29146e5c87009b8a9b5320e2373f05c86289b8a990718b2373f05c84d8058a9b5320e2373965c87009b8a9b5322341c46e6f0a78e08a9b5320e2373383804d87c8a9b071f0a6746e5c87009b8a9b072092372e45047009b8a9b5320e2372e43804d84d8a9b5320e2372e43bc4d89b8a9b071642372e43804d8558a9b5320e28a4ce5c87009b8001536a641c46e5c86d09b7a9b53214a372e43804d8058a9b071642373783804d8558a9b5320e2744a25c86089b80010719430346e5c8700247) else if Nat.blt b 62 then (if Nat.blt b 60 then (if Nat.blt b 59 then 0xa9b5326241c46e5c8700978a9b07181a8a46e5c87009b8a9b07181a8a46e5c8700ab8a9b53214a372e43804d8008a9b071f0a372e43804d8228a9b5320e2372e4430700828a9b5320e2372e63804d8558001536a641c4ce55c7009b7a9b5320e2373c0780b909b8a9b5325f2672e43806089b8a9b5320e2372e43804d8928a9b5320e2372e450c7009b8a9b5320e2373783804d8928a9b11973a372e43804d87c8a9b0715a23f2e43804d8098a9b071b325146e5c87009b8a9b532622372e43044d8098a9b5320e2372e44307009b8a9b50a0e2372e43804d8718a99071cb27646e5c87009b8a9b5322341c51c8dcb90e08a9b5320e2373c069cb90e08a990718c23f2e43804d8098a9b5320ea372e43804d8018a9b5320e28a2e43802a84f8a9b5326241c46e7f4b909b8a9b5320e2372e45687009b8a9b5320e2672ae4f87009b80015360e30346e6d8b90e07a9b0715d2372e43804d80980015360e3e146e780b909b7a991aa0e2372e43804d8028 else 0xa9b0715a2372e43804d8688a9b5320e26746e5c88009b8838ca15d2372e43804d8248000002a6d4c8528dcb910c6a9b5329dc1c5145c87009b8a9b07181a372e43804d85f8a9b532622372e44304d8808a991aa0e2372e43806089b8a99071cb2372e44004d87c8a9b5320e29146e5c8700558a9b5320e2372e43804e00580015360e30346e5f07009b7a9b5326241c46e69cb90e08a9b5320e2372e44307002e8a9b07181a373785c8b90e08a9b5320e2512e43044d8098a9b53226a372e44f87009b8a9b5320e2392e45047009b8a9b07181a373785c87004f8a9b5320e2374225c87009b8a99071942372e43804d84f800153270c1c46e7f4b909b7a9b532622372e45187009b8a99071a129c46e5c87009b80000020e3966068dcb90246a991520e38c46e5c87009b8a9b17a0e23738261cb90e08a9946e6241c72c8dcb909b8a9b5320e2514a25c86089b8a9b5320e2373dc5c8830e08a9b071b32372e43804d8098a9b5320e237382670c38e08) else if Nat.blt b 61 then 0xa9b5320e2372e43804d8018a9b071f0a373c05c87009b8a9b071612372e43806089b8a9b5320e2372e45987009b80015360e2b446e5c8700a370015360e36646e7b87009b7a99071e7b9646e5c87009b8a9b5320e2373f05c84d82c8a99071c62372e43804d8248a9b5320e2373f06f04d82c80015320e31846e5c8700a37a9b1520e30346e5047009b8a9b2f981a372e43806089b8a9b5329641c4765c87009b8a9b5320e2373f05c87489b80015362a30346e5047009b7a9923a0e34246e5c87009b8a9b5320e2372e43804d8538a9b5320e2372e43a84d8488a9b53226c1c46e5c87009b80015320e39646e5c8830e07a9b071fc3f846e5c87009b8a9b5320e23741669cb90e08a9b5322341c4fa8dcb90e08a9b5320e2373fa704b90e08a9b5320e2372e43b87009b8a9b5320e2372e43806d09b8001536a64298388dcb910c7a9b5320e2372e43804d84c8a9b0720a2372e43804d8718a9b49e0e3035a25c87009b8a9b5326241c46e780b909b8 else 0xa993860e2373fa5c87009b8a99071cb2373fa61cb909b8a9b2ce0e36646e5c87009b8001071cb30346e5c8700247a9b3120e3e146e5c87009b8a9b5320e2672e456c7009b8a9b07182b0346e5c87009b8a9b5320e24730e5c87009b8a9b5321fa5a46e5c87009b8a9b07181a372e43804d8098a9b12a0e28a46e5c87009b8001071d339646e5c87009b7a9b071572372e43804d84f8a9b4b20e2fb46e5c87009b8a9907198a372e44307009b8a9b5320e2373386587009b8a9b5326241c46e5c8860248a991fa0e23733861c7009b8a9b07181a5146e5c87009b8a99071cb2372e43804d85e8a99071cb2372e43804d8038001071a12e746e5c87009b7a9b5322a41c46e8407009b8a9b5320e23737853c7009b8a9b532232372e43804d8928a9b5322a41c4fa5c87009b8a9b07173a373f05c87009b8a9b5320e23737c5c87009b8001536a641c4a27b86089b7a99071a6b1846e5c87009b8a993120e34546e5c87009b8a9b0716128a2e43804d84f8) else if Nat.blt b 64 then (if Nat.blt b 63 then 0xa9b53261a372e43806609b8a9b5320e2373fa5c8ab89b8a99071a12372e43804d8888a99071982372e43805a89b8a9b5320e2372f03804d8558a9b5329b41c4b45c87009b8a9b07181a6746e3804d8558a9b53214c1c46e5c8860e08a99071c62372e43804d8008a9b5320e2372e44fc7009b8a9b071642372e43804d84880015369641c7f05c87009b7a9b5326241c46e704b90e08a9b5320e26736c5c87009b8a9b5320e28a4ce7e07009b8a9b5320e27d2e43804d8248001536a642946e5c8860e07a9b5322341c46e7e0de0e08a991fa0e2373fa5c87009b8a9b5320e25a30e5c87009b8a9b5321ba372e43804d84f8a9b071bd2372e4418700c18a9b071572372e43804d87c8a9b5320e28a4a25c86609b8a9b5320e2372e43804d8548a990718b28a46e5c87009b80015360e2b046e5c87009b7a990c20e39646e5c87009b8a9b1520e2c846e5c87009b8a9b5320e2373f06707009b8838cc181a372e43804d8558a99071cfb4246e5c87009b8 else 0xa99071cb2373d65c87009b8a99071a12372e44007009b8a9b5320e28a2e43a47009b8a9b532961872e43806289b8a9b5320e41c46e7f4b909b8a9b5320e25146e5c86089b8a9b5320e26746e5947009b8a9b5320e2372e43804d8588a9b5320e2373783804d8588001536a641c46e7f4b909b7a99071cb2372e45c87009b8a99071cb2372e43804d84f8a9b5320e2372e43804d84b8a9b071b323746e5c87009b8a9b5320e2802e44307009b80015360e30346e5c87d89b70015360e30346e6b47009b7a9b5322a41c46e5cc7009b8a9b0715a23f46e5c87009b8a9b5320e2373f05687009b8a9b07181a372e456c7009b8a99071cb2372e44484d8248a9b071b32372e43d47009b8838ca181a372e43804d82480015360e30346e7b87009b7a990718c23f46e5c87009b8a99071cb2372e45947009b8a9b5320e2512e43044d8058a9b5320e2373fa5c89f09b8a9b5320e23f30e5c87009b8a9b5320e2472e43804d8108a9b071b32372e43804d8058) else if Nat.blt b 65 then 0xa9b07181a372e43ec7009b8a9b071f0a372e455c7009b8a99071cb23738261cb90e08a9b532622373785c84d8098a993462a41c72c8dcb909b8a9b5320e2373f03805009b8a9b5320e2372e455c860248a9b5322a41c4785047009b8a9b07181a373f05c88609b8a9b2f20e30346e5c87009b8a9b5320e28a46e5c8700a08001536a64544785047009b7a9b5320e41c46e780b909b8a9b5320e2373e05c87009b8a9b17a0e23730e5c87009b8a9b5322a41c46e7e04d8058001536a641c46e780b909b7a9b18e0e30346e5a07009b8a9b5329618730e5c87009b8a9926e3f41c46e5c87009b8a993123f41c46e5c87009b8a9b5320e2373125c87009b8a9b5320e23730e5c88009b8a9b5320e26746e5c87009b8a9b5320e2373c05c89f09b8a990718b2372e43804d8098a9b5320e27d2e43804d8008a9b5320e2373f27e0b909b8a9b07181a612e43804d8718a990718b25146e5c87009b8a993120e39646e61cb909b8a9b5320e2373c05c8ab89b8 else if Nat.blt b 66 then 0xa9b071612372e43804d84f8a9b5320e2373805c87009b8a9b07181a3737861cb90e08a9b5320e2372f03804d8488a990719423730e5c87009b8838e5981a372e43804d82480015360e2c846e5c87789b7a9b0720e3e146e5c87009b8a9b07183b0346e5c87009b80015360e3e146e5c87009b7a9b1520e3034ce8dc7009b8a9b5320e2372e43803e05f8a9946e0e39646e5c87009b8a9b5320e28a46e5c8778558a9b5329dc1c46e5c87009b8a9b071b4a372e43806289b8001536a641c46e5c8860247a9b532622372e426c3e0098a99071ea39646e5c87009b8a993b20e31846e5c87009b8a990718c2372e43805189b8a9b071f0a372e44f87009b8a9b5320e2373fa5c87009b8a9b5320e23735a57c7009b8a992fa0e39646e5c87009b8a9b5320e2373785c87005f88a9071cb30346e5c87009b80015320e34546e5c87009b70015325f39646e5c87009b70015360e3fb46e5c87009b7a99071cb2372e44187009b8a9b11a0e30346e5c8700298 else 0xa9b5320e2372e44f87009b8a9b5320e2372e455c7009b8a9b5326241c47e5c84d8098001536a64c447e5c84d8097a990719823730e5c87009b8a9b07158a372e43806089b8a991aa0e2373f05c87009b8a9b07181a373785c8b00e080015360e3034785c87009b7a9b5326244646e5c87009b8a9b5320e2372e43804d8578a9b532a041c46e5c87009b8a9b5320e2372e6380518098a9b5321141c46e5c87009b8a9b5329641c46e5c87789b8a9b5320e2373e25c87009b8a9b5320e2372e45047009c8001536a642246e5c87009b7a9b07181a372e43802a824800153270c1c46e5c87009b70010718c30346e5c87009b7a9b5320e2372e4430700248a9b5320e2372e43804d84980015360e30351499cb90e07a9b532964c446e5c88609b8a9b5322328a46e5c87007c8a9b5320e2372e83804d8108a9b5320e2372e43804d84a8a9b53214a372e44307009b8a9b17a0e3f846e5c87009b8a9b5320e2422e45187009b8838e595a2372e43804d8098
def htChunk_16 (b : Nat) : Nat := if Nat.blt b 3 then (if Nat.blt b 1 then 0x17d57c17ce9e177fd0175aa117362c16fb8c16867216609e16484b15e7a715e289156830150bdc14f77914d919148451146edd1440e9143b6513ee6e13be3013a48d138ad513612f1348bf1302c812db6112abf31282d41263b2124c85124004121a3211ba7c10fb4210dbd510d05310cb4710aac7105b390fce160f6f090f5a9b0f54b10f00180e9a690e98ab0e91fc0e1dc30e06320dfd310df15e0dedba0de2000d67330d5ebb0d09df0ca83a0c7f280c5ac70c56d60c54dd0bff980bc32d0b7ea90b5c410af14e0ae2350ab5cc0a52cd0a1da209e29509d6a50984dd08f23008cfde08c0b40877be08411a08331808237b07f7a207e28d07ce0d07b85d07625707285e07224707160506f1fc06aa34069e78068ace068152067fd40649320645fb063c040634fe06074b05eb44058eda056d6604edf50483c2046055043abb03f28503bfe403898103270902ef7b02ef3802e82302a3020257c20238f602086901c55f01810f0169d301470001173c00de0c008549007b3900483c0036ef else if Nat.blt b 2 then 0x325b8c3218d331ca223154d831445d3108cc30f2113087bb3057902ff3a02fc0a12fa40f2f89de2f693f2f4bd42f0fde2ee7322ec7a22ddb052d8c262d0dd32cb1062c9e2c2c9cb92c96d62c27f42bbcc62b69662b2c562b0e3029ec8b29d36629b76a29b574295f9e28aa3928a4d827daff27d9f727b78627b3dd2767422761c1275434274d642736512724c927014926f14f26cf902651ea264b8d26259625df6425c3bf25a234253c472539bd2539b525253524bb0a24b947249c01247861245bdb2447d824046b23c432234aad230d8522f8c022cda822ae3922ad2121d3aa219e192199a021768f216184212be3210cd320d39820bbd5209b25208f3e207c582072de2057122031d320271f201a891fd6f51fd4931fa0f81f6f4d1f6d371ebc741e5dcd1d7d191cc5a81ca0d01c935b1c705c1c5f421c56dd1c569a1c506a1c4f8a1c1c261badb81b609a1adea11acea01ac4261a7b311a6f041a6ad61a37411a2b2c19f8a2199a5f1972ca1962ad192c4218c64918c25f18ac19183345 else 0x4ee8ee4eb7554ea3f74e891b4e6fa04e5c354e46c34e2ae84dd80d4d882c4d46124d0d1d4d01dd4be4dc4b6fb74b64ab4b1b914aa4324a85064a5f0a4a581f4a4c384a44664a3b9f49ac3a49a757499956497aa4496fe848ae3e48a2f848930d481ee5481e7447fde247f4f045a94245132c44fef644e6e944e6b144bb4844b443446caa4441234420774416bc437dce431e9242e264426225425bee4255d74242e341eb8041e11d41d40941bd5b41a7fc41965b41748341327040ec6940ebe840bbe6405a834010543f954a3eca993eb9163eb4733e9a243e8daf3e21813dd0453dab683d6a713d5a433d05b93cd8623cd2d53cced23c41eb3c1f003bf4c53bd6f23bc4703ba77c3b67553b3c543ad61d3aa01e3a47d83a2ac83a27b739c43c398bdd38ee3838de95383c833825733814ee37eef237dafe379fb13761e537164c36b4b636245b360cec35f46235e57135c155357640351dac351ba63502f134ddcd34d5af34b290349bb3348e8a3407c4336e21330ebd32e33232c92d328034) else if Nat.blt b 5 then (if Nat.blt b 4 then 0x6d9f176d87d16d594a6d0c9f6ca2066c847d6c3c3f6bc6026b50f06b0dd96ac6bc6a49fe6981db68b4916861e0684ff0683a6d68374867b8ae6765cd66e1eb66d1dd66c307665ffa66462b65f14265b0e76555716552b76540876514f4648d83645937639a5f637e16635c18632fe06322796226ea61d61e618285614c67613713612c7160cd2e603c255fcf775fc5c85f8f805ef8655ebf435e376b5e0b025e047d5de6165dc4795d97575d89c25d66875d61f35d0ac95cefcc5caa745c8f4c5c697e5c33a95c23e15c10375bb3165bae215b6b9a5afa385ae0245ab9285a7f495a62535a4b495935105934d3592af358ef9557d187578b5b570d4d56efec56c39b5659b3560d3b55c7b85590a655552c53f07753bf7153b8545326825301f552af3852ae47523fb852397c52102d52089851fc46517caa51071250e91a50d67750bbd650b1d650b10050adfb5080ca5077ea50439c5013485012225008874ff57d4fe5284fc12c4fb94d4fb13a4f96ac4f966f4f8dc04f5b674f5aca4f2ee4 else 0x92120491cc7191b63c9134739007ff8f7c1b8f126b8f02028edac38e900c8e62178e2c8c8da2d98d2a288cef878c1de18b9bc88b97d58b079d8afe3b8a8fba8a1ce38a07a888ca9a887c50880fd488063987a001876901872858870c7c87065286f77786e6dd8692cc85f0a3856b1b84142084084383e85083d2c483b343834e6b8331a8830c6782b96081af6f811cd88109e280c1848074478072688050c0804447801f087f772c7f437d7eb1787ea2527e8b147e88247e06907dfbb07dcbe07d8b257d6d037d27567caa397c6b1d7bc1177bbc6f7bb7b87b68c27b374d7b27d97ac40c7a726b7a2ceb79c74279ba5a7933b878c7d978be0a78aa61787b9477ad1477a6f47749e377466776c32876abe0768d8f75e80775acf17598a875759074b9d374a87274305f73b4f27371a773231c73079f72d9f972cedd7282327258c471e9e0716ac4714198710a0e70bcbc70a9cb7060e870563d70389e6fd5646f73066f500d6f07786ed9d46ec82a6ebbf06e98076e52606e0c8a6dfe766df121) else if Nat.blt b 6 then 0xde66f3dc6044dac906da0203d9323ed90d4fd8ce43d80966d7be92d69785d5d924d4f68dd4a683d295c1d268d1d225b0d1db02d166ded014c7cfe8c4cfa878cf472ecf06b0ce3326cd896bcd32c2cd11ddcbb088cb601cca39b9c98e55c91bdfc90444c6961dc6761ec5c530c5922bc514ddc447f8c212c5c19b23c08462c0573ac039b1bf4178befb25be72d0bb6a98bab030ba1ed2b971cab8b1fab8901ab88d15b6c808b66bddb5ef94b59dffb53afab46401b44260b3e2c7b2e914b0fe9fb0e21cb0a420b0784db04fc6af1c72ae99ddae6661ade4daadc202acdc0eac4db4abdf16aba165ab3511aa0dbaaa0343a97575a8bef9a865b3a78fefa7481fa6d98fa63e68a52587a4db0da41378a3e9e5a3e255a3d6b9a3ce33a37d27a25ff0a223a7a03566a00a129f5e0c9efd369ef2fa9d667f9d35849d21139d11ad9cfac09cb7ce9c44c19c045e9bffd29ba4069b4f799abb909a5a5099861098df959894109883c298091a9724b1972305960df795f6ce935568930c499270739241b6 else 0xfed681fca943f7f020f50fd6f1db7af14b43f010ecee4a82ebc563ea8f0be8f75de76512e66e3de2a939df7929df2e81df2b1ade68d7
def stChunk_16 (b : Nat) : Nat := if Nat.blt b 12 then (if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0xa99071cb2d746e5c87009b8a9b5320e30c46e5c87009b8a9b5325641c46e5c87009b8a993120e3965bc8dcb909b8a9b5320e1d42e43806089b80015360e2ae46e5c87009b7a9b532a1c1c46e5c8700a38a9b5322a41c46e54c7009b8a9b5323241c46e5c87009b8a9b5320e3b546e5c87009b8a9b5327ec1c46e5c87009b8a9b5320e41c46e5c87009b8a99071cb2372e44607009b8a9b5320e2dd46e5c87009b8a99071cb2372e43804d8948a9b532a3c1c46e5c87009b8a9b071f0bbc46e5c87009b8001536a641c46e5c87009b7a9b53296c1c46e5c87009b8a9b5320e3bc4b45c87009b8a9b5322b41c46e5c87009b8a9b5320e41846e5c87009b8a9b5328241c46e5c87009b8a9b5322a23728244c7009b8a9b5325241c46e5c87009b8a9b5320e2372e43804d83b8a99071cb237434734b909b8a9b5320e2373825c87009b8a9b07181a3730c5c87009b8a9b5320e2372e43806009b8a99071d939646e5c87009b8a9b5320e2372e43804d8628 else if Nat.blt b 2 then 0xa9b28e0e30346e6f0b90e08a9b07181a372e45047009b8a9b532962de30e5c87009b8a9928e0e32846e5c87009b8a9b5321041c46e5c87009b8a9b5320e2672e44847009b8a9b5320e2372e43406089b8a9b5320e2372e44bc7009b8a9b5320e2372e43804d8608a9b28e0e2fd46e5c87009b8a9b5320e2e246e5c87009b8a9b5320e2373f25c87009b8a9b5320e2de46e5c88009b8a9b5322341a46e5c87009b8a9b5320e2372e45c07009b8a9b5320e2de46e3804d85b8a9b53214a372e44907009b8a9b5320e2372e43804d89a80015320e32146e5c87009b7a993ea0e33046e5c87009b8a9b5320e3bc46e704b90e080015360e2a546e5c87009b7a993ea0e39646e5c87009b8a991fa0e2372e44407009b8a9b07173ade46e5c87009b8a9b5320e2372e44887009b8a9b5320e3bc47e5c87009b8a9b532622372e44a04d8098a990718c2374305c87009b8a9b5320e2372e43804d8078a9b5320e2372e43805489b8a9b5320e2dc4785c87009b8 else 0xa9b5327d41c46e6f0700558a9b5320e23735a3804d87c8a9b5320e23730a5c87009b8a99071cb2372e43806009b8a9b5320e2372e43804d8178a9b5322341c46e5c87009b8a9b5320e3bc46e5c88009b8a9b53290c1c46e5c87009b8a9b07181b0346e5c87009b8a9b07181a372e44307009b8a9b5320e2374205c87009b8a9b5320e2372e43804d8968a9b071de2e746e5c87009b8838e5981a3739a5c87009b8a99071cb29446e5c87009b8a9b5320e28a46e5c8700948a9b5320e3f446e5c87009b8a9b5320e2373605c87009b8a9b53252c1c46e5c87009b8a993120e3bc72c8dcb909b80015320e31c46e5c87009b7a9b5320e23735a5c87009b8a9b5325f2372e43805c09b8a9b5329cc1c46e5c87009b8a99071cb2372e455c7009b8a9b5320e2372e43805b09b8a9b5320e2373dc5c87009b8a991aa0e2372e44a07009b8a9b5320e2de46e6707009b8a9b53254c1c46e5c8860e08a990720d39646e5c87009b8a9b5320e37246e5c87009b8) else if Nat.blt b 4 then 0xa9b5329c41c4a25c87009b8a9b5320e2a146e5c87009b8a9b28e0e2ae46e5c87009b8a9b5320e25a2e43804d8558a9b5320e2372e43805409b8a9b07181ad046e5c87009b8a9b5320e40446e5c87009b8a9b5320e2372e43804d8048a9b5320e2352e43804d8248a9b5328341c5145c87009b8a99071cb23732a5c87009b8a9b5329541c46e5c87009b8a991fa0e3bc46e5c87009b8001536a641c46e5c86b09b7a9b53251c1c46e5c87009b8a9b5320e2632e45a87009b8a9b5327d4c446e5c84d8098a9b5320e3bc46e6707009b8a9b5320e2d446e5c87009b80015320e33046e5c87009b7a9b07181a372e44847009b8a9b5320e24146e5c87009b8a9b5320e2372e43944d8398a9b53295c1c46e5c87009b80015320e39646e5c87009b70015360e30346e5c8700867a9b532963bc30e5c87009b8a9b071612372e44a07009b8a9b5320e23746c5c87009b8a9b5322a41c46e3804d8398a9b5320e2372e43807009b8a9b5320e27d2e43804d87c8 else if Nat.blt b 5 then 0x15320e38946e5c87009b7a992960e39646e5c87009b8a9b07181a372e43804d83c8a9b5328fc1c46e5c87009b8a9b07181a372e43805b89b8a9b07181a372e43804d84f8a9b07181a373785c87009b8a9b5320e2372e65c87009b8a9b5320e2372e43806889b8a9b5320e2372e447c7009b8a9b5320e27046e5c87009b8a99071c4a372e43806009b8a9b5320e2372e44a0700a38a9b532a441c46e5c87009b8a9b07181ade46e6f0b90e08a9b5320e2373205c87009b8a9b5320e2372e43cc7009b8a99071942de46e5c87009b8a9b53253c1c46e5c87009b80015320e39646e5c84d81e7a9b5320e3be46e5c87009b8a99071cb2372e43804d8608a993ea3541c46e5c87009b8a9b5320e2372e43b07009b8a9b5320e35d46e5c87009b8a9b5320e2372e43804d81e8a99071cb38446e5c87009b8a9b5320e2372e43804d80b8a9b4d60e30346e5c8700248a9b5320e2374645c87009b8a9b5320e2a046e5c87009b8a9b5320e2342e43804d87c8 else 0xa9b5320e2372e43806b09b8a9b5329ac1c46a5c87009b8a9936a0e39646e5c87009b8a992a20e39646e5c87009b8a9b071de30346e6f0b90e08a9b5324a41c46e5c87009b8a9b5320e2373b85c87009b8a9b07181a372e444c7009b8a99071de32846e5c87009b8a99071cb2372e43807009b8a9b53214a372e44a07009b8a994b20e32246e5c87009b8a9b5326241c46e5c84d8098a9b071662372e44a07009b8a994860e33046e5c87009b8a9911a0e39646e5c87009b8a9b07181aa246e5c87009b8a9b07181a372e43804d87c8a994860e39646e5c87009b8001536a641c46e5c89e0e07001536a64c446e5c84d8097a9b3ea0e2c246e5c87009b8a9b5328041c46e5c87009b8a99071cb2372e44a06689b8a9b5320e2372f45c87009b8a9b5320e37446e5c87009b8a9b5326241c46e5c89509b8a9b5320e3c546e6f0b90e08a9b5326241c4a28dcb909b8a9b5329641c4e05c87009b8a9b5322a3cc46e5047009b8a9b5320e41746e5c87009b8) else if Nat.blt b 9 then (if Nat.blt b 7 then 0xa9b5328ec1c46e5c87009b8a9907190ade46e5c87009b8a9b5320e23c2e45047009b8a993b60e39646e5c87009b8a9b5320e1722824cc7009b8a9b5320e35846e5c87009b8a99071cb2372e43804d8448a9b5320e3c446e5c87009b8a9b5320e2372e44306809b8a9b3fa0e30346e5c87009b8a9b0716f2ae46e5c87009b8a9928e0e31146e5c87009b8a9b5320e37446e5c84d81e8a9b5320e2372e43804d8828a9b5320e2372e4418700c18a9b5320e40d46e5c87009b8a9b5320e1872e44847009b8a9b07181a374486f0b90e08a9b071db30346e5c87009b80015323541c46e5c87009b7a9b5320e2312e43804d8558a9928e0e33046e5c87009b8a9b5320e3bf46e5c87009b8a9b5320e28a46e5c8700608a99071de39346e5c87009b8a9b53285c1c46e5c87009b8a9928e0e39646e5c87009b8a9b5320e2372e44247009b8a9b5320e2de46e5c87009b8a9b5320e28a4a25c87009b8a99071cb2d446e5c87009b8a990718e2372e43804d81e8 else if Nat.blt b 8 then 0xa9b5320e2372f05c87009b8a9b07181a6746e5c87009b8a9b5320e2373ac5c87009b8a9b5320e2372e43804a0248a9b5328941c46e5c87009b8a9b5320e2372e43804d8138a9b5320e24f46e5c87009b8a99071cb37446e5c87009b8a9b53297c1c2e44b47009b8a9b532622372e43804d8098a990718e2de46e5c87009b8a9b5327d42946e5c87009b8a9b5322a2372824a07009b8a9b5320e2372e43804d8748a9b071de2ae46e5c87009b8a9b5320e2df46e5c87009b8a9b5320e22c2e43804d84f8a9b5320e2d346e5c87009b8a9b45a0e30346e5c87009b8a9b5320e26046e5c87009b8a9b5320e2372e43804d81b8a99071cb27046e5c87009b8a9b5320e35c46e5c87009b80015360e2c246e5c87009b7a9b5322341c5148dcb90e08a9b5320e2372e43804d80f8a9b5326341c46e5c87009b8a9b5328841c46e5c87009b8a9b071b5a372e43806809b8a9b5320e2372f84a07009b8a9b5327d41c46e5c8700a38a99071cb2372e43804d81e8 else 0xa9b532a1c1c46e5cc7009b8a9b5320e2372e43804d8808a9b5327d41c46e5f07009b8a9928e3541c46e5c87009b8a9b071d42372e444c7009b8a9b5320e2372e44647009b8a9b4460e30346e5c87009b8a9b5321a2d046e5c87009b8a9b5327fc1c46e5c87009b8a9907206b9646e5c87009b8a99071c62372e44a07009b8a9b5320e2472e43804d8248a99071dfb9646e5c87009b8001536a641c46e5c8700a37a99071cb25146e5c89409b8a9b07181a372e43804d8868a99071982de46e5c87009b8a9b531f9a372e43804d87c8a9b5320e41b46e5c87009b8a99071cb2de46e5c87009b8a9b5328e41c46e5c87009b8a99071cb2372e43804d8368a9b07181ade46e5c8700868a9b5329c41c46e5c87009b8a99071d1b9646e5c87009b8a9b07181a5546e5c87009b8a9b5320e28a2e44b47009b8a992520e39646e5c87009b8a9b5328544646e5c87007c8a9b53252c1c46e5a87009b8a9b5320e2372e44ac7009b8a9b532624a346e5c84d8098) else if Nat.blt b 10 then 0xa9b071e630346e5c87009b8a9b5320e2373dc4a07009b8a9b5320e2372e43804d8088a9b5320e3c246e5c87009b8a9b5320e30b46e5c87009b8a9b5320e2372e44e4700608a9b5320e3bc46e5c86b09b8a9b07181a372e43804d8738a9b28e0e2c246e5c87009b8a9b5320e24746e5c87009b8a9b5324b41c46e5c88009b8a99071de33046e5c87009b8001536a641c4c65c87009b7a9b5327d45446e5047009b8a99071de39646e5c87009b8a9b07181aa25148dcb90e08a9b0715d2372e44a07009b8a9b53214c1c46e5c87009b8a99071cb2de46e5c84d81e8a9b5320e40d4ce8dc7009b8a9b53281c1c46e5c87009b8a9b11a0e30346e5c8940e08001536a642946e5c87009b7a99071cb2372e43804d88a80015360e2cc46e5c87009b7a9b5329241c46e5c87009b8a9b07181a373f05c87009b8001536a641c46e5b47009b70015320e39646e5c86689b7a9b5320e2372e44447009b8a9b50e0e30346e5c87009b8a9b5320e3ac46e5c87009b8 else if Nat.blt b 11 then 0xa9b07181a4346e5c87009b8a991aa0e2de46e5c87009b8a9b53251c1c46e5c8700a38a9b5329a41c46e5c87009b8a9b5320e2372e43804d85f8a994e20e39646e5c87009b8001536a641c46e5f07009b7a9b5329641c5145c87009b8a993ea0e38c46e5c87009b8a9b5320e27446e5c87009b8a9b5329ac1c48e5c87009b8a9b5320e2674585c87009b8a9b07181a373a45c87009b8a9b5329fc1c46e5c87009b8a9b5327c41c46e5c87009b8a9b5320e2372e44f07009b8a9b5320e2374425c87009b8a99071cb2d74a28dcb909b8a9b532622de46e5c84d8098a9b5320e2d946e5c87009b8a9b071662372e43804d8608a9b5320e27d2e44a07009b8a9b5320e2373405c87009b8a9b07181a372e45a87009b8a9b071b32372e44a07009b8a9b5320e23735a4a07009b8a9b5320e2372e43804d8558a9b5320e28a46e5c87009b8a99071cb2372e43805889b8a9b5320e23743a5c87009b8a9b52e0e30346e5c87009b8a9b5320e2372e43804d88e8 else 0xa9b5320e25146e5c87009b8a9b07181a3730e5c87009b8a9950e0e31846e5c87009b8a9b29a0e30346e5c87009b8a9b0716f2c246e5c87009b8a9b532964c446e5c87009b8a994be0e39646e5c87009b8a9b5327d41c46e7b87009b8a9b07181a374585c87009b8a9b5320e3ab46e5c87009b8001536a641c46e5c86e89b7a9b07181a374525c87009b8a9b5320e2372e43805c09b8a9b5320e27346e5c87009b80015360e3034f68dcb90e07a99071cb2372e44a04d8248a9b5325441c46e5b47009b8a9b5320e2373f05c86089b8a9b5322a41c46e5047009b8a9b5325f2372e43806089b8a9b5320e3bc46e5c89e0e08a9b532623bc46e5c84d8098a9b5320e2373da5c87009b8a9b071fc2372e44d07009b8a99071cb2372e43806689b8a9b3ea2341c6068dcb90e08a9b07181a372e44b07009b8001536a645446e5047009b7a9b5328441c46e5c87009b8a9b5328ac1c46e5c87009b8a9b5320e2372e449c7009b8a9b5320e2373ae5c87009b8) else if Nat.blt b 18 then (if Nat.blt b 15 then (if Nat.blt b 13 then 0xa9b5320e2cd46e5c87009b8a99071982372e43804d8558a9b5320e2372e44807009b8a9b5329641c4a25c87009b8a9b5325141c46e5c87009b8a99071cb2372e43804d8558a9b5329623730e5c87009b8a99071cb2372e43804d86c80015320e38c46e5c87009b7a9b5320e2372e43804d81d8a9b07181a372e44a07009b8a9b5320e2372e4380608998a9b5326641c46e5c87009b8a9b5328f41c46e5c87009b8a9b5320e2372e43804d8098a9b5320e2372e43806209b8a9941a0e39646e5c87009b8a9b5320e2374625c87009b8a9b5327d41c4fa5c87009b8a9b0715d27846e5c87009b8a991aa0e3bc46e5c87009b8a9b53297c1c46e5c86b09b80015320e3964a28dcb909b7a9b5320e26246e5c87009b8a9b5324ac1c46e5c8830e08a9b50e0e2b446e5c87009b8a9b07181a373a85c87009b8a9b5320e3c746e5c87009b8a9b5327d41c46e6b47009b8a9b53251c1c4c65c87009b8a9b07184b0346e5c87009b8a9b5320e2372e44a87009b8 else if Nat.blt b 14 then 0xa9b5320e2702e44847009b8001536a641c4fa5c87009b7a9b5322a41c46e5c87009b8a9b5320e37d46e5c87009b8a9b5325d41c46e5c87009b8001536a641c46e6b47009b7a9b53251c5446e5047009b8a9b5320e2372e456c7009b8a99071cb29646e5c87009b8a9b53290c1c46e5c86e89b8a9b5325041c46e5c87009b8a99071942372e43804d8248001536a641c46e7b87009b7a993ea0e39646e5c84d8248a9b5324c41c46e5c87009b8a9b5322341c46e5c8700848a9b5320e2372e43805189b8a990718aa372e44a07009b8a9b53254c1c46e5c8700948a9b5320e2372e43804d83a8a9b53251c1c46e5f07009b80015360e2ba46e5c87009b7a9b071de2c246e5c87009b8001536a641c46e5c07009b70015362341c6068dcb90e07a9b5328a41c46e5c87009b8a9b3ea0e2c846e5c87009b8a9b5327e41c46e5c87009b8a9b5320e2db47e5c87009b8a9b2aa0e30346e5c87009b8a9b5320e40946e5c87009b8a9b5320e3bd46e5c87009b8 else 0xa9b5320e2372e43804d8248a9b5320e2372e44a07789b8a9b0720d30346e5c87009b8a9b5326241c46e5c86809b8a9b5320e27246e5c87009b8a99071cb2374465c87009b8001536a641c4685c87009b7a9928e0e3964a28dcb909b8a992a20e38c46e5c87009b8a9b53283c1c4ce8dc7009b8838e5981a372e44a07009b8a9b5329d41c46e5c87009b8a9b5320e3c646e5c87009b8a9b5321fa372e44a07009b8a9b5320e2372e43804d8488a9b5320e23736c5c87009b8a99071cb2372e44a87009b8a9b5329041c46e5c87009b8a9b5320e3cc4785c87009b8a9b5320e2372e44b47009b8a9b5327d41c46e5cc7009b8a9b5320e3cc2e44cc7009b8a9b5320e2372e454c7009b8a9b07181ad746e5c87009b8a9b53214ade46e5c87009b8a9b5328f44646e5c87009b8a9b5320e2372e45587009b8a9b53219c1c46e5c87009b8a9b5320e2372e43805e89b8a9b5320e2372e43804304f8a9b5320e2372e43806e89b8a9941e0e39646e5c87009b8) else if Nat.blt b 16 then 0xa9b53251c1c46e6b47009b8a9b5320e3ad46e69cb90e08a9b5320e3ca46e5c87009b8a9b5320e23734e5c8a08e08a9b07181a8a46e5c8940e08a991520e39646e5c87009b8a9b53251c1c46e7b87009b8a9b5320e23746e5c87009b8001536a641c2e44b87009b7a99071cb2372e44e47009b8a9b5325441c46e7b87009b8a9b5322941c46e5c87009b8a9b5320e25446e5c87009b8a9b28e0e2ba46e5c87009b8a994d60e32846e5c87009b8a9b5320e2373d05c87009b8a9b5320e2373f05c88609b8a9b5320e30a46e5c87009b8a9b28e2341c6068dcb90e08a99071cb2373f0734b909b8a9b5320e2372e43804d8058a9b5320e2de46e5f07009b8a9b5329641a46e5c87009b8a9b0715a2372e44a07009b8a9b5320e3bb46e5c87009b8a994520e39646e5c87009b8a9b5320e2d848e5c87009b80015320e39646e5c84d8247a990718c2372e44a07009b8a99071cb37e46e5c87009b8a9b532a241c46e5c87009b8a9b5320e3b146e5c87009b8 else if Nat.blt b 17 then 0xa99071cb2372e43804d8248a9b5320e2372e43805e09b8a9b3ea0e2b446e5c87009b8a9b5320e2372e43804d8858a9b5320e2372e43805209b8a993ea0e31846e5c87009b8a9b071572372e43804d8008a99071c62de46e5c87009b8a9b5320e2372e43804d8378a9b5320e2372e43804d8878a9b5329ac1c46e5c87009b8a9b5320e3cb46e5c87009b8a9b5327d41c46e5c87789b8a9b5322a41c4ce8dc7009b8a9b5320e3a446e704b90e08a99071cb2372e44487009b8a9b5320e2372e45046e09b8a9b5320e2372e43804d8008a9907190a372e43804d8398a9b5325a41c46e5c87009b8a9b53255c1c46e5c87009b8a9b5320e2372e43806909b8a9b5321941c46e5c87009b89f5071cb30346e5c87009b8a9b5320e23c2e44a07009b8a9b5320e2373c05c8a089b8a9b5320e3bc46e5f07009b8a99071cb2372e44b47009b8a9b07181a7b46e5c87009b8a9b5327d43f46e5c87009b8a9b5320e23745c5c87009b8a9b5321741c46e5c87009b8 else 0x1536a641c46e5c87789b7a9b0716427746e5c87009b8a9b53299c1c46e5c87009b8a9b5327d41c4785c87009b8a9b5320e17225a3806089b8a9b5320e2373f054c7009b8a99071cb2372e43804d8398a9b5320e2372e43c87009b8a9b5320e2372e44d47009b8a9b5321fc1c46e5c87009b8001071cb30346e5c87009b7a99071de38c46e5c87009b8a9b3ea0e3035148dcb90e08001536a643f46e5c87009b7a9b071f0a372e45047009b8a9b5320e2db46e5c87009b8a9b5320e23744a5c87009b8a9b5320e2e446e5c8700868a9948e0e39646e5c87009b8a9b11a0e30346e5c87009b8a9b5326241c46e5c88609b8a9b5320e2372e43344d8098a993120e39646e734b909b8a9b5320e2373cc5c87009b8a9928e0e39646e5c84d8248a99071e0b9646e5c87009b8a9b5320e3c346e5c87009b8a9b071fc3b646e5c87009b8a9b5320e25146e5c86689b8a9b5329941c46e5c87009b8a9b53250c1c46e5c87009b8a995120e39646e5c87009b8) else if Nat.blt b 21 then (if Nat.blt b 19 then 0xa9b5320e2372e43804d82f8a9b5320e2372e45bc7009b80015360e3035148dcb90e07a9b5320e3bc4fa5c87009b8a9b5320e3bc46e6b47009b8a9b071dc30346e5c87009b8a9b5320e3bc46e7b87009b8a9b5320e36146e5c87009b8a9b5320e2372e4380518098a9928e0e31546e5c87009b8a99071a123742c5c87009b8a9b5320e2373aa5c87009b8a994960e39646e5c87009b8a994d60e39646e5c87009b8a9b5320e28a2e44847009b8a9b5320e3b646e7f4b909b8a9b5322a41c46e5a87009b8a99071cb2372e43804d8008a9b5320e3f346e5c87009b8a9b5320e2372e448c7009b80015360e2b446e5c87009b7a9b5320e35a46e5c87009b80015360e3a846e5c87009b7a994b20e39646e5c87009b80015320e31846e5c87009b7a9b5320e24446e5c87009b8a99071cb29946e5c87009b8a99071cb2372e43804d8848a9b5320e2372e45ac7009b8a9b5320e2de4fa5c87009b8a9b5320e2372e44947009b8a9b5320e2372e43804d8778 else if Nat.blt b 20 then 0xa9b48e0e2c246e5c87009b8a9b53284c1c46e5c87009b8a9b5320e29046e5c87009b8a9928e0e31846e5c87009b8a9b5325ec1c46e5c87009b8a9b53251c1c46e5c87789b8a99071de39646e5c84d8248a9b5320e2512e44847009b8a9b5320e3b646e5c8700988a9b5320e2372f65c87009b8a9b532622d046e5c87009b8a9b5320e3bf2e44b87009b8a9b071dfb0346e5c87009b8a9b5320e2372e44047009b8a9b5320e2372e43bc7009b8a9b53251c3f46e5c87009b8a9b5320e2372e4430700608a9b5320e35b46e5c87009b8a99071c9a372e43806809b8a9b53290c1c46e5c87789b8a9b53254c1c46e5c87009b8a99071a12372e43804d87c8a9b5320e2372e4380420558001536a641c4785c87009b7a9b5320e2372e43804d81c8001536a641c2e44cc7009b7a9b071ba30346e5c87009b8a9b53290c3f46e5c87009b8a9b5320e2373e85c87009b8a99071cb2de46e5c84d8248a99071e1b9646e5c87009b8a9b53184a372e45047009b8 else 0xa9b0716f2b446e5c87009b8a9b071642372e43804d8558a9b5320e28a4ce5c87009b8a9b5320e2de46e5c87789b8a9b53222c1c46e5c87009b8a9b071fc23730e5c87009b8a9b5320e24a46e5c87009b8a9b53214a372e43804d8248a99071cb31146e5c87009b8a990d20e39646e5c87009b8838e5981ade46e5c87009b8a9b5320e2373385c87009b8a9b5320e2cf46e5c87009b8a9b5320e3c046e5c87009b8a9b5321fade46e5c87009b80015360e36b46e5c87009b7a9b07173a372e43804d87c8a9b53251c1c4785c87009b8a99071cb2372e43806089b8a9b5320e3b646e704b90e08a9b53282c1c46e5c87009b8a9b5320e2372e43804d85b8a9b28e0e3035148dcb90e08a9b07181a374485c87009b8a9b5324fc1c46e5c87009b8a9b5329141c46e5c87009b8a993120e39646e5c85b89b8a9b5320e3a446e5c87009b8a9b5320e2d846e5c87009b8a9b5328541c46e5c87009b8a9b5320e2372e43806809b8a9b28e0e2b446e5c87009b8) else if Nat.blt b 23 then (if Nat.blt b 22 then 0xa9b532a341c46e5c87009b8a9b5329c41c3a85c87009b8a9b53226c1c46e5c87009b8a9b071de3035148dcb90e08a9b5320e2d046e5c87009b8a9b5320e2ce46e5c87009b8a9b5320e2372e44987009b8a9b5320e2372e43804d80e8a9b5328a45446e5c87009b8a9b5320e3c55148dcb90e08a9b532a1c1c47e5c87009b8a9b5320e2372e44847009b8a9b5320e2373fa5c89409b8a9b5329ac2946e5c87009b8a9b071de2b446e5c87009b8a9b5320e3c846e5c87009b8a9b07181a8a46e5c87009b8a9b5320e2372e43804d8928a9b07181ade5148dcb90e08a9b5320e2372e44307009b8a9b5320e3bc46e5c87789b8a991fa0e3b646e5c87009b8a9b5320e2372e43804d8678a9b5320e2372e45687009b8a9b4660e30346e5c87009b8a9b532a1c1c46e5bc7009b8a9b5321fbbc46e5c87009b8a9b5320e3cd46e5c87009b8a990718b2374325c87009b8a9b5329e41c46e5c87009b8a9b5320e2372e45047009b8a9b532a2c1c46e5c87009b8 else 0xa9b5320e2372e43804d86b8a9b5320e25146e5c86089b8a9b5320e2372e43804d8588a9b07181a372e454c7009b8001536a641c46e7f4b909b7a99071cb2372e43804d84f80015360e2f146e5c87009b7a9b5327d41c46e780b909b8a99071cb2372e45747009b80015327f41c72c8dcb909b7a9b5327d41c46e69cb90e08a990719fade46e5c87009b8a9b071f0a372e44a07009b8a990719823742e5c87009b8a9b5320e3b646e5c87009b8a9b5320e2372e43804d8548a9b5320e2372e44a47009b8a9b07181a372e44807009b8a9b5327d41c46e7f4b909b8a9b5320e2372e44e07009b8a9b47a0e30346e5c87009b8a9b07181a372e43804d8098a9b07181a5146e5c87009b8a9b5320e2372e43804d81f8a9b5320e2372e43805f09b8a9b5320e2372e43804d83c8a9b5320e23737c5c87009b8a993fa7d41c72c8dcb909b8a9b5320e2373c05c89409b8a9b5320e2372e43804d8018a9b5320e2372ae3804d8398a9b53256c1c46e5c87009b8) else if Nat.blt b 24 then 0xa99071cb2372e43804d8868a9b53212c1c46e5c87009b8a9b5320e2372e43804d81a8a9b5320e2372e45a87009b80015360e3e146e5c87009b7a9b532a5c1c46e5c87009b8a9946e0e39646e5c87009b8a9b5320e3ce46e5c87009b8a9b5329dc1c46e5c87009b8a9b07181a374485c8700248a9b5320e2372e43804d8388a9b5320e2373fa5c87009b8a9b5327cc1c46e5c87009b8a9b5320e2372e44e87009b8a9b532622372e42dc4d8098a9b5320e2d54b45c87009b8a9b5327d41c46e704b90e08a9b5326241c46e5c86009b8001536a641c46e5c86e09b7a993fa0e39646e5c87009b8a9b5320e3b446e5c87009b8a9b5320e2372e44907009b8a9b5320e2372e45b87009b8001536a641c46e780b909b7a9b5320e3bb46e5cc7009b8a9b5328f3f346e5c87009b8a9b3ea0e3e146e5c87009b8a9b5320e2372e43804d84e8a9b5320e2373125c87009b8a9b5320e26746e5c87009b8a99071cb2a246e5c87009b8a9b5320e2514585c87009b8 else 0xa9b5320e2372e44f87009b8a9b5320e2372e455c7009b8a9b5320e3bc46e780b909b8a9b5320e2372e44ec7009b8a9b5320e2372e43804d8958a9b5327dc1c46e5c87009b8a9b5326244646e5c87009b8a9b5320e2de46e69cb90e08a9b5320e23745a5c87009b8a9b5320e3f246e5c87009b8a9b5320e2372e44a07009b8a9b5320e2de46e7f4b909b8a9b5320e3bf46e7e0b909b8a9950e0e39646e5c87009b8a9b5320e2372e43806e09b8a993ea3f41c46e5c87009b8a9b5320e2372e45487009b8a9b071612372e43804d84f8
def htChunk_17 (b : Nat) : Nat := if Nat.blt b 1 then 0x38ee38385ed036f0cb36b4b6360cec34ddcd349e13349bb334681733adf033179832d906325b8c3218d33108cc3101dd30fe0230fa502ff3a02f38f52ea1802e33812d1d502c9cb92c96d62c32c12baacd295f9e28c1c528ab3c28aa3927d9f7278c692736512724c9266d43264b8d2598142586732522eb24b94724046b23757722ad2121f80321e6622199a0212be320e2ae20d39820bfaf20bcdb208f3e1fd4931ef7ce1eae6b1e3a931c935b1c705c1c5f421adea11a659219f8a21915ca18ae0917ff9117dc8f17d26017b1fe175aa1163a8416255516025615b8221553db14f8e414ca2813ee6e1348bf1295821266e6124c8512400412303c11d5a911c6fa11ba7c11b6dc11a53b110b4510f5ec10cb470fce160fab940f6f090f5a9b0e57c00defff0de2000dcd000d09df0c7f280c0cde0b89b70b5c410ab5cc0a8c670a058709010308f99208e7f108cfde0829be0786580776ef076b6306ba5604ee3b0483c203f28502e823027a1902571a01fab700de0c00cbad00b50c00920d else if Nat.blt b 2 then 0x7f437d7e2c8c7d8b257b374d7b27d97a2ceb79c74278aa61787b94779ecf76464d75522274c50f74b9d373bd9971419870bcbc7060e86f00d96ee1856ec82a6eaf946de9cc6d0c9f6c847d6bc6026b1dea6acebd6ac09c6a9d9d6a251a684ff0683a6d66e1eb66c52166805f665d60663a61658722655571648aa564790464593760d0bf60a30b60125d5fcf775fc5c85e911f5e4d505e1a575dbf805d9c4a5d2e435ccc125c33a95c23e15bae215afa385ae0245a62535a4b495a08945990975986e859390e58ef9558a3e956c5b356c39b55e50155c7b85306a852ae4752397c52089852039b51fc4651b85d51071250b1d650adfb5080ca4fe5284fb61a4f8b204f797f4f66974ee8ee4eb7554e5c354c37bb4b696c4ad2034aa4324a85064a6f1b4a5f0a4a0772497aa448aa0e4824f347bd824731f245a94244fef644e6e944bb4844a93e44207744122b42e95c41eb8041a7fc41965b411d3c40ebe840060f3f25703e21813cced23c73e83bc5d23bc4703ba2d33b691c3b577b3ad61d else 0xfed681fca943f897a1f66a63f559a2f2d793f11b4ef010ecedf37ce61e5ae2d4eadf697bde68d7dd9604d9323ed8ce43d7bf8cd7be92d6b9f8d5fa7fd4f68dd1d1fccea2acce3326cb601cca39b9c8b98dc8524ec6961dc6761ec5ca4bc5922bc514ddc41a8ec3fad9bd94f5bb6a98b88d15b6f451b6e71bb6c808b55f9fb53afab3e2c7b19f76b1604bb0784db04ee4af20c1add669ad1a55ac72edaa89c0aa396da97575a8e91ba8bef9a78fefa6b56da52587a48789a37d27a31910a1510fa03566a00a129f6b859f10289ef2fa9e3fe69d3e479d35849ce4969cb7ce9b5ffb9b4f799ae3ba9a5a5098815a9390f192b1b2918b4f8fef488f89628cef878a1ce389035e88ca9a87dff6876d3f8692cc852ae284c32184bcec84a02283d2c483cd2e80a7e68050c08044938038807f772c
def stChunk_17 (b : Nat) : Nat := if Nat.blt b 6 then (if Nat.blt b 3 then (if Nat.blt b 1 then 0xa9b5322a41c46e5c8b90e01373536a64548388dcb90e013613e40054da990711b9ad2e43804dc54da991520e2373785c87009b90015320e39646e5c8ab8e01370002a6d4c8388dcf71721c026e2a6d4c8389d133a372e43804dcd4da990711b9722183804d80590015360e30346e5c8a08e01370002a6d4c8410711b9721c026e2a6d4c88d0711b9722ae3804dcd4da990711b9721c026c028039a9b5320e2372e44307009b0493536a641c4ce8dcb90e01361566a6d4c838a2933a372e43804dc800a9b5320e2373f25c87009b8a9b5320e28e4a28dcb90e01373536a64c48388dcb90e013620a6a6d4c8388dcb91411c026c02cd4da9907128a372e43804d8549a9b5320e2372e43804d87c0133536a641c46e5c8a08e013609240054da991920e2372e43804dc000a9b5320e41c46e5c87009b8000002a6d4c8388dcb90e0136f536a641c46e5c87009b09e0266a6d4c8388dcde1721c026c04cd4da991520e2372e43804d8929001536a641c46e704b90e01371536a64548388dcb910c1c026e6a6d4c8389451b9721c026c27cd4da9907128a373785c87009b9 else if Nat.blt b 2 then 0xa9b5320e2372e43804d84f00b3536a641c4ce8dcb90e01360266a6d4c8388dcb90e013601400cd4da9907133a372e43806209b9a9b5320e2372e43805009b00b2002a6d4c838968b90e01361562a6d4c83899d28a372e43804dcd4da990711b9721c026c278249a9b5320e2373785c87009b0493536a641c46e7e0b90e013617e6a6d4c8388dcb90e013609000cd4da990711b9872e43804d8139a9b5320e27446e7e0b90e013720000054c838cc11b9721c026dc00000a99071cb2372e43804dbd4da990711da372e43804d8059a9b532324468388dcb90e01372002a6d4c8388dcb90e01c026e00054da990713e9721c026c3e454da991520e2372e43804d87c9a9b5322341c8388dcb90e01372002a6d4c83899d1b9571c026e00054da990711b9ad1c026c3e454da990711b9f82e43804d8559a9b5320e28a46e7e0b90e01373536a641c46e5c8700c118226e6a6d4c8388dcb91411c026c004800a9b5322341c46e5c87009b80015360e3036068dcb90e01371536a652c8388dcb91411c026e40054d838c0d1b9722183804dc000a9b5320e2374205c87009b8 else 0x1536a641c46e7e0b909b00b0002a6d4c8388dcb90e013620a00054da990711b97220c38060c54da990711b9721c026c3e0009000002a646a8388dcb90e0136f536a641c46e61cb90e01361566a6d4c838a291b9872e43804dcd4da994b20e2372e43804d87c9001536a641c514944b90e01370002a64da838e591b9721c026e2a6d4c8a907133a372e43804dc800a99071cb2372e43807009b8a9b5326241c46e5c87009b0ab3536a64c4838a291b9721c026e40054da993120e2372e426c04c000a9911a0e39646e5c87009b8a9b5329641c46e5c87009b09f2002a6c1c6068dcb90e01361f22a6d4ca590711b9bc2e43804dcd4da990711b9f82e43804d8099000002a6d4c9888dcb909b012e002a6d4c98907128a372e426e2a6d4c8389451b9f82e43804dcd4da9911a2341c46e5c87009b9000002a6d4c8388dcde0e00aae002a6c1c6068dcb90e013613e00054d838c0d1b9bc2e43804dc000a9b5320e2372e65c87009b8001536a641c46e640b90e01371536a641c46e5c87009b0f809240054da990711b9721d83804dc54da990711b9722e43804d8059) else if Nat.blt b 4 then 0x1536a641c46e5c87009b1011536a641c46e7e0f41721c026e6a6d4c8388dcfc1721c026c02c800a9b5320e2472e43804d8248000002a6d4c8388dcb90e0146e002a641c72c8dcb90e01360da2a6d4c8388dcc39721c026c04c800a99071d1b9646e5c87009b8a9b5320e2373f05c87009b0493536a64468388dcb90e013626e6a6d4c83899d1ba372e43804dcd4da9907128a3730e5c87009b9001536a641c46e5e0b90e01370002a6c1c60699d1b9721c026e00054da990711b9721c026c09c54da993326241c46e5c87009b9a9b5326241c46e5c87009b0133536a653b8a90711b9721c026e40054da993111b9721c026c04c54da993120e25146e5c87009b9a9b5320e2372e4430700c11373536a641c4ce8dcb90e01360166a6d4c8388dcb90e018226c01c8000015360e2c246e5c87009b7001536a6446838a291b9721c11536a64548388dcfc1721c026e6a6d4c83899d1b9721c026c124800a9b5320e23c2e45047009b8a9b5322341c46e640b90e01373536a64548388dccb1721c026e40054c9db071cb2372e43804dc000a99071cb2372e43804d8448 else if Nat.blt b 5 then 0xa9b5320e2372e455c7009b0132002a6d4c97c8dcb90e018226e2a6d4c8388dcb91061c03044dc800001536a645446e5047009b7a9b5320e25146e5c8ab8e01373536a641c46e5c8a090c1c026e6a6d4c9a30711b9f82e43804dcd4da993120e2372e43804d8059001536a641c46e5c87009b0bf00000054da990711b97c1c026dc0054da994b20e28a2e43804dc000a9b5320e27446e5c87009b8a9b5326241c46e5c87009b0492002a6d4ca7f0711b9721c026e2a6d4c8388dcb91412823804dcd4da9907148a373785c87009b9001536a641c46e680b90e01370002a6d4c8388dcb90e013615600054da99071452372e43804dc000a9b5320e2373783804d8558001536a641c46e5c87009b11d1536a641c46e5c8700c11361f26a6d4ca590711b9f82e43804dc800a9b5320e24746e5c87009b8001536a64298388dcb90e01371536a64c48a90711b9721c026e6a6d4c8388dcb90e018226c27c800001536a642946e5c87009b7a9b5320e2373785c8700c11373536a641c46e5c8ab8e01361566a6d4c838a291b9722ae3804dc800a9b07181a373f05c87009b8 else 0xa9b5320e23736c5c8ab8e01373536a641c46e6f0b910c1c026e40054da990711b9721c028c4dc54da990711b97c2e43804d8249001536a641c4ce8dc7009b0ab00000054d838ae91b9721c026dea6d4c8a90711b9722ae3804dc8000015362341c6068dcb90e07a9b5329641c46e61cb90e01372002a641c6608dcb90e013615600054da994b20e2512e43804dc000a99071cb2372e43804d8558a9b5329fc468388dcb90e01372002a6d4ca588dcc39721c026e2a6d4c8390711b9721c026c04c8000015320e38c46e5c87009b7001536a64cc8388dcb90e01370002a6d4c8388dcb90e013602600054da990711b9721c03104dc0000015320e3964a28dcb909b7a9b5320e23746e61cb90e01373536a64468388dcb90e01361566a6d4c88d071452372e43804dcd4da994b26241c46e5c87009b9001536a641c4a28dcb90e01370002a6c1c6068dcc39721c026e00054da994b2622372e43804dc54da990711b9722184307009b9a9b5325f41c46e5c8700c11373536a641c46e61cb90e013601640054da990711b9f82e43044dc000a9b5322a41c46e5047009b8) else if Nat.blt b 9 then (if Nat.blt b 7 then 0x1536a641c46e7e0b910c1370002a6d4c8388dcb90e01360162a6d4c8388dcde1722e43804dcd4da990711b9721c026c2784f9a9b5320e2373785c87009b09f3536a641c46e6f0de1721c026e6a6d4c8388dd1b9722ae3804dc8000015320e39646e5c84d8247a9b5320e2372e43804d89b0ab3536a641c5148dcb90e013626e40054da990711b9721c026c12454da99071472372e44307009b9a9b5320e2372e455c7009b00b3536a641c46e5c8700e013602640054da990711b9721c026c244000a9b5320e23736c5c87009b8a9b5322341c46e5c87009b0133536a641c4a28dcb90e01c026e6a6d4c8388dcb91571c026c124d4da991922a41c46e5c87009b9a9b5320e2372e44307009b0f93536a64548390711b9721c026e6a6d4c88d07128a372e43804dc800001536a641c4fa5c87009b7001536a64548388dcb90e013700000054da990711b9ad1c026dc0054da990711b9722b63804dc000a99071cb29646e5c87009b80015320e32846e5c87009b04900000054da990711b9ee1c026dea6d4c8388dcfc1721c03044dcd4da990711b9722ae3804d8489 else if Nat.blt b 8 then 0x2a641c6308dcb90e0136f536a641c46e780b91411c026e400000a9b5320e2372e43bc4db800a9b5321fc1c46e5c87009b80000020e3966068dcb90e0136e0000054da990fd1b9721c026dc0054d838f851b9722823804dc000a9b11a0e30346e5c87009b8001536a64c48388dcb910c1371536a641c46e7e0b910c1c026e6a6d4c8388dcb90e01c026c02cd4da990711b9721c03044d8109a9b5322341c46e5c87009b00b2002a641c72c8dcb90e01360922a6d4c8388dcb90e01c026c124800a9b5322a41c4ce8dc7009b80015320e39646e5c8890e01370002a6d4c8388dcb90e01360022a6d4c8388dcb90e01361f03e4d4da9907133a372e44307009b9001536a641c46e780b91411371536a64208388dcb90e01360166a6d4c8388dcc39721c03044dc800a9b5320e23734e5c8a08e080015322a41c72c8dcb90e01370002a6d4c8388dd1b9721c026e2a6d4c8388dcb910c1c026c2c4d4da9907133a372e45047009b9a9b5320e2372e43804d87c09f3536a641c46e6f0b90e01361f26a6d4c8388dcb99721c026c04c800a9b5320e2373d05c87009b8 else 0xa9b5320e2372e455ca08e01372002a6d4c8528dcb90e01360922a6d4c8388dcc39721c026c3e4800a9b5320e2373385c87009b8a9b5320e2373f05c8a30e01372002a6c1c5ce8dcb90e01361f22a6d4c8a90711b9721c026c2ac800a99071cb2372e43806089b8a9b5320e23737861cb90e01373536a641c47e8dcb90e01360266a6d4c83899d1b9892e43804dcd4da9907133a6746e5c87009b9a9b5320e23734e5c8a08e01373536a65318389451b9721c026e40054da990711b9721de3804dc000a99071a12372e43804d87c8a9b5320e2373f05c87009b0f920000054da990711e1721c026dea6d4c9890711b9722183804dcd4da990711b9872e45047009b9000002a6c1c606a291b9721c0f536a641c46e7e0b91721c026e6a6d4c8388dcfc1721c026c27c800a9b5320e2373f03804d8058a9b5320e2373f06f0b90e01372002a6d4c8388dcb90e01460262a6d4c9890711b9722823804dcd4da990711b99c30e5c87009b9000002a6c1c5688dcb90e0136f536a641c514a291b9721c026e6a6d4c8389691b9721c026c2ac800a994b20e39646e5c87009b8) else if Nat.blt b 10 then 0xa9b5320e2372e4430700e01373536a641c46e7e0c39721c026e40054d838c0d28a372e43804dc54da991522a41c46e5c87009b9001536a641c46e6f8b90e01370002a6d4c8388dcb90e01360062a6d4c8389451b98a2e43804dcd4da9911a0e2372e45047009b9001536a644d8388dcb90e01371536a653fa590711b9721c026e6a6d4c8388dcb90e0136154004d4da994b20e2372e43804d8559a9b5329641c46e5c87009b11d3536a641c46e6f0b91601c026e6a6d4c98907133a372e43804dcd4da991360e2372e455c7009b90015360e3035148dcb90e013700000054da99071339571c026dc0054da990711b9721c026c494000a9b5320e2372e44307009b8a9b5320e2372e43805189b0132002a6d4c8388dcb915a1c026e2a6d4c8390711b9722823804dc800a9b5320e2372e45047009b8a9b5320e2372e43804d8550493536a641c46e5c8ab90c1c026e40054d838b211b9721c026c2ac000a9b5320e28a4ce5c87009b8a9b5320e2372e45049f0e01373536a653b83899d1b9721c026e40054d838fe11b9872e43804dc54da990a60e2372e43804d8249 else if Nat.blt b 11 then 0xa9b532624468388dcb90e01372002a6d4c9891191b9721c026e2a6d4c8388dcb90e018226c02c800a9b5320e2372e4430700248a9b5320e2372e43804d84f0273536a641c46e840fc1721c026e40054d838b091b9721c026c27c54da990711b9722183804d8809000002a6c1c7c28dcb90e0136e002a651b838e591b9721c026e2a6d4c8388dcb90e018226c04c800a9b5329dc1c46e5c87009b8000002a6d4c8388dcb910c048f536a641c4a28dcb90e018226e40054da990711b9fd2e43804dc54da990711b9721c026c120009a9b5320e2372e43804d80900520000054da990711b9e02e426dc0054da990711b9892e43804dc000a9b5320e26746e5c87009b8a9b5320e2372e43806089b0ab3536a652c8a90711b9721c026e40054da9907128a372e43044dc000a9b5320e2372e43804d8588a9b5320e2372e43804d82404920000054da990711b9fd2e426dc0054c838e591b9721c026c27c54da9911a0e2372e453c7009b9a9b5320e26746e5c8ab8e01373536a64548388dcb90e013609240054da990711b9721c026c2a4000a9b07181a372e43804d8098 else 0x54da990711b97227c3804dc000a9b5320e2372e455c7009b8a9b5320e2372e455c9f0e01373536a641c46e5c8ab9571c026e6a6d4c9990711b9722183804dcd4da990711ba372e43806089b9
def htChunk_18 (b : Nat) : Nat := if Nat.blt b 1 then 0xb56e1db048f3af1c72abdf16a78fefa37d279c80b09b6f8e98091a975cc6930c499270739233cf91ee50909ee58d9f298a8fba898c6188b4d287f465862c1e85e0db8074478044477f4da07df6c87a6af57971d078d2e178a5e876abe07280e27258c470bbd5706d007060e86b64f66b535566e1eb6514f4645937644087637ae363694262f62f629ef160d9e46022dc5e376b5de6165c23e15ac18a5838d65670225590a65398f2538751523fb851c5b550d67750b10050adfb5053275003804f80b94f2ee44f1b124ee8ee4d882c4cf1254a687148d43044909f448d9a42c88d42331b41fa0641e62a41a7fc41965b400e4f3d05b93b45b136bd3535879b3575fa353e1e351ba634f82834b29027b73627a59527014925c3bf2539b524bb0a230d8522bc3d20271f200e751fee271f5ad81e7c2a1c506a1a298c1972ca14d919143b65142a4c1348bf1138aa10cb47109535105b390e9a390dfd310d8ff20cf52409d6a508ab2207285e050b1104b76304aae602e82302ca49025fa4007b39 else 0xfca943ec0ca0e8f75de2b87ddb8cfbda0203d9d892d90d4fd3c9d8cceceeca39b9c962d6c94764c7b551bf1c89be72d0be1958bc2d6db59dff
def stChunk_18 (b : Nat) : Nat := if Nat.blt b 2 then (if Nat.blt b 1 then 0x1536a64948388dcb90e01371536a64a388d0711b9721c026e40054da99071ba2372e43804dc54da9950e0e2372e43804d8099a9b53252ca38388dcb90e01373536a641c46e5c8940e019a26e6a6d4c838b791b9722ae3804dc800a9b5320e27046e5c87009b8a9b53291c1c46e5c87009b09f2002a6d4c8388dcb90e013607a00054da9928e0e2372e43804dc000a9b5320e2d446e5c87009b8a9b5322a41c46e5c8898e013720000054c838e591b9721c026dea6d4c838ef184a372e43804dc800a9b5322341c46e5c87009b8a9b5320e3bc46e61cb90e01372002a6d4ca430711b9721c026e2a6d4c9470711b9722ae3804dc800a9b53252c1c46e5c87009b8a9b53251c1c8348dcb90e01373536a64c4838ef11b9721c026e40054da990711b9721c026c30454da990716f23730e5c87009b90015327d41c72c8dcb90e01371536a64c4838b791b9721c026e6a6d4c9470711b9721c026c4a4d4da993ea2341c46e5c87009b9000002a6d4c8388dcb90e0136f536a654b838ef11b9721c026e6a6d4c8389c11b9722503804dc800a9b5320e2372e43806009b8 else 0xa9b5320e3bf7788dcb90e01372002a6d4c8388dcb912a1c026e2a6d4ca430711b9721c026c2ac800a9b5320e25146e5c87009b8001536a641c7568dcb90e01371536a641c46e5c8940e01360166a6d4c8388dcb91281c026c124d4da9907206ade46e5c87009b9a9b5328f4fa8388dcb90e01373536a64fa8388dcb90e01360266a6d4c9f507128a372e43804dcd4da991520e2372e44a07009b9a9b5320e3745bc8dcb90e01373536a641c5ae9451b9721c026e40054da990711b9721c026c2ac000a9b5320e28a46e5c87009b8a9b53283cfa8388dcb90e01372002a641c778e591b9721c026e2a6d4c838b791b9721c026c0f4d4da990711b9722503804d8099a9b5327d41c46e5c87009b0ab3536a64fa838a291b9721c026e6a6d4c8388dcb912a2503804dc800a99071cb2de46e5c87009b8a9b5320e25146e5c8940e01372002a6d4ca710711b9721c026e2a6d4c8388dcb91281c026c2acd4da99071452372e44a07009b9001536a641c81a8dcb90e01370002a6d4c838efd1b9721c026e00054c947071cb2372e43804dc000a9b5320e2de46e5c87009b8) else if Nat.blt b 3 then 0x1536a65358388dcb90e01371536a641c5bc9451b9721c026e6a6d4c838f0d1b9722ae3804dc800a9b5320e2372e43804d8008a9b5320e3bc46e5c87009b0ab3536a641c778a291b9721c026e40054da990711b9721c026c02c000a9b532a241c46e5c87009b8001536a641c46e5c87009b0491536a64fa8388dcb90e01360026a6d4c838b791b9721c026c2acd4da990716f28a46e5c87009b9a9b532964fa8388dcb90e01373536a64a38388dcb90e01360266a6d4c94707128a372e43804dcd4da9911a0e2372e44807009b9001536a641c46e5c8968e01370002a6d4c8388dcb91531c026e00054da991520e2372e43804dc54da993ea0e2372e43804d8059a9b5327d41c46e5c87009b0493536a641c46e5c8940e013600240054da994520e2372e43804dc54da9928e0e2372e43804d8559a9b53251c1c5148dcb90e01372002a6d4c8388dcb91201c026e2a6d4c9f50711b9722a63804dc800a9b07181a372e44a07009b8001536a651e8388dcb90e01370002a6d4c8388dcb90e01360262a6d4c838d691b9f82e43804dcd4da993ea2a41c46e5c87009b9 else if Nat.blt b 4 then 0xa9b53251c1c46e5c8a08e01373536a641c4ce8dcb91281c026e40054da99071682372e43804dc000a9b5320e2372e44847009b8001536a641c46e5c8860e01370002a6d4c8388dcb91411c026e2a6d4c95328e0e2372e43804dcd4da993ea0e2372e44307009b90015360e30346e890b90e01371536a64fa8388dcb91411c026e40054da9942a0e2372e43804dc000a9b5320e2372e43806809b8a9b5320e2de46e5c87009b0013536a641c46e5c8941211c026e6a6d4c838ef11b9721c026c02cd4da990711b9722504307009b9001536a64a98388dcb90e01371536a641c46e5c8a09281c026e6a6d4c838b791b9721c026c02cd4da99071de2372e44b47009b9a9b5320e2de46e5c87009b0493536a6454838ef11b9721c026e40054da99071f9a372e43804dc000a9b5320e35a46e5c87009b8a9b5328a41c7788dcb90e01373536a6454838b791b9721c026e6a6d4c838ef11b9721c026c04cd4da99071e62372e45047009b9a9b53251c1c46e5c87009b00b3536a641c7789451b9721c026e40054da99071e1a372e43804dc54da990716f2372e43804d8099 else 0x2a6d4c8388dcb91571c026e2a6d4c838b7933a372e43804dc800a9b5320e2372e44a07009b8a9b5320e2372e455c940e01373536a641c5a899d1b9721c026e40054da990711b9722d43804dc54da993ea0e2374585c87009b9001536a654b8388dcb90e01371536a65358388dcb90e01360926a6d4ca973ea0e2372e43804dc800a9b5320e26746e5c87009b8a9b5320e2de46e5c8860e01373536a64c48388dcb91281c026e6a6d4c9290711b9722183804dcd4da9952e0e2372e44a07009b9001536a641c76c8dcb90e01371536a64fa83899d1b9721c026e6a6d4c838ef11b9721c03404dc800a9b5320e2372e43804d83c8
def htChunk_19 (_ : Nat) : Nat := 0xfca943ca39b9a78fefa37d2766e1eb6459375c23e150adfb4ee8ee41a7fc41965b1348bf10cb4702e823
def stChunk_19 (_ : Nat) : Nat := 0xa9b5320e2372e455c7009b8a9b5320e26746e5c87009b8a9b5320e2372e44307009b8a9b5320e2372e45047009b8a9b5320e2372e43804d8058a9b5320e2372e43804d8248a9b5322a41c46e5c87009b8a9b5320e2372e43804d8098a9b5320e25146e5c87009b8a9b5320e2372e43804d8558a9b5320e28a46e5c87009b80015320e39646e5c87009b7a9b5322341c46e5c87009b8001536a641c46e5c87009b7
def htChunk_20 (_ : Nat) : Nat := 0xe8f75d24bb0a14d91902e823
def stChunk_20 (_ : Nat) : Nat := 0xa9b5320e2372e44a07009b8a9b5320e2de46e5c87009b8a9b53251c1c46e5c87009b8001536a641c46e5c87009b7
def htChunk_21 (_ : Nat) : Nat := 0x2e823
def stChunk_21 (_ : Nat) : Nat := 0x1536a641c46e5c87009b7
def HT (u i : Nat) : Nat := match u with
  | 7 => Nat.land (Nat.shiftRight (htChunk_7 (i / 128)) (24 * (i % 128))) 16777215
  | 9 => Nat.land (Nat.shiftRight (htChunk_9 (i / 128)) (24 * (i % 128))) 16777215
  | 10 => Nat.land (Nat.shiftRight (htChunk_10 (i / 128)) (24 * (i % 128))) 16777215
  | 11 => Nat.land (Nat.shiftRight (htChunk_11 (i / 128)) (24 * (i % 128))) 16777215
  | 12 => Nat.land (Nat.shiftRight (htChunk_12 (i / 128)) (24 * (i % 128))) 16777215
  | 13 => Nat.land (Nat.shiftRight (htChunk_13 (i / 128)) (24 * (i % 128))) 16777215
  | 14 => Nat.land (Nat.shiftRight (htChunk_14 (i / 128)) (24 * (i % 128))) 16777215
  | 15 => Nat.land (Nat.shiftRight (htChunk_15 (i / 128)) (24 * (i % 128))) 16777215
  | 16 => Nat.land (Nat.shiftRight (htChunk_16 (i / 128)) (24 * (i % 128))) 16777215
  | 17 => Nat.land (Nat.shiftRight (htChunk_17 (i / 128)) (24 * (i % 128))) 16777215
  | 18 => Nat.land (Nat.shiftRight (htChunk_18 (i / 128)) (24 * (i % 128))) 16777215
  | 19 => Nat.land (Nat.shiftRight (htChunk_19 (i / 128)) (24 * (i % 128))) 16777215
  | 20 => Nat.land (Nat.shiftRight (htChunk_20 (i / 128)) (24 * (i % 128))) 16777215
  | 21 => Nat.land (Nat.shiftRight (htChunk_21 (i / 128)) (24 * (i % 128))) 16777215
  | _ => 0
def S (u j : Nat) : List Nat := match u with
  | 7 => let p := Nat.land (Nat.shiftRight (stChunk_7 (j / 32)) (48 * (j % 32))) 0xffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 9 => let p := Nat.land (Nat.shiftRight (stChunk_9 (j / 32)) (59 * (j % 32))) 0x7ffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 10 => let p := Nat.land (Nat.shiftRight (stChunk_10 (j / 32)) (70 * (j % 32))) 0x3fffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 11 => let p := Nat.land (Nat.shiftRight (stChunk_11 (j / 32)) (70 * (j % 32))) 0x3fffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 12 => let p := Nat.land (Nat.shiftRight (stChunk_12 (j / 32)) (81 * (j % 32))) 0x1ffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 13 => let p := Nat.land (Nat.shiftRight (stChunk_13 (j / 32)) (81 * (j % 32))) 0x1ffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 14 => let p := Nat.land (Nat.shiftRight (stChunk_14 (j / 32)) (92 * (j % 32))) 0xfffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 15 => let p := Nat.land (Nat.shiftRight (stChunk_15 (j / 32)) (92 * (j % 32))) 0xfffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 16 => let p := Nat.land (Nat.shiftRight (stChunk_16 (j / 32)) (92 * (j % 32))) 0xfffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 17 => let p := Nat.land (Nat.shiftRight (stChunk_17 (j / 32)) (103 * (j % 32))) 0x7fffffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 18 => let p := Nat.land (Nat.shiftRight (stChunk_18 (j / 32)) (103 * (j % 32))) 0x7fffffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 19 => let p := Nat.land (Nat.shiftRight (stChunk_19 (j / 32)) (92 * (j % 32))) 0xfffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 20 => let p := Nat.land (Nat.shiftRight (stChunk_20 (j / 32)) (92 * (j % 32))) 0xfffffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | 21 => let p := Nat.land (Nat.shiftRight (stChunk_21 (j / 32)) (81 * (j % 32))) 0x1ffffffffffffffffffff; stateWires (Nat.land p 15) (Nat.shiftRight p 4)
  | _ => []
def symTag : Nat := 0xfffffffc00000003fffffff
def symD : Nat := 30
theorem sym_ok : moveOK 62 (symTag, symD) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := let img := zs.map (moveBits symTag symD); if Nat.blt (hk 1 img) (hk 1 zs) then img else zs
theorem ori_ok {u ys} (h : NatRun1T 62 true (goal 62) u ys) : NatRun1T 62 true (goal 62) u (ori ys) := ori_move_ok 1 symTag symD sym_ok h
def bsrFuel : Nat → Nat
  | 7 => 4
  | 9 => 9
  | 10 => 6
  | 11 => 12
  | 12 => 9
  | 13 => 13
  | 14 => 11
  | 15 => 13
  | 16 => 11
  | 17 => 10
  | 18 => 9
  | 19 => 5
  | 20 => 3
  | 21 => 2
  | _ => 0
def idx (u : Nat) (zs : List Nat) : Nat := bsr (HT u) (hk 1 zs) (bsrFuel u) 0 (NN u)
def poolG : List (Nat × Nat × Nat × Nat × Nat × Nat) := [(68, 69, 94, 18, 6, 30), (98, 99, 64, 48, 36, 0), (99, 62, 64, 16, 18, 25), (69, 92, 94, 46, 48, 55), (97, 65, 67, 3, 18, 23), (67, 95, 97, 33, 48, 53), (65, 66, 108, 16, 3, 23), (95, 96, 78, 46, 33, 53), (99, 62, 64, 8, 12, 18), (69, 92, 94, 38, 42, 48)]
theorem poolG_ok : poolOK 62 poolG = true := by decide +kernel
def Z (u : Nat) := bar1T true S NN idx ori poolG u
abbrev Ok (u a b : Nat) := ∀ i, a ≤ i → i < b → Z u i = true
theorem z0 : Ok 0 0 (NN 0) := by simp [Ok, NN]
theorem z1 : Ok 1 0 (NN 1) := by simp [Ok, NN]
theorem z2 : Ok 2 0 (NN 2) := by simp [Ok, NN]
theorem z3 : Ok 3 0 (NN 3) := by simp [Ok, NN]
theorem z4 : Ok 4 0 (NN 4) := by simp [Ok, NN]
theorem z5 : Ok 5 0 (NN 5) := by simp [Ok, NN]
theorem z6 : Ok 6 0 (NN 6) := by simp [Ok, NN]
set_option maxHeartbeats 0 in
theorem z7 : Ok 7 0 (NN 7) := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
theorem z8 : Ok 8 0 (NN 8) := by simp [Ok, NN]
set_option maxHeartbeats 0 in
theorem z9_0 : Ok 9 0 100 := span_ok (by decide +kernel : span (Z 9) 100 0 = true)
set_option maxHeartbeats 0 in
theorem z9_100 : Ok 9 100 200 := span_ok (by decide +kernel : span (Z 9) 100 100 = true)
set_option maxHeartbeats 0 in
theorem z9_200 : Ok 9 200 223 := span_ok (by decide +kernel : span (Z 9) 23 200 = true)
theorem z9 : Ok 9 0 (NN 9) := (range_split z9_0 (range_split z9_100 z9_200))
set_option maxHeartbeats 0 in
theorem z10 : Ok 10 0 (NN 10) := span_ok (by decide +kernel : span (Z 10) 23 0 = true)
set_option maxHeartbeats 0 in
theorem z11_0 : Ok 11 0 100 := span_ok (by decide +kernel : span (Z 11) 100 0 = true)
set_option maxHeartbeats 0 in
theorem z11_100 : Ok 11 100 200 := span_ok (by decide +kernel : span (Z 11) 100 100 = true)
set_option maxHeartbeats 0 in
theorem z11_200 : Ok 11 200 300 := span_ok (by decide +kernel : span (Z 11) 100 200 = true)
set_option maxHeartbeats 0 in
theorem z11_300 : Ok 11 300 400 := span_ok (by decide +kernel : span (Z 11) 100 300 = true)
set_option maxHeartbeats 0 in
theorem z11_400 : Ok 11 400 500 := span_ok (by decide +kernel : span (Z 11) 100 400 = true)
set_option maxHeartbeats 0 in
theorem z11_500 : Ok 11 500 600 := span_ok (by decide +kernel : span (Z 11) 100 500 = true)
set_option maxHeartbeats 0 in
theorem z11_600 : Ok 11 600 700 := span_ok (by decide +kernel : span (Z 11) 100 600 = true)
set_option maxHeartbeats 0 in
theorem z11_700 : Ok 11 700 800 := span_ok (by decide +kernel : span (Z 11) 100 700 = true)
set_option maxHeartbeats 0 in
theorem z11_800 : Ok 11 800 900 := span_ok (by decide +kernel : span (Z 11) 100 800 = true)
set_option maxHeartbeats 0 in
theorem z11_900 : Ok 11 900 1000 := span_ok (by decide +kernel : span (Z 11) 100 900 = true)
set_option maxHeartbeats 0 in
theorem z11_1000 : Ok 11 1000 1100 := span_ok (by decide +kernel : span (Z 11) 100 1000 = true)
set_option maxHeartbeats 0 in
theorem z11_1100 : Ok 11 1100 1200 := span_ok (by decide +kernel : span (Z 11) 100 1100 = true)
set_option maxHeartbeats 0 in
theorem z11_1200 : Ok 11 1200 1300 := span_ok (by decide +kernel : span (Z 11) 100 1200 = true)
set_option maxHeartbeats 0 in
theorem z11_1300 : Ok 11 1300 1400 := span_ok (by decide +kernel : span (Z 11) 100 1300 = true)
set_option maxHeartbeats 0 in
theorem z11_1400 : Ok 11 1400 1500 := span_ok (by decide +kernel : span (Z 11) 100 1400 = true)
set_option maxHeartbeats 0 in
theorem z11_1500 : Ok 11 1500 1577 := span_ok (by decide +kernel : span (Z 11) 77 1500 = true)
theorem z11 : Ok 11 0 (NN 11) := (range_split (range_split (range_split (range_split z11_0 z11_100) (range_split z11_200 z11_300)) (range_split (range_split z11_400 z11_500) (range_split z11_600 z11_700))) (range_split (range_split (range_split z11_800 z11_900) (range_split z11_1000 z11_1100)) (range_split (range_split z11_1200 z11_1300) (range_split z11_1400 z11_1500))))
set_option maxHeartbeats 0 in
theorem z12_0 : Ok 12 0 100 := span_ok (by decide +kernel : span (Z 12) 100 0 = true)
set_option maxHeartbeats 0 in
theorem z12_100 : Ok 12 100 152 := span_ok (by decide +kernel : span (Z 12) 52 100 = true)
theorem z12 : Ok 12 0 (NN 12) := (range_split z12_0 z12_100)
set_option maxHeartbeats 0 in
theorem z13_0 : Ok 13 0 80 := span_ok (by decide +kernel : span (Z 13) 80 0 = true)
set_option maxHeartbeats 0 in
theorem z13_80 : Ok 13 80 160 := span_ok (by decide +kernel : span (Z 13) 80 80 = true)
set_option maxHeartbeats 0 in
theorem z13_160 : Ok 13 160 240 := span_ok (by decide +kernel : span (Z 13) 80 160 = true)
set_option maxHeartbeats 0 in
theorem z13_240 : Ok 13 240 320 := span_ok (by decide +kernel : span (Z 13) 80 240 = true)
set_option maxHeartbeats 0 in
theorem z13_320 : Ok 13 320 400 := span_ok (by decide +kernel : span (Z 13) 80 320 = true)
set_option maxHeartbeats 0 in
theorem z13_400 : Ok 13 400 480 := span_ok (by decide +kernel : span (Z 13) 80 400 = true)
set_option maxHeartbeats 0 in
theorem z13_480 : Ok 13 480 560 := span_ok (by decide +kernel : span (Z 13) 80 480 = true)
set_option maxHeartbeats 0 in
theorem z13_560 : Ok 13 560 640 := span_ok (by decide +kernel : span (Z 13) 80 560 = true)
set_option maxHeartbeats 0 in
theorem z13_640 : Ok 13 640 720 := span_ok (by decide +kernel : span (Z 13) 80 640 = true)
set_option maxHeartbeats 0 in
theorem z13_720 : Ok 13 720 800 := span_ok (by decide +kernel : span (Z 13) 80 720 = true)
set_option maxHeartbeats 0 in
theorem z13_800 : Ok 13 800 880 := span_ok (by decide +kernel : span (Z 13) 80 800 = true)
set_option maxHeartbeats 0 in
theorem z13_880 : Ok 13 880 960 := span_ok (by decide +kernel : span (Z 13) 80 880 = true)
set_option maxHeartbeats 0 in
theorem z13_960 : Ok 13 960 1040 := span_ok (by decide +kernel : span (Z 13) 80 960 = true)
set_option maxHeartbeats 0 in
theorem z13_1040 : Ok 13 1040 1120 := span_ok (by decide +kernel : span (Z 13) 80 1040 = true)
set_option maxHeartbeats 0 in
theorem z13_1120 : Ok 13 1120 1200 := span_ok (by decide +kernel : span (Z 13) 80 1120 = true)
set_option maxHeartbeats 0 in
theorem z13_1200 : Ok 13 1200 1280 := span_ok (by decide +kernel : span (Z 13) 80 1200 = true)
set_option maxHeartbeats 0 in
theorem z13_1280 : Ok 13 1280 1360 := span_ok (by decide +kernel : span (Z 13) 80 1280 = true)
set_option maxHeartbeats 0 in
theorem z13_1360 : Ok 13 1360 1440 := span_ok (by decide +kernel : span (Z 13) 80 1360 = true)
set_option maxHeartbeats 0 in
theorem z13_1440 : Ok 13 1440 1520 := span_ok (by decide +kernel : span (Z 13) 80 1440 = true)
set_option maxHeartbeats 0 in
theorem z13_1520 : Ok 13 1520 1600 := span_ok (by decide +kernel : span (Z 13) 80 1520 = true)
set_option maxHeartbeats 0 in
theorem z13_1600 : Ok 13 1600 1680 := span_ok (by decide +kernel : span (Z 13) 80 1600 = true)
set_option maxHeartbeats 0 in
theorem z13_1680 : Ok 13 1680 1760 := span_ok (by decide +kernel : span (Z 13) 80 1680 = true)
set_option maxHeartbeats 0 in
theorem z13_1760 : Ok 13 1760 1840 := span_ok (by decide +kernel : span (Z 13) 80 1760 = true)
set_option maxHeartbeats 0 in
theorem z13_1840 : Ok 13 1840 1920 := span_ok (by decide +kernel : span (Z 13) 80 1840 = true)
set_option maxHeartbeats 0 in
theorem z13_1920 : Ok 13 1920 2000 := span_ok (by decide +kernel : span (Z 13) 80 1920 = true)
set_option maxHeartbeats 0 in
theorem z13_2000 : Ok 13 2000 2080 := span_ok (by decide +kernel : span (Z 13) 80 2000 = true)
set_option maxHeartbeats 0 in
theorem z13_2080 : Ok 13 2080 2160 := span_ok (by decide +kernel : span (Z 13) 80 2080 = true)
set_option maxHeartbeats 0 in
theorem z13_2160 : Ok 13 2160 2240 := span_ok (by decide +kernel : span (Z 13) 80 2160 = true)
set_option maxHeartbeats 0 in
theorem z13_2240 : Ok 13 2240 2320 := span_ok (by decide +kernel : span (Z 13) 80 2240 = true)
set_option maxHeartbeats 0 in
theorem z13_2320 : Ok 13 2320 2400 := span_ok (by decide +kernel : span (Z 13) 80 2320 = true)
set_option maxHeartbeats 0 in
theorem z13_2400 : Ok 13 2400 2480 := span_ok (by decide +kernel : span (Z 13) 80 2400 = true)
set_option maxHeartbeats 0 in
theorem z13_2480 : Ok 13 2480 2560 := span_ok (by decide +kernel : span (Z 13) 80 2480 = true)
set_option maxHeartbeats 0 in
theorem z13_2560 : Ok 13 2560 2640 := span_ok (by decide +kernel : span (Z 13) 80 2560 = true)
set_option maxHeartbeats 0 in
theorem z13_2640 : Ok 13 2640 2720 := span_ok (by decide +kernel : span (Z 13) 80 2640 = true)
set_option maxHeartbeats 0 in
theorem z13_2720 : Ok 13 2720 2800 := span_ok (by decide +kernel : span (Z 13) 80 2720 = true)
set_option maxHeartbeats 0 in
theorem z13_2800 : Ok 13 2800 2880 := span_ok (by decide +kernel : span (Z 13) 80 2800 = true)
set_option maxHeartbeats 0 in
theorem z13_2880 : Ok 13 2880 2960 := span_ok (by decide +kernel : span (Z 13) 80 2880 = true)
set_option maxHeartbeats 0 in
theorem z13_2960 : Ok 13 2960 3040 := span_ok (by decide +kernel : span (Z 13) 80 2960 = true)
set_option maxHeartbeats 0 in
theorem z13_3040 : Ok 13 3040 3120 := span_ok (by decide +kernel : span (Z 13) 80 3040 = true)
set_option maxHeartbeats 0 in
theorem z13_3120 : Ok 13 3120 3200 := span_ok (by decide +kernel : span (Z 13) 80 3120 = true)
set_option maxHeartbeats 0 in
theorem z13_3200 : Ok 13 3200 3280 := span_ok (by decide +kernel : span (Z 13) 80 3200 = true)
set_option maxHeartbeats 0 in
theorem z13_3280 : Ok 13 3280 3338 := span_ok (by decide +kernel : span (Z 13) 58 3280 = true)
theorem z13 : Ok 13 0 (NN 13) := (range_split (range_split (range_split (range_split (range_split z13_0 z13_80) (range_split z13_160 (range_split z13_240 z13_320))) (range_split (range_split z13_400 z13_480) (range_split z13_560 (range_split z13_640 z13_720)))) (range_split (range_split (range_split z13_800 z13_880) (range_split z13_960 (range_split z13_1040 z13_1120))) (range_split (range_split z13_1200 (range_split z13_1280 z13_1360)) (range_split z13_1440 (range_split z13_1520 z13_1600))))) (range_split (range_split (range_split (range_split z13_1680 z13_1760) (range_split z13_1840 (range_split z13_1920 z13_2000))) (range_split (range_split z13_2080 z13_2160) (range_split z13_2240 (range_split z13_2320 z13_2400)))) (range_split (range_split (range_split z13_2480 z13_2560) (range_split z13_2640 (range_split z13_2720 z13_2800))) (range_split (range_split z13_2880 (range_split z13_2960 z13_3040)) (range_split z13_3120 (range_split z13_3200 z13_3280))))))
set_option maxHeartbeats 0 in
theorem z14_0 : Ok 14 0 80 := span_ok (by decide +kernel : span (Z 14) 80 0 = true)
set_option maxHeartbeats 0 in
theorem z14_80 : Ok 14 80 160 := span_ok (by decide +kernel : span (Z 14) 80 80 = true)
set_option maxHeartbeats 0 in
theorem z14_160 : Ok 14 160 240 := span_ok (by decide +kernel : span (Z 14) 80 160 = true)
set_option maxHeartbeats 0 in
theorem z14_240 : Ok 14 240 320 := span_ok (by decide +kernel : span (Z 14) 80 240 = true)
set_option maxHeartbeats 0 in
theorem z14_320 : Ok 14 320 400 := span_ok (by decide +kernel : span (Z 14) 80 320 = true)
set_option maxHeartbeats 0 in
theorem z14_400 : Ok 14 400 480 := span_ok (by decide +kernel : span (Z 14) 80 400 = true)
set_option maxHeartbeats 0 in
theorem z14_480 : Ok 14 480 560 := span_ok (by decide +kernel : span (Z 14) 80 480 = true)
set_option maxHeartbeats 0 in
theorem z14_560 : Ok 14 560 640 := span_ok (by decide +kernel : span (Z 14) 80 560 = true)
theorem z14 : Ok 14 0 (NN 14) := (range_split (range_split (range_split z14_0 z14_80) (range_split z14_160 z14_240)) (range_split (range_split z14_320 z14_400) (range_split z14_480 z14_560)))
set_option maxHeartbeats 0 in
theorem z15_0 : Ok 15 0 50 := span_ok (by decide +kernel : span (Z 15) 50 0 = true)
set_option maxHeartbeats 0 in
theorem z15_50 : Ok 15 50 100 := span_ok (by decide +kernel : span (Z 15) 50 50 = true)
set_option maxHeartbeats 0 in
theorem z15_100 : Ok 15 100 150 := span_ok (by decide +kernel : span (Z 15) 50 100 = true)
set_option maxHeartbeats 0 in
theorem z15_150 : Ok 15 150 200 := span_ok (by decide +kernel : span (Z 15) 50 150 = true)
set_option maxHeartbeats 0 in
theorem z15_200 : Ok 15 200 250 := span_ok (by decide +kernel : span (Z 15) 50 200 = true)
set_option maxHeartbeats 0 in
theorem z15_250 : Ok 15 250 300 := span_ok (by decide +kernel : span (Z 15) 50 250 = true)
set_option maxHeartbeats 0 in
theorem z15_300 : Ok 15 300 350 := span_ok (by decide +kernel : span (Z 15) 50 300 = true)
set_option maxHeartbeats 0 in
theorem z15_350 : Ok 15 350 400 := span_ok (by decide +kernel : span (Z 15) 50 350 = true)
set_option maxHeartbeats 0 in
theorem z15_400 : Ok 15 400 450 := span_ok (by decide +kernel : span (Z 15) 50 400 = true)
set_option maxHeartbeats 0 in
theorem z15_450 : Ok 15 450 500 := span_ok (by decide +kernel : span (Z 15) 50 450 = true)
set_option maxHeartbeats 0 in
theorem z15_500 : Ok 15 500 550 := span_ok (by decide +kernel : span (Z 15) 50 500 = true)
set_option maxHeartbeats 0 in
theorem z15_550 : Ok 15 550 600 := span_ok (by decide +kernel : span (Z 15) 50 550 = true)
set_option maxHeartbeats 0 in
theorem z15_600 : Ok 15 600 650 := span_ok (by decide +kernel : span (Z 15) 50 600 = true)
set_option maxHeartbeats 0 in
theorem z15_650 : Ok 15 650 700 := span_ok (by decide +kernel : span (Z 15) 50 650 = true)
set_option maxHeartbeats 0 in
theorem z15_700 : Ok 15 700 750 := span_ok (by decide +kernel : span (Z 15) 50 700 = true)
set_option maxHeartbeats 0 in
theorem z15_750 : Ok 15 750 800 := span_ok (by decide +kernel : span (Z 15) 50 750 = true)
set_option maxHeartbeats 0 in
theorem z15_800 : Ok 15 800 850 := span_ok (by decide +kernel : span (Z 15) 50 800 = true)
set_option maxHeartbeats 0 in
theorem z15_850 : Ok 15 850 900 := span_ok (by decide +kernel : span (Z 15) 50 850 = true)
set_option maxHeartbeats 0 in
theorem z15_900 : Ok 15 900 950 := span_ok (by decide +kernel : span (Z 15) 50 900 = true)
set_option maxHeartbeats 0 in
theorem z15_950 : Ok 15 950 1000 := span_ok (by decide +kernel : span (Z 15) 50 950 = true)
set_option maxHeartbeats 0 in
theorem z15_1000 : Ok 15 1000 1050 := span_ok (by decide +kernel : span (Z 15) 50 1000 = true)
set_option maxHeartbeats 0 in
theorem z15_1050 : Ok 15 1050 1100 := span_ok (by decide +kernel : span (Z 15) 50 1050 = true)
set_option maxHeartbeats 0 in
theorem z15_1100 : Ok 15 1100 1150 := span_ok (by decide +kernel : span (Z 15) 50 1100 = true)
set_option maxHeartbeats 0 in
theorem z15_1150 : Ok 15 1150 1200 := span_ok (by decide +kernel : span (Z 15) 50 1150 = true)
set_option maxHeartbeats 0 in
theorem z15_1200 : Ok 15 1200 1250 := span_ok (by decide +kernel : span (Z 15) 50 1200 = true)
set_option maxHeartbeats 0 in
theorem z15_1250 : Ok 15 1250 1300 := span_ok (by decide +kernel : span (Z 15) 50 1250 = true)
set_option maxHeartbeats 0 in
theorem z15_1300 : Ok 15 1300 1350 := span_ok (by decide +kernel : span (Z 15) 50 1300 = true)
set_option maxHeartbeats 0 in
theorem z15_1350 : Ok 15 1350 1400 := span_ok (by decide +kernel : span (Z 15) 50 1350 = true)
set_option maxHeartbeats 0 in
theorem z15_1400 : Ok 15 1400 1450 := span_ok (by decide +kernel : span (Z 15) 50 1400 = true)
set_option maxHeartbeats 0 in
theorem z15_1450 : Ok 15 1450 1500 := span_ok (by decide +kernel : span (Z 15) 50 1450 = true)
set_option maxHeartbeats 0 in
theorem z15_1500 : Ok 15 1500 1550 := span_ok (by decide +kernel : span (Z 15) 50 1500 = true)
set_option maxHeartbeats 0 in
theorem z15_1550 : Ok 15 1550 1600 := span_ok (by decide +kernel : span (Z 15) 50 1550 = true)
set_option maxHeartbeats 0 in
theorem z15_1600 : Ok 15 1600 1650 := span_ok (by decide +kernel : span (Z 15) 50 1600 = true)
set_option maxHeartbeats 0 in
theorem z15_1650 : Ok 15 1650 1700 := span_ok (by decide +kernel : span (Z 15) 50 1650 = true)
set_option maxHeartbeats 0 in
theorem z15_1700 : Ok 15 1700 1750 := span_ok (by decide +kernel : span (Z 15) 50 1700 = true)
set_option maxHeartbeats 0 in
theorem z15_1750 : Ok 15 1750 1800 := span_ok (by decide +kernel : span (Z 15) 50 1750 = true)
set_option maxHeartbeats 0 in
theorem z15_1800 : Ok 15 1800 1850 := span_ok (by decide +kernel : span (Z 15) 50 1800 = true)
set_option maxHeartbeats 0 in
theorem z15_1850 : Ok 15 1850 1900 := span_ok (by decide +kernel : span (Z 15) 50 1850 = true)
set_option maxHeartbeats 0 in
theorem z15_1900 : Ok 15 1900 1950 := span_ok (by decide +kernel : span (Z 15) 50 1900 = true)
set_option maxHeartbeats 0 in
theorem z15_1950 : Ok 15 1950 2000 := span_ok (by decide +kernel : span (Z 15) 50 1950 = true)
set_option maxHeartbeats 0 in
theorem z15_2000 : Ok 15 2000 2050 := span_ok (by decide +kernel : span (Z 15) 50 2000 = true)
set_option maxHeartbeats 0 in
theorem z15_2050 : Ok 15 2050 2100 := span_ok (by decide +kernel : span (Z 15) 50 2050 = true)
set_option maxHeartbeats 0 in
theorem z15_2100 : Ok 15 2100 2144 := span_ok (by decide +kernel : span (Z 15) 44 2100 = true)
theorem z15 : Ok 15 0 (NN 15) := (range_split (range_split (range_split (range_split (range_split z15_0 z15_50) (range_split z15_100 (range_split z15_150 z15_200))) (range_split (range_split z15_250 z15_300) (range_split z15_350 (range_split z15_400 z15_450)))) (range_split (range_split (range_split z15_500 z15_550) (range_split z15_600 (range_split z15_650 z15_700))) (range_split (range_split z15_750 (range_split z15_800 z15_850)) (range_split z15_900 (range_split z15_950 z15_1000))))) (range_split (range_split (range_split (range_split z15_1050 z15_1100) (range_split z15_1150 (range_split z15_1200 z15_1250))) (range_split (range_split z15_1300 (range_split z15_1350 z15_1400)) (range_split z15_1450 (range_split z15_1500 z15_1550)))) (range_split (range_split (range_split z15_1600 z15_1650) (range_split z15_1700 (range_split z15_1750 z15_1800))) (range_split (range_split z15_1850 (range_split z15_1900 z15_1950)) (range_split z15_2000 (range_split z15_2050 z15_2100))))))
set_option maxHeartbeats 0 in
theorem z16_0 : Ok 16 0 50 := span_ok (by decide +kernel : span (Z 16) 50 0 = true)
set_option maxHeartbeats 0 in
theorem z16_50 : Ok 16 50 100 := span_ok (by decide +kernel : span (Z 16) 50 50 = true)
set_option maxHeartbeats 0 in
theorem z16_100 : Ok 16 100 150 := span_ok (by decide +kernel : span (Z 16) 50 100 = true)
set_option maxHeartbeats 0 in
theorem z16_150 : Ok 16 150 200 := span_ok (by decide +kernel : span (Z 16) 50 150 = true)
set_option maxHeartbeats 0 in
theorem z16_200 : Ok 16 200 250 := span_ok (by decide +kernel : span (Z 16) 50 200 = true)
set_option maxHeartbeats 0 in
theorem z16_250 : Ok 16 250 300 := span_ok (by decide +kernel : span (Z 16) 50 250 = true)
set_option maxHeartbeats 0 in
theorem z16_300 : Ok 16 300 350 := span_ok (by decide +kernel : span (Z 16) 50 300 = true)
set_option maxHeartbeats 0 in
theorem z16_350 : Ok 16 350 400 := span_ok (by decide +kernel : span (Z 16) 50 350 = true)
set_option maxHeartbeats 0 in
theorem z16_400 : Ok 16 400 450 := span_ok (by decide +kernel : span (Z 16) 50 400 = true)
set_option maxHeartbeats 0 in
theorem z16_450 : Ok 16 450 500 := span_ok (by decide +kernel : span (Z 16) 50 450 = true)
set_option maxHeartbeats 0 in
theorem z16_500 : Ok 16 500 550 := span_ok (by decide +kernel : span (Z 16) 50 500 = true)
set_option maxHeartbeats 0 in
theorem z16_550 : Ok 16 550 600 := span_ok (by decide +kernel : span (Z 16) 50 550 = true)
set_option maxHeartbeats 0 in
theorem z16_600 : Ok 16 600 650 := span_ok (by decide +kernel : span (Z 16) 50 600 = true)
set_option maxHeartbeats 0 in
theorem z16_650 : Ok 16 650 700 := span_ok (by decide +kernel : span (Z 16) 50 650 = true)
set_option maxHeartbeats 0 in
theorem z16_700 : Ok 16 700 750 := span_ok (by decide +kernel : span (Z 16) 50 700 = true)
set_option maxHeartbeats 0 in
theorem z16_750 : Ok 16 750 786 := span_ok (by decide +kernel : span (Z 16) 36 750 = true)
theorem z16 : Ok 16 0 (NN 16) := (range_split (range_split (range_split (range_split z16_0 z16_50) (range_split z16_100 z16_150)) (range_split (range_split z16_200 z16_250) (range_split z16_300 z16_350))) (range_split (range_split (range_split z16_400 z16_450) (range_split z16_500 z16_550)) (range_split (range_split z16_600 z16_650) (range_split z16_700 z16_750))))
set_option maxHeartbeats 0 in
theorem z17_0 : Ok 17 0 30 := span_ok (by decide +kernel : span (Z 17) 30 0 = true)
set_option maxHeartbeats 0 in
theorem z17_30 : Ok 17 30 60 := span_ok (by decide +kernel : span (Z 17) 30 30 = true)
set_option maxHeartbeats 0 in
theorem z17_60 : Ok 17 60 90 := span_ok (by decide +kernel : span (Z 17) 30 60 = true)
set_option maxHeartbeats 0 in
theorem z17_90 : Ok 17 90 120 := span_ok (by decide +kernel : span (Z 17) 30 90 = true)
set_option maxHeartbeats 0 in
theorem z17_120 : Ok 17 120 150 := span_ok (by decide +kernel : span (Z 17) 30 120 = true)
set_option maxHeartbeats 0 in
theorem z17_150 : Ok 17 150 180 := span_ok (by decide +kernel : span (Z 17) 30 150 = true)
set_option maxHeartbeats 0 in
theorem z17_180 : Ok 17 180 210 := span_ok (by decide +kernel : span (Z 17) 30 180 = true)
set_option maxHeartbeats 0 in
theorem z17_210 : Ok 17 210 240 := span_ok (by decide +kernel : span (Z 17) 30 210 = true)
set_option maxHeartbeats 0 in
theorem z17_240 : Ok 17 240 270 := span_ok (by decide +kernel : span (Z 17) 30 240 = true)
set_option maxHeartbeats 0 in
theorem z17_270 : Ok 17 270 300 := span_ok (by decide +kernel : span (Z 17) 30 270 = true)
set_option maxHeartbeats 0 in
theorem z17_300 : Ok 17 300 330 := span_ok (by decide +kernel : span (Z 17) 30 300 = true)
set_option maxHeartbeats 0 in
theorem z17_330 : Ok 17 330 358 := span_ok (by decide +kernel : span (Z 17) 28 330 = true)
theorem z17 : Ok 17 0 (NN 17) := (range_split (range_split (range_split z17_0 (range_split z17_30 z17_60)) (range_split z17_90 (range_split z17_120 z17_150))) (range_split (range_split z17_180 (range_split z17_210 z17_240)) (range_split z17_270 (range_split z17_300 z17_330))))
set_option maxHeartbeats 0 in
theorem z18_0 : Ok 18 0 30 := span_ok (by decide +kernel : span (Z 18) 30 0 = true)
set_option maxHeartbeats 0 in
theorem z18_30 : Ok 18 30 60 := span_ok (by decide +kernel : span (Z 18) 30 30 = true)
set_option maxHeartbeats 0 in
theorem z18_60 : Ok 18 60 90 := span_ok (by decide +kernel : span (Z 18) 30 60 = true)
set_option maxHeartbeats 0 in
theorem z18_90 : Ok 18 90 120 := span_ok (by decide +kernel : span (Z 18) 30 90 = true)
set_option maxHeartbeats 0 in
theorem z18_120 : Ok 18 120 147 := span_ok (by decide +kernel : span (Z 18) 27 120 = true)
theorem z18 : Ok 18 0 (NN 18) := (range_split (range_split z18_0 z18_30) (range_split z18_60 (range_split z18_90 z18_120)))
set_option maxHeartbeats 0 in
theorem z19 : Ok 19 0 (NN 19) := span_ok (by decide +kernel : span (Z 19) 14 0 = true)
set_option maxHeartbeats 0 in
theorem z20 : Ok 20 0 (NN 20) := span_ok (by decide +kernel : span (Z 20) 4 0 = true)
set_option maxHeartbeats 0 in
theorem z21 : Ok 21 0 (NN 21) := span_ok (by decide +kernel : span (Z 21) 1 0 = true)
theorem checked : ∀ u ≤ 21, ∀ i < NN u, Z u i = true := by
  intro u hu; interval_cases u
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
  · exact fun i hi => z11 i (Nat.zero_le i) hi
  · exact fun i hi => z12 i (Nat.zero_le i) hi
  · exact fun i hi => z13 i (Nat.zero_le i) hi
  · exact fun i hi => z14 i (Nat.zero_le i) hi
  · exact fun i hi => z15 i (Nat.zero_le i) hi
  · exact fun i hi => z16 i (Nat.zero_le i) hi
  · exact fun i hi => z17 i (Nat.zero_le i) hi
  · exact fun i hi => z18 i (Nat.zero_le i) hi
  · exact fun i hi => z19 i (Nat.zero_le i) hi
  · exact fun i hi => z20 i (Nat.zero_le i) hi
  · exact fun i hi => z21 i (Nat.zero_le i) hi
def RootG (u : Nat) : Bool := (Nat.beq (u % 2) 0 && Nat.beq xsG.length (u / 2 + 1) && scr62 poolG xsG) || found S NN idx u (ori xsG)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 10 12 = true := by decide +kernel
theorem noRunFull (u : Nat) (hu : u ≤ 21) (h : NatRun1T 62 true (goal 62) u xsG) : False := by
  have hmin : 12 ≤ u := by
    have hl := run1T_len h
    change 7 ≤ u / 2 + 1 at hl
    omega
  have hr := span_ok rootChecked u hmin (by omega)
  unfold RootG at hr
  rw [Bool.or_eq_true] at hr
  rcases hr with hscr | hf
  · simp only [Bool.and_eq_true, Nat.beq_eq] at hscr
    have hbad := scr62_no poolG_ok h hscr.1.1 hscr.1.2
    rw [hbad] at hscr; cases hscr.2
  · simp only [found, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact bar1T_all poolG_ok ori_ok checked u hu _ hf.1 (Run1T.perm (isPermFast_sound hf.2) (ori_ok h))
theorem rowsG_len : rowsG.length = 124 := by decide +kernel
theorem enc_inputsG : (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map (encT rowsG 62 true) = xsG := by decide +kernel
theorem enc_goalG : encT rowsG 62 true (fG, false) = goal 62 := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG → Nat.land (cov 62 zs) (lo 62) ≠ lo 62 := by decide +kernel
theorem noCircuit : ¬ Has1Not 7 fG 11 10 := by
  intro h
  obtain ⟨u, hu, _, ws, hsub, hrun⟩ := exists_run_1not true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn 11 10 htag_fn h
  have hr : NatRun1T 62 true (encT rowsG 62 true (fG, false)) u (ws.map (encT rowsG 62 true)) :=
    Run1T.map (encT rowsG 62 true) (fun a => encT_inv rowsG 62 rowsG_len true a) (fun a b => encT_and rowsG 62 rowsG_len true a b) (fun a b => encT_or rowsG 62 rowsG_len true a b) (fun a => encT_tag rowsG 62 rowsG_len true a) hrun
  rw [enc_goalG] at hr
  have hsub' : (ws.map (encT rowsG 62 true)).Sublist xsG := by rw [← enc_inputsG]; exact hsub.map _
  by_cases he : ws.map (encT rowsG 62 true) = xsG
  · rw [he] at hr; exact noRunFull u hu hr
  · exact proper_failG _ (List.mem_sublists.2 hsub') he (required hr)
end Main

def wg : List Gate :=
  [⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [9, 5]⟩,
   ⟨.and, [0, 10]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [6, 11]⟩,
   ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem bridge : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) =
    Main.fG x := by decide +kernel

theorem weval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Main.fG x := by decide +kernel

end PEqualNP.Outside.L_meta_10742_aux

theorem PEqualNP.Outside.L_meta_10742 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits huniq computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have hnot1 : PEqualNP.Outside.L_meta_10742_aux.notCount gates ≤ 1 := by
      obtain ⟨g0, hg0, hop0⟩ := hasNot
      obtain ⟨i0, hi0, rfl⟩ := List.getElem_of_mem hg0
      have hcount : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate),
          (∀ i j : Fin l.length, (l.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            (l.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
          PEqualNP.Outside.L_meta_10742_aux.notCount l ≤ 1 := by
        intro l hu
        induction l with
        | nil => simp [PEqualNP.Outside.L_meta_10742_aux.notCount]
        | cons x xs ih =>
          simp only [PEqualNP.Outside.L_meta_10742_aux.notCount, List.countP_cons]
          by_cases hx : x.op = PEqualNP.CircuitLowerBounds.GateOp.not
          · have hzero : xs.countP (fun g => PEqualNP.Outside.L_meta_10742_aux.isNot g.op) = 0 := by
              rw [List.countP_eq_zero]
              intro y hy
              obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
              intro hyop
              have hop' : xs[k].op = PEqualNP.CircuitLowerBounds.GateOp.not := by
                cases h : xs[k].op <;> simp [PEqualNP.Outside.L_meta_10742_aux.isNot, h] at hyop ⊢
              have heq := hu ⟨0, by simp⟩ ⟨k + 1, by simp; omega⟩ hx hop'
              simp at heq
            rw [hzero]; simp [hx, PEqualNP.Outside.L_meta_10742_aux.isNot]
          · have hnx : PEqualNP.Outside.L_meta_10742_aux.isNot x.op = false := by
              cases h : x.op <;> simp [PEqualNP.Outside.L_meta_10742_aux.isNot] at hx ⊢
              exact hx h
            simp only [hnx, Bool.false_eq_true, ite_false, Nat.add_zero]
            apply ih
            intro i j hi hj
            have heq := hu ⟨i.val + 1, by simp⟩ ⟨j.val + 1, by simp⟩ hi hj
            exact Fin.ext (by simpa using congrArg Fin.val heq)
      exact hcount gates huniq
    have hge12 : 12 ≤ gates.length := by
      by_contra! hsmall
      obtain ⟨g0, hg0, hop0⟩ := hasNot
      have hnot_pos : 1 ≤ PEqualNP.Outside.L_meta_10742_aux.notCount gates :=
        List.countP_pos_iff.2 ⟨g0, hg0, by simp [PEqualNP.Outside.L_meta_10742_aux.isNot, hop0]⟩
      have hsum := PEqualNP.Outside.L_meta_10742_aux.notCount_add_binCount gates
      have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
        intro g hg
        refine ⟨?_, (fits g hg).2⟩
        rcases (fits g hg).1 with h1 | h1 | h1 <;> simp [h1]
      exact PEqualNP.Outside.L_meta_10742_aux.Main.noCircuit
        ⟨⟨gates, o⟩, hfan, by dsimp only; omega, by dsimp only; omega, hnot1,
          fun x => (computes x).trans (PEqualNP.Outside.L_meta_10742_aux.bridge x)⟩
    exact ⟨PEqualNP.Outside.L_meta_10742_aux.wg, 18, PEqualNP.Outside.L_meta_10742_aux.wfits,
      by simp [PEqualNP.Outside.L_meta_10742_aux.wg]; omega,
      fun x => (PEqualNP.Outside.L_meta_10742_aux.weval x).trans (PEqualNP.Outside.L_meta_10742_aux.bridge x).symm⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
