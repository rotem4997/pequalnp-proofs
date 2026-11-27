import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9167_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunT {α : Type} (inv : α → α) (meet join : α → α → α) (tag : α → Bool)
    (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), tag a = false →
      P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (c = true → tag a = false ∧ tag b = false) →
      (ka = true → tag a = false) → (kb = true → tag b = false) →
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {tag : α → Bool} {y : α}

theorem RunT.done : RunT inv meet join tag y 0 [y] := fun _ d _ _ _ => d

theorem RunT.perm {s xs zs} (p : List.Perm xs zs) (h : RunT inv meet join tag y s xs) :
    RunT inv meet join tag y s zs := fun P d q u b => q p (h P d q u b)

theorem RunT.one {s a r} (save : Bool) (ht : tag a = false)
    (h : RunT inv meet join tag y s (inv a :: kept save a r)) :
    RunT inv meet join tag y (s + 1) (a :: r) := fun P d q u b => u save ht (h P d q u b)

theorem RunT.two {s a b r} (c ka kb : Bool)
    (hc : c = true → tag a = false ∧ tag b = false)
    (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
    (h : RunT inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    RunT inv meet join tag y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb hc hta htb (h P d q u v)

theorem RunT.fold {P : ∀ t ws, RunT inv meet join tag y t ws → Prop}
    (done : P 0 [y] RunT.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunT inv meet join tag y s xs),
      P s xs h → P s zs (RunT.perm hp h))
    (one : ∀ {s a r} (save : Bool) (ht : tag a = false)
      (h : RunT inv meet join tag y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (RunT.one save ht h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (hc : c = true → tag a = false ∧ tag b = false)
      (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
      (h : RunT inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (RunT.two c ka kb hc hta htb h))
    {t ws} (h : RunT inv meet join tag y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunT inv meet join tag y s xs, P s xs h')
    ⟨RunT.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨RunT.perm hp h', perm hp h' ih⟩)
    (fun k ht ⟨h', ih⟩ => ⟨RunT.one k ht h', one k ht h' ih⟩)
    (fun c a b hc hta htb ⟨h', ih⟩ => ⟨RunT.two c a b hc hta htb h', two c a b hc hta htb h' ih⟩)
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

theorem RunT.map {α β : Type} (e : α → β)
    {inv : α → α} {meet join : α → α → α} {tag : α → Bool}
    {inv' : β → β} {meet' join' : β → β → β} {tag' : β → Bool}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    (htag : ∀ a, tag' (e a) = tag a)
    {y : α} {s : ℕ} {ws : List α} (h : RunT inv meet join tag y s ws) :
    RunT inv' meet' join' tag' (e y) s (ws.map e) := by
  induction h using RunT.fold with
  | done => exact RunT.done
  | perm hp _ ih => exact RunT.perm (hp.map e) ih
  | @one s a rest save ht _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact RunT.one save ((htag a).trans ht) ih
  | @two s a b rest conj ka kb hc hta htb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact RunT.two conj ka kb
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

theorem simplify_none_of_inl (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (h : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
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
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [simpNot]
    · simp at hl1

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpStep_len_le (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
  simp only [simpStep, List.length_append]
  cases (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 := simpStep_len_le n acc g
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

theorem simpPass_len_drop (m v : ℕ) (b : Bool) (gs : List Gate) :
    ∀ acc : List (Sum Bool ℕ) × List Gate,
      (∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      v < acc.1.length →
      acc.1.getD v (Sum.inl false) = Sum.inl b →
      (simpPass m gs acc).2.length + (gs.countP (fun g => decide (v ∈ g.inputs)))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [simpPass]
  | cons g gs ih =>
    intro acc hok hvl hvb
    have hstep_v : v < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have hstep_b : (simpStep m acc g).1.getD v (Sum.inl false) = Sum.inl b := by
      simp only [simpStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hvb
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
      simp only [hv, decide_true, ite_true]
      omega
    · have hlen1 := simpStep_len_le m acc g
      simp only [hv, decide_false, Bool.false_eq_true, ite_false]
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

def substIn {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => match c i with
    | Sum.inl b => b
    | Sum.inr j => x j

def initSubst {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) : List (Sum Bool ℕ) :=
  List.ofFn fun i : Fin n => match c i with
    | Sum.inl b => Sum.inl b
    | Sum.inr j => Sum.inr j.val

theorem sclean_fanInTwo {m : ℕ} {gs : List Gate} (hcl : SCleanL m gs) (o : ℕ) :
    FanInTwo ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
  have hcg := hcl p gs[p] (List.getElem?_eq_getElem hp)
  rcases hcg with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
  · exact ⟨by simp [hop], by simp [hin]⟩
  · rcases hop with hop | hop <;> exact ⟨by simp [hop], by simp [hin]⟩

theorem restrict_sclean_drop {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hev : ∀ x, val gs n o x = f x) :
    HasCircuitSize m (fun y => f (substIn c y))
      (gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs))) := by
  have hok_inv : ∀ g ∈ gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop), by simp [hin]⟩
    · rcases hop with hop | hop
      · exact ⟨Or.inl hop, by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop), by simp [hin]⟩
  have hok_drop : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop with hop | hop <;> exact ⟨by simp [hin], by simp [hop]⟩
  set init := initSubst c
  set acc := simpPass m gs (init, [])
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y
    refine ⟨by simp [init, initSubst], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with
      | inl b => simp [statValid, statVal]
      | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool,
      SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := fun y =>
    simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hv_init : init.getD v.val (Sum.inl false) = Sum.inl false := by
    simp [init, initSubst, v.isLt, hv]
  have hlen_drop := simpPass_len_drop m v.val false gs (init, []) hok_drop
    (by simp [init, initSubst, v.isLt]) hv_init
  simp only [List.length_nil, zero_add] at hlen_drop
  change acc.2.length + gs.countP (fun g => decide (v.val ∈ g.inputs)) ≤ gs.length at hlen_drop
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c0 =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← h1, ← h2]
    rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', ?_, ?_⟩
    · show acc.2.length ≤ gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs))
      omega
    · intro y
      have h1 := ((hinv y).2.2 o).2
      rw [hst] at h1
      dsimp only
      rw [← hev (substIn c y)]
      exact h1

theorem simpPass_acc1_len (m : ℕ) (gs : List Gate) :
    ∀ acc : List (Sum Bool ℕ) × List Gate,
      (simpPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep m acc g)
    have h2 : (simpStep m acc g).1.length = acc.1.length + 1 := by simp [simpStep]
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, h1, h2, List.length_cons]
    omega

theorem simpPass_acc1_getD (m : ℕ) (gs : List Gate) (i : ℕ) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, i < acc.1.length →
      (simpPass m gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hi
    have hstep : i < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, ih (simpStep m acc g) hstep]
    simp only [simpStep]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem simpPass_append (m : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    simpPass m (gs₁ ++ gs₂) acc = simpPass m gs₂ (simpPass m gs₁ acc) :=
  List.foldl_append

theorem restrict_sclean_drop2 {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (hev : ∀ x, val gs n o x = f x)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g)
    (hvin : v.val ∈ g.inputs) (hop : g.op = GateOp.not ∨ g.op = GateOp.and) :
    HasCircuitSize m (fun y => f (substIn c y)) (gs.length - 2) := by
  have hok_inv : ∀ g' ∈ gs,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
    intro g' hg'
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop'), by simp [hin]⟩
    · rcases hop' with hop' | hop'
      · exact ⟨Or.inl hop', by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop'), by simp [hin]⟩
  have hok_drop : ∀ g' ∈ gs, g'.inputs.length ≤ 2 ∧ (g'.op = GateOp.not → g'.inputs.length ≤ 1) := by
    intro g' hg'
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop' with hop' | hop' <;> exact ⟨by simp [hin], by simp [hop']⟩
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  set init := initSubst c
  set acc1 := simpPass m pre (init, [])
  set acc2 := simpStep m acc1 g
  set acc := simpPass m post acc2
  have hacc_eq : acc = simpPass m gs (init, []) := by
    conv_rhs => rw [hsplit]
    rw [simpPass_append]
    rfl
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y
    refine ⟨by simp [init, initSubst], by intro q g' hqg; simp at hqg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with
      | inl b => simp [statValid, statVal]
      | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool,
      SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := by
    intro y; rw [hacc_eq]
    exact simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hl1 : acc1.1.length = n + p := by
    have h1 := simpPass_acc1_len m pre (init, [])
    change acc1.1.length = init.length + pre.length at h1
    simp only [init, initSubst, List.length_ofFn] at h1
    omega
  have hv1 : acc1.1.getD v.val (Sum.inl false) = Sum.inl false := by
    rw [simpPass_acc1_getD m pre v.val (init, []) (by simp [init, initSubst, v.isLt])]
    simp [init, initSubst, v.isLt, hv]
  have hcl_g := hcl p g hg
  have hg_res : (simplify g.op (m + acc1.2.length)
      (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none ∧
      ∃ b0 : Bool, (simplify g.op (m + acc1.2.length)
        (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 = Sum.inl b0 := by
    rcases hcl_g with ⟨hnot, j, _, hin⟩ | ⟨hor_and, j, k, _, _, _, hin⟩
    · rw [hin] at hvin
      have hjv : j = v.val := (List.mem_singleton.1 hvin).symm
      subst hjv
      rw [hnot, hin, List.map_cons, List.map_nil, hv1]
      exact ⟨rfl, true, rfl⟩
    · rcases hop with hnot | hand
      · rcases hor_and with h | h <;> rw [h] at hnot <;> cases hnot
      · rw [hin] at hvin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
        rcases hvin with h | h
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD k (Sum.inl false) <;> simp [simplify, simpAnd]
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD j (Sum.inl false) <;> simp [simplify, simpAnd]
  obtain ⟨hnone_g, b0, hb0⟩ := hg_res
  have hacc2_len : acc2.2.length = acc1.2.length := by
    simp only [acc2, simpStep, hnone_g, Option.toList_none, List.append_nil]
  have hacc2_1_len : acc2.1.length = n + p + 1 := by simp [acc2, simpStep, hl1]
  have hacc2_np : acc2.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    simp only [acc2, simpStep]
    rw [getD_snoc_len _ _ _ _ hl1]
    exact hb0
  have hacc_np : acc.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    rw [simpPass_acc1_getD m post (n + p) acc2 (by omega)]
    exact hacc2_np
  have hne_o : n + p ≠ o := by
    intro ho_eq
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [← ho_eq, hacc_np] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← ho_eq, ← h1, ← h2]
    rfl
  obtain ⟨q, g', hqg', hnp_in⟩ : ∃ (q : ℕ) (g' : Gate), gs[q]? = some g' ∧ n + p ∈ g'.inputs := by
    rcases hnd p hplt with h | h
    · exact absurd h hne_o
    · exact h
  have hq_gt : p < q := by
    have := (hcl q g' hqg').lt (n + p) hnp_in
    omega
  have hg'_post : g' ∈ post := by
    have hlt_q : q < gs.length := (List.getElem?_eq_some_iff.1 hqg').1
    have hq_sub : q - (p + 1) < post.length := by
      have : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
      omega
    have hget : post[q - (p + 1)] = g' := by
      have h1 : gs[q]? = post[q - (p + 1)]? := by
        conv_lhs => rw [hsplit]
        rw [List.getElem?_append_right (by omega)]
        have : q - pre.length = (q - (p + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      rw [hqg', List.getElem?_eq_getElem hq_sub] at h1
      exact Option.some.inj h1.symm
    rw [← hget]
    exact List.getElem_mem hq_sub
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
    exfalso
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← h1, ← h2]
    rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', ?_, ?_⟩
    · show acc.2.length ≤ gs.length - 2
      omega
    · intro y
      have h1 := ((hinv y).2.2 o).2
      rw [hst] at h1
      dsimp only
      rw [← hev (substIn c y)]
      exact h1

theorem wiresFrom_indep (gs : List Gate) (v : ℕ) (hni : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ a, a ≠ v → w₁.getD a false = w₂.getD a false) →
      ∀ a, a ≠ v → (wiresFrom gs w₁).getD a false = (wiresFrom gs w₂).getD a false := by
  induction gs with
  | nil => intro w₁ w₂ _ heq a ha; exact heq a ha
  | cons g gs ih =>
    intro w₁ w₂ hlen heq
    have hg : v ∉ g.inputs := hni g List.mem_cons_self
    have hmap : g.inputs.map (fun i => w₁.getD i false) = g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro a ha
      exact heq a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => w₁.getD i false)
    rw [wiresFrom_cons, wiresFrom_cons, ← hmap]
    apply ih (fun g' hg' => hni g' (List.mem_cons_of_mem _ hg')) (w₁ ++ [c]) (w₂ ++ [c]) (by simp [hlen])
    intro a ha
    by_cases hal : a = w₁.length
    · subst hal
      rw [getD_snoc_len _ _ _ _ rfl, getD_snoc_len _ _ _ _ hlen.symm]
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact heq a ha

theorem countP_pos_of_dep {n : ℕ} (f : BFn n) (v : Fin n)
    (hdep : ∃ y : Fin n → Bool, f y ≠ f (Function.update y v (!y v)))
    (hnoproj : ∃ y : Fin n → Bool, f y ≠ y v)
    (gs : List Gate) (o : ℕ) (hev : ∀ x, val gs n o x = f x) :
    1 ≤ gs.countP (fun g => decide (v.val ∈ g.inputs)) := by
  by_contra! h0
  have hzero : gs.countP (fun g => decide (v.val ∈ g.inputs)) = 0 := by omega
  have hni : ∀ g ∈ gs, v.val ∉ g.inputs := by
    intro g hg
    have hfalse := (List.countP_eq_zero.1 hzero) g hg
    simpa using hfalse
  have hne_o : o ≠ v.val := by
    intro ho
    obtain ⟨y, hy⟩ := hnoproj
    apply hy
    rw [← hev y, ho, val_input]
  obtain ⟨y, hy⟩ := hdep
  apply hy
  rw [← hev y, ← hev (Function.update y v (!y v))]
  unfold val
  apply wiresFrom_indep gs v.val hni (List.ofFn y) (List.ofFn (Function.update y v (!y v))) (by simp)
  · intro a ha
    by_cases han : a < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, han, dite_true, Option.getD_some]
      have hne_fin : (⟨a, han⟩ : Fin n) ≠ v := fun e => ha (congrArg Fin.val e)
      simp [Function.update, hne_fin]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · exact hne_o

theorem direct_f0_step {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (hdep : ∃ y : Fin n → Bool, f y ≠ f (Function.update y v (!y v)))
    (hnoproj : ∃ y : Fin n → Bool, f y ≠ y v)
    (cap : ℕ) (h : HasCircuitSize n f cap) :
    HasCircuitSize m (fun y => f (substIn c y)) (cap - 1) := by
  obtain ⟨gs, o, hlen, hcl, _, hev⟩ := exists_sclean f hnc cap h
  have hpos := countP_pos_of_dep f v hdep hnoproj gs o hev
  obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop f c v hv hnc_sub gs o hcl hev
  exact ⟨C, hfan, by omega, hevC⟩

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

abbrev invFT {n : ℕ} : BFn n × Bool → BFn n × Bool := fun p => (invF p.1, false)
abbrev meetFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (meetF p.1 q.1, false)
abbrev joinFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (joinF p.1 q.1, false)

theorem countP_le_one_not_live (gs : List Gate) (o p a : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (ha : a ∈ g.inputs) (hne : a ≠ o)
    (hc : gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1) :
    ¬ Live gs o (p + 1) a := by
  intro hl
  rcases hl with rfl | ⟨q, hq, g', hg', ha'⟩
  · exact hne rfl
  · obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
    have hq_post : g' ∈ post := by
      have hlt : q < gs.length := (List.getElem?_eq_some_iff.1 hg').1
      have hge : gs[q] = g' := (List.getElem?_eq_some_iff.1 hg').2
      have hq' : q - (p + 1) < post.length := by
        have hlen : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
        omega
      have hget : post[q - (p + 1)] = g' := by
        have h1 : gs[q]? = post[q - (p + 1)]? := by
          conv_lhs => rw [hsplit]
          rw [List.getElem?_append_right (by omega)]
          have : q - pre.length = (q - (p + 1)) + 1 := by omega
          rw [this, List.getElem?_cons_succ]
        rw [hg', List.getElem?_eq_getElem hq'] at h1
        exact Option.some.inj h1.symm
      rw [← hget]
      exact List.getElem_mem hq'
    have hpos : 0 < post.countP (fun g => decide (a ∈ g.inputs)) :=
      List.countP_pos_iff.2 ⟨g', hq_post, by simp [ha']⟩
    rw [hsplit, List.countP_append, List.countP_cons] at hc
    simp only [ha, decide_true, ite_true] at hc
    omega

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
theorem run_live_tagged (n : ℕ) (useTag : Bool) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (tagged : ℕ → Bool)
    (htag : ∀ a, a < n → tagged a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or)) :
    let encW := fun a => (val gs n a, decide (a < n ∧ tagged a = true))
    ∀ d p, p + d = gs.length →
      RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false) d
        ((liveList gs n o p).map encW) := by
  intro encW d
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
    have ho_tag : encW o = (val gs n o, false) := by
      simp only [encW, Prod.mk.injEq, true_and, decide_eq_false_iff_not, not_and]
      intro holt hto
      exact (htag o holt hto).1 rfl
    have hdone : RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false) 0 ([o].map encW) := by
      simp only [List.map_cons, List.map_nil, ho_tag]
      exact RunT.done
    exact RunT.perm (hperm.map encW) hdone
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
    have hguard : ∀ a ∈ g.inputs, decide (Live gs o (p + 1) a) = true → (useTag && (encW a).2) = false := by
      intro a ha hlive
      have h2 : (encW a).2 = false := by
        simp only [encW, decide_eq_false_iff_not, not_and]
        intro halt hta
        have ⟨hne, hc, _⟩ := htag a halt hta
        exact countP_le_one_not_live gs o p a g hg ha hne hc (of_decide_eq_true hlive)
      simp [h2]
    have hnot_or : ∀ a ∈ g.inputs, g.op ≠ GateOp.or → (useTag && (encW a).2) = false := by
      intro a ha hne_or
      have h2 : (encW a).2 = false := by
        simp only [encW, decide_eq_false_iff_not, not_and]
        intro halt hta
        exact hne_or ((htag a halt hta).2.2 p g hg ha)
      simp [h2]
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
      have hval : encW (n + p) = invFT (encW j) := by
        apply Prod.ext
        · funext x
          simp only [encW, invFT, invF]
          rw [hvg x, hop, hinp]
          simp [GateOp.eval]
        · simp [encW, invFT]
      have IH' := RunT.perm (hp2.map encW) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact RunT.perm (hp1.map encW).symm
        (RunT.one _ (hnot_or j (by simp [hinp]) (by simp [hop])) IH')
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
      have IH' := RunT.perm (hp2.map encW) IH
      have hval : encW (n + p) = (if decide (g.op = GateOp.and)
          then meetFT (encW j) (encW k) else joinFT (encW j) (encW k)) := by
        rcases hop with hop | hop
        · simp only [hop, decide_true, ite_true]
          apply Prod.ext
          · funext x; simp only [encW, meetFT, meetF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, meetFT]
        · simp only [hop, decide_false, ite_false]
          apply Prod.ext
          · funext x; simp only [encW, joinFT, joinF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, joinFT]
      have hand_guard : decide (g.op = GateOp.and) = true → (useTag && (encW j).2) = false ∧ (useTag && (encW k).2) = false := by
        intro ha
        have hgop : g.op = GateOp.and := of_decide_eq_true ha
        exact ⟨hnot_or j (by simp [hinp]) (by simp [hgop]), hnot_or k (by simp [hinp]) (by simp [hgop])⟩
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact RunT.perm (hp1.map encW).symm
        (RunT.two _ _ _ hand_guard (hguard j (by simp [hinp])) (hguard k (by simp [hinp])) IH')

open Classical in
theorem exists_run_tagged {n : ℕ} (useTag : Bool) (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (tagged : ℕ → Bool)
    (htag_fn : ∀ (gs : List Gate) (o : ℕ), gs.length ≤ s → SCleanL n gs →
      (∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) →
      (∀ x, val gs n o x = f x) →
      ∀ a, a < n → tagged a = true →
        a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
        (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or))
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n × Bool),
      ws.Sublist (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val)) ∧
      RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (f, false) s' ws := by
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
  let encW := fun a => (val gs n a, decide (a < n ∧ tagged a = true))
  refine ⟨gs.length, by omega, (liveList gs n o 0).map encW, ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val))
        = (List.range n).map encW := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, encW]
        have hi : i < n := by simpa using h1
        apply Prod.ext
        · exact (val_input gs n ⟨i, hi⟩).symm
        · simp [hi]
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live_tagged n useTag gs o hcl ho hnd tagged (htag_fn gs o (by omega) hcl hnd hev) gs.length 0 (by omega)

theorem runT_len {α inv meet join tag y s xs} (h : @RunT α inv meet join tag y s xs) :
    xs.length ≤ s + 1 := by
  induction h using RunT.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

abbrev NatRunT (k : Nat) (useTag : Bool) :=
  RunT (fun w => (w &&& mask k) ^^^ mask k)
       (fun a b => (a &&& b) &&& mask k)
       (fun a b => (a ||| b) &&& mask k)
       (fun w => useTag && w.testBit (2 * k))

theorem mask_testBit_lt {k i : Nat} (hi : i < 2 * k) : (mask k).testBit i = true := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega]

theorem mask_testBit_ge {k i : Nat} (hi : 2 * k ≤ i) : (mask k).testBit i = false := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show ¬ i < k + k by omega]

theorem run_bits {k useTag y s xs} (h : NatRunT k useTag y s xs) (i j : Nat)
    (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi := mask_testBit_lt hi
  have hmj := mask_testBit_lt hj
  induction h using RunT.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb, hmi, hmj] | exact hw _ (by simp only [List.mem_cons]; tauto)

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

theorem required {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) (by omega) (by omega) hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def nextT (k : Nat) (useTag : Bool) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  let m := mask k
  let tk := 2 * k
  ws.any fun a =>
    let ra := ws.erase a
    let ta := useTag && a.testBit tk
    (slack ≥ 1 && !ta &&
      (let w := (a &&& m) ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let tb := useTag && b.testBit tk
        [false, true].any fun conj =>
          !(conj && (ta || tb)) &&
          (let w := if conj then (a &&& b) &&& m else (a ||| b) &&& m
           f (w :: r) ||
             (slack ≥ 1 && ((!ta && f (w :: a :: r)) || (!tb && f (w :: b :: r)))) ||
             (slack ≥ 2 && !ta && !tb && f (w :: a :: b :: r))))

theorem nextT_one {k useTag a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (ht : (useTag && a.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s (((a &&& mask k) ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := runT_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨by simp [hsl, ht], ?_⟩
  have hfn := hf _ (RunT.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at hfn; simp [hfn]
  | true =>
    simp [kept] at hfn hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [hfn, hsl2]

theorem nextT_two_sorted {k useTag a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (hc : conj = true → (useTag && a.testBit (2 * k)) = false ∧ (useTag && b.testBit (2 * k)) = false)
    (hta : ka = true → (useTag && a.testBit (2 * k)) = false)
    (htb : kb = true → (useTag && b.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s
      ((if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := runT_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have hcg : !(conj && ((useTag && a.testBit (2 * k)) || (useTag && b.testBit (2 * k)))) = true := by
    cases conj
    · rfl
    · obtain ⟨h1, h2⟩ := hc rfl; simp [h1, h2]
  rw [Bool.and_eq_true]; refine ⟨hcg, ?_⟩
  have hfn := hf _ (RunT.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at hfn hh
  · simp [hfn]
  · have htbb := htb rfl
    have hsl1 : 1 ≤ s + 2 - ws.length := by omega
    simp [hfn, htbb, hsl1]
  · have htaa := hta rfl
    have hsl1 : 1 ≤ s + 2 - ws.length := by omega
    simp [hfn, htaa, hsl1]
  · have htaa := hta rfl
    have htbb := htb rfl
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [hfn, htaa, htbb, hsl2]

theorem nextT_two {k useTag a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (hc : conj = true → (useTag && a.testBit (2 * k)) = false ∧ (useTag && b.testBit (2 * k)) = false)
    (hta : ka = true → (useTag && a.testBit (2 * k)) = false)
    (htb : kb = true → (useTag && b.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s
      ((if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextT_two_sorted hab p hc hta htb h f hf
  · apply nextT_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (fun h => (hc h).symm) htb hta _ f hf
    have he : (if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k)
        = (if conj then (b &&& a) &&& mask k else (b ||| a) &&& mask k) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply RunT.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_doneT {α inv meet join tag y t ws} (h : @RunT α inv meet join tag y t ws) :
    t = 0 → ws = [y] := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem nextT_complete {k useTag t ws} (h : NatRunT k useTag (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) →
      nextT k useTag (s + 2 - zs.length) zs f = true := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save ht h ih => intro s he zs p f hf; cases he; exact nextT_one p ht h f hf
  | two conj ka kb hc hta htb h ih => intro s he zs p f hf; cases he; exact nextT_two p hc hta htb h f hf

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
    (useTag : Bool) (p : BFn n × Bool) :
    encT l k useTag p &&& mask k = encL p.1 l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encT, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    cases hb : (useTag && p.2) <;> simp [hm, Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge p.1 l j (by omega)
    simp [hm, he]

theorem encT_tag {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    (useTag && (encT l k useTag p).testBit (2 * k)) = (useTag && p.2) := by
  rw [encT, Nat.testBit_or, encL_testBit_ge p.1 l (2 * k) (by omega), Bool.false_or]
  cases useTag <;> cases p.2 <;> simp [Nat.testBit_shiftLeft]

theorem encT_inv {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    encT l k useTag (invFT p) = (encT l k useTag p &&& mask k) ^^^ mask k := by
  rw [encT_and_mask l k hl useTag p]
  simp only [encT, invFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, encL_testBit, encL_testBit]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    simp [hm, hjl, invF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [hm]

theorem encT_and {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (meetFT p q) = (encT l k useTag p &&& encT l k useTag q) &&& mask k := by
  simp only [encT, meetFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by
      simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;>
      simp [hm, hs, encL_testBit, hjl, meetF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (meetF p.1 q.1) l j (by omega)
    simp [hm, he]

theorem encT_or {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (joinFT p q) = (encT l k useTag p ||| encT l k useTag q) &&& mask k := by
  simp only [encT, joinFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by
      simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;>
      simp [hm, hs, encL_testBit, hjl, joinF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (joinF p.1 q.1) l j (by omega)
    simp [hm, he]

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

theorem move_runT {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k)
    (ht1 : tag.testBit (2 * k) = false) (ht2 : (tag <<< d).testBit (2 * k) = false) :
    NatRunT k useTag (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact RunT.map _
    (fun a => by rw [(move_hom tag d hz _ _).2.2, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).2.1, hm])
    (fun a => by rw [moved tag d (2 * k) a hz, ht1, ht2]; rfl)
    h

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK (k : Nat) (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) &&
  (moveBits p.1 p.2 (mask k) == mask k) &&
  (moveBits p.1 p.2 (goal k) == goal k) &&
  (!p.1.testBit (2 * k)) &&
  (!(p.1 <<< p.2).testBit (2 * k))

theorem applyMoves_runT {k useTag s} (ms : List (Nat × Nat)) (hok : ms.all (moveOK k) = true) :
    ∀ ws, NatRunT k useTag (goal k) s ws →
      NatRunT k useTag (goal k) s (ws.map (applyMoves ms)) := by
  induction ms with
  | nil =>
    intro ws h
    have e : ws.map (applyMoves []) = ws := by
      have hfn : applyMoves [] = id := funext fun _ => rfl
      rw [hfn, List.map_id]
    rw [e]
    exact h
  | cons p ps ih =>
    intro ws h
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hp := hok.1
    simp only [moveOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    have h1 := move_runT h p.1 p.2 hp.1.1.1.1 hp.1.1.1.2 hp.1.1.2 hp.1.2 hp.2
    have h2 := ih hok.2 _ h1
    have e : ws.map (applyMoves (p :: ps)) = (ws.map (moveBits p.1 p.2)).map (applyMoves ps) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact h2

theorem bits_le {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (i j : Nat) (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  have hmi := mask_testBit_lt hi
  have hmj := mask_testBit_lt hj
  induction h using RunT.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save _ h ih =>
    have hh := runT_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := runT_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and, hmi, hmj] <;>
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

theorem required_up {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (hl : ws.length = s + 1) :
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
      apply bits_le h hl (k + i) i (by omega) (by omega)
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) : covers k s ws = true := by
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

theorem score_bound {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat)
    (hand : ∀ a b, v ((a &&& b) &&& mask k) ≤ v a + v b)
    (hor : ∀ a b, v ((a ||| b) &&& mask k) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save _ h ih =>
    have hh := runT_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := runT_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : a < 2 * k) (hb : b < 2 * k) (hc : c < 2 * k)
    (hd : d < 2 * k) (he : e < 2 * k) (hf : f < 2 * k) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  have hma := mask_testBit_lt ha
  have hmb := mask_testBit_lt hb
  have hmc := mask_testBit_lt hc
  have hmd := mask_testBit_lt hd
  have hme := mask_testBit_lt he
  have hmf := mask_testBit_lt hf
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_and, Nat.testBit_or, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih =>
    rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]
    omega

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    let tk := 2 * k
    a < tk && b < tk && c < tk && d < tk && e < tk && f < tk &&
      ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f (goal k))

theorem scoreCheck_no {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hlt :
        (code &&& 1023) < 2 * k ∧ ((code >>> 10) &&& 1023) < 2 * k ∧
        ((code >>> 20) &&& 1023) < 2 * k ∧ ((code >>> 30) &&& 1023) < 2 * k ∧
        ((code >>> 40) &&& 1023) < 2 * k ∧ ((code >>> 50) &&& 1023) < 2 * k ∧
        ws.length = s + 1
    · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hlt
      simp only [ha, hb, hc, hd, he, hf, hl, decide_true, beq_self_eq_true, Bool.true_and]
      by_contra hbad
      have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
      exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      tauto

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

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i)
    (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw (seed w : Nat) : Nat :=
  let x := ((w &&& 4294967295) + ((w >>> 32) &&& 4294967295) * 3 +
            ((w >>> 64) &&& 4294967295) * 7 + ((w >>> 96) &&& 4294967295) * 11 +
            ((w >>> 128) &&& 4294967295) * 13 + ((w >>> 160) &&& 4294967295) * 17 +
            ((w >>> 192) &&& 4294967295) * 19 + ((w >>> 224) &&& 4294967295) * 23 +
            (w >>> 256) * 29 + seed) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} {useTag : Bool} (pool : List Nat) {zs : List Nat}
    (h : NatRunT k useTag (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (useTag : Bool) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(nextT k useTag (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k useTag S N idx ori pool} {s i : Nat}
    (hb : bar k useTag S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRunT k useTag (goal k) u ys → NatRunT k useTag (goal k) u (ori ys))
    (h : NatRunT k useTag (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRunT k useTag (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_doneT h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRunT k useTag (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (RunT.perm p (hr hz))
    have hN := nextT_complete h s rfl _ (List.Perm.refl _) F hF
    change !(nextT _ _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k useTag S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRunT k useTag (goal k) u ys → NatRunT k useTag (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k useTag S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRunT k useTag (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runT {k useTag u} (seed : Nat) (orig : List Nat)
    (h0 : NatRunT k useTag (goal k) u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all (moveOK k)) = true →
      NatRunT k useTag (goal k) u best →
      NatRunT k useTag (goal k) u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    unfold pickMin
    dsimp only
    split
    · exact pickMin_runT seed orig h0 rest _ _ hok.2 (applyMoves_runT ms hok.1 orig h0)
    · exact pickMin_runT seed orig h0 rest best bestH hok.2 hb

namespace Main
abbrev fG : BFn 9 := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 4 && x 8)

def cSub_0 : Fin 9 → Sum Bool (Fin 8) := (fun i : Fin 9 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inl false
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩
  | ⟨8, _⟩ => Sum.inr ⟨7, by omega⟩)

namespace Sub_0
abbrev fG : BFn 8 := fun y : Fin 8 → Bool => PEqualNP.Outside.L_meta_9167_aux.Main.fG (substIn PEqualNP.Outside.L_meta_9167_aux.Main.cSub_0 y)

def cSub : Fin 8 → Sum Bool (Fin 7) := (fun i : Fin 8 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨4, _⟩ => Sum.inl false
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩)

namespace Sub
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_9167_aux.Main.Sub_0.fG (substIn PEqualNP.Outside.L_meta_9167_aux.Main.Sub_0.cSub y)

def cSub_0 : Fin 7 → Sum Bool (Fin 5) := (fun i : Fin 7 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inl false
  | ⟨2, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inl false
  | ⟨6, _⟩ => Sum.inr ⟨4, by omega⟩)

namespace Sub_0
abbrev fG : BFn 5 := fun y : Fin 5 → Bool => PEqualNP.Outside.L_meta_9167_aux.Main.Sub_0.Sub.fG (substIn PEqualNP.Outside.L_meta_9167_aux.Main.Sub_0.Sub.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 6) (_ : SCleanL 5 gs)
    (_ : ∀ p, p < gs.length → 5 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 5 + p ∈ g.inputs)
    (_ : ∀ x, val gs 5 o x = fG x) :
    ∀ a, a < 5 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 2, 2, 4, 4, 3, 6, 3, 3, 6, 6, 12, 1, 16, 16, 8, 8, 17, 24, 17, 17, 24, 24, 12, 12, 5, 10, 18, 5, 20, 11, 22, 7, 19, 7, 14, 14, 9, 20, 18, 9, 10, 21, 26, 25, 19, 25, 28, 28, 13]

def xsG : List ℕ := [0x27527521a11a1, 0x2a9fcc0007e6, 0x3845db3800e58, 0x3db3845e58800, 0x1fcc2a87e6000]

theorem rowsG_len : rowsG.length = 50 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 5) => ((fun x : Fin 5 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 25 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 25 false (fG, false) = goal 25 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 25 zs &&& lo 25) ≠ lo 25 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 6, ¬ NatRunT 25 false (goal 25) s xsG) :
    ∀ s ≤ 6, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 25 false (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 6, ¬ NatRunT 25 false (goal 25) s xsG) :
    ¬ HasCircuitSize 5 fG 6 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 25 false (encT rowsG 25 false (fG, false)) s'
      (ws.map (encT rowsG 25 false)) :=
    RunT.map (encT rowsG 25 false)
      (fun a => encT_inv rowsG 25 rowsG_len false a)
      (fun a b => encT_and rowsG 25 rowsG_len false a b)
      (fun a b => encT_or rowsG 25 rowsG_len false a b)
      (fun a => encT_tag rowsG 25 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x5ef45c185567af1a
  | 6, 0 => 0x5567af1a
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x1ee8931ffc69fdb3845e58800e1176ce003961fcc2a87e60009d49d486846842a9fcc0007e6
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x25442c6885
  | 6, 0, 0 => 0x46885
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0

def idWidth : Nat := 3

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 50 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x1ffe000fff, 12)], [(0x810100408080, 1), (0x2000001, 2), (0x80000040000, 6), (0x820000410, 9), (0x1000000800, 10), (0x49400024a, 11)], [(0x100810080408, 1), (0x2000001000, 2), (0x24a000125, 13), (0x400000200, 14), (0x104000082, 15), (0x80000040, 18)], [(0x400044200022, 1), (0xc300006180, 2), (0x2000001, 3), (0x100000080000, 4), (0x40000020000, 7), (0x20000010, 8), (0x1000000800, 9)], [(0x44400022200, 1), (0x30000c180006, 2), (0x2000001000, 3), (0x100000080, 4), (0x200000100, 15), (0x2000001, 16), (0x40000020, 19)], [(0x1800000c, 10), (0xa00000500, 11), (0xc0000060, 12), (0x500000280, 13), (0x6000003, 14), (0x400000200000, 2), (0x4000002000, 3), (0x80000040000, 6), (0x10000008, 9), (0xc00000600, 10), (0x10a0000850, 11), (0x4000002, 13)], [(0x24a000125000, 1), (0x100200080100, 3), (0x2000001, 4), (0x8000004, 14), (0x100000080, 16), (0x40000020, 19), (0x400000200000, 2), (0x4000002000, 3), (0x80000040000, 6), (0x10000008, 9), (0xc00000600, 10), (0x10a0000850, 11), (0x4000002, 13)], [(0x24a000125, 1), (0x200100100080, 3), (0x2000001000, 4), (0x40000020000, 7), (0x1000000800, 8), (0x20000010, 10), (0x400000200000, 2), (0x4000002000, 3), (0x80000040000, 6), (0x10000008, 9), (0xc00000600, 10), (0x10a0000850, 11), (0x4000002, 13)], [(0x400000200, 2), (0x4000002, 3), (0x8000004, 11), (0x850000428, 13), (0x300000180, 14), (0x2000001, 15), (0x80000040, 18), (0x400000200000, 2), (0x4000002000, 3), (0x80000040000, 6), (0x10000008, 9), (0xc00000600, 10), (0x10a0000850, 11), (0x4000002, 13)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 25)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 25 false (goal 25) u ys) :
    NatRunT 25 false (goal 25) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 3 0 (NN s)

def poolG : List Nat := [19152412410410009, 19146900883137565, 12390414825843738, 12390403003147301, 19145807816058907]

def Z (s : Nat) := bar 25 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 25 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : NatRunT 25 false (goal 25) s xsG) : False := by
  have hmin : 4 ≤ s := by
    have hl := runT_len h
    change 5 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 5 fG 6 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 1) || (a == 5)

def perm_1 : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩

def cu_1 : Fin 7 → Sum Bool (Fin 5) := fun i => cSub_0 (perm_1 i)

theorem hperm_1 : ∀ y : Fin 5 → Bool, fG (substIn cu_1 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_1 : ∃ y y' : Fin 5 → Bool, fG (substIn cu_1 y) ≠ fG (substIn cu_1 y') := by decide +kernel

def perm_5 : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨5, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨1, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩

def cu_5 : Fin 7 → Sum Bool (Fin 5) := fun i => cSub_0 (perm_5 i)

theorem hperm_5 : ∀ y : Fin 5 → Bool, fG (substIn cu_5 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_5 : ∃ y y' : Fin 5 → Bool, fG (substIn cu_5 y) ≠ fG (substIn cu_5 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 7, ∃ y : Fin 7 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 8) (hcl : SCleanL 7 gs)
    (hnd : ∀ p, p < gs.length → 7 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 7 + p ∈ g.inputs)
    (hev : ∀ x, val gs 7 o x = fG x) :
    ∀ a, a < 7 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a ha hta
  have hne : a ≠ o := by
    intro ho
    obtain ⟨y, hy⟩ := hno_projG ⟨a, ha⟩
    apply hy
    rw [← hev y, ← ho]
    exact congrFun (val_input gs 7 ⟨a, ha⟩) y
  refine ⟨hne, ?_⟩
  interval_cases a
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
      · exact hop
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 4, 4, 8, 8, 7, 14, 37, 44, 7, 14, 37, 44, 7, 7, 14, 14, 26, 37, 37, 44, 44, 56, 5, 12, 6, 10, 36, 40, 5, 5, 12, 12, 24, 3, 6, 6, 10, 10, 33, 36, 36, 40, 40, 1, 64, 64, 16, 16, 67, 82, 97, 112, 67, 82, 97, 112, 67, 67, 82, 82, 26, 97, 97, 112, 112, 56, 65, 80, 66, 18, 96, 48, 65, 65, 80, 80, 24, 3, 66, 66, 18, 18, 33, 96, 96, 48, 48, 2, 32, 26, 56, 26, 56, 24, 3, 33, 9, 20, 68, 9, 72, 23, 78, 53, 108, 39, 46, 39, 46, 15, 71, 15, 30, 30, 45, 101, 45, 60, 60, 21, 76, 38, 42, 38, 42, 13, 69, 13, 28, 28, 11, 22, 70, 11, 74, 41, 52, 100, 41, 104, 17, 72, 68, 17, 20, 75, 86, 105, 116, 99, 114, 99, 114, 83, 71, 83, 90, 90, 113, 101, 113, 120, 120, 73, 84, 98, 50, 98, 50, 81, 69, 81, 88, 88, 19, 74, 70, 19, 22, 49, 104, 100, 49, 52, 34, 34, 27, 57, 58, 58, 25, 35, 35]

def xsG : List ℕ := [0x398949c139d552949c139d55380084608c6aa1084608c6aa1, 0x76e0f83c07fcc00f83c07fcc09507c0603e66007c0603e660, 0x14a0821082a8637d7ffffcc0000000000000319ebbdffe6, 0xf821601c601459cf6aef6ab27c00200420000c6395739558, 0xf99cf6aef6ab221601c601447cc639573955800200420000, 0x777f003cf83f01f003cf83f012af80187c1980f80187c1980, 0x637d7ffffcd4a0821082a800319ebbdffe600000000000]

theorem rowsG_len : rowsG.length = 194 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 97 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 97 true (fG, false) = goal 97 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 97 zs &&& lo 97) ≠ lo 97 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 8, ¬ NatRunT 97 true (goal 97) s xsG) :
    ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 97 true (goal 97) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 8, ¬ NatRunT 97 true (goal 97) s xsG) :
    ¬ HasCircuitSize 7 fG 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 97 true (encT rowsG 97 true (fG, false)) s'
      (ws.map (encT rowsG 97 true)) :=
    RunT.map (encT rowsG 97 true)
      (fun a => encT_inv rowsG 97 rowsG_len true a)
      (fun a b => encT_and rowsG 97 rowsG_len true a b)
      (fun a b => encT_or rowsG 97 rowsG_len true a b)
      (fun a => encT_tag rowsG 97 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 7 => 2
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 7, 0 => 0x3638dea610aadead
  | 8, 0 => 0x3638dea6
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x7312938273aaa52938273aaa700108c118d542108c118d543ddfc00f3e0fc07c00f3e0fc04abe0061f06603e0061f06603b707c1e03fe6007c1e03fe604a83e0301f33003e0301f3300676b63ec62aad6b63ec62aac7ff7b9f73955ef7b9f73955e1f339ed5ded56442c038c0288f98c72ae72ab0004008400003e08580718051673dabbdaac9f00080108000318e55ce55600031bebffffe6a50410841540018cf5defff3000000000000014a0821082a8637d7ffffcc0000000000000319ebbdffe6
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x3ead10fac6887
  | 8, 0, 0 => 0x1f56887
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 7 => 25
  | 8 => 25
  | _ => 0

def idWidth : Nat := 3

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 195 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x1ffffffffffe0000000000000fffffffffff, 44)], [(0x12a0000000000000000000000950000000000000000000000, 1), (0xc000cc00000c000cc0000000600066000006000660, 2), (0xf80007c0000f80007c0000007c0003e00007c0003e000, 5)], [(0x12a0000000000000000000000950000000000000000000000, 1), (0x1f0000f800000000000000000f80007c0000, 39), (0x30003300000000000000000018001980, 42), (0x7c300003e0000000000000003e180001f, 44), (0xc000cc0000000000000000006000660, 46), (0xf80007c000000000000000007c0003e000, 49)], [(0x11421000021001001544000008a10800010800800aa2, 1), (0x6300000000c000c018c0000031800000006000600c6000, 2), (0x10800000002000000000000008400000001, 3), (0x4008400000000000000000002004200000000000000, 4), (0x100000000000000000000000080000000000000000, 27), (0x100000000000000000000000080000000000000, 38), (0x40000000000000000000000020000000000000, 39), (0x10108000000020000000000008084000000010, 40), (0x4000400840000000000000002000200420000, 41), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x8420042001000040084000004210021000800020042000, 1), (0x10800000002000000000000008400000001, 2), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x108200420020000000000000084100210010, 41), (0x400840000000000000000000200420000, 42), (0xa512a212a9400000000000005289510954a, 43), (0x10000000000000000000000008000000, 69), (0x4000000000000000000000002000000, 70)], [(0x4008400084200420010000002004200042100210008, 1), (0x1080000000200000000000000840000000100000000000, 2), (0x1000000000000000000000000800000000000000000, 25), (0x400000000000000000000000200000000000000000, 26), (0x5289510954a00000000000002944a884aa5, 45), (0x100210000000000000000000080108000, 46), (0x21040084004000000000000010820042002, 47), (0x2000000000000000000000001000000, 70), (0x2000000000000000000000001000, 81), (0x800000000000000000000000400, 82), (0x200000000000000000000000100, 83), (0x80000000000000000000000040, 84)], [(0x21001001544001142100000010800800aa20008a108000, 1), (0xc018c0006300000000c00000600c600031800000006, 2), (0x1080000000200000000000000840000000100000000000, 3), (0x40084000000000000000000020042000, 4), (0x2000000000000000000000001000000000000000000, 24), (0x800000000000000000000000400000000000000000, 25), (0x80108000000000000000000040084000, 47), (0x10800000002000000000000008400000001, 48), (0x1000000000000000000000000800000, 71), (0x1000000000000000000000000800, 82), (0x400000000000000000000000200, 83), (0x100000000000000000000000080, 84), (0x40000000000000000000000020, 85)], [(0x20020000001000040000000010010000000800020000000, 1), (0x800000000000000442000000400000000000000221, 2), (0x2000000000000000000000001000000000, 3), (0x800004000000000008000000400002000000000004000, 4), (0x400002000000000004000000200001000000000002000, 6), (0x800000000000000000000000400000000, 7), (0x200000000000000000000000100000000000000000, 26), (0x200100000400000000000000100080000200000, 36), (0x800000000000000000000000400000, 37), (0x200a0000200000000000000010050000100000, 38), (0x80000000000000000000000040000000000000, 39), (0x8000220002220000000000004000110001110, 41), (0x400000000000000000000000200000000, 42), (0x10200001400000000000000008100000a, 43), (0x8000880000000000000000004000440, 45), (0x8000020000000000000000004000010000, 46), (0x40000000000000000000000020000, 47), (0x5000010000000000000000002800008000, 48), (0x10000000000000000000000008000000, 68), (0x4000000000000000000000002000000, 71)], [(0x20010804000000001000884010008402000000000800442, 1), (0x88c040c4000000000000000044602062000000, 2), (0xc00400000000000030442000600200000000000018221, 3), (0x4002000002000000000000002001000001000000000, 4), (0x1000001000000000000000000800000800000000, 6), (0x30000000000000000c000000180000000000000006000, 7), (0x800000000000000000000000400000000, 8), (0x400000000000000000000000200000000000000, 9), (0x100000000000000000000000080000000000000000, 27), (0x100000000000000000000000080000000000, 35), (0x800000000000000000000000400000, 36), (0x100000000000000000000000080000000000000, 37), (0x10000000000000000000000008000000000000, 39), (0x40000000000020000000000020000000000010, 40), (0x400000000000000000000000200000000, 41), (0x4000000000000000000000002000000000000, 42), (0x8000000000000000000000004000000000, 45), (0x40000000000000000000000020000, 46), (0x20000000000000000000000010000000, 67), (0x8000000000000000000000004000000, 70)], [(0xc600000001800000000000006300000000c, 42), (0x2a8528000000000000000000154294000, 43), (0x3003fc0000000000000000001801fe0, 44), (0x1402940000000000000000000a014a000, 45), (0x31800000006000000000000018c00000003, 46), (0x10000000000000000000000008000000, 69), (0x4000000000000000000000002000000, 70), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x20000100088400108040000010000080044200084020000, 1), (0x40c40000000000000088c000206200000000000000446, 2), (0x304420c004000000000000001822106002000000, 3), (0x200000000000040020000000100000000000020010000, 4), (0x100000000000000010000000080000000000000008000, 6), (0xc00003000000000000000000600001800000000, 7), (0x80000000000000000000000040000000000000000000, 8), (0x4000000000000000000000002000, 9), (0x2000000000000000000000001000000000000000000, 23), (0x800000000000000000000000400000000000000000, 26), (0x100000000000000000000000080000, 42), (0x10000000000000000000000008000000000, 43), (0x80000000000000000000000040000000, 47), (0x2000000000000000000000001, 48), (0x8000000000000000000000004000, 52), (0x800000000000000000000000400000000, 53), (0x1000000000000000000000000800000, 71), (0x1000000000000000000000000800, 81), (0x100000000000000000000000080, 83), (0x400000000000000000000000200, 84), (0x40000000000000000000000020, 86)], [(0x20004000000000200000010010002000000000100000008, 1), (0x44200008000000000000000022100004000000, 2), (0x200000000000000000000000100000000000000000000, 3), (0x800008000040000000000000400004000020000, 4), (0x400004000020000000000000200002000010000, 6), (0x80000000000000000000000040000000000000000000, 7), (0x1000000000000000000000000800000000000000000, 24), (0x400000000000000000000000200000000000000000, 27), (0x50000100000000000000000028000080000, 40), (0x200000000000000000000000100000, 41), (0x20000080000000000000000010000040000, 42), (0x10001100000000000000000008000880, 43), (0x8100000a000000000000000040800005, 45), (0x100000000000000000000000080000000, 46), (0x44000444000000000000000022000222, 47), (0x2800008000000000000000001400004000, 50), (0x10000000000000000000000008000, 51), (0x1000004000000000000000000800002000, 52), (0x2000000000000000000000001000000, 70), (0x2000000000000000000000001000, 80), (0x200000000000000000000000100, 82), (0x800000000000000000000000400, 83), (0x80000000000000000000000040, 85)], [(0x5289510954a00000000000002944a884aa5, 1), (0x8010800000040084000000004008400000020042000, 3), (0x1080000000200000000000000840000000100000000000, 4), (0x2000000000000000000000001000000000000000000, 24), (0x800000000000000000000000400000000000000000, 25), (0x100000000000000000000000080000000000000000, 27), (0x100000000000000000000000080000000000000, 38), (0x40000000000000000000000020000000000000, 39), (0x10000400840000000000000008000200420000, 40), (0x4000000000000000000000002000000000000, 41), (0x108000000020000000000000084000000010, 42), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x100210000000000000000000080108000, 2), (0x21000000004000000000000010800000002, 3), (0x42000000008000000000000021000000004, 43), (0x3c00000000000000000000001e000000, 44), (0x84201421550000000000000042100a10aa8, 45), (0xc018c0000000000000000000600c6000, 46), (0x10800000002000000000000008400000001, 47), (0x2000000000000000000000001000000, 70), (0x2000000000000000000000001000, 81), (0x800000000000000000000000400, 82), (0x200000000000000000000000100, 83), (0x80000000000000000000000040, 84), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x5288110954a000000000000029440884aa500000000000, 1), (0x4008400000080108000000002004200000040084000, 3), (0x10800000002000000000000008400000001, 4), (0x1000000000000000000000000800000000000000000, 25), (0x400000000000000000000000200000000000000000, 26), (0x1400000000000000000000000a000000, 45), (0x42000000008000000000000021000000004, 46), (0x40084000000000000000000020042000, 48), (0x1000000000000000000000000800000, 71), (0x1000000000000000000000000800, 82), (0x400000000000000000000000200, 83), (0x100000000000000000000000080, 84), (0x40000000000000000000000020, 85), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x2a0000000000000000000000150000000000000000000000, 1), (0x800000000000000000000000400000000000000000, 2), (0x800004000008000040000000400002000004000020000, 5), (0xc0000000000000000000000060000000000, 37), (0x500000000000000000000000280000, 38), (0x280000000000000000000000140000, 40), (0x30020000000000000000000018010000000, 41), (0x331800000000000000000000198c, 42), (0x280000000000000000000000140000000, 43), (0x3000000000000000000000001800000, 44), (0x1480000000000000000000000a4000000, 45), (0xcc6000000000000000000000663, 46), (0x6000000000000000000000003000000000, 47), (0x28000000000000000000000014000, 48), (0x1400000000000000000000000a000, 50), (0x1800000000000000000000000c00000000, 51), (0x10000000000000000000000008000000, 68), (0x4000000000000000000000002000000, 71), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x2080000000000008900088a010400000000000044800445, 1), (0x404088000000020000000000202044000000010000, 2), (0x8000000000044000440000004000000000022000220, 3), (0x205000010000000000000000102800008000, 4), (0x500003000000000000000000280001800000000000000, 5), (0x2800008000000000000000001400004000, 6), (0x800000000004000000000000400000000002000, 8), (0x80000000000000000000000040000000000000000000, 9), (0x2000000000000000000000001000000000000000000, 23), (0x800000000000000000000000400000000000000000, 26), (0x100000000000000000000000080000000000000000, 27), (0x800000000000000000000000400000, 35), (0x100100000000000000000000080080000000000, 37), (0x10000000000000000000000008000000000000, 39), (0x40000400000000000000000020000200000000, 40), (0x4000000000020000000000002000000000010, 42), (0x40000000000000000000000020000, 45), (0x8000000000000000000000004000000000, 47), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x20008100088a08000000000010004080044504000000000, 1), (0x2000000008040880000000001000000004020440, 2), (0x4000044000080000000000002000022000040000000, 3), (0x500001000000000000002000280000800000000000001, 4), (0x5000030000000000000000002800018000, 5), (0x280000800000000000000000140000400000000000000, 6), (0x400000000008000000000000200000000004000, 8), (0x800000000000000000000000400000000, 9), (0x1000000000000000000000000800000000000000000, 24), (0x400000000000000000000000200000000000000000, 27), (0x40000000000000000000000020000000000, 41), (0x10080000000000000000000008040000, 43), (0x8000000000000000000000004, 46), (0x4000000000000000000000002000000, 47), (0x40000000000000000000000020000000, 48), (0x2000000000000000000000001000000000, 51), (0x4000000000000000000000002000, 53), (0x1000000000000000000000000800000, 71), (0x1000000000000000000000000800, 81), (0x100000000000000000000000080, 83), (0x400000000000000000000000200, 84), (0x40000000000000000000000020, 86), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)], [(0x1020000000000000000000000810000000000000000000000, 1), (0x44008100000000000000000022004080000000, 2), (0x40004000000000000000000020002, 3), (0x280000c00000000000000000140000600000000000000, 5), (0x10000000000000000000000008000, 7), (0x1000000000000000000000000800000000, 8), (0x40000000000000000000000020000000000, 38), (0x80000400000000000000000040000200000, 40), (0x1800000000000000000000000c0000, 41), (0x10030000000000000000000008018000000, 42), (0x1108000000000000000000000884, 43), (0x201000010000000000000000100800008, 45), (0xcc000000000000000000000066000000, 46), (0x442000000000000000000000221, 47), (0x2000000000000000000000001000000000, 48), (0x4000020000000000000000002000010000, 50), (0xc000000000000000000000006000, 51), (0x800000000000000000000000400000000, 52), (0x2000000000000000000000001000000, 70), (0x2000000000000000000000001000, 80), (0x200000000000000000000000100, 82), (0x800000000000000000000000400, 83), (0x80000000000000000000000040, 85), (0x1400000000000000000000000a00000000000000000, 1), (0x10021000000000000000000008010800000000000000, 2), (0x2100000000400000000000001080000000200000000000, 3), (0x200000000000000000000000100000000000000000, 26), (0x200000000000000000000000100000000000000, 37), (0x80000000000000000000000040000000000000, 38), (0x20000000000000000000000010000000000000, 39), (0x8000000000000000000000004000000000000, 40), (0x84000000010000000000000042000000008, 41), (0x300630000000000000000000180318000, 42), (0x108402842aa0000000000000084201421550, 43), (0x21000000004000000000000010800000002, 45), (0x20000000000000000000000010000000, 68), (0x8000000000000000000000004000000, 69)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 97)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 97 true (goal 97) u ys) :
    NatRunT 97 true (goal 97) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 3 0 (NN s)

def poolG : List Nat := [55187840968004705, 19145802519774349, 55174611353045091, 55175697977672805, 19145848735763554]

def Z (s : Nat) := bar 97 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 97 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : NatRunT 97 true (goal 97) s xsG) : False := by
  have hmin : 6 ≤ s := by
    have hl := runT_len h
    change 7 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 7 fG 8 := mainG noRunFull

end Sub


theorem noCircuit : ¬ HasCircuitSize 8 fG 9 := by
  intro h
  have hsub := direct_f0_step fG cSub ⟨4, by omega⟩ rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 9 h
  exact Sub.noCircuit hsub
end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 3) || (a == 5)

def perm_3 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨8, by omega⟩

def cu_3 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 8 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

def perm_5 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨7, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨5, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨3, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨1, by omega⟩
  | ⟨8, _⟩ => ⟨8, by omega⟩

def cu_5 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_5 i)

theorem hperm_5 : ∀ y : Fin 8 → Bool, fG (substIn cu_5 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_5 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_5 y) ≠ fG (substIn cu_5 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 9, ∃ y : Fin 9 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 11) (hcl : SCleanL 9 gs)
    (hnd : ∀ p, p < gs.length → 9 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 9 + p ∈ g.inputs)
    (hev : ∀ x, val gs 9 o x = fG x) :
    ∀ a, a < 9 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a ha hta
  have hne : a ≠ o := by
    intro ho
    obtain ⟨y, hy⟩ := hno_projG ⟨a, ha⟩
    apply hy
    rw [← hev y, ← ho]
    exact congrFun (val_input gs 9 ⟨a, ha⟩) y
  refine ⟨hne, ?_⟩
  interval_cases a
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_5 ⟨5, by omega⟩ rfl hnc_u_5 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_5 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 4, 4, 16, 16, 45, 60, 15, 30, 165, 180, 15, 30, 165, 180, 15, 30, 165, 180, 45, 45, 60, 60, 45, 45, 60, 60, 120, 15, 15, 30, 30, 90, 165, 165, 180, 180, 240, 5, 20, 6, 18, 132, 144, 1, 256, 256, 64, 64, 297, 360, 267, 330, 417, 480, 267, 330, 417, 480, 267, 330, 417, 480, 297, 297, 360, 360, 297, 297, 360, 360, 120, 267, 267, 330, 330, 90, 417, 417, 480, 480, 240, 257, 320, 258, 66, 384, 192, 2, 128, 2, 128, 8, 32, 120, 90, 240, 90, 240, 90, 240, 120, 120, 10, 160, 10, 160, 40, 40, 80, 3, 129, 17, 68, 260, 17, 272, 109, 316, 47, 62, 173, 188, 79, 286, 229, 436, 143, 158, 167, 182, 47, 173, 62, 188, 61, 301, 61, 124, 124, 31, 271, 31, 94, 94, 181, 421, 181, 244, 244, 69, 276, 38, 50, 140, 152, 65, 272, 260, 65, 68, 313, 364, 299, 362, 425, 488, 283, 334, 433, 484, 395, 458, 419, 482, 299, 425, 362, 488, 361, 301, 361, 376, 376, 331, 271, 331, 346, 346, 481, 421, 481, 496, 496, 273, 324, 290, 98, 392, 200, 34, 136, 130, 130, 136, 34, 121, 122, 248, 91, 241, 218, 242, 122, 248, 42, 168, 138, 162, 42, 168, 81, 35, 137]

def xsG : List ℕ := [0xe0064004e739aaaa904e739aaaa9c00000046319aaaa1046319aaaa1, 0x4ebaad301f02f9980301f02f9980428a85301f0019980301f0019980, 0x84210050545ffffffffe6000000000000000005def7ffffe6, 0x19bebd2c01fff99fe0c01fff99fe01aead0001fff999e0001fff999e0, 0x207fc00718c002822abbdee55559207fc002108000000ab9ce655558, 0x15df5e133e0ffe67e033e0ffe67e01d756003e0ffe666003e0ffe6660, 0x207fc0abbdee555590718c002822207fc0ab9ce65555802108000000, 0x975d1ec3e0057e600c3e0057e60085150ac3e00066600c3e00066600, 0x5ffffffffe6084210050540000005def7ffffe600000000000]

theorem rowsG_len : rowsG.length = 224 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 9) => ((fun x : Fin 9 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 112 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 112 true (fG, false) = goal 112 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 112 zs &&& lo 112) ≠ lo 112 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 11, ¬ NatRunT 112 true (goal 112) s xsG) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 112 true (goal 112) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 11, ¬ NatRunT 112 true (goal 112) s xsG) :
    ¬ HasCircuitSize 9 fG 11 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 112 true (encT rowsG 112 true (fG, false)) s'
      (ws.map (encT rowsG 112 true)) :=
    RunT.map (encT rowsG 112 true)
      (fun a => encT_inv rowsG 112 rowsG_len true a)
      (fun a b => encT_and rowsG 112 rowsG_len true a b)
      (fun a b => encT_or rowsG 112 rowsG_len true a b)
      (fun a => encT_tag rowsG 112 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 6 => 1
  | 7 => 5
  | 8 => 12
  | 9 => 31
  | 10 => 14
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0x2985d777
  | 7, 0 => 0xb2d5aac89eeacd8043b5a14d3133dc76033c8199
  | 8, 0 => 0xe588b337c81bca11916747bf7c2b8a467a248dda57e445a73bf4fc163494d2922abec9d22996b8c026f872210afa5615
  | 9, 0 => 0xd9ef4096ba9844506ea8048562a565475f164f8b57e445a751ddbff94df26b8a4da8db523e4826e93b4580fa392702af3597ecf330a6e50929395c642605b44b242a78ba21e0d7a01f7def191eafc5751be01bc21ad6a7f01950d0200c0ca8c509056a83082c5cae075d03d00723fff303d7ec63027081b000e9f303
  | 10, 0 => 0x893ef3976bda0b1e62a565474da8db52445a3a3820c38de120253d741f7def19132c29c20ca249050a541a7d0723fff304be015503f4d117
  | 11, 0 => 0x1f7def19
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x5bbfef75def7bebace38c62bd711103fe055ce732aaac01084000000577d784cf83ff99f80cf83ff99f8075d5800f83ff999800f83ff99981c00c8009ce735555209ce735555380000008c6335554208c63355542207fc0abbdee555590718c002822207fc0ab9ce65555802108000000103fe0038c600141155def72aaac903fe00108400000055ce732aaac00000017ffffffff982108401415000000177bdfffff98000000000000000001084200a0a8bffffffffcc00000000000000000bbdefffffccdff9bff00007f8780f00007f87800000000000000000000000000000
  | 0, 1 => 0x6fffdff9ff83fffc079ff83fffc063cfc7f9ff803ffc079ff803ffc037fe7ffc003ffe1f83c003ffe1f806181000003fe001800003fe00181bffb7fe7c00ffcf01e7c00ffcf010a2a1587c000ccc0187c000ccc00dffbfff01ffff9fe0f01ffff9fe01aead0001fff999e0001fff999e04bac8f600002bc300600002bc300000000000000000000000000000013ae2b4c0000be0600c0000be06000000000000000000000000000001eebebd89ce7bf5d5389ce7bf5d5380000008c6335554208c633555424ebaad301f02f9980301f02f9980428a85301f0019980301f0019980
  | 0, 2 => 0x6ffefff9f07fff3f079f07fff3f00ebab001f07ff333001f07ff333013ae2b4e1084bf4751fffffffff980000000000000000177bdfffff98d14dc27ffff50f3fe7ffff50f3fffffffffffffffffffffffffffffe68a2e13c1ffa819ff3c1ffa819ff7aeaf53c1fff999ff3c1fff999ff6fc01ffc739ffebeeaa2108d55536fc01ffef7bffffffaa318cd5553a5d747b0f8015f98030f8015f980214542b0f8001998030f80019980337d7a5803fff33fc1803fff33fc035d5a0003fff333c0003fff333c0dffbfff01ffff9fe0f01ffff9fe05aead5301fff999e0301fff999e0
  | 0, 3 => 0x103fe0078c6003c3957def72bebd903fe00108400000055ce732aaac2c5154b3f83f4199ff3f83f4199fef5d5eb3f83ff999ff3f83ff999fcbffbda67c1fffcfc067c1fffcfc03aeac007c1ffcccc007c1ffcccc0fffffff7bdeffafaba0000000019fffffffffffffffffa21080000190ffcdffd8c632aaab7d8c632aaab1ffffffdce732aaaf7dce732aaaf00000003d6b401e19821084014150000000000000000000000000000137f7a5803fff33fc1c03fffb3fc035d5a0003fff333c0403fff333c0dffdfff3e0fffe7e0f3e0fffe7e09d756ac3e0ffe6660c3e0ffe6660
  | 0, 4 => 0x2e8041d0022a20001800001000000a8041c0002220001000000000081ff02bef7b95f5e41ef7a00a0ac81ff02ae73995556008420000001ffffff40000000033ef7bdff5f57ffffff44210000033ffffffffffe2004000fe0000601f0fe0000601fa5152acfe0006661fcfe0006661f030c060421083e82a2fffffffff3000000000000000002ef7bfffff338019017ffffffffbc339ce6bebf700000177bdfffff9c118c66aaa8400000009ce73555400084200000000000008c63355540000000000006ebeed30bf2af9989341f02fb9a0428a85301f0019980301f0019980
  | 0, 5 => 0x38c600141104000002828000000000000000000000000000000000002ef7b9555000000000000000000026319955500000000000000c3018000000f0000000000f000000000000000000000000000000005df5e13be0ffe77f037f8ffe6fe21d756003e0ffe666003e0ffe6660103fe055ffff2aaaeafffffffff3103fe055ce732aaac2fffffffff30000000200000141401c63000a0880000000000000000000000000001fbebe7ffc1ffccfffffc1ffccfff7aeaf59fc1ffcccff9fc1ffcccfeb77fdeebfdef7f759c7f8c57ee22a57fcaebfce677758c3f08066600
  | 0, 6 => 0x703fe057ffffffffc83fffcd5555f03fe057ffffffffc8339ccd5550800000000080004000407c0be660000000000000000000403c00666012eba3d97c42afeca9bffffffffcd0a2a1587c000ccc01bfdefffffcc207fc0fffffffffff0f5ad007876207fc0ffffffffffe02108000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x1440c20406
  | 7, 0, 0 => 0x535010308173c510338205c53440cc08171440c204b29c92070c60817
  | 8, 0, 0 => 0x14d2040d108183c561010308181522040ce08183c510344204a814d10344204a814810318204b81524040c204a81481035c204b815210344258a85452040c6081815410344204a84c548444204a8
  | 9, 0, 0 => 0x7251522040c646457941031910819164488103182064548810319108191522040c64428e6248810319184191528040c6442065c4c548810644291584840d10812a4548811f19108194c5792106442064548810375108197054881031910a524086c40c608191522040c64416a454881031990819
  | 9, 0, 1 => 0xf1524040c608191584902040c2064548810344204a91524081031820645a522040d108190052040c60812e0f1440c644206d915e612103442064550810319108191522040ec4420645488ac31910aa915e4901031820645a5e4840d108191682031919c206454889831910819
  | 10, 0, 0 => 0x4c5488103191081a15e488103191081a0054902040c6081900550810319108191522040c644206dacc5488103191081a1522040c6442072a0054881031910819171488103191081a3c5488103191081a152230103191081a01c1522040c644291522040c644206fa1522040c6442b81a
  | 11, 0, 0 => 0x54881031910819
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 40
  | 7 => 46
  | 8 => 52
  | 9 => 58
  | 10 => 64
  | 11 => 58
  | _ => 0

def idWidth : Nat := 6

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 225 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xfffffffffff00000000000000000fffffffffff, 44)], [(0x4aaa9500000280000000002800004aaa950000028000000000280000, 1), (0x30000019980300000199800000003000001998030000019980, 2), (0x1f0000000001f0000000000000001f0000000001f0000000, 5)], [(0x4aaa9500000000000000000000004aaa950000000000000000000000, 1), (0x3e000000000000000000000000003e00000000, 39), (0xc000006660000000000000000000c0000066600, 42), (0x5000000000000000000000000000500000, 43), (0xc00f80007f000000000000000000c00f80007f, 44), (0x2800000000000000000000000000280000, 45), (0x300000199800000000000000000030000019980, 46), (0x1f000000000000000000000000001f0000000, 49)], [(0x1084000008002108000000000000108400000800210800000, 1), (0x10000000000000000000000000001, 2), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000010840000100000000000000100001084000010, 41), (0x400021086000000000000000000040002108600000, 42), (0x100a884205554a00000000000000100a884205554a, 43), (0x40000000000000000000000000004000000000000, 44), (0x400000000000000000000000000040000000000, 69), (0x100000000000000000000000000010000000000, 70)], [(0x508420000000400002aaa2000000508420000000400002aaa2, 1), (0x6006319800000000000000000000600631980000, 2), (0x10000000000000000000000000001, 3), (0x210800000000000000000000000021080000000000000000, 4), (0x4000000000000000000000000000400000000000000000000, 27), (0x180000000000000000000000000018000000000000000, 38), (0x20000000000000000000000000002000000000000000, 39), (0x8000000000000100000000000000800000000000010, 40), (0x2000021080000000000000000000200002108000000, 41), (0x800000000000000000000000000080000000000000, 42), (0x200000000000000000000000000020000000000000, 43), (0x80000000000000000000000000008000000000000, 44), (0x20000000000000000000000000002000000000000, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0x210800000010840000080000000021080000001084000008, 1), (0x1000000000000000000000000000100000000000, 2), (0x40000000000000000000000000004000000000000000000000, 25), (0x10000000000000000000000000001000000000000000000000, 26), (0x5442102aaa5000000000000000005442102aaa5, 45), (0x8421800000000000000000000000842180000, 46), (0x2108000020000000000000000000210800002, 47), (0x80000000000000000000000000008000000000, 70), (0x6000000000000000000000000000600000, 80), (0x400000000000000000000000000040000, 82), (0x100000000000000000000000000010000, 83), (0x40000000000000000000000000004000, 84), (0x10000000000000000000000000001000, 85), (0x4000000000000000000000000000400, 86), (0x1000000000000000000000000000100, 87), (0x400000000000000000000000000040, 88)], [(0x400002aaa2508420000000000000400002aaa250842000000, 1), (0x631980000000000000060000000063198000000000000006, 2), (0x1000000000000000000000000000100000000000, 3), (0x2108000000000000000000000000210800000, 4), (0x80000000000000000000000000008000000000000000000000, 24), (0x20000000000000000000000000002000000000000000000000, 25), (0x4210000000000000000000000000421000000, 47), (0x10000000000000000000000000001, 48), (0x40000000000000000000000000004000000000, 71), (0x1800000000000000000000000000180000, 82), (0x200000000000000000000000000020000, 83), (0x80000000000000000000000000008000, 84), (0x20000000000000000000000000002000, 85), (0x8000000000000000000000000000800, 86), (0x2000000000000000000000000000200, 87), (0x800000000000000000000000000080, 88), (0x200000000000000000000000000020, 89)], [(0xa801520102200000040001111220a80152010220000004000111122, 1), (0x11106100018000000000000000001110610001800000, 2), (0x10000000000000c008888100000010000000000000c0088881, 3), (0x80800000000000000000000000008080000000000000000, 4), (0x40000000000000000000000000004000000000000000000, 6), (0x300000000000000000000000000030000000, 7), (0x10000000000000000000000000001000000000000000000, 9), (0x4000000000000000000000000000400000000000000000000, 27), (0x20000000000000000000000000002000000000, 36), (0x100000000000000000000000000010000000000000000, 37), (0x20000000000000000000000000002000000000000000, 38), (0x80000000000000000000000000008000000000000000, 39), (0x2000000000000100000000000000200000000000010, 40), (0x8000000080000000000000000000800000008000000, 41), (0x200000000000000000000000000020000000000000, 42), (0x800000000000000000000000000080000000000000, 43), (0xa000000000000000000000000000a000000000000, 45), (0x1000000000000000000000000000100000000, 46), (0x800000000000000000000000000080000000000, 67), (0x200000000000000000000000000020000000000, 70)], [(0xa801500004000008000008800000a80150000400000800000880000, 1), (0x20000000000000000088810000002000000000000000008881, 2), (0x100000000000200000000000000010000000000020000000, 4), (0x80000000000100000000000000008000000000010000000, 6), (0x8000000000000000000000000000800000000000000000000, 26), (0x400000000000000000000000000040000000000000000, 35), (0x10000000000000000000000000001000000000, 36), (0x240000020000000000000000000024000002000000000, 37), (0x8000000000000000000000000000800000000, 38), (0x4000000000000000000000000000400000000000000, 39), (0x10000000000000000000000000001000000000000000, 40), (0x400800044444100000000000000040080004444410, 41), (0x1000000080000000000000000000100000008000000, 42), (0x800220004a000000000000000000800220004a, 43), (0x140000000000000000000000000014000000000000, 44), (0x200000111000000000000000000020000011100, 45), (0x800000000000000000000000000080000000, 46), (0x1000000000000000000000000000100000000, 47), (0x400000000000000000000000000040000000, 48), (0x400000000000000000000000000040000000000, 68), (0x100000000000000000000000000010000000000, 71)], [(0xc000000000000000000000000000c, 42), (0xa14a500000000000000000000000a14a5000000, 43), (0xc0007fffe0000000000000000000c0007fffe0, 44), (0xa528000000000000000000000000a52800000, 45), (0x30000000000000000000000000003, 46), (0x400000000000000000000000000040000000000, 69), (0x100000000000000000000000000010000000000, 70), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0xa801504000111122201022000000a80150400011112220102200000, 1), (0x10001800000000000111060000001000180000000000011106, 2), (0xc008888110000000000000000000c008888110000000000, 3), (0x808000000000000000000000000080800000, 4), (0x400000000000000000000000000040000000, 6), (0x30000000000000000000000000003000000000000000000, 7), (0x100000000000000000000000000010000000, 9), (0x80000000000000000000000000008000000000000000000000, 23), (0x20000000000000000000000000002000000000000000000000, 26), (0x4000000000000000000000000000400000000, 42), (0x10000000000000000000000000001000000, 47), (0x10000000000000000000000000001, 48), (0x200000000000000000000000000020000000, 52), (0x40000000000000000000000000004000000000, 71), (0x1000000000000000000000000000100000, 81), (0x200000000000000000000000000020000, 82), (0x800000000000000000000000000080000, 83), (0x20000000000000000000000000002000, 84), (0x80000000000000000000000000008000, 85), (0x2000000000000000000000000000200, 86), (0x8000000000000000000000000000800, 87), (0xa000000000000000000000000000a0, 89)], [(0xa801500000880000000040000080a80150000088000000004000008, 1), (0x8881200000000000000000000000888120000000000, 2), (0x20000000001000000000000000002000000000100000000, 4), (0x10000000000800000000000000001000000000080000000, 6), (0x40000000000000000000000000004000000000000000000000, 24), (0x10000000000000000000000000001000000000000000000000, 27), (0x4000000000000000000000000000400000000, 40), (0x8000000000000000000000000000800000000, 41), (0x2000000000000000000000000000200000000, 42), (0x400000222000000000000000000040000022200, 43), (0x40011000250000000000000000004001100025, 45), (0x20000000000000000000000000002000000, 46), (0x100008888820000000000000000010000888882, 47), (0x200000000000000000000000000020000000, 50), (0x400000000000000000000000000040000000, 51), (0x100000000000000000000000000010000000, 52), (0x80000000000000000000000000008000000000, 70), (0x4000000000000000000000000000400000, 79), (0x2400000000000000000000000000240000, 81), (0x40000000000000000000000000004000, 83), (0x100000000000000000000000000010000, 84), (0x4000000000000000000000000000400, 85), (0x10000000000000000000000000001000, 86), (0x1400000000000000000000000000140, 88)], [(0xaaa9500000000000000000000000aaa950000000000000000000000, 1), (0x20000000000000000000000000002000000000000000000000, 2), (0x100000000001000000000000000010000000000100000000, 5), (0x14000000000000000000000000001400000000, 38), (0xa000000000000000000000000000a00000000, 40), (0x800000000000000000000000000080000000000, 41), (0x6660c000000000000000000000006660c, 42), (0x55000000000000000000000000005500000, 43), (0xc000000060000000000000000000c000000060, 44), (0x20002a800000000000000000000020002a80000, 45), (0x199830000000000000000000000019983, 46), (0xa000000000000000000000000000a0000000, 48), (0x500000000000000000000000000050000000, 50), (0x400000000000000000000000000040000000000, 68), (0x100000000000000000000000000010000000000, 71), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0x5442102aaa5000000000000000005442102aaa5, 1), (0x1800000000000000000000000000180000, 2), (0x421000000002108000000000000042100000000210800000, 3), (0x1000000000000000000000000000100000000000, 4), (0x80000000000000000000000000008000000000000000000000, 24), (0x20000000000000000000000000002000000000000000000000, 25), (0x4000000000000000000000000000400000000000000000000, 27), (0x180000000000000000000000000018000000000000000, 38), (0x20000000000000000000000000002000000000000000, 39), (0x8000021080000000000000000000800002108000000, 40), (0x2000000000000000000000000000200000000000000, 41), (0x800000000000100000000000000080000000000010, 42), (0x200000000000000000000000000020000000000000, 43), (0x80000000000000000000000000008000000000000, 44), (0x20000000000000000000000000002000000000000, 45), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0x8420000000000000000000000000842000000, 2), (0x20000000000000000000000000002, 3), (0x40000000000000000000000000004, 43), (0xf000000000000000000000000000f0000000000, 44), (0x508402aaa8000000000000000000508402aaa8, 45), (0x6319800000000000000000000000631980000, 46), (0x10000000000000000000000000001, 47), (0x80000000000000000000000000008000000000, 70), (0x6000000000000000000000000000600000, 80), (0x400000000000000000000000000040000, 82), (0x100000000000000000000000000010000, 83), (0x40000000000000000000000000004000, 84), (0x10000000000000000000000000001000, 85), (0x4000000000000000000000000000400, 86), (0x1000000000000000000000000000100, 87), (0x400000000000000000000000000040, 88), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0x442102aaa5000000000000000000442102aaa500000000000, 1), (0x180000000000000000000000000018000000000000000, 2), (0x210800000004210000000000000021080000000421000000, 3), (0x10000000000000000000000000001, 4), (0x40000000000000000000000000004000000000000000000000, 25), (0x10000000000000000000000000001000000000000000000000, 26), (0x500000000000000000000000000050000000000, 45), (0x40000000000000000000000000004, 46), (0x2108000000000000000000000000210800000, 48), (0x40000000000000000000000000004000000000, 71), (0x1800000000000000000000000000180000, 82), (0x200000000000000000000000000020000, 83), (0x80000000000000000000000000008000, 84), (0x20000000000000000000000000002000, 85), (0x8000000000000000000000000000800, 86), (0x2000000000000000000000000000200, 87), (0x800000000000000000000000000080, 88), (0x200000000000000000000000000020, 89), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0xa801500000200000240011111250a80150000020000024001111125, 1), (0x10100011100000800000000000001010001110000080000000, 2), (0x1000000100008888800000000000100000010000888880, 3), (0x1000400000000000000000000000100040000000, 4), (0xc000000000000000000000000000c000000000000000000, 5), (0x200000000000000000000000000020000000, 6), (0x20000000000100000000000000002000000000010000000, 8), (0x80000000000000000000000000008000000000000000000000, 23), (0x20000000000000000000000000002000000000000000000000, 26), (0x4000000000000000000000000000400000000000000000000, 27), (0x20000000000000000000000000002000000000, 35), (0x100000000000000000000000000010000000000000000, 37), (0x20000000000000000000000000002000000000000000, 38), (0x80000000000000000000000000008000000000000000, 39), (0x2000000080000000000000000000200000008000000, 40), (0x8000000000000000000000000000800000000000000, 41), (0x200000000000100000000000000020000000000010, 42), (0x800000000000000000000000000080000000000000, 43), (0xa000100000000000000000000000a000100000000, 45), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0x4a801500000080000000000000004a80150000008000000000000000, 1), (0x8880000020000000000000000000888000002000000, 2), (0x1000000020000000000000000000100000002, 3), (0x30000000000000000000000000003000000000000000000, 5), (0x400000000000000000000000000040000000, 7), (0x10000000000000000000000000001000000000, 40), (0x6000000000000000000000000000600000000, 41), (0xc000000000000000000000000000c0000000000, 42), (0x222040000000000000000000000022204, 43), (0x40041000280000000000000000004004100028, 45), (0x300018000000000000000000000030001800000, 46), (0x888810000000000000000000000088881, 47), (0x800000000000000000000000000080000000, 50), (0x300000000000000000000000000030000000, 51), (0x80000000000000000000000000008000000000, 70), (0x4000000000000000000000000000400000, 79), (0x2400000000000000000000000000240000, 81), (0x40000000000000000000000000004000, 83), (0x100000000000000000000000000010000, 84), (0x4000000000000000000000000000400, 85), (0x10000000000000000000000000001000, 86), (0x1400000000000000000000000000140, 88), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)], [(0xa801504001111125000002000000a80150400111112500000200000, 1), (0x80000000201000111000000000008000000020100011100, 2), (0x888880000010000000000000000088888000001000000, 3), (0x40000000000000000010000000004000000000000000001, 4), (0xc000000000000000000000000000c0000000, 5), (0x20000000000000000000000000002000000000000000000, 6), (0x10000000000200000000000000001000000000020000000, 8), (0x40000000000000000000000000004000000000000000000000, 24), (0x10000000000000000000000000001000000000000000000000, 27), (0x402000000000000000000000000040200000000, 43), (0x40000000000000000000000000004, 46), (0x100000000000000000000000000010000000000, 47), (0x8000000000000000000000000000800000, 48), (0x100000000000000000000000000010000000, 53), (0x40000000000000000000000000004000000000, 71), (0x1000000000000000000000000000100000, 81), (0x200000000000000000000000000020000, 82), (0x800000000000000000000000000080000, 83), (0x20000000000000000000000000002000, 84), (0x80000000000000000000000000008000, 85), (0x2000000000000000000000000000200, 86), (0x8000000000000000000000000000800, 87), (0xa000000000000000000000000000a0, 89), (0x50000000000000000000000000005000000000000000000000, 1), (0x842000000000000000000000000084200000000000000000, 2), (0x2000000000000000000000000000200000000000, 3), (0x8000000000000000000000000000800000000000000000000, 26), (0x600000000000000000000000000060000000000000000, 36), (0x40000000000000000000000000004000000000000000, 38), (0x10000000000000000000000000001000000000000000, 39), (0x4000000000000000000000000000400000000000000, 40), (0x1000000000000080000000000000100000000000008, 41), (0x400018c660000000000000000000400018c6600000, 42), (0x1000a108055550000000000000001000a108055550, 43), (0x40000000000000000000000000004000000000000, 44), (0x20000000000000000000000000002, 45), (0x800000000000000000000000000080000000000, 68), (0x200000000000000000000000000020000000000, 69)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 112 true (goal 112) u ys) :
    NatRunT 112 true (goal 112) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 6 0 (NN s)

def poolG : List Nat := [55198836100026480, 10140801322655946, 30405947331561610, 56324687644442806, 30404801603944604, 55174622106207368, 11268948551191664, 9014949714250864]

def Z (s : Nat) := bar 112 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_24 : ∀ i, 24 ≤ i → i < 31 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 24 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 31 → Z 9 i = true := (range_split z9_0 z9_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 14 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 14 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
  interval_cases s
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

def RootG (s : Nat) : Bool :=
  scr 112 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 8 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRunT 112 true (goal 112) s xsG) : False := by
  have hmin : 8 ≤ s := by
    have hl := runT_len h
    change 9 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 9 fG 11 := mainG noRunFull

end Main

end PEqualNP.Outside.L_meta_9167_aux

theorem PEqualNP.Outside.L_meta_9167 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 2 && x 8) || (x 4 && x 8)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_9167_aux.Main.noCircuit
  exact ⟨C, hfan, by omega, hev⟩
