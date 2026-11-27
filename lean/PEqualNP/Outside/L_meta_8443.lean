import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8443_aux

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
abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

def cSub_0 : Fin 8 → Sum Bool (Fin 7) := (fun i : Fin 8 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inl false
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩)

namespace Sub_0
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_8443_aux.Main.fG (substIn PEqualNP.Outside.L_meta_8443_aux.Main.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 10) (_ : SCleanL 7 gs)
    (_ : ∀ p, p < gs.length → 7 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 7 + p ∈ g.inputs)
    (_ : ∀ x, val gs 7 o x = fG x) :
    ∀ a, a < 7 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [2, 16, 1, 8, 1, 8, 2, 2, 25, 25, 38, 38, 66, 66, 25, 25, 28, 28, 28, 28, 38, 38, 9, 6, 34, 6, 34, 6, 34, 6, 34, 9, 9, 12, 12, 12, 12, 17, 24, 17, 24, 17, 24, 64, 16, 4, 32, 4, 32, 64, 64, 52, 52, 73, 73, 66, 66, 52, 52, 49, 49, 49, 49, 73, 73, 36, 65, 72, 65, 72, 65, 72, 65, 72, 36, 36, 33, 33, 33, 33, 20, 48, 20, 48, 20, 48, 66, 18, 18, 3, 10, 5, 40, 3, 10, 27, 89, 54, 102, 67, 74, 29, 57, 29, 60, 30, 92, 39, 46, 11, 7, 42, 14, 35, 22, 50, 70, 98, 13, 41, 13, 44, 14, 76, 19, 26, 21, 56, 81, 88, 80, 80, 68, 96, 5, 40, 68, 96, 116, 54, 89, 75, 70, 98, 53, 60, 53, 57, 113, 51, 77, 105, 100, 69, 104, 97, 76, 81, 88, 67, 74, 37, 44, 37, 41, 97, 35, 84, 112, 21, 56, 22, 50, 82]

def xsG : List ℕ := [0x27aaafd304151c268e9aa00f155f86002a18040c314, 0x38418020e800343ffa1ee7c00000018000007fb03cc1, 0xa8e13474d504f555fa608150c020618a01e2abf0c00, 0x41554ca3082afc1b7f1d40002a98060055f804fc328, 0x3f80603f1c0ff00c07e381bf00007e1817e0000fc302, 0x157e0dbf8ea082aa9946102afc027e19400055300c00, 0x21a1ffd0f73f0830041d004003fd81e6080000003000]

theorem rowsG_len : rowsG.length = 174 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 87 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 87 false (fG, false) = goal 87 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 87 zs &&& lo 87) ≠ lo 87 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 87 false (goal 87) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 87 false (goal 87) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 87 false (goal 87) s xsG) :
    ¬ HasCircuitSize 7 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 87 false (encT rowsG 87 false (fG, false)) s'
      (ws.map (encT rowsG 87 false)) :=
    RunT.map (encT rowsG 87 false)
      (fun a => encT_inv rowsG 87 rowsG_len false a)
      (fun a b => encT_and rowsG 87 rowsG_len false a b)
      (fun a b => encT_or rowsG 87 rowsG_len false a b)
      (fun a => encT_tag rowsG 87 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 6 => 52
  | 7 => 406
  | 8 => 361
  | 9 => 23
  | 10 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0xcfc91d40c05c19cc8f51b6ca8746bb7775655953686dea105f53d92f5b3b127a5b225b7058dabee157cfe6f155ae7d1951313af54da241fb4a0031c24962b5d64843046643d35ec8421baee73d0deb383adbf741379a0f6e2e28df752d985ede2b0085102a2baca829ec87a62906ab1c262bf0c623974a00237c15e5219ed564211c0aeb211474761f9a9bfd1c86c5131bb47ba21b1cd69918d044a1177f439c1750f1c51695fb0b1675a55f137bdd101241cb96121f5f190f5941bb09b9155d0938b21202fd755d010eea8b00937e1c
  | 7, 0 => 0x8c0606008bdab8208a46d01086c58cc086ba4330843842c07fef32a07d00c8d07119a3f06debde006c6b7ee068cf885064534be05d3e70105d0ad8c05824558058220cf056a5383053ac48c0535848f0505eec304ec0d9b04a3940104a1202404696f2b044cbcf704402de803de3cb303bdf38603b9697503973b280388bce70362e2780345d4dc033d8c9e0323cbdf02f743ba02f130e002e7f09702cebc7902cd9e8d02c56df402c24098023535bd0233cd200220f8240212205e01f5b8c001b36638018444600171102f016f847a015f95ab014040800133da54012cfe7b00e28a5800b3736c00a08914009d1490005c910a0052a46f0035ee1e00224117
  | 7, 1 => 0x17bc0d991765cd301707928816a284b915da2c3615c3cca61545d5811543aacb1523dcda14d9d1341486a50c14683eb5143dd63713ca918b13a858c2138523a41304bcbc1236a7e3120fcd6411ae19081171042f1143eb861105312c1103d08710df5ad110c3849e108804a9107477fe104451b4100ad20b0fe137200fd9e1160f8bd3a70f6fded90f0c91600eba442e0e70a85e0e67583e0de6f1560dd48be00dbd7d610d0396d80cc3157c0c9b43320ba1add40b91292c0b82a8d30b77fc110b6507ba0b3a61040b1eec950b1553e80aed06a50a6d6d8e0a4810950a1653e10a032f0509d6a26009c6791009a6e239096f06cf0911264a08cf157c08c8bc66
  | 7, 2 => 0x25fe74b525fb2fe225e6135225ddc4f725dae53c25d38377257ac8fa25531c8f246c9431242eeacc231949d922dafdb12231f8c92215d8a021be3eac21af8c9e216932322131251d20f729b6206988a4201668911fe921bc1fb763201fb08fd01fa064011f70381a1f67c13c1f3028e81e524dd51e2b39681e2721191e0e90cb1e0bbf101df231371df14f4a1d85b16a1d4d7a6c1d3d5d4a1cf31afc1ce28b3d1cb7d7de1cab29f71c4e75aa1c363e371c2728c11b84abfe1b64509c1ae2650a1ac0fb811aaf9a8d1a8edd4b1a3096b61a1673ca19b02fce19925815197aa7c51908203a1901bb5e1849f33f1821ed9f1810222217de1d6b17d080a217c2f7e4
  | 7, 3 => 0x3afef2a63aba44e23a7b284a3a79b2d53a7732463a52e1a439e6b5083987c33a397c9421393c252e39212e5a38d42f8e38377e5b37c928cd37498dea372b423936baf404367012c935f9b89c35284d9834fb42c834f86caa34f7a32e34f6596734cf3e1c3484413833b79ba5333438603308135b32f7b783328878ae327e15a9326027af31cecaad31b962c530b16fb030527410304952fd2fa0f5092f3659bc2f2de41c2ea5aa9f2e0eaff22ddcc6962d5db26c2d3bc5522cb130fb2c3125502bbe58f22af114fd2a14673329f61e1a29956d4028d4e7c1288f427628775017285736b627d2f6a327b2c8312783f19a273653eb26d8c3f326a37b1f2625fe84
  | 7, 4 => 0x5c495d425c2045345b1b5d4e5b03cc705ad7c4915a95d16b59660274591bb8c557d6b27357508a8b5718bd5756980a91563d06d7561b117855bd42ea54e57a7554caf66954616b9752644c5852592e4650b74b5c50a2944e4f19544c4ed9c7aa4d969c1e4d8e3c1e4bfb3bc04ab145bc4a2a42cd49aa38f64853259448330ea24782c79c46c0b00246ba5292469450d84647ade2453ac54244cc29d743c6c551433abce542f3032542dce3f242bee7a141d23f2641c073a9412df44f410f918b40e0f85f40c4ce2940bc165440930d98404601fa3f9e35923f0f2a4e3ee0e7223ea82f793e72a1603e50d4003d8997093c9167603c740a153c360fdf3b4af3ff
  | 7, 5 => 0x9f76cd859dddf2ba9cbef9e09b9ebf619812034595e6d71594e154ce94dd9e6a92341d188fc67fbb8ca794b38c002a0c8b93d7e48b67e67c8b2ce4a58a6484688879141487e8c06b86d6b8af859bf7078588ed358412c8be82ca5e2b8153ccaf8133c10c80df3540804e670b7f597f857d56489e784dd5b4773506f67476d5177435a409730ce1ee71269c1b705ab94a703535ee701d4e1a6ca9e7a66bd997c369afe13a698730706975eb62680ab6cb67edb1ec6729ee8c6723929166fe7ba5659786496565e7f96558d54264593a276392e14063842a0c61ae7b8d61372e0d607e7b7a605487c8604d8a855fedcc5d5ebb279e5dc1d6395db7fa2d5d5af5de
  | 7, 6 => 0xf9368f87ee519c29eb9d1969d8613e52d738155dd52ca589d1fd0863cbc8c14ccb4abd7fc4a27af4baa1aa79b827fb80b59ec4d6b3f7d37bac75188aa83536e8a627709da5d49107a4bbf4d3a3c18431a26e2535a04a71cb
  | 8, 0 => 0xd4254890d288b100cb343050c7cde4d0c505f550bfc77650b91292c0b7a9e780b527c8f0b3cfa720b38eab80b1553e80abc938a0a9a2a7a0a65218a0a55d3830a3fe4aa0a0bfca409d9d1ee09ceda7009cafd1e09ae5ec1098b95bc09028cb408ec7acc08d8abf008bb176508b157ad086c58cc07e3c3a007c2a8d9076d7b24072840700703ded506d3bec306b077940691ab0b06548c0305d3e70105b6179b05a80ae00583f628052b82a604dda65504b7870204a3940104a0774e047aa086046d4ce00435f6f6042e274b0385a8230334b2da0326da9b02cd9e8d02ad916d02555f7d01df113401d187f1017d24ab01713958011d3407004dffe500153d79
  | 8, 1 => 0x1bd4c7ac1bae77351b2763eb1b0aeaaa1aaf9a8d1a77f82d1a754d6a1a53f2021a4e48c01a192d5919f5f2b718ad95c3183877c717f3efe117f0d12e17a08ce01786b70c1763e31616fafbd116eed72116cacfff16cace0916c0fd7516bbacb3166c3693162384d715b4c792153443a31520ee4515064be014f62a8114c4bced14a0875d1475c3991469f8651453b8d613f24a8e13df1e6d13a9045b139e0b52138523a4130c3c021304bcbc12a9333e11c259c511ae3dfc11a69cac117bd8e81069bf7910560eee100ad20b1008e4150fe1e35d0fda0ff70fcab0ee0f5bcdf90f41ae540f1e6fd80ed8a61c0eb33c510e53c39a0e32d5690dc3ae4f0d4e7ee7
  | 8, 2 => 0x3534d78b3525ae3a34c86342347535cf328878ae321c02593161c33a3153f114306dec0c304d3f462fbe8e162f3659bc2f0d59692efba73f2e67d8892df731882dde91da2dd9b30c2d8e73c82d1dce8c2cdff05f2c9477932ad615702a69501428e9a4dc28e5e81928d4e7c128bda5e2287750172851fff12800b231279fee5326022b4825d383772575274b255d4cf625531c8f2539061123f506fe23d47b2723c3e8fd23c2d47d2394379a2288dc622200648221d33a8d217ffd9a215096b420d8804020c9cfd8206e579b1ff21f611fc6edfd1f1f2bb21df249c61dce439b1dc4cba71daf9e3d1da993d71d6650411d4ddcb31d3df4e41cb7d7de1c626af3
  | 8, 3 => 0x597636235902b95658f2d30558365248579bb31a5705547a5660437a5558fadd5500322750ed779d50b74b5c506d10b5506ceebc4f8371634d7326044c21b8054a90f36149aa38f6491a971848f7707848da77a1489bb886480b6f6d4716a1c846c395a245fd575345c5561745703d3844e976e044d11f6143adf77342f4536642e3f84a410f918b410b4927402a63a640061b6c3fcf439d3f38c1e43e6801f23e637a303d80b20e3d14a5bd3d004b263cf96faf3c416e8a3bb06c943b9aa9bb3b4af3ff3b2a7fef3b20a8e13a7d67a63a732be9397a202739698da039253187379bb149371a3e48367916a836646b63364f19b53636273535d07a633582e828
  | 8, 4 => 0x862ffcaf859bf70783a2665080a8fa5b7f597f857f49fa697e230a627d68968d7d61adda7d0927107cc9b1087c64ee9a7ad55daf79825e8574e503ad74d5f2d874658e956f6340a16ef56c2e6ee2d9b96ddedffd6d57027f6cb45b146ca9e7a66b72d5576aac5e8669ea12ed69d2f6e5695cb48368a499c568177fc5678cd4a7676ea5406729ee8c6727a3de66ead1f765e262ea65978649656dae9f64f330fe6452c7dc63f6b77a63974671631cdcad62f955ed626ef76f61372e0d6122c319607e7b7a604d8a855fff6b3c5f7426345f6ce4b55f547a055e82f6855ddb5c985db397595ced714b5cc408c45c71c8255bac94275b45d04b5a32701b5a0a937f
  | 8, 5 => 0xee519c29ed5228d2e9c6b307e18983e1dffa429ddcaa251dd8613e52c4cae098c2e920e9bde01a2bbd85e0cdbc996a0cb6560c59b58f801fb3f7d37bb0ec7008af42b9b4ac57f8a7ac4dd1dbaa1d77d2a5d49107a12f0ce49da66dd89d6811d89a161a5799c3d9d49844b181978a4b379513a1fd93c0a6bb935627e092341d18921727cb90f5113b90db7bdf8fb0cd478e972ea08c367bae8b91d3da8b67e67c8ab16d66
  | 9, 0 => 0xdcaa251dd8613e52978a4b37676ea540631cdcad607e7b7a5cc408c45bac9427583652485705547a40061b6c3f38c1e43c416e8a3b9aa9bb3b4af3ff36646b63306dec0c28d4e7c123d47b272288dc621ff21f610e53c39a08b157ad
  | 10, 0 => 0x28d4e7c1
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x55f836fe3a820aaa651840abf009f865000154c03000455d4ea3082bfc3fff9f60002a98060055f804fc3288687ff43dcfc20c0107401000ff6079820000000c0038418020e800343ffa1ee7c00000018000007fb03cc1fe0580fcf03fd036dfcf16fc0001f8605f80003f0c08a8e13474d504f555fa608150c020618a01e2abf0c0009eaabf4c1054709a3a6a803c557e1800a8601030c505340d9a86a082a09144100000000000000000000000
  | 0, 1 => 0xd37fc9bde67e2a6a756c41abfffffffd200154c0f0023db552dc77e59f26cf4aa40f2a879860aa18040f3140beaeff5d5456749b3b6a803c557e1800a8601030c523ebfff5f77f59726cbdaa4003fd81e6080000003000ff2b89fcf13fc539bfaeaefc0001f8605f80003f0c0841554ca3082afc1b7f1d40002a98060055f804fc328e92e0997a101d5ffeafbbf00000006000001fec0f307f80603f1c0ff00c07e381bf00007e1817e0000fc302
  | 0, 2 => 0xf655d3e8f23eff36dfcf56000aa60180157e013f0ca23abffd5f77f49704cbd084003fd81e60800000030002bfaeffdf5457f5dffbea857f55ff9e28afeabff3c535ffffffffbf8aba9d5f106affffffff480055303c00e58636c3b880d0ffe87b9f00000006000001fec0f30437aaffdb66151e268edaa00f155f86002a18040c31445ad65d6f888b5acbadf10abfaaff9e5157f55ff3ca14d013684590b89aa444f7aaf000780157e1d540c3ff
  | 0, 3 => 0xff0780fff03fd0ffffff9ffc0001fe605f81feffff0f9a1fff0ff3f383c061f81c003fd81e6080000003000f05553a8e20aff36dfcf56000aa60180157e013f0ca065fd6ef30c2ffc3fff9fe0002a98060055f804fc3285dfa3ffebb834fabe7bae8abf009f865000154c03003d758dbaeea0b6bffb5ef7c00000018000007fb03cc114d5776ada8abf86dfd750000aa60180157e013f0ca3dfe6dbf9eafb2ae9f4791aafc027e19400055300c00
  | 0, 4 => 0xfe5192fc723fca325f8e46fc0001f8605f80003f0c0957f5dffbea2afebbff7d42afeabfe79455fd57fcf28f15753abe20affffffffdf000aa60780157fffffffa557f0dbfaea0a6abbb56d42afc027e19400055300c00e9eeabf7e105d7ffebffbf03c557e7800a87ffc3ff5557e8dbfaea092aaf94eb22afc027e19400055300c0057f87fff3ec22aea751840abf009f865000154c030007c1e01ff40fc433fdfd667f00007f9817e07fbfffc3
  | 0, 5 => 0xe9eaabf4e105c739abaeae03c557e1800a8601030c539c1e030fc0f343ffe1fe7c00000018000007fb03cc1e787ffc3fcfcf0fff87f9f000ff607982001fec0f307fc1e03f3c0ff40ffffbe7bf00007e1817e0000fc302692d5394e1096039304caefffaaff9e7ca81fec0335d77e0fff8ee0c3ead9e6182afc027e19400055300c00187d5b3cc30bbf07ffc770000aa60180157e013f0ca3c5584aae880b6bffb5ef7c00000018000007fb03cc1
  | 0, 6 => 0x7fc07be30fc337ff1b8060ffc001e0078079fe3c0001704a742bee1d368f1afba2a0d57867942a1d570cf14a3ed62f50478b25c39411757caa1e61af578aa3cc3ad7fe1fffcff0cbfadde6182afc027e19400055300c001a7d5f3dd74bbf47ffd770000aa60180157e013f0ca19e07ff01f3f3c0ffe03e78003fd806608007fb00cc196d7ff6bdefe2ac2557441000ff6079820000000c003a8e13674d507f5d5fa689950c020618a01e2abf0c00
  | 0, 7 => 0x9655d368d23ebf06dfc750000aa60180157e013f0ca3b8e73775d5f7f5d5fa789950c020618a01e2abf0c002b3a4d9db5417d5dfebaa854300818628078aafc3003ffaeaff3c4ff1ce6febabbff155fe7817e1804fc316fe39cdfd757ffd757f9e26fc3009f862dff8aaff3c0bfc0e03f3c0ff00e6feba3bf00007e1817e0000fc302d7f9b6fe7abe0aaa751c40abf009f865000154c03002b8e73575d5f4f555fa708150c020618a01e2abf0c00
  | 0, 8 => 0x3ef87f7f3fc33fd77f986054300818628078aafc300261f800fe0c0c3f001fc187ffc027f99f7ff804ff33e14d4366a9a829a86cd53500000000000000000000002bafffd7ff7f4f755fbf08550fff87fea81e2abf3c00e3064d83b440f0fff87b9f00000006000001fec0f30427baafd304175c3faf9ee00f155f86002a18040c31411ab2c2b4dca80c93fb6a903f558061fb501feffff57fa1ffffff3ff83c07ff81ff03fdfffe1fe0000ff302
  | 0, 9 => 0x1054122882029a06cd4350000000000000000000000370b464582eee168c8b05dea02a801875d40550030ebfed1b6fe7abfcab25f9e46fc0001f8605f80003f0c0a00fe1073c0f3200391fe7c00fff87fe1fe18070ffff3a785f3d37433f577f986054300818628078aafc30021de601014cf07c3fc017e00fc020001e01ffff00cfd8787ffc3dcfc60c9b07689000ff6079820000000c002afe6d8092af72a69ea59195fc02000157e0553fcf02
  | 0, 10 => 0x797800bc2303df3fef8bfefff009f867dfffffff3ffe1807350551f08100405000000000000000000000000ae01805c703d00101e8c0054000018600000003c0003571ecb8b2afb0aaa059f7eaf3fdf9e75fe1d540f3ff0a384d1d15413d457e902000000000000078003c000027a8ac5204041c268a82a00f15580600001804000141efdff7cdfffbf06dfc770fffffff9fffffe013f0cf841454ca10828bc005e1100002a98060055f804fc328
  | 0, 11 => 0x9eaabf4c105570deba6a803c557e1800a8601030c5026aaa753041514268a9aa00f155f86002a18040c31401fe7f038fc03fcfe071f903fffe079fa07fffc0f3f65b5ffdaf7bfaff1b7fdd44003fd81e60d5f804ff32800055300c0082000104400000aa6018000000000000026aaa750041514248a82a00f154780002a000000014aa07c901c57df5559ae7bf540ff6079afffeab3fcffee9574ca308fffc5b7f1d59502a9806017ff804fc32a
  | 0, 12 => 0x8685ff435cfc20c0105401000ff6079820000000c000e9f57cf7dd2efd5fff7dc150eab8678a55faaffcf281050532802023f065f804000000000000078003c000387f9fe0ebf03ffffa1effc0ffff81e7e81ffff03cfd01060003800010cfe0719900000006000001fec0f3061b1ffd8f73f09f024fd804003fd81e608018040f30019fffbfcc30fff0fffe7f803cff7e1801ffe013f0cf0200203d1001500000e180000000780002a00000c300
  | 0, 13 => 0xe60180c0703cc030180e060000000000000000000003f84603f1c0ff20c17e381bf00007e1817e0000fc3028687ff43dcfc20c0907601000ff6079820000000c001e5e026f08c0f7cffbe2ffbffc027e19f7ffffffcffffffdf7fefabfffbeffdf56fffaaff9e55fff55ff3ca8414048a00808280914010000000000000000000000010d7fb68c20ebf06dfe750000ff60180157e013f0ca3ffa68bf1c0ff08e0fe381bff0007e1817e0000fc302
  | 0, 14 => 0x8280914010105012280200000000000000000000003f84707f1c0fff4d17e381bf00007e1817fe000fc3020087fb40c00c2000106400000ff601800000000000029a1ffd0ff3f0834061f004003fd81e60800000030001cf9b27c4bbf0f00078460fffffff9fffffe013f0cfbf80737f5d1ff81c07e781bf00007e1817e0000fc302ffe9b6fe78bfc2b83f9e06ffc001f8605f80003f0c08a8e13674d505f555fa688150c020618a01e2abf0c00
  | 0, 15 => 0xefaabed73df540f92038affff559fe7fea81fec0f35f80000200800300c0202818000000000000000000000d5ffb6fefabecaaae57fdfabfffffffd7f8755c3fffd5700cb882a080aa8040102af000780140005500000010541328c2029f06cfc7500000060180000601030c03beaab35cf7d503e480e2bfffd567f9ffaa07fb03cd7fe81b6fe78bfc0b01f9e06fc0001f8605f80003f0c0bf8a627f1c4ff14c4fe389bf00007e1817e0000fc302
  | 1, 0 => 0xfe0180fc703fd0345f8e06fc0001f8605f80003f0c0800154c030022c01b611c40002a98060000000000000fe39c9fc713ffd357f8e26fc0001f8605ff8003f0c0bd0544028aaea62d931255ff0eaa079ffd5e7fbf3ceb10555329c20abf46dfd750000aa60180157e013f0ca3d855502cfbeae3d971655ff0eaa079ffd5e7fbf3ceb19fabbfcc3074f0be7a6e803c557e1800a8601030c535f1ecb8b6afb0aaa459f7eaf3fdf9e75fe1d540f3ff
  | 1, 1 => 0x1ef9ff7c5fff2f00178460fffffff9fffffe013f0cfbd7e0dbf8ea0b2ae9b4691aafc027e19400055300c0010555228020aba065d4150000aa000001578003c00a3f80603f5c0ff01c07e781bf00007e1817e0000fc302ff6980fc713fc739bf8eaeffc001f8605f86013f0c5808013404510081004040000000000000000000000000a284d15154125413290200000000000000000000003d006038180fb00c024381aa0000780017e00000c302
  | 1, 2 => 0x2a00001c300100101e880054000018600000003c0002380603d140f500004e180000000780002a00000c300e1060983a000d0ffe87b9f00000006000001fec0f3060018000e0000030001c00400000018000000000300055f832fe2a820aaa650840abf009f865000154c030023fbfffdf77f59f26cfdaa40f3fdf9e60aa18040f31409eaabf4c105470be3a6a803c557e1800a8601030c52881f000711f3c152619e7d503fd81e6bfffaacff3ff
  | 1, 3 => 0xe116008ba000d8ffec7b9f00000006000001fec0f304bae1fd7cf704f755fa608150c020618a01e2abf0c003a7c5f3db743bf57ffdb7054300818628078aafc3003a418025e800743ffabee7c00000018000007fb03cc112555f29d64abf46dfd750000aa60180157e013f0ca1ace1367cd504f7fdfa608150c020618a01e7fbf0c008687ff43dcfcb0c6d87711000ff6079820000000c000001000020002401b210c40000000000000000000000
  | 1, 4 => 0x6b384d9d3541fd7ffe9bbe54300818628079fefc330407f8c80a2e007e3f8187e40ffff81e7e81ffff03cfd8681ff435cfc20c010140000000000000000000000001200d9086200020000400000000000000000000000019efbbf4c30fc70ba3e7f803cff7e1801f8601030cf3acf9367ed507f7fffbeefd50c020798a01e7fbf3cc1200000012000105568180000000000000000aac030038418060e800357ffabee7c00000018000007fb03cc1
  | 1, 5 => 0xfefdff7f7fffbff65fdd77fffffffffffffffffffffe27aaafd304151c268e9aa00f155f86002a18040c3147ff87fff3fc33fff7f9860fff009f8678079fefc300020e03470c40434059a608000c020618000000300c00efaeacd7bdf5d0ffe87bbffff559fe7fea81fec0f35f8408020c800103e480e23c00000018000007fb03cc155f837fe3a820faa679840abf009f865000154c03002a81f240795f7d557ebfefd503fd81e6bfffaaffffff
  | 1, 6 => 0x455320c008270093c600000aa60180000601030c03571ecb8b2afb4abb259f7eaf3fdf9e75fe1d540f3ff0038041c300008006418000030081860000000c03000535ffdab6a3afe1b7fdd40003fd8060055f804fc32880060003800090c6c87311000000060000000000c003b8060351c0f700c06a381bf00007e1817e0000fc302fe55d3fcf23fff36dfcf56fc0aa7f9e05ffe013f0ca8a8f13476d506f55ffb6cc150c020618a01e2abf0c00
  | 1, 7 => 0x19febbfcc307df0fefe7f803c557e1800a8601030c5027aa8bd304151c268e9aa00f155f86002a18040c314fff8b6fe3ab74aba651846fff009f8654a8154c0300847fdfcaf3f2aff3fffdfe40ffff81e7ed5ffffffffd0054530082003f06c04150000aa60180007e010000a157e0dbfaea082aab946902afc027e19400055300c002a284d15354135557a982000000000000000aac03002001e000300f30002019e7c003fd81e61fe18040f3ff
  | 1, 8 => 0x1fffff7fdfff3fcff7f5f9fffffffffffffffffffffeafbfafd715f7dd76ef9efd5f3fdf9e6bfffaacff3ff08028900c105450182a6a800055601800a8601030c500a0bbd075110810040d0000015580600000000000008687f643dcfc20c0107401000ff6079820000000c00027bfefd30437dc3fef9ee00f3fdf86002a18040c31461060083a000d0ffe87b9f00000006000001fec0f307f80603f1c0fd00c05e301bf00007e1817e0000fc302
  | 1, 9 => 0x14203a0c0004709a3a6880000060180000601030c0007f9fe0e3f01ff3f81cfe40ffff81e7e81ffff03cfd092a89f4c1054509a3a6a8000001e0000a8000030c03bebfb75ff7f7d7f6ebfeffffffffffffffffffffffff5fe36ffba82daffed7bdfabf009fe650001fec0f307f80603f3c0ff00c27e381bf00007e1817e0000fc3029effff7fdfff2fc017f461fffffffffffffe013fccf81a07fd0173f08000401000003fd8066080000000000
  | 1, 10 => 0x96a00b481014709a3a2a803c001e0000a8601030c5027aeafd304351c26ce9aa00f155f86002a18040c31469280094210140392008aefff009f867ca81fec0335d57e0dbf8ea092aa9946902afc027e19400055300c0010555028020abf06dfc350000aa00000157e013f0ca0584550207be8a000500103f0eaa061ffd5e000f002a0102008080004009a022880000000000000000000002a01e000304f754562b9efd503fd81e6bfffaacff3ff
  | 1, 11 => 0x860554031cf820c0105001000aa0061820000000c00065e000f00c0c7c3f9e07e3ffc027e19f7ffffffcffffffabeff3ff74afb6538effff559fe7fea81fec0f35d16a09358e20002a0806002afc027e19400055300c0041000082200000aa6018000000000000000154c03000a8013474d10481407a60015000006180000000f00001a55db28c77fbf06dfc770540ff6019afffe013f0cf81a01fd0c73008300404000000000000000000000000
  | 1, 12 => 0x1050002802029f06cf83500000000000157e013f0ca027a28bd1001508208e18000f000780002a00000c30015f8367e1a820a8a651040abf009f865000154c03000aaebbd77d514f555faf08150d578678a01e2abf0c00797c00bca303df3fefcbfefff009f867dfffffff3ffff81f27f7d5ffd5d67fbefff03fdfffebfffaacff3ffaa018000403dc0101a860654000000005f80003f0c0bda5ffd2ffbfae3d971f55ff0fff87fffd5e7fbf3ceb
  | 1, 13 => 0x92a099481014509a2a2a80000000000000000000002171ecb8b22f10a22059a240f3fdf9e60aa18040f314e14603a3e000d7ffebff9f00000607800007ffc3ff06bae7fd7df7f4f755fa708150c020618a01e2abf0c00abffff03cffdffdffaf7ff57fffe079fffffffffffffffe6dbf9eaff2ae9fe791bffc027e1957e0553fcf02d5d7b2eacabecaaac567dfabcff7e79d7f875503cffde5f54ef38c2ffcffff3ffbffeabfe79f7ffffffcfff
  | 1, 14 => 0x1aa2c030dc000c92030a903f558061fa001fec0f35477eafffb6e1d3e2f9edba00f155f86002a18040c3148681b64258bc0080101400000000000000000000000008157c0751208100415000002a9806000000000000010010028400a80001f860000000000001500003f0c027be7fdf17ffcbc005e1183ffffffe7fffff804fc33ef60180fc703ec0301d0e06a80001f86000000000000127aaafd384151ca68ebaa00f155f86002a18040c314
  | 1, 15 => 0x8feffbf4d13d6709b3e6a803cff7e1800a8601030c521a1fff0f73f1830041d804003fd81e60800000030008febabf4d13d4709b3a6a803c557e1800a8601030c5005e000000c007c3f8007e00fc020001e01ffff00cfd86018040503c00001004000000000000000000000003c855002499eae1d971255ff0eaa079ffd5e7fbf3ceb8a07c900c57de50092e7bf540ff6079afffe013fcffca8e33575d514f555fa708150c020618a01e2abf0c00
  | 2, 0 => 0x2a384d1f35413dd57e982054300818628078aafc3003f85f742ffffff7df7bfffff0fff87ffffffffffffff96d5f76adabebf86dfd750000aa60180157e013f0ca177eafffbee1d3eaf9efba2afd57fe7942a1d570cf1401e822f40000020821000003c001e000000000000001d7e0dbfcea086bfdb46102afc027e1940007fb00c0014f8367e1a820a80051040abf009f8650000000000039e19ff0ef303c3ffe1ee7c00000018000007fb03cc1
  | 2, 1 => 0x400320c00007008386000000060180000601030c00a8a02470c4041444fa20815000006180000000f000055f836fe3a821aae6d1840abf009f865000154c0300218174d0340f08000411000002a9806000000000000054f8367e3a820aa2451840abf009f865000154c03001c051502cbb0ae3d931655ff0eaa079ffd5e7fbf3ceb16d5ff68defebf06dfc750000ff60198357e013f0ca0a0a0245484045555aa608000000000000002ab00c00
  | 2, 2 => 0x51f836be2a820aaa651840abf009f865000154c03001ffe7fff1fffffcfffe3ffbffffffe7fffffffffcfff0010410800003d045e800000000000000078003c0003a81f260795f7d5d66bbefd503fd81e6bfffaacff3ff18fffb7cc30fbf07ffe770000ff60180157e013f0ca027bfefd304359c26cf9aa00f3fdf86002a18040c314fe5180fc723fdf36df8f56fc0001f8605ffe013f0ca83fabffdf77159f26cedaa00f155f86002a18040c314
  | 2, 3 => 0xf5d7b2eaeabedabecd6fdffffffffffffffffffffffc4b5ffda7593afd1b7fdd40003fd8060055f804fc328fe0180fc703fc0325f8e06fc0001f8605f80003f0c08a01924061507d5562b8efd503fd81e6bfffaacff3ff01867f038cc030cfe07199000ff607982001fec0f307501440082aea028801055ea02a801875d40550030eb1878003c03030f00078060fff009f867dffe013f0cfb9a1fff0ff3f3c3db61fc5c003fd81e6080000003000
  | 2, 4 => 0x11fe7f2b8fc23fcfe571f903fffe079fa07fffc0f3f7fbe7fff1ffffbcc07e399bffffffe7fffff804fc33e1e01807c503f0000178400fc0001f8605f80003f0c08084134245100f5117a4000000000000001e000f00003a384d3d35433d557f982054300818628078aafc300027aaafd304171c26ae9aa00f155f86002a18040c314fe0780fff03fc0f01ffe07fc0001fe605f80003fcc08020aad0300100000009000001558060000000000000
  | 2, 5 => 0xae87ff5ffcfd20d01efc01540ff61ff82000003cc003d855502efbeae3db716d5ff0eaa079ffd5e7fbf3cebdffffffedfffefaa97e7ffffffffffffffff553fcffff9e603f1ccff3cc07e399bffc027e19f7ff804fc33efe018008703fc0301e8e06fc000018605f80003f0c0bd7e8dbfaea0b2aefb4eb3aafc027e19400055300c001054532882023f06c54150000aa60180007e010000a1c54002a0880b68fb342f7bffc027e19f7ffffffcfff
  | 2, 6 => 0xc582a0c208b440a800208fabc551e61d6a815400c35d57f0dbfaea082aa9956102afc027e19400055300c0001ee3e038fc002cba071f903fffe079fa007ffc0f3f467f9fcfe3f0cff3f9fc7e7fffffffffffffffffffff01d676038ec03acec071d903fffe079fa07fffc0f3f407f9fc2e3f00ff3ffbc7e40ffff81e7e81fffff3cfde18622c3a000d0ffe87b9f00000006000001fec0f30441556ca3082afc1b7f1d40002a98060055f804fc328
  | 2, 7 => 0x89eeabf7c10547c9a3f6a903c557e7800a860103cc5007a08fd300001c228e18000f001f86000018040c3000000804040040000000400000000000000000000000008e13474d100a101d0600000c020618000000300c00e0040003200090f648591700000006000001fec0f307fffffffffffffffffffffffffffffffffffffffffffffc7fbe3cffff7ff9be7ffffcff7e79fffffff3fcffe181e010f40f0030041d004000000180000000003000
  | 2, 8 => 0x2a10411c30013d145e880054000018600078003c0001f7e0dbf8ee0f7effbe6ffbffc027e19f7ffffffcfff280000000101d5158a83be5400000002dffeab3f0ffcaff9fc7eff04ff7ffbe7e55ffff87ffe81fffff3cfd41020082a00040abe03a880000000000000154c03003f80603f5c0ff41d5fe781bf00007e1817e02abfcf0201f836020a800a8a60104003f0080005000154c03003d7fddfffea2bffffffff7eafeabfff9455fffffffe9
  | 2, 9 => 0x87effff7dcfc22c831740103cff7e79820000000c00027a0afd004041c248e00800f000780000000000000011fd73fcc20abf0effc75003caa7e180157e013f0ca00000000000000009000000000000000000000000000ae87ff43ddfdf5d59af7bf540ff6079afffeab3fcffc00000070c0000000102000000000618000000000000000000000000000000000000000000000000000000038018020e800303c021e81c000000180000000003000
  | 2, 10 => 0xffffb6fffabfdaffffffdffff009fe655f81feffff0fffeab3fcffdf7fffbeefffffd567f9fffffffffffff2a38041c300108107e98005430081860000000fc3003fd5f4fffc8ffffffffff7ff02a9fff817ffffffffeb87ffff43dffc3fcff075f903fffe079fa07fffc0f3f70418020e800003a981e004000000180000055303c0049eaabf6e10547abe3bea803c557e1800a8755c33c51f80003f0c00c00c07e2003f00007e180000000f0000
  | 2, 11 => 0xd5d7f3eacabeffaedfe7dfabcff7e79d7fff553fcfffd9555caffbeaffdb7f7d5ff0eab87fffd5fffffffeb01000080000000082000000000000000000000000003bffbff5effd5ffff81e7ffffffffffffabffff03cffeb07c983e57df5fffaffbf540ff6079afffffffffffc0219fc0e3300830001c004003fd81e608000000300001c2a2e0c004420881268803c557e1800a8601030c53c00402a1802b00c07e38180000000000540000fc300
  | 2, 12 => 0x96800b401014709a382a803c001e0000a8601030c5104e01278c00022a990600000c020618000055300c0001eaabf4c004020821240003c557e180000000000001e00002f0800f00c03e281bf00007e1817e0000fc3022a38cdfd75457d557f9e20543009f8628af8aaff3c03a41a03df801743ffaffe7c00000798002a07fb0ffc1f9fffbffe30fffffffffff03cff7e7801ffffffffff777beefdb2eff1eae8f9ffeaf3fdf9e75fe1d540f3ff
  | 2, 13 => 0x10055328c00aa0001fc600000aa601801500003f0c021a0ab10c73d0030000c00400154018608000000300010155008020ab8065c4150000aa000001578003c00a23a1fffdf73f583004fd804003fdf9e60aa00000f300f7d7f6ebfefefafedd7fdffffffffffffffffffffffd45e002f0880828a9942102afc027e19400055300c00fe4183fcf03fc7309f8e06fc0007f9e05f86013f0c0bfeaeb3fdf7ff03e4fefabfffd567f9fffe07fbfffd7
  | 2, 14 => 0x1855d3fcc20fff06dfc750000aa7e1801ffe013f0ca008000000400000004000000000000000000000000003a01003c700b80101f8e0054000018601500003f0c0021a02cd304041c068e188000001806000018040c3007b784dbd3743ff7fff9bfefff009f867dfffffff3fff5006038100fb008004181aa0000780017e00000c3027ffd7fffffcbbfffffdf70fffaaff9e7957fffff3ca3f9f77ff7ddfffddfff7ddbf0eabfe78b7ffaaffcf2a
  | 2, 15 => 0xf7d7ffebfefeffffffffdf000ff60798357fffffffa427fbffdf3f15ff3f8fdfe40fffff9e7eabffff0fffdf6010008303a80301c0806fc000018605500003c000bffffeff3ccfffcffffbffbff3fdfe7817ff804fc33e0002000080000000002000000000000000000000000000000c03000000000010000000180600000000000003ef9ff7d7fff3f557f9c60fffffff9fffffeabff3cfafbfffdfffffeff5ffffdc550fff87fead5faaffff28
  | 3, 0 => 0xfdffb2feebbfdfbfefeffffffffffffffffffffffffd50405028ea082289106102a0c020619400055300c00f97e00bfa303dfffeffbfffff009fe67dffffffffffd84000200800340ffa02e7800000000000007fb00cc1e10000822000c0ba681a060000000000000154c03001500003f0c0080080142002a00007e18000000000000001454030ec038c6405151003aa8061fa079fec0f3a7841d4e0f8023c3ffe1fe7c002a981e000007fb03cc1
  | 3, 1 => 0x8000000001e800000000000000000003c000177e2dbf9ea1d2aa99e7902afc027e1942a05530cf00fffe7fffbfc3fffffffbfffff009fe678079fefcf305500403f1c02a00807e3802a00007e180540000fc30009aaa8d4010540092020a803c551e0000a800000005145404aa888082aa9946100000000000000055300c0010050028c00a9006dfc71000000000001500003f0c0041144883082a080a051d40002a9806005418040c328
  | 3, 2 => 0x400220000002000100000000000000000000000003fe1ffffff3ffc3fffffe7ff03fdfffe1fe07fbfffc300000400100000000010000000000000000000000001e7f9fefebf0fffffbfeffffffffffffffffffffffff86bfff5ffcfc28c0747c01003ffe1ff8200000c0f003d71ecb8faafb4bffa5ff7eaf3fdf9e75fe1fff0ffff00f87f000fc02f0000006003fffe019fa07e010000f041f55cf3c82afc1bff7d4000eab8678055f807fcf28
  | 3, 3 => 0x2000000000000000000000000000000000000000000008000014000100000280000000000000000000000003ffbefbdfffff0bee85fffffffffffffffe1fff0ffff
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x800a070100414c000f8780e02008758000c020200e020e300018040406c040a60001434080100432c000281030020085d80016048200e15053000281304008240a60001408080880802c00020200e10008298000f0202004010530001c040401c040a60001412080383414c000601016070102980005048200e020330000a040180802006
  | 6, 0, 1 => 0x1408071c0043ac00028106e080082980005020206c020530006a0502020040a60001408081a00466c000401c040119029800310200c0e0200b0003e05038c05e0a6000145c07010042ec2d028b00e0200829c0004158200e0200b0000a04040a82a2960001450271300802c0002894062401005800230282044020330000a0904084020a6
  | 6, 0, 2 => 0xc408081312c02c000201c044a0082980023248e80e020530000a0424008020a6000c408082380414c00230200e02008298000502020040122b00088430401c1a0a60001408080110800c0020814080701005800401701c04011fb0000a04038f8021760008c0a08038f40cc0002824783b0382980005048e80e020530003c041c808020a6
  | 6, 0, 3 => 0x1380a040401c14c00028100e381782980031021340401053000980502020020a6
  | 7, 0, 0 => 0x1500a041e01c1460700014080803808be0a700014080803808bc0a700174b80403808025b700014080803808b40a7001640a0404008b001700024ae0803808020a7001100808038041456700014083b03954020a7001500a090401c020a70001408080380414537000140808130080200700014080803808a40a700014084d010041400700014a208038080250700014080812008024f7
  | 7, 0, 1 => 0x140808039c0020a700010ae6803808020a7001500a0403804146f700014086e03808020a7001b4080803808020a7001642c0404008020a700010d80803808020a700014086b04008026a70001408080380802697001500a043401c020a70019c080803808020a700124083a03808020a700010ae3c03808146070001408080399802657001900a6303808020a7001880a040401c04617
  | 7, 0, 2 => 0x7cb20501004147e7001f40a04041f0020a700014080803808027b7001e80a043c81c0401700014123c0401c040a7000140878038541477700014087603808020a7001700808038080275700150b8040401c025b7001d0080803808020a700014e60803808020a700014120803808c20a700010ae0701004146f700014087210808020a700014087103808020a700014083a11008020a7
  | 7, 0, 3 => 0x14088c03808020a700014088b03808020a700110087203804148a70001408080380414897001640a04040085e0a7001500a0403a20020a700014088703808020a7001700808038080286700014088503808020a7002100a040401c040a70001408080380802837001e80a040408404017002080a040401c044f700014080803809020a7002000a040401c020a7001fc0a040401c04017
  | 7, 0, 4 => 0x152a0803808020a7001640a0404008840a7001e90405478200e027000b5280803808020a7001740a040380802297000151e0803808240a700014080849808020a7000c4080803808c2017002480a040401c0469700014080803809220a7002400a0404008020a7000500808010041400700014127803808020a7000151e0847008020a7001e80a040181c04017002080a040401c048d7
  | 7, 0, 5 => 0x1e892040401c0401700288b2050400414a1700014083c1c808020a700015400803808020a7000153e0803808020a700010ae080380802297001500a040401c02297000151e0803a78020a700014080803a74020a700015380803808020a700014080810808029b7000151e0803a68020a7002644a08038080298700014083b03a5c020a700014083c0380814967001e888040401c028a7
  | 7, 0, 6 => 0x150b20502020020a700014083901004147e700014080854808020a700110080803805368a700014084d03808020a7001e8ba042b81c04017002a00a0404008020a700010ae0803a9c020a7001e80a040408804017001e8a85d028100e017002980a0403808020a70001010070100414a570001450080100414a4700164ba0502008020a7001500a040401d460a7001740a040380802067
  | 7, 0, 7 => 0xb5660803808020a700014080812008840a70001408b203808020a70001408780380802297000140808110f4020a7000c408b10401c040170005008080100432a47000151e080380802697001740a0403ac0020a7002bc46050401c040a7001240808038f4020a7000140808038095c0a7001e8a8042b8200e0170001408ad04005580a7002ac0aaa0401c0401700164085704008020a7
  | 7, 0, 8 => 0x2e00a04040056a0a7000140808038c0020a700014080803808c2b7700010ae2703808020a7001e80a280401c04017001500a041381c020a70001408b11c808020a700014083c1d81c1477700014080847008021d7002d80a040401c020a7000151e0803809020a7001e83c040401c04017001e80a045682002b570001408080380802b47002083e0503808147e700014083a0380814777
  | 7, 0, 9 => 0x30c080803808020a700014080803809840a700015820803808020a70001408c003808020a7000140808038097e4f7000140808038097c0a70001408bd04008020a7002f00a040380802bb7000140808038e0020a7001e828040400802a470001408085d008020a7001740a0412008020a7000140808038e0023f70001408080380414b970008c0a041d01c040a7000151e080380414897
  | 7, 0, 10 => 0x3380a0403808020a70001408080380814cd7003300a04040980401700010ae08038081a0a70001408080100400987001500a040401c1a0a70032c0a04040080219700010ae0812008020a70001408080c008020a70001408ca03808020a700324100701005900a7001500a0404090020a70031c3e0503808020a7003180a040400814c570024808080380814c47000c4080803809020a7
  | 7, 0, 11 => 0x1000a04038e0020a7001651e5704008020a700014080803809ac0a700011aa0803808025b70001408086a008020a70020808570401c040a700150b20547820020a700208a805020200e0a7001640a1304008020a70001408080380802d37000145c08038e0020a700015a4080380814d17003400a0404008020a700014340801004140070020944050401c14a1700014080803808c2cf7
  | 7, 0, 12 => 0x3880a0401384020a700381be040401c040a7000140808038f414777000c408081301c0401700011bc0803808020a700014080803808020a7003740a0404370040170032c0a080100414db700014080813009026a700014083b03b68020a700014500803808024f700014080803809b2017001e80a041d01c04017000c408080392c020a70011008080380414d8700010ae0803809ae0a7
  | 7, 0, 13 => 0x10ae7903808020a7001640a0404268020a7001e80a043901c04017003a40a040401c020a7001e90459028101002700011d0080380802e77001640a0404008240a7000145c0803808020a7000151e08038e0020a7000145c0803808023f7002080a043c01c040a700014083c03809cc0a700014080872808020a700248080803b90040a700011c60803808020a700014083a038f4020a7
  | 7, 0, 14 => 0x2080a130401c040a70001408ad0401c14ef700010ae0303808020a700110ba0403804148a70001408084f004146a7003b80a040401c020a700015da040401c0461700014080803bb0020a700208ba054781c040a7003ac0a0475008020a700010ae0810808020a700014340803808020a7001640a0404278020a7000b5280701004146f700014860803808020a70008c0a08038080cd17
  | 7, 0, 15 => 0x140808013d814007000151e0803808023f7001700a040401d600170010008070100414f57001640a0404008026970017008080380802f47000151eb10380802f37001e80a040401c7a01700015e40803808020a700174920403808020a7002880a0404084020a700014080778808020a7000144a0812008020a700208a805478200e0a70007c3c0701004147e700014080803809e00a7
  | 7, 1, 0 => 0x500a0404278020a700170080801004b6007003f8080803808020a7002080a0404238040a700014080803809fa3f71681010070100414d88000100e027e00414fb7000151e080380814ef70001412080380814d17003e80a040401c040a7003e40a0404008020a7001500a0404088020a700014080803be0020a7003dc0a040380802f370015092040401c020a7000151e0803808020a7
  | 7, 1, 1 => 0x14081801004146f7001500a280401c020a7002080a250401c04987002080a0404408040a7001640a040412c020a700010aead040056a0a7001503c040401c020a7001740a2803808020a7001640a041da5c020a700014080880808020a700016000803808020a7001645a9404008020a7001743c0403808020a7001740a04568056a0a700014080803809fe0a7000c4080803808020a7
  | 7, 1, 2 => 0x1408ea04008024f7001640a04040e0020a7002080a040401c14897001640a04040c0020a700014080701004146f700014080803808021c7001e80a04040a804017001005c0803808020a70001408080380803097002880a08038041508700014080803c1c020a7004180a0404410040a7002651e0803808020a700014080803854147770001408080380803057001e80a040441005037
  | 7, 1, 3 => 0x1740a040380a240a7000151e08038541477700010af1103808020a700014082c03808020a70001408080380a200a700078083b03808020a700010ae0803808c30f700014083b03c38020a7001700a040181c0401700014080886808020a7000145c0701004146f700170080803808030c700014080885808020a7004280a040401c040a700014080744008020a70010008390100414fb7
  | 7, 1, 4 => 0x14080803ac0020a70001408ad0401c02297000b62c0803808020a7001711e0803808025b7000c4080813008026a7001740a040399803157002080a040400814007001e8a805020200e017001640a0404008020a7004500a0404008020a70001408080380802067001640a0404008023f70001408080380803137001e80a04040e404017000151e0803808021d700014080803809460a7
  | 7, 1, 5 => 0x47c0a040401c020a700014080803808031e700014091d03808020a700100080701004146f7004700a0404008020a70046c0a0403808020a700014080812008020a7001740a0403808024f7004680a040401c14777000145c0701004147e700252320803808020a700460080803808020a700010ae0803808029b700014082703808020a70001408088b808020a700010ae080399803157
  | 7, 1, 6 => 0x12500803808020a7001640a0434008020a7001640a041e0081460700110080803804148a70049c0a0403808020a7000164d2503808020a70001408080399803247001640a04040541477700014080803c8c020a70007cae0701004147e7001740a04038085e0a700014087903808020a70001408080380a440a7004845a0803808020a700248080803808d320700264080803ac0020a7
  | 7, 1, 7 => 0x4bc0a041d81c020a7001751e5703808020a7004b80a040401c040a70007c0a8e01004147e7001111e0803804148a7001e8b25d0281004017004b544050401c020a700014092c03808020a70001408ad040056a0a7000140876039980315700014092b03808020a700014080895008020a7511705a0803808020a800174085703808020a7001740a04038080329700014860810808020a7
  | 7, 1, 8 => 0x4dc0a040401c031570001408081c8e0020a70001408089b008020a7004d40a0403808020a7001745a9403808020a7004d00a0403808020a7004cc0a0403808020a70001408080399803157000c4500803808020a7001e9045d028100e027001740a0447008020a70010008070100414fb7000791e0803808020a7004c80a0403808020a700016620803808020a70001408080380803307
  | 7, 1, 9 => 0x1740a0403854147770023cae0803808020a70001408080392d020a7001740a0403808020a7004e40a0456820020a7000b6700803808020a7
  | 8, 0, 0 => 0x1640a04040092e01054000ba050201c05410082a000cb1681410070100415000a0014080803808020a8004fc0a040401c04010540000a130401c0401052920000002810100701004d2e0002811d00803808020a800014080803808033e0540002805022b410020082a00005020200e020082a7b00002810100701006780a8001640a042b82004010540010405024ec10070102a0013a41014080803808150000281010220100414d18
  | 8, 0, 1 => 0x32c0a250401c04010540000a04040900e020082a00004a315c1007010041500002810100701514020a8001740a0403808020a79c0010405022b410070102a000000281010070120414e00a2014080803808020a800014080803808020aa1c0000a04a10200e020082a00005020200e02009a9310000281010070100414c48001e88805020200e0200c0000005021d80e0200829c005902810100200829b70006e9e80a040401c04018
  | 8, 0, 2 => 0x52c0a040401c040105400008570401c0401053ce0008202a3c100701004150003d0140808038080320800014080803808020aa540000a13020200e020082a0005402810100700829e70002e814080701004154980001408760401c0401054000f405020204c07010060000502520100701004150000a014080803808020a8000000a040401c020a44b8000a8f1d8200e020082a0005d028111e0701004150000281010070151c020a8
  | 8, 0, 3 => 0x1409520401c04010540000a040401c0401052ee00005020200e02a8804150000215c10070100415498001740a04038540401054000a805020200e0105526000000281076074b80414e0002810115003808020a80053c0a040401c0401054000088f2b8200e020082a0005d02811d4070100415000000b5280803808020a7001500a04478200e010540000a040401c0401a702a00005020200e02a68041500002810100701004154c8
  | 8, 0, 4 => 0x1408080380aaa01054000f405020200e0200bee000002c9740a040100414e000281011020100414a18005500a040401c04010540000a041d8200e970082a000042b8200e150100415000028101007010bc147e8000151e0803808020a35400088040401c04010522a00005020200e020082a490000215dd40803808020a8000b40a040401c0401054000a805023a810070082a0015302810100701004150002c8151e0803808020a8
  | 8, 0, 5 => 0x1500a040401c0303054000a805020200e010543e000542e814080701004150002c9740a0404008020a800014080803b900401054000ba05ad0100e020082a0005402810100700d6415000028101007010041558800000b2042b8200401053802ae05020200e020082a000002a1640a040400414e002e814080701184020a800014080803a78020a524002ac05020200e020082a0005d028100e0200c0c150002e814080701004150f8
  | 8, 0, 6 => 0x5780a040401c0401054000a8540281010070082a0005d028100e0200828fd0004101408080380814db8001500a041e0200e010540000a040401c040105576000050281010070100415000410140808038092e0a800014083a03808020a68c00008570401c04610082a0015c028101007010041500051014080803854020a800010ae0803808030305400062040401c0401051aa000042b8200e020082a1f000ad9640a0404008020a8
  | 8, 0, 7 => 0x14087603808020a8ac0000a040401ec6020082a0001402a3c1007010041500002810102103808020a8000000a040401c6001053800ba050201c04010516e000042b8200e0200828fd000511740a0403808020a80001408080380a1c0105400104056f81010070102a00005b101010070100415000b0814080803808020a8005800a040401c0401054002be540281010070082a0002302810100701029a300002810100701184150f8
  | 8, 0, 8 => 0x14080803808020a4340005a05478200e020082a000cb02810110401004150003d014080803808020a8005a0f405020200e0200c0000a040401c0401053d6000042b8200e0200828b700051010ae0803808020a80001408080380803670540000a040401c0401b302a00005020200e02009d4150003d01408080399804018001514405020200e010540000a040401c0401b282a000000281010071c00414e0002810116403808020a8
  | 8, 0, 9 => 0x5ac0a040401c040105400000820215c100701029c0005020200e0200828a100002810102203808020a80000104540281010070538000a040401ccc0105456000042b8200f6a01004150000281010070100414778000144a8f0401c0401054000f405020200e0200b4600005025a410070100415000028101007010056a0a80017008570401c040105400124040401c040105482000542e014080803804150002a01408b10401c020a8
  | 8, 0, 10 => 0x1e80a04044100e0200c0000a04568200e01051de00005020200e02008289f00002810100803808020a8001e80a040401c04014540000a041e0ec0e020082a00005b70101007010041500002810100701004156d8005b00a040401c04010540000a04550200e020082a000000281010070100414e000281010071e80414d1800001960504008020a6db800f405020200e0200a620002d0225010070100415000559e80a040401c04018
  | 8, 0, 11 => 0x14080847008020a3f40000a04b88200e020082a000cb028115a0801004150002c814080801004146a8000000a430401c04010538000a04b80200e020082a00054220140808038041500002810100701448020a80001408940401c04010540000a040401c0401055be00005020ec0e0200828fd000000145c0803808020a700208b2050202004010540006205020200e020082a000442e81408070100415000200b4080803808020a8
  | 8, 0, 12 => 0xa8f0401c04010538000a040401c0401bb82a000050209c0e0200828d50003d2480a040401c0401800014086b0401c04010540000a040401c0401055da00005020200e02ba8041500002810100701004157480001409730401c04010540000a041dac40e020082a000540281010070082a4100020014080803808020a8001e83e05020200e0200c0005a050201c0401051be00005020200f7201004150002a01408081301c020a8
  | 8, 0, 13 => 0x15288f0401c04010540000031020200e0200829c0005020200e020082af700002810100701004157a800014080803808020a8ac000b805020200e020096e00005020200e02008294900002de51e0803808020a8001f4a805020200e0105400008570401c0401053ee00005022cc100701004150002a01408080380414fb800190ba050201c04010540000a040401c04010528600178028101007010041500065814080803808020a8
  | 8, 0, 14 => 0x10ae080399804010540000005020200e15051ddc017f02810100701004150002c8144a0404008020a8001000a8f0401c04010540b40a040401c04610082a40005020200e0200829b10002e814080733008020a8002080a040401c040a354000b22d0281010020082a0017e2e81408070100415000410140808be81c040a8002e00a040401c04010540000a04be0200e020082a0005c028116208038080300002811aa0803808020a8
  | 8, 0, 15 => 0x14080803808020aa4c0030205020200e020082a00005020200e02008292d000028111e0803808020a8001e8b2050202004010540000a040401c0401053ce00005020200e02008a4ef000028101007010bc020a800014080803808020a37c00008570401c04010534600000028100e0200828dee002a01408080380414d180001700040401c0401054001c405020200e020082a0005d028100e0200829a3000028b8080803808020a8
  | 8, 1, 0 => 0xb2050202004010538000005020200e0200819c001f2e8140807010041500051014080803804148a800014080803e1804010540030a042b8200e020082a000042b8200e020082b090002e014080801004140080001408088201c04610540000a040401c04010560e00005020200e1501004150000215c1007c1008020a80001408ea0401c040105400104051281010070102a0005902810100200ad4150000215c100701004148a8
  | 8, 1, 1 => 0x14080803808020a3f400000050209c0e0200829c005449014080803804150000281076080380414778004e8ba050201c04010540000005020200eb000829c015f02810100701004150002001408ea03808020a800016b4040401c04010540030e05020200e020082a00005020205407010041500002810100701184020a80007ca805020200e010540000a04930200e020082a000003d1500a040401c02e0002810100701006b20a8
  | 8, 1, 2 => 0x151e0803808020a87c0000857568200e020082a0007a02810100701007170002a01408ad0401c020a800014080803808020ac540000a040401c04010562600005024641007010041500000014080812008020a70001408270401c04010540000a8f478200e020082a0007a41014080803808150002a01408080380415888004e808570401c040105400008570401c04010539e0005902811280801004150009c814080803808020a8
  | 8, 1, 3 => 0x1408080380b22010540000044020200e0105229c0005021e41007010041500002810100701005900a8000000a043c81c0401053800a805020200e970082a00005478224a07010041500002810100701007200a8000151e0803808020a2dc0b40a040401ccc020082a4011a028101007010041500002810100701004158f8000140808c701c04010540031a05020200e020082a000059323c10070100415000028101007c6008020a8
  | 8, 1, 4 => 0x1640a040400803030540000a040401c04010565600005020200e6601004150000281076070125c020a8001000a0403808020a7dc000b205023a810020082a00000028115a0800ad414e00ca014080803808020a80001408084701c04010540000a2e0401c0401053ee0005d0215c10070100415000c9814080803808020a800174ba050201c04010540032405020200e020082a000002e810ae070100414e00028122c0803808020a8
  | 8, 1, 5 => 0x1745a050201c0401054000c405020200e020082a00005020204c0200828d50009d014080803808020a8004dc0a040401c04010540000005020200e6600c55d445c02810100701004152000281010070100415978001740a0403808020a3540030a05020200e020082a00040020200e0200829f70000010008070100414fb7000500a047502004010540024205020200e020082a00196028101007010041500002810100701004140a8
  | 8, 1, 6 => 0x23cae0803808020a700014080803808020acd40000a040401c0401056660019802810100701004150002e814089403808020a8001740a040401c0401054000005d028100e0200829c00050201c0401051f9f70000f8151e0803808020a8
  | 9, 0, 0 => 0x2811d40803808020a8028111e0803808020a80281010070100414f3802810100701004151580281010070100414a480281010070100414a1865814080803808020a8000151e0803808020a720014080803808020a802811280803808020a800014080803808020a70281010070100414778028101007010056a0a83d014080803808020a816814080803808020a80a014080803808020a8
  | 9, 0, 1 => 0x2e814080803808020a8001740a0403808020a702810100733008020a802810100701004147e802810100701184020a8001640a0404008020a70281010070a808020a8
  | 10, 0, 0 => 0x14080803808020a7
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 67
  | 7 => 76
  | 8 => 85
  | 9 => 76
  | 10 => 67
  | _ => 0

def idWidth : Nat := 9

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 174 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3ffffffffff800000000007ffffffffff, 43)], [(0xa82aa414151505548282a1505548282a2a0aa905054, 1), (0xa0005000000000000000014000a0000, 42), (0x5000280000000000000000a00050000, 44)], [(0x280014000005000280000050002800000a00050000, 1), (0x2a0aa905054000000000005415520a0a8, 42), (0x2007818000000000000000400f03, 43), (0x1505548282a000000000002a0aa905054, 44)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 87)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 87 false (goal 87) u ys) :
    NatRunT 87 false (goal 87) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 10 0 (NN s)

def poolG : List Nat := [66439144476335193, 11267808185903196, 13519652019856471, 59690295975046276, 59683703202341979, 18025448483150938, 66486377346330757, 59681502031600770, 59683753669258372, 59683725707929689, 13575727111825495, 42797447642178647, 18023207609132123, 13519651987392599, 57431947408926807, 25904550962661463, 13569090310462553, 59683745073028186, 11267808150294619, 59681502032649346]

def Z (s : Nat) := bar 87 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_24 : ∀ i, 24 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 40 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_40 : ∀ i, 40 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 52 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 48 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 52 → Z 6 i = true := (range_split (range_split z6_0 (range_split z6_8 z6_16)) (range_split (range_split z6_24 z6_32) (range_split z6_40 z6_48)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 40 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_40 : ∀ i, 40 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_56 : ∀ i, 56 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_72 : ∀ i, 72 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 88 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_88 : ∀ i, 88 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 104 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_104 : ∀ i, 104 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_120 : ∀ i, 120 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 136 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_136 : ∀ i, 136 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 152 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_152 : ∀ i, 152 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_168 : ∀ i, 168 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 184 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_184 : ∀ i, 184 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 200 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_200 : ∀ i, 200 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 216 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_216 : ∀ i, 216 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 232 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_232 : ∀ i, 232 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 248 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_248 : ∀ i, 248 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_264 : ∀ i, 264 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 280 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_280 : ∀ i, 280 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 296 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_296 : ∀ i, 296 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 312 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_312 : ∀ i, 312 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 328 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_328 : ∀ i, 328 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 344 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_344 : ∀ i, 344 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 360 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_360 : ∀ i, 360 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 376 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_376 : ∀ i, 376 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 392 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_392 : ∀ i, 392 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_400 : ∀ i, 400 ≤ i → i < 406 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 400 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 406 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 (range_split z7_8 z7_16)) (range_split z7_24 (range_split z7_32 z7_40))) (range_split (range_split z7_48 (range_split z7_56 z7_64)) (range_split z7_72 (range_split z7_80 z7_88)))) (range_split (range_split (range_split z7_96 (range_split z7_104 z7_112)) (range_split z7_120 (range_split z7_128 z7_136))) (range_split (range_split z7_144 (range_split z7_152 z7_160)) (range_split (range_split z7_168 z7_176) (range_split z7_184 z7_192))))) (range_split (range_split (range_split (range_split z7_200 (range_split z7_208 z7_216)) (range_split z7_224 (range_split z7_232 z7_240))) (range_split (range_split z7_248 (range_split z7_256 z7_264)) (range_split (range_split z7_272 z7_280) (range_split z7_288 z7_296)))) (range_split (range_split (range_split z7_304 (range_split z7_312 z7_320)) (range_split z7_328 (range_split z7_336 z7_344))) (range_split (range_split z7_352 (range_split z7_360 z7_368)) (range_split (range_split z7_376 z7_384) (range_split z7_392 z7_400))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_40 : ∀ i, 40 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 56 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_56 : ∀ i, 56 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_72 : ∀ i, 72 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 88 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_88 : ∀ i, 88 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 104 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_104 : ∀ i, 104 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_120 : ∀ i, 120 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 136 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_136 : ∀ i, 136 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 152 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_152 : ∀ i, 152 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 168 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_168 : ∀ i, 168 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 184 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_184 : ∀ i, 184 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 200 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_200 : ∀ i, 200 ≤ i → i < 208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_208 : ∀ i, 208 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_216 : ∀ i, 216 ≤ i → i < 224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_224 : ∀ i, 224 ≤ i → i < 232 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_232 : ∀ i, 232 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_240 : ∀ i, 240 ≤ i → i < 248 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_248 : ∀ i, 248 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_264 : ∀ i, 264 ≤ i → i < 272 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_272 : ∀ i, 272 ≤ i → i < 280 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_280 : ∀ i, 280 ≤ i → i < 288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_288 : ∀ i, 288 ≤ i → i < 296 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_296 : ∀ i, 296 ≤ i → i < 304 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_304 : ∀ i, 304 ≤ i → i < 312 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_312 : ∀ i, 312 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 328 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_328 : ∀ i, 328 ≤ i → i < 336 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_336 : ∀ i, 336 ≤ i → i < 344 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_344 : ∀ i, 344 ≤ i → i < 352 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_352 : ∀ i, 352 ≤ i → i < 360 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_360 : ∀ i, 360 ≤ i → i < 361 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 360 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 361 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 (range_split z8_24 z8_32))) (range_split (range_split z8_40 (range_split z8_48 z8_56)) (range_split z8_64 (range_split z8_72 z8_80)))) (range_split (range_split (range_split z8_88 (range_split z8_96 z8_104)) (range_split z8_112 (range_split z8_120 z8_128))) (range_split (range_split z8_136 (range_split z8_144 z8_152)) (range_split z8_160 (range_split z8_168 z8_176))))) (range_split (range_split (range_split (range_split z8_184 z8_192) (range_split z8_200 (range_split z8_208 z8_216))) (range_split (range_split z8_224 (range_split z8_232 z8_240)) (range_split z8_248 (range_split z8_256 z8_264)))) (range_split (range_split (range_split z8_272 (range_split z8_280 z8_288)) (range_split z8_296 (range_split z8_304 z8_312))) (range_split (range_split z8_320 (range_split z8_328 z8_336)) (range_split z8_344 (range_split z8_352 z8_360))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_8 : ∀ i, 8 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 23 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 23 → Z 9 i = true := (range_split z9_0 (range_split z9_8 z9_16))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 87 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRunT 87 false (goal 87) s xsG) : False := by
  have hmin : 6 ≤ s := by
    have hl := runT_len h
    change 7 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 7 fG 10 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 2) || (a == 3) || (a == 4) || (a == 5)

def perm_2 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_2 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_2 i)

theorem hperm_2 : ∀ y : Fin 7 → Bool, fG (substIn cu_2 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_2 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_2 y) ≠ fG (substIn cu_2 y') := by decide +kernel

def perm_3 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩
  | ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨4, _⟩ => ⟨5, by omega⟩
  | ⟨5, _⟩ => ⟨4, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨6, by omega⟩

def cu_3 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 7 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

def perm_4 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨4, by omega⟩
  | ⟨3, _⟩ => ⟨5, by omega⟩
  | ⟨4, _⟩ => ⟨2, by omega⟩
  | ⟨5, _⟩ => ⟨3, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_4 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_4 i)

theorem hperm_4 : ∀ y : Fin 7 → Bool, fG (substIn cu_4 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_4 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_4 y) ≠ fG (substIn cu_4 y') := by decide +kernel

def perm_5 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨5, by omega⟩
  | ⟨3, _⟩ => ⟨4, by omega⟩
  | ⟨4, _⟩ => ⟨3, by omega⟩
  | ⟨5, _⟩ => ⟨2, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨6, by omega⟩

def cu_5 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_5 i)

theorem hperm_5 : ∀ y : Fin 7 → Bool, fG (substIn cu_5 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_5 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_5 y) ≠ fG (substIn cu_5 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 8, ∃ y : Fin 8 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 12) (hcl : SCleanL 8 gs)
    (hnd : ∀ p, p < gs.length → 8 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 8 + p ∈ g.inputs)
    (hev : ∀ x, val gs 8 o x = fG x) :
    ∀ a, a < 8 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a ha hta
  have hne : a ≠ o := by
    intro ho
    obtain ⟨y, hy⟩ := hno_projG ⟨a, ha⟩
    apply hy
    rw [← hev y, ← ho]
    exact congrFun (val_input gs 8 ⟨a, ha⟩) y
  refine ⟨hne, ?_⟩
  interval_cases a
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exact hop
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
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exact hop
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

def rowsG : List ℕ := [64, 1, 2, 64, 64, 4, 4, 16, 16, 104, 74, 97, 60, 14, 49, 104, 104, 14, 49, 104, 104, 74, 74, 97, 97, 74, 74, 97, 97, 20, 65, 66, 6, 17, 72, 96, 6, 17, 72, 96, 6, 17, 72, 96, 128, 1, 2, 128, 128, 8, 8, 32, 32, 148, 134, 145, 60, 14, 49, 148, 148, 14, 49, 148, 148, 134, 134, 145, 145, 134, 134, 145, 145, 40, 129, 130, 10, 33, 132, 144, 10, 33, 132, 144, 10, 33, 132, 144, 1, 2, 14, 49, 60, 60, 12, 48, 192, 5, 18, 68, 80, 5, 68, 18, 80, 232, 90, 101, 124, 30, 53, 108, 120, 78, 113, 105, 106, 75, 202, 99, 225, 78, 106, 105, 113, 84, 69, 82, 7, 19, 200, 224, 22, 21, 76, 112, 38, 25, 88, 100, 192, 9, 34, 136, 160, 9, 136, 34, 160, 212, 166, 153, 188, 46, 57, 156, 180, 142, 177, 149, 150, 135, 198, 147, 209, 142, 150, 149, 177, 168, 137, 162, 11, 35, 196, 208, 42, 41, 140, 176, 26, 37, 164, 152, 3, 3, 15, 51, 61, 62, 13, 50]

def xsG : List ℕ := [0x5f22359ac482222359ac4822092225984480222259844802, 0xaf11386f2248411386f22484061118662240411186622404, 0x1746440e7bb6009716202f86a74444067bb60011120023060, 0x1749716202f86a6440e7bb6007411120023060444067bb600, 0x1b89881d9dda006b2b0057594b8888199dda0022220045180, 0x1b86b2b00575949881d9dda00b822220045180888199dda00, 0xc01400201cccffff9f590000000000000cccdff98e19, 0xcccffff9f5900c0140020100cccdff98e1900000000000]

theorem rowsG_len : rowsG.length = 192 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => ((fun x : Fin 8 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 96 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 96 true (fG, false) = goal 96 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 96 zs &&& lo 96) ≠ lo 96 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 12, ¬ NatRunT 96 true (goal 96) s xsG) :
    ∀ s ≤ 12, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 96 true (goal 96) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 12, ¬ NatRunT 96 true (goal 96) s xsG) :
    ¬ HasCircuitSize 8 fG 12 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 96 true (encT rowsG 96 true (fG, false)) s'
      (ws.map (encT rowsG 96 true)) :=
    RunT.map (encT rowsG 96 true)
      (fun a => encT_inv rowsG 96 rowsG_len true a)
      (fun a b => encT_and rowsG 96 rowsG_len true a b)
      (fun a b => encT_or rowsG 96 rowsG_len true a b)
      (fun a => encT_tag rowsG 96 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 7 => 54
  | 8 => 382
  | 9 => 427
  | 10 => 107
  | 11 => 7
  | 12 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 7, 0 => 0xa0eca626954e55f78b0686c8844709737954c834734292b07094f3826c3f706c59438da6556a27324f3d82dc4db3894b4b12f0dc486d64a5477c37f044cfdf643d91736e3c87a4413af1c3083474dbd4337340a73072ff1e30554a012edb6a8d2ec8029f2d94794128f8d95628d016d324f176cc23e67a2a22c046941e61a2a119e17c3e197c1d2318a506bf183a03631816c14817852a1a164b1d5313a798a613202d9613202ad811c1271a0cbe00e50caa98f709b7126108ee628b0836b2a507fb98b6072a007e04d0a8f90403bc3e033bc14d00985e6c
  | 8, 0 => 0x7f73bad07eccd9a07e89b0207d6f2b807d4d8fb07ae269b0780c1a70779ac240743859d074025130734ceb807159bb40702486006ec5335068212f3067661f20657106d062b259e061f37b405ec43da05cc84f705c1a79b05b7c06605b242a505a12a3e058b40fd05243f3504f4e8c504da5e080491338f0408d52403eec0bb03dbcfc80381da520327656402f0752502d586ca02bea1cf02b61bf5027c4e7e0262b3da025ad77402289ceb020e5fc201ee49e501c99837019243490170fbca015d93dc014a180f0140122d0132aafc012d08be010de01600be78880099706700985e6c008ebb98004ddd2e00400f730038c2d7002d61f100124ec4000c7e07
  | 8, 1 => 0x101d9ea40fe7cf220f9c09ad0f9408e70f6ea8950f156c710eadd1de0ea28cfd0e7ce68e0e3689f90df7c3730ddbd1d20dd9e4eb0db7b18d0da9a06e0d56aeb70d45547f0d1572e70c92e20d0c806ed00c645dde0c58b0d30bfa2c4b0bc06b0d0ba9f35f0ba86e050b8f52390b51f6d10b4df3120b3f11420b3c83510b39557a0af9d3b50accd3b60aa98f490aa27c1d0a9f34720a9a0ea00a8d4be50a8bea1c0a6b19240a5f6fb90a3d6bcf0a2e92420a1bfe3e09db5e6809bb952509a2b72a098915310971207d095cba180936720a08ee628b08db9f2808d0d54708cb40a708aaf96d0868ad32082e6bba081fd882081b25880813a437080aa39b0801d2d8
  | 8, 2 => 0x1add7eb81a6faddf19b4e8e5199d77af198c07ee1974249a191b59f618dc41a918d239f218ccc26b184188101829d00b180042b617fe4a7817d4059917ccfc10175cbf1f1733d8af1708a95616ebf44316990a041691e79d1601a30315e7a1e615d271ae15a56e3915930a3a157b26e6155208aa14ef1f9214ebe3ee149bbf7314169c5813c0f92e137eb9671356380413417519133c61761335f2f1130bd658129710e61267207f1262e8051261a9a41253b891124da99212427b5d12232d7311f2b3e511e1cafc1195e3cf11827be111748100116c0ce011645d7d1142e2a9111af3ea10c1e8b310aae0c110a2c1bf107bb498105cc35b105023601020b8d6
  | 8, 3 => 0x2d5683d42d075d8d2cb68d092c1cce302afc3eda2a24ad3e2a0399ad296a8d6c289ef88b287333fe2841adac282f40f227a9344927a6b1c7279b948f2798297e276ccb7a276ade93275904c72754808d273740a326f55acd26f1683c26e7a85f26c8e93426c51f5126b0a48d264bf8c425d76290259bb26925709ec22549294f253d784e24cd7cf9245c5ea824565609239df977236b451622ecaaba22636a85225a102521b0a4e32145219c21129b8320ff339520c37eeb1fbc1f461f45fd611f3d30a11ee0802d1dce13131dc470901dc0dcb51db10ff81d83c9ac1cfc87e31cce6f6c1ccd3c591bd570ce1bcd113e1b98e80d1b9830891b4465751aef105a
  | 8, 4 => 0x42ad4964427cbe4642695658425f77754213cb124137db1541281bc53fb8ce203f9ecaf43f7fa4003efa80e53ebe31563e70eb283e390e3b3e230e823db0415c3da09ec93d91736e3d39448c3c87a4413c05b0fe3bbfd06c3ba8e24c3b33a6383af20cbd3a6c347a3a3fcfe33a1879ad39087bdc38fc3f2738af6da337c309e237be8afb37135878367147c43565d0d434e5b9703498fd7f34984ac8337340a7336fda00332d758a329688e231f44a3c31bd5803314fd66130ff88b830eedd8b30d0ab4830a8a8153084f7742ff4e5a32f929cab2f64f06f2f0fea2d2f0659f52efad5932edd1e572e8bb5e02e41ed962e08fe012d9f35ee2d9479412d8cc934
  | 8, 5 => 0xc3fb6260c346196dbca63310a0eca6269ae736fc9278bf60887271a2868f77db84634c2e82973b477f15660f7a74c2a17784e33277767cd2748b6e896f4799ab6caa415b64c5fc0c64975d44636b426862f7b49d6198b7d15ffca0e25f777dc75e42c4985a516856596a843d5954b52859438da659109da8588b7a8d580c84a9576ea28e5760481a561ae5c1542dbf15541565c653cdb6ce526b73fa50d44225504f1f0a4fead3c64e3b69454b3f08424a2566fe4a1aa10f4920d64a47fe71a747db321e477323464772f36d468798db45ba6e8645a6be0d457632ef454c0ced4543599c44310f6b439493554378a1b4436d1ded4304ee5a
  | 9, 0 => 0x6b1f029066d3b270657ba7b0657106d062bdf8106273daa061f37b4060d9b0d060bae2605ddd73e05bd3919058d6042058877f20571750205717444055ff8250503ad1904fa768804f10a4d04a48ed004a42399048663760470e0cb046e5c070447882603fa475803dbcfc803ad54c0038f0e93038423d90381da52036e4c8c0334e2f2030ef74402e9aa0102e4126e02df54cc02b91ee302b3958e02994a0a0289d4290289a4ca024eb1260224b43f01ed1ce501eb2ffe01e938df01cfcbc601c43b65018e83530167f9ca014732db0111a60800f7163d00db500f00d7ee8400b41d9800b3d4d800a7636600a5779a00a14f11007eeeed00518039000c8ff7
  | 9, 1 => 0xf4e325f0f3b48540f1686a60f16345b0e91638b0e09f87c0e06e6e60df7c3730ddbd1d20dc4d3750da323910d97371f0d86a4f20d56c0a70d56aeb70d1c287c0d1572e70d07e1020ccf69460c3b329b0c04e5d70bfb21d20bf97a480bc414b60bbdb9dd0b97116d0b83bd030b5331e50b4d87690b1cfc4b0afc0e740accd3b60ac00e3a0a6ffc6d0a5e4e670a3d6bcf0a1bfe3e09c13e9709b2a1f709abb90a09758370096d69960936720a090045f208f3743c08d7f43308d2ffce08bfa33408a9895708924846088a485a0881ec9b0859bd3c08459b4f080b291c07f0248d07d6f2b807bfa9b5079bc2c0073c704e071d0c5206ec533506caf1a406b24461
  | 9, 2 => 0x1893e3d018936ca71879b17618400ffc183c8123182e1aee17eef63717ccfc1017b2eb66177782fb175cf2b916fcd88116937bb0167d21291608d5ce15f2873f15e1fbad15dd3aba1588729615841517157b26e61550b9ed15433be8153f87201528064a14c8388414b0d6af149371b31488100c14169c5814096e3413ffbcad13ed4f5b13cb22ed13c55c9813b6645e13a7df51138f455713724d3a136ea67913693c8412f4136d12d702c312c1054d125f49dd12376f901234bcfd122def5111ed55d111eb02dd11be88f911bdd12911bbc439116456031100148010b8785410905887106ec43f105cc35b104563e0101d9ea40fe163540f9408e70f6ea895
  | 9, 3 => 0x27f209d127d86bb3278023c0276ccb7a272125e026f68e0326e7a85f25b05be125709ec225542c372440e57523d8299923aa8fa523a28472236ba52c2353067e234d271622e7a95d22798dd0226cd10222604450223562e82204829f21fb745d21c2b3d120eaac3f206b6a5c205859522040b56f1ffcbde01f9fee8c1f3c7b741f3676741f2106841f0a732b1ee8794b1ec749ac1e8c08ac1e67a4231e5832751e2ba47a1dc0fe2b1db9c2481db586ee1d8f94901d4c7e791cfc87e31ce2b65a1cce6f6c1cca478f1cc3de151cb6ed5d1c978e141c74e32a1ba993131b4465751b3ac2fc1b1175771a60b5b81990e5bd197a0ba519769a39194bcdd6194b9311
  | 9, 4 => 0x3d4329a63d320c043bbfd06c3b19559e3abe4f223a3fcfe339dabf0239ce223e38fc3f2738af6da3380a9b4f37c9ad7537842a8d36c69e6636bf39bb367147c435a7fd7135677e2634ccae95344ae82d33c84df533c5c51233232b9732e0e0eb32c6f9a3326fa1b23257a70631ce114930aeeafe3084f77430128e722ff4e5a32fbf31262f1159682f02b0b72efbddbe2efad5932e36a5ca2e0bddc02e0aec492db5b6a82d6f60de2d52c6d92d075d8d2c766def2c6c026c2c2e0a1c2bf14ad42bc922b22b7921742b2c22a42b07bb1a2ad5ae592aad48692a45794929c324d029abac57296a8d6c296a6e4c28e1150128b397132813b6c12803ab3727f75635
  | 9, 5 => 0x5eacd2425e4b16a35a68171a59f704f259e57860591192a6590a238f58f4b6ae58d7074858a7b4bd588b7a8d576ea28e56abeb8254f6d8ac52962b54511007c250d44225508c4b79504f1f0a502d9a535026e0ec4ffb92064f509bf24f3366be4e7b62cc4e3e9d824d6f911a4d4e96c74ba495ce4b5675484b012b354a3aadeb492a94f34862a9f24533178544bd8cba44ba1cfb447de934442e336d43382cd7432cb0f7430828314304ee5a42ee23cf42b1aed642ad4964427cbe464269565842563ec94225946442112776420a8ce441d394c141af11e141281bc540f2048d40df1a824080c5363fb8ce203efa80e53ea0e50e3e733b743e390e3b3dcb9874
  | 9, 6 => 0xf3ca0a4ff0764ac2d961b100d0dd61e1c3157216c305e81cc280c501c1d80850b8eca258a0ebb2b99a16f8c68cff0b918aac01f7893ab30e8837b069880e93ab87b28d4e86b80d7f82973b477d14628c7cd5d52f7a5ccfe27a1aede3748b6e89747edbea741cb58a72fd3ad2711de8376f5bdcc06ec2a8626cb6d0fc6c0667c26a87026e6a215c4d6a139ae5668b7a1e65369570645ec54663e01b8d61bbfd6b5fca79435fc5745c5f777dc7
  | 10, 0 => 0x2c766def2c2e0a1c2bf14ad4295fc3b828e115012867f52627f7563526e7a85f237024eb2353067e2287be43218bdff41ee8794b1cef16c3199c32ad188d438f1880a16317fdb5e2173c6b1a16fcd88116ca07c01662bb1e15dd3aba152fab8313c55c9813c5512f13a7df51138f45571372bc6f12c1054d120e16eb11ed55d111645603101d9ea40f4e325f0f3b48540e91638b0d97861e0d59cf850d56c0a70d56aeb70adb40e30ad0930e0a1bfe3e097583700939515d080b291c075687fb065e9e2c058877f20550b55c0529632304fa76880447882603d53aa902ef71d602e1c07b026ae055017766270167f9ca0159377500b3d4d8007eeeed001e816c
  | 10, 1 => 0xcb6f7a99c280c5019a16f8c6988f23728f83e4e187b28d4e81ec45767cd5d52f7a1aede3768c3e1d743471e76f5bdcc06d4c6de46c5ff7a9668b7a1e645ec54663e01b8d5ff1ce305f777dc75eacd2425d0978295ce22ea0565e29aa50d44225504f1f0a5026e0ec4f3366be4d6f911a434100f3432cb0f74304ee5a42b1aed63cebe6363bbfd06c3b971ca538cb680e3817431c33c5c51232b5cdc83257a70631c2539a2fbf31262e36a5ca
  | 11, 0 => 0x87b28d4e504f1f0a33c5c5120e91638b0a1bfe3e058877f20167f9ca
  | 12, 0 => 0x504f1f0a
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x7e67ffffcfac80780f00100806666ffcc70c80000000000143b81e13765e88821bc9108be7bb9e6776fec88a9991578b713103b3bb400d65600aeb2971110333bb4004444008a301b86b2b00575949881d9dda00b822220045180888199dda00ba322073ddb004b8b1017c353a222033ddb00088900118305d25c5880be1a991039eed801d04448008c18111019eed800be446b3589044446b358904412444b3089004444b308900400cccffff9f5900c0140020100cccdff98e1900000000000
  | 0, 1 => 0x3a4beb1a17d35b2607bddb00ba08890011830222033ddb002bc44e1bc8921044e1bc8921018446198890104461988901001999ffff3eb3999ffff3eb201999bff31c33999bff31c32bf98b1dbdda006b3b0a57594b8888199dda00222200451807fba3877ddb004b9f1517e773a222033ddb000889001183000003005000807333fffe7d6400000000000033337fe63865e1fe1fc3ffbfc6600000c14dffffffffffffe666400ce3ccff333dffe6ca6333dffe6ca60f333dfe66c06333dfe66c06
  | 0, 2 => 0x57eefbc86ddee88fc3d91342836eeaccdd50e888c3311202283742984ed773742984ed773db77699eedff777699eedff55e23f0fe44d0a23f0fe44d0a0c2230cc448082230cc44808746440f7bb6009716302f86a74444067bb600111200230602f917acf62511f77ffffefbd849112cc224017776ffee70d803333fffe7d6403167b02804033337fe638640016600200170d7d628aef2b3183bbbb403704444008a301110333bb4007464c0f7bb60197d6342fa6b74444067bb60011120023060
  | 0, 3 => 0x57eefffffdfee88fc3f91342836eeeffdd70e888c33112020000021fc8100000167b02000000021980100000166002001fffe7fd7ffbfc6660000c14dffffffffffffe666400ce3ccbf6b3b0a5759498b1dbdda00b822220045180888199dda003fb23877ddb004b9b1517c353a222033ddb00088900118303fcccc0001829bfcffafff7fbfcccc8019c79bffffffffffcff2e6c545f0d4c8e1df76c00e8222400460c08880cf76c00a810c05d0020149eb1453795000000000000000000000000
  | 0, 4 => 0x7a7ea573ddbee4b8b1017c777b6eed33ddbfe888900118f2201a3275741e566e3c41127fe2fbbb7ff73e7eeefe61127fc1f99e414326b399e414326b3e1998403327f3998403327f2746448efbb6009716242f86a74444867bb60011120023060781986faf36531986faf365307999eff33603199eff3360300003005000807333fd7e7d6400000000000033337fe638655e2270fe449082270fe449080c2230cc448082230cc448085f22f59ec4a2322f59ec4a23092225984480222259844802
  | 0, 5 => 0x5c4c60eeeed00b5f58a2bbcadc4440cceed00111100228c00000321fc81807333fffe7d6400002198010033337fe63864bfddfffffbef645eb3d8944613dddbffb9c36444b30890040000c59ec0a01cccffff9f590000059800800cccdff98e19204a627ad4535b3a712112ffa3eeeeffdd73fbbbf33112ffa026e3c41127fda3275741e562eeefe61127ffbbb7ff73e7c1e01e03c0040399fffff3eb20000000000001999bff31c32a0dd0a713b5dc11059ac2884f6ddda67bb7fd111798239e4
  | 0, 6 => 0x5c4c40eceed003595852baca5c4440cceed00111100228c0143bb1e4376defbb1e4376defe7bb9e6776fefbb9e6776fecbe45eb1d89447ddf4ca7aef612444b3089005ddd0cfb8c36ff6578efbb68497366b2f86a74444067bb6001112002306057e6fffffdfee88782f80100806666ffcc70c800000000002e1acac295d65262076776802e088880114602220667768015e227bffc59082270fe449080c223bfc458082230cc4480800ccc20019359ccc20019359f0ccc201993f9ccc201993f9
  | 0, 7 => 0x7807acf60500807c3f90300800002cc004000004330020003c03c0780080403c0780080400000000000000000000000140220b3585109ba14e276bb9ec222f30473c9bbb4cf76ffa5f22359ec482222359ec48220922259844802222598448027f99980003053199800030537f999900338f3199900338f3283772994edf77772994edf77db77699eedff777699eedff401981fd7f3ab1981fd7f3ab001999bff31c33999bff31c325022086f24422ee0784dd97af9222a66455e2eee799ddbfb
  | 0, 8 => 0x5c3595802baca4c40edeed005c111100228c04440cceed001d25c58c0be1a99103deed801d04448008c18111019eed80170d65620aeb29310bb7bb401704444008a301110b33bb4000000059ac0800000010000000000059800800000000000000000600a0010080600a001008000000000000000000000002fe63c77f76805afec795de56e22206677680088880114600000010de4080000000800000000010cc0080000000000000af11f87f22685ddfffffbfdd0611186622404ddddffbae1d
  | 0, 9 => 0x5c35f58a2bbcacc62efeed00dc111100228c04442cceed001d191039eed8025c5890be1a9d111019eed8004448008c1817ed67600aeb293163b7bb401704444008a301110333bb400fffffa653f7ffffffefffffffffffa67ff7fffffffffffff3a76657bddbaccbeb1a17d35ba666433ddb0c8889001183022da0a72f416526cfc21127fa2fbbb7ff73e7eeefe61127fce8c881cf76c012e2c5c5f0d4e88880cf76c00222400460c05420c09680201cedffffdf7b0000000000000cccdff98e19
  | 0, 10 => 0x3a322073ddb004b8b1017c353a222033ddb000889001183011d9cf888897fa5053aea21a91dddf998897ff7777feeb9fcff2e6c5c5f0d4c8f1df76c00e8222400460c08890cf76c00479414eba886a673e22225fe47ddddffbae7f777e66225ff07801acd6040000180d00000000002cc004000000000000015083025a008061b58d0b69ac000000000000000000000001fffe7fc3ffbfc6660000c14dffffffffffffe666400ce3cc746448efbb60097162e2f86a74444867bb60011120023060
  | 0, 11 => 0x8000000002cd6040000000000000000002cc004001d25c5880be1a991039eed801d04448008c18111019eed8017f3163bfbb400d6761caeb2971110333bb4004444008a300a810805b00200492b10535940000000000000000000000000780180500000001805000000000000000000000000000003fffcffbfff7f8cce1bc9929bffffffffffffccce9999d7995e2270d644908226000041080c2230cc4480822200044008b89881d9dda006b2b0057594b8888199dda0022220045180
  | 0, 12 => 0x5c35f5882bbcaee63eceedacdc111100228c06662cceed0cae262176f76801acac415d652e22216677680088880114601fe646bb789044467b358d94c12444b3089004444b30890045f22358ac482222358ac4822092225984480222259844802287763ca6edbdf767fffefbdfcf773cceedfdf777ffeeffd97c88f7ff9308888d67b120882488b7f913008889661120088f2829df510d446704c4494c8fbbbbff75cfe6674cc44bccb86b2b10575949881d9dda00b822220045180888199dda00
  | 0, 13 => 0x2cf6040000043f90200000002cc00400000433002002e3bcbc91ff77263077776802e08888011460222066776800e92e2c485f0d4c891df76c00e8222400460c08890cf76c00af95fe7f2becd11f87f226850611186622404111866224047fbabc77ddb424b9b1017c773b2aac33ddb020889001183222e6efdfd937fda3a77f41e562eeefff9137ffbbb7ff73e7df1fd0fb3bb6f4d65600aeb6df3ddcf33bb7f64444008a3c4ffff3febffdfeff3780df9feffffffffffffffff799ffbff
  | 0, 14 => 0x5c4c40eeeed003595822baca5c4440cceed00111100228c02e1acac115d65262077776802e08888011460222066776801fffe7fd7ffbfdfe7fd7ffbfdfffffffffffffffffffffffe0000000000000cc0febf9d580000000000000cccdff98e19287763ca6edbdf763ca6edbdfcf773cceedfdf773cceedfdbc3ff3fd7fffffff3fd7ffffffffffffffffffffffffffffd4022000004109ba14c276bb9ec222400463c9bbb4cf76ffaaf593b7f7359411b87f22684061118662240411186622404
  | 0, 15 => 0x6667fffcfac80600f00100806666ffcc70c800000000002fdefedfddde5667e7ffffa16f8cce9999d6126667ffff811500250080490820009a00000000000000000000000000000ffbaf5dfdda236bff9ed7fb7b9aaa599dda02222798459820c0000cc6240011108822000040000cc22400111000220001d19323feed8065f58d0be9add111219eed8004448008c18001098c6853493999ffff3eb20000000000001999bff31c32af11f87b22685ddf790dbbdd0611186622404ddd599baa1d
  | 1, 0 => 0x5c3595802baca4c40eceed005c111100228c04440cceed002bc44e1fc8921044f7ff8b21018446198890104477f88b010a044000008045dc0f01bb2f5f24444008a3c5ddcf33bb7f60000c87f2060100c01400201000008660040000000000000281102c8624111102c862411049112cc224011112cc224011d25c5880be1a99103beed801d04448008c18111019eed801713103b3bb400d65620aeb2971110333bb4004444008a300fc973e242fcee7440efbb6007411120023060444067bb600
  | 1, 1 => 0x7fb59d802badb5d5aedeed115c911100228c15552cceed0122da3a76f41e566efc61127fe2fbbb7ff73e7eeefe61127fce8c881df76c012e2c405f0d4e88880cf76c00222400460c0a0ddca753b7ddddcffffbfddf6ddda67bb7fddddfffbbffd0000600200100e665329cbac8000000000000666433cc30c91e5353bea29ad9de890897fd1f7777feeb9fddde998897fc01999ffff3eb3098c7c5349201999bff31c3200000000000ff7578efbb6849736242f8ee76555867bb60411120023064
  | 1, 2 => 0x454388224bdb464efe8388c4d553cc224fdf776ffee7cd9d191039eed8025c58a8be1a9d111019eed8004448008c18170d7d600aef2bb987b3bb6b3704444008a301998333bb4320000000400000000004000000000000000000000000000003a4bcb1817d353625f7fdb883a08890011830222033ddb001d2dc5acabe1a99953deff889d04448008c18111019eed80171b98fb3bb6b2d7d620aef2b71998b33bb4324444008a300000000040000000086f20400000000000000000086600400
  | 1, 3 => 0x600f00100e667fffcfac80000000000006666ffcc70cafe62d76f76801acec695d652e22216677680088880114601ff2e6c405f1dceaf1df76d08ec222400460c8aab0cf76c08749796302fa6a6c4bf7fb7107411120023060444067bb6003a4beb1217d35b26073ddb00ba08890011830222033ddb003e2ea076776889acac015d6dbe6aa8e6776f8888880114788ff2e6c545f0d4c8e1cf76c00e8222400460c08880cf76c008b68e9cfd07959bbf08449ff8beeedffdcf9fbbbf98449ff
  | 1, 4 => 0xf911885220000018cd6240004111000220000000cc224003ffffffffffffccff7ff9ba9c3ffff7fffb87cccf7f99b01800001bffc18000000280000000001bfc0180000000000000b86beb1457795dcc7ddddb59b822220045180ccc599dda19006667fffcfac80643f90300806666ffcc70c8004330020000003004000807331e4366d640000000000003331666628657ed67634aeb293163b7bb401704444008a301110333bb4004794d4ffa8a6b677e26225ff47ddddffbae7f777e66225ff
  | 1, 5 => 0x24658a28b8880600a001008000000000000000000000003fcccc0281829bfcffafff7fbfcccc8019c79bffffffffffc00018028004020190fe40c0200000000000000010cc00800f47548e7bb6849716202f8ee76555867bb60411120023064506e85309daee088000010427b6eed33ddbfe888900118f23fccfc05018a9fffffffffffffcccc8019c79bffffffffffd402210ca449082210ca449080c2230cc448082230cc44808ff6b3f9ad7db6bab5dbdda22b922279845982aaa599dda02
  | 1, 6 => 0x5788980001042089c35912420308880011002088c33112021d19303deed8077f7cd1ffdedd111019eed8004448008c180be446b3d89044447bffc984412444b3089004445bfc898048b68e9dbd07959bb710449ff8beeedffdcf9fbbb798449ff0000000700000000437902000000000000000000433002002a04201640080124ac014d6500000000000000000000000015e22f0de44d092a7cde579980c2230cc448082230cc44808b8efeffffffdd98c1dddda01b8eeefffddf99888199dda00
  | 1, 7 => 0x57889c3591242089c359124203088c3311202088c33112021019d2890897fe531396a29ad1ddde998897ff7777feeb9fd713103b7bb400d65600aeb2971110333bb4004444008a300ff33fdffe6ea7fffffffffff0f333dfe66c06fffdfffee1f0780180d00000001acd6040000000000000000002cc004002e3733ffff7d65afac515de56e33337ff778648888011460001110bb7b34000000200000001110b333140000000000000ff33386f264a6ff3fefffdfeff333a66675e6fffffffffff
  | 1, 8 => 0x3a322473ddb004b8b1217c353a222433ddb00088900118303f2e2076f76801acfc015f6dae22206677680088880114600e0c881cb76c012e0c405f0d4e88880cf76c00222400460c0746ccbf7fb71197d6342fa6b74444067bb6001112002306005b474efe8388815a8c2241184f776ffee70d9112cc224010000300500080403007800804000000000000000000000001ffffef21bf7fffffff7fffffffffef33ff7ffffffffffffeb89881dbdda006b2b1057594b8888199dda0022220045180
  | 1, 9 => 0x2fd37bdf76d35917acf62511849112cc224011112cc2240117c8bd66b1288c8bd66b1288c24889661120088896611200917377e30893fed1d3bfa0f2b17777f30893ffdddbffb9f3ea0ddca753b7ddddca753b7ddf6ddda67bb7fdddda67bb7fd5400f40a01342ee67fffcfac80000000000006666ffcc70c83c03c0500080733ffffe7d6400000000000033337fe6386516d1d3bfa0f2b377e30893ff17dddbffb9f3f777f30893fe4f94f4ffa8a6b677e2e225ff47ddddffbae7f777e66225ff
  | 1, 10 => 0x7fff9ff5ffeff199805030537ffffffffffff999900338f31d25c5880be1a99102026c801d04448008c181110006ec801f0d65600aeb6dfd0fb3bb6f5f24444008a3c5ddcf33bb7f67497d6342fa6b64c8ffbb6017411120023060444867bb60023b3bd12112ffca6a77d4535a3bbbd33112ffeeeeffdd73fae262077776801acac395d652e222066776800888801146017ef676feeeb29337bffffd097c6674ccceb09333bffffc08a80128000248410004b00000000000000000000000000000
  | 1, 11 => 0x287703c06ecbd110000020117cf773cceedfd911100228f11d19303deed8065f58c0be9add111019eed8004448008c180e8c881ef76c012e2c685f0d4e88880cf76c00222400460c050eecffffdf7beec794ddb7bf9eeefffddffbeee799ddbfb006663c86cdac80600800100806662cccc50c800000000001d25c5880be1a99123beed801d04448008c18111219eed801fed67620aeb6d756bb7bb445724444008a305554b33bb40400cccff5f9f5900c0140020100cccdff98e1900000000000
  | 1, 12 => 0x7f99f80a0315399f80a03153ff999900338f3199900338f33ffffffeffffffffde437effffffffffffffffffde67feffcbfddef35bb6f7ddef35bb6f7f3ddcf33bb7f7ddcf33bb7f6afddfa6f3b7ddddfa6f3b7ddf6ddda67bb7fdddda67bb7fd0000600a00100e6653a9cbac8000000000000666433cc30ca2e6edc41127fda3a76f41e562eeede61127ffbbb7ff73e7dfe67fbffcdd4e67fbffcdd4e1e667bfccd80c667bfccd80c0f00300e0000000300e00000000000000000000000000000
  | 1, 13 => 0x2ff71ffdfeebd111acd6241104f776ffee70d9112cc2240103c00c0380000000e1bc81000000000000000000219801000bfddfffffbef7ddfffffbef613dddbffb9c37dddbffb9c36000000000000000000000000000000000000000000000000506ee7fffdfeeeee7fffdfeefb6eefffddffeeeefffddffe83f33ffffe7d6733ffffe7d64033337fe638673337fe63864bfddf4ca7aef645eb1d8944613ddd0cfb8c36444b3089004000000100000000001000000000000000000000000000000
  | 1, 14 => 0x600a001008062cf6050080000000000000002cc004003fffce984fd7f8ccc0001829bffffe99ffdffcccc8019c79941bb94ca76fba2390ca44d0a0dbbb0cf74c3a2230cc44808bf99f9ffffe857bfb7f77795be9999ffffe04333a66675847fbabc77ddb424b9f3797e773b2aac33ddb02088d3311a3217fbbfffff7defbbde7b76defe7bbbfff77fefbb9e6776fedfffff4de7efffffffdfffffffffff4cffefffffffffffffe5f2230000402222358ac4822092220004400222259844802
  | 1, 15 => 0x600f0010080600a001008000000000000000000000002804421bc8921044219489210184461988901044619889011fe667bdfcd94c6670de4c94c1e667bfccd80c6670cccc80cff33359ac68a6ff3ffbffdfeff333798679e6fffffffffff7fcb9f3797e773abc77ddb423b088d3311a322aac33ddb02003303fafe756000000000000033337fe63864000000000015fbbfffff7fbbbbfffff7fba0dbbbbff75c3bbbbbff75c3a50eecffffdf7b22c594c4a2309eeedffdce1b22259844802
  | 2, 0 => 0x4329020000000200000000004330020000000000000003332994e5d64030010008040333219e6186400000000000bfddef3dbb6f7ddfffffbef7f3ddcf33bb7f7dddfffbbff6fffffffffffff33f014062a7fffffffffffff333200671e62f917efff2711917acf62511849116ff226011112cc2240100003004000807331e6b66d640000000000003331666628655e22600004109ba7fd7f7bb80c22200044009bbbbff75c3a000000000000000000a00000000000000000000000000000
  | 2, 1 => 0x3a32607bddb00efeffffffbdba222033ddb006eefffddf3cbfffcffefff7f8ccd66b1a29bffffffffffffcccde619e7980000001400000000000000000000000000000000000000000f00386f2040000300e000000000086600400000000000007ffff9000f9fffffff5ffffffffff900ff9fffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffca1dd8f21bb6f7dd8f35bb6f7f3ddcf33bb7f7ddcf33bb7f60000001400000000dffe0c000000000000000000dfe00c00
  | 2, 2 => 0x7ffffffdffffffffffdfffffffffffffffffffffffffffff943bb3ffff7defbb3ffff7defe7bbbfff77fefbbbfff77fec01999ffff3eb3998428326b3e1999fff33ff3998403327f28b9b3f08449fe6829cbd05948bbbbf98449ffeeedffdcf9f0000600000100e661000c9ac8000000000000666000cc10cbffffffbffffffffe994fdffffffffffffffffffe99ffdffc1e0070de408000070de40800000010cc008000010cc008005f22358ac482222300004022092225984480222200044002
  | 2, 3 => 0x437902000004379020000000433002000004330020003c00c0280000000c000000000000000000000000000000005e226054440000060de4480008222000440000000cc448000000001000000cc0ffbf9d580000000000000cccdff98e1957889c37912426e9d379daee7b088d3311af26eed33ddbfe9d25c5890be1a991039eed801d04448008c18111019eed800e92fac485f4d7d995cf76eb2e8222400460c19990cf76c32ffff3febffdfeff3a613f5feffffffffffffffffa67ff7ff
  | 2, 4 => 0x7fbafc7fddb42cbff3f97f77bb2aac33ddb02088d3311a32283773fffeff777729d4edf77db777ffeefff777699eedff4be45eb3589447ddef35bb6f612444b3089005ddcb33b943600ccca753975900c0140020100ccc8679861900000000000000062cf6050080600a00100800002cc0040000000000000000000000000000021ac8100000000000000000021980100001999ffff3eb39994ea72eb201999bff31c339990cf30c327f667dffffe22b737beef86a7d666dffffe0233379867862
  | 2, 5 => 0x6601000c8ac78000100008f0666100cc9fc800000010000011123bee5800000000000000111219e61801fffe7ff7ffbfc6660200c14dffffffffffffe666400ce3cc5f02340a0482220308a800000000000000000000000000002a10004940000010a08024110000000000000000000000001d3b32b9eedd665f5890be9add333219eed8644448008c18000000000000019814c272ab000000000000019990cf30c325f22f01404223eefffffdf7b0922200044002eeedffdce1b
  | 2, 6 => 0x5788fefff1742eefffffdfee83088eff116026eeeffdd70ebfcccf7af9b298ccc000182983cccf7f99b018ccc00198018a1dc0f01bb2f5dc0f01bb2f5f3ddcf33bb7f7ddcf33bb7f6f0ffcff5fffffffcffffffffffffffffffffffffffffffff000002cd604000002cd60400000002cc004000002cc004003fcccc00018298ccf7af9b2983cccc00198018ccf7f99b0180001800800402018008004020000000000000000000000000000c00400201cccfeff9f590000000000000cccdff98e19
  | 2, 7 => 0x7fffffffffffffffffffffff87fffeffff70ffffeffff70f8000037ff830000037ff83000000037f8030000037f8030000000002800000000028000000000000000000000000000000f00f87f2060100f59ec0a01000008660040000059800800006663ca6cdac80600a00100806662cccc50c80000000000003333fffe7d640337ff83804033337fe638640037f803000000000080000000001c00000000000000000000000000000008406242984800400400200000000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x28440602100541ae050200c041310849c0a1108008400e06b81408030104c3e1e70e8143803010200ee1a06010360204029c340c0200c32080538100602008381a1870281006020085c14e1602810200207035c0a110183c021506b81408140104c1c12702844200f008381ae0c0202c040800029c12050200c040803b8180a040180802007
  | 7, 0, 1 => 0x28c80602168c414e3006010360200029c600c0200c320005381408030108c000a70601036020401c14e2f0200c04010f8b9c0a040183c5a0e163814360215820000a70281054020400052e05020401e2007035c4a050e00c04000538a04e05020081c007028704c030400014e1a12814080301029c0a0412008021705381408030108c00227
  | 7, 0, 2 => 0x281006021e0541ae3b02810060f10039c0a0401808401506b8e80a04018081c3970e830081b0102000e3802810480200829c6e0401808100014b8d80a04018086a0070287068020400014e050200c0423000a5c0a1c0186410000538142210010041c0d7028100602168c452e2502810060203829c180401808100014b814380301020660a7
  | 7, 0, 3 => 0x4a050200c04000538140803010b4803f71d8140803010802ae050880c0401070e5c0a0401808100d1f38d87a050200c040a7
  | 8, 0, 0 => 0x28100619040040e0a802934060200838000a8260d80a04018085a0a81d014084b01038000a8028700602040040e0a817810940300838000a802810920200838000a80281020020083800488000180a0401808020071d0148e0301038000a81d0142203010381a00802810064600838002c802914060216838880a802810060f008541a43821010060200838000a80284406020087c820a8
  | 8, 0, 1 => 0x2d014080301004b200802870060204038000a82c010ae0200838000a80e81006022b0041c00802810065504004000a80280c0454008381a008048e80a04018081c008028100602100042a0d80e8140803010b41c5380281004010700014528178100602009001c0d8288140803010041c00802810a00200838000a81b0149e0301004000a81b014084e01004000a8028103602040040e0a8
  | 8, 0, 2 => 0xe8140857010041c0080880c045600838000a80d0148a03010041c0a80291c0602008380e0a82d18c0a040180802008028104802310043e0a80280c046100838000a802980060209838005f81d16008032f038000a8178109c0200838000a82e810060210038000a806010200200838000a802914280200838000a80200c040107000145c80e8d80a040183c0200818014080301000525b8
  | 8, 0, 3 => 0x2914061900838000a8029b8066d00838000a802810060f009b0000a802810d60200838000a802810d40200838000a8028100602008381a3980d1a40803010041c0a834014080301004800081b014220307804000a81801408030c804000a81d014ce0301038000a80e8e8cc04018081c00833010060232838000a82c010060200838000a802810060f1e038000a802810060f32038000a8
  | 8, 0, 4 => 0x2810065509838005f83a8140803078041c0d8028440602008380074839814080301004000a8000140803010042e0a706010160200838000a80e8e80a04019781c008390140803010200e0a81b1c40a0401808880a80d0d80a0412008020a8029140602009c0000a806010060200854000a802810060200900006f8048140803010041c07802914360200838000a80e8bc0803078041c008
  | 8, 0, 5 => 0x1b03008030120c000a802810200210038000a81b0580a0401808000a802914068200838000a80ea040803010041c00802844068000838000a802914060200838fe0a802810480209838005f83f014060200800147d83e01006023d838000a802810f40200838000a802810060f00838007980e8140803010041c00802810060200900f0008398140803010041a4383b9d8060200838000a8
  | 8, 0, 6 => 0x1b014060245004000a80e814080301020005b802810360200839120a80e8d8180401808020080d0e8b004018081c0a81b0e80a042b808000a80e8140824010043e41802811100200838000a80e9610e03010041c00802810066d00a18000a81d0140803078381a008028102002100381a43802810060f0087c820a81401408030104c1c00817844060f00838000a842814080301005080a8
  | 8, 0, 7 => 0x1b0e80a0401808000a80d0d9220401808020a802844060200900009080e86874050200c040e80d23c0a03010041c0a806010060204000520a8390c00a0401808000a80b0bc080301038000a8028100602100541a438028111c0300838000a802810060210054000a8028440602008381a43840844060200838000a80e814088d010041c0081b2300a0401808008b802844060200838000a8
  | 8, 0, 8 => 0x2811300300838000a802810060216838584380d030081b010041c0a80d03008030c8041c0a80e8140897010041c0080e8e80a04018641c0080d0140896010041c0a802a54060200838000a80281006020087c5c9481d8e80a04018081c43806010069300838000a81b0e80a04018081a4380d0d80a04018080229802810540200838000a802844060204000145b802810209200838000a8
  | 8, 0, 9 => 0x1d0bc080301038000a81b014080301004009f81d278080301038000a802810540204000145b80d0e80a044e80c1c0a8028112c1900838000a833010069c00838000a8028712c0200838000a81d01408034d838000a81b014081b010040029802810280200838002c80281006020085c820a81b01408030c804002984d010060200838000a802810069900838000a81b01438030100400298
  | 8, 0, 10 => 0x29d8066d00838000a802810060241aa4000a854014060253838000a802810060253294145b80e8143803010041c07802a90060200838000a802844060200839460a8028112c8200838000a8028112c0200838fe0a80281006020096400a281b014220301080000a81b0140803010040e0a802a84060200854000a80e8140810010041c0d80d0140602500041c0a81d0bc0803010381a438
  | 8, 0, 11 => 0x2810060f00900009085801406020083814af80eab80a0401808020e80281006021007c820a817844060210038000a8178100602008380e0a840810060f00838000a84f0100602008380e0a80d01408030100480ad802811580200838000a80e81408032a8041c008028442002008381a0a8028100602009e01c00813aac0a0401038005f8550140810010041c0a842814080301004820a8
  | 8, 0, 12 => 0x5d010060200839720a802810060200884002c8128c00a0401808000a85c014089d018056e0a8028104c1b00838000a80d1dc0803010041c0a8178116c0200838000a81d0148a0301038000a813814080200838000a80291c06025a838000a80d0140826018041c0a80e81408b4018041c0080281006020090000b380200c04010700014b2802810200200854000a802810360200ac4000a8
  | 8, 0, 13 => 0x2810060232054000a817810060f10038000a860010060200838000a80d0140803010057e0a80e8bc0810010041c00802810200f008381a0a833010066d00838000a80200c04be00838000a8029140602008380e0a85e81006020087c820a80281006025e00120bb802810360200a18000a802810061900a18000a80ea440803010041c0080200c045610038000a81b0e80a0412008000a8
  | 8, 0, 14 => 0x28100602100381a43840810060210038000a81b0e80a040180800298028440602008381aaf802845880200838000a842814082401004820a80281006021684c3e40802810060210038000a80e8bc0803010042a0081b0e9220401808000a80281006c300838000a81d23c0a0301038000a8028100602008381ac2802810064616838880a8608140803010043e0a80281006021e054000a8
  | 8, 0, 15 => 0x2810366d00838000a81b01408030104c005f81b0140803010040e2981d01406022a038000a80e81408c9018041c0080280c04c800838000a817844060200854000a81d0150e0301038000a814014080301038000a81d030081b01038000a81d014089601038000a81d030380301038000a8028118e0200838000a863010480200838000a8028118a0200838000a80281054020083800298
  | 8, 1, 0 => 0x291406020083800cb8570300803010041c0a833010060216838880a8550140803010041c74802810060210039460a80d0140803010041cca8390740a0401808100083a8140803011901c0d85e810060200838000a80d0d85e0401808020a82e810060200838000a802a84060200838000a802810060204000143e8028112c02008380e0a80001408030108c000a7060700602008380e0a8
  | 8, 1, 1 => 0x2810280216838880a869010060200838000a80281006020087d080a802810060211800145b8028100602100541a0a8608140824010043e0a86881406020080014d08000300803010200029702810060f67838000a8029d89c0200838000a85e8111a0200838000a85e810060204000145b802810060267038000a8028119a0200838000a80eb300a04018081c0080281006021e07c820a8
  | 8, 1, 2 => 0x2810360200839b00a80001438030c820000a702810060204000445b8000142210010041c0d76b8300803010041c0080e8d80a0401808020081b810060204000145b81d0140803012fc000a80281006d600838000a802844060f008381a00802810060200838002280d3540a03010041c0a80281006d40090000ad80200c04d300838000a81b810060200838000a80d0d80a4501808020a8
  | 8, 1, 3 => 0x2810361900838000a802870360200838000a802870061900838000a81d014080323038000a80d3640a03010041c0a80e8686c3a02810060283a8140803010041c0d80e8bc0803010041c0081d8142203010041c4381b0142203010041a4381b014220301004000a80281006021e0381a4380e8680a1101808020e80281006021e038000a802810060210038002981d014060215838000a8
  | 8, 1, 4 => 0x2811ba0200838000a81c014080301004820a802810068200838fe0a80d0149e03010041c0a80eb700a040180802db802810480200854000a81b0e85e0401808000a802810361904000145b802870360204000145b8048300803010041c00802810360200838fe0a80d0d80a8701808020a817810060210054000a8178440602008381a4380d01408036d0041c0a80281006020087c820a8
  | 8, 1, 5 => 0x1b014080301080000a80d0e80a0401808809081d014380301038000a83901408030108c000a84601408030103800e3802811c4020087c820a80e830081b010041c00802810060204034b64380281006027080014e08028100602008381a43802810060200838000a81b810060200838002980337c0a0401808020081d01408572f038000a812814080301004000a81b01408de01004000a8
  | 8, 1, 6 => 0x48140803010041c0080e8680a0401808c80e802810060211838000a80e8e84e05020081c008028100602100381ae883b844060200838000a8738140803010041c438550d80a040180802748028104802008381a43802810480200838000a866014080301054000a87337c0a0401808020080d0140803010041c9f872b900a0401808000a8000140803010802a0d71b0140803010801a438
  | 8, 1, 7 => 0x28100602169008890802810486d00838000a802810060200839d4438000940a0401808000a7028100602322fc000a83481006020090000908260140803013a41c0a802844360200838000a812814080301020000a81d8140803010041c438028100602168387e0a80d1600857010041c0a804814080301020005b82c010065e00838000a8
  | 9, 0, 0 => 0xd80a040180840010002a400050200c040107000e8439000140803010041c002202a400050200c04130087c820a9000686c050200c04010516e400660200c04010f838000a9000740a0401809da01070024003a02810061900838000a90035c3a050200c040107002400050200c04010700014ec9000e80a1c01808020e0002a4003a0281006020728c000a9003ac0a0401808020e0002a400052280c040107000145f9000140803010200e000516e400050200c04620087c820a9
  | 9, 0, 1 => 0x1408030104c1c002f96e400050200c04200703414439000d80a040186402000516e400050200c04010701c525b9000680a040180826f00702a4003602870060200800145b9000686c050200c04012082a4001a0281006020083814ad9000140803010801c000502a400050200c04b507000145b9000740a0401809de0107002400050200c042d07034880a9000140803010041c0d2210e400810200c040107000880a9000740a0401808020e003ba400dc1b0140803010043e0a9
  | 9, 0, 2 => 0x14088d010041c002202a4003602810060216804000a90001408f30d808020e0002a400050200c1e010700014909003540a03010043e0e0002a4000c0200c040800838000a90007434050200c042d0083a4001d02810060200838008b902810060216804800e0002a800f21b014080301004000a900000b4050200c04012c802000050200c04012000088909000140803010b43e0e2202a400f102810060200838000a9000000a1c01808100e0002a0002f0200c1e010700014439
  | 9, 0, 3 => 0x14080301005f20e4202a400050200c04f800838000a9000140803010801c00053de400000e8140857010041c0080006874050200c040e053b24003a02810060207000580a90000034052280c04010702a000050200c04010703486439002040803010041c000510e400f602810060200838000a9000bc080301080020e0002a400050200c04017a838000a9000140803010041c000510e4001d02a1c06020083800ec9003d05e0401808020e0002a400050200c04010700014b39
  | 9, 0, 4 => 0xd80a040180826000517e400050200c04fd00838000a90001408030c8041c0e0002a400050200c040800028b6439000143803010041c0e0002a400721d014080301038000a9000680a0401808020e0682a4001d7e0140803010041c009000000a0435808020e0002a000050200cdab500838000a90001408fb019b4020e0002a4001d550140803010041c00900014087a010041c004202a400002c010060200838000a8000140803010041c0d003ea4001a028100602008381c0a9
  | 9, 0, 5 => 0x140803010041c00053fe400361d014080301000148b900014080301020400e0002a4000002810f40200838000a8000003a050200c040107002000ab02810060209838005f9000143803010041c0d0002a4001a02810060204038145b9000680a0401808021f0702a4003a028100602073f8000a900000e6050200c04010002a0001d1b0e80a04018081c009000bc0803010b4020e0002a400050200c0401202dc000a9000140803010041c122202a400e41d014080301020000a9
  | 9, 0, 6 => 0x3a050200c04080016e000050200c050300838000a9000140803010041c000540a4001a0281006020083a020a9000140803010b402310702a400050206c360200838000a9000d80a8701808020e0002a4000502258040107000145f9000140803368041c0005402400aa02810060200838147490001408030c8201c000516e400050e00c040807000145b90001408030c8043e0e0002a400050e00c04010f838000a9000140803078041c00053a24000002810200210038000a8
  | 9, 0, 7 => 0x1300a0401808020e0002a400050200c040107000150890001408030104c020e0690e4003a028100602070020e0a90001408030104c020e0002a4001d0281006020083801069000146403010041c002202a4000002810060210054000a8000000a1101808020e0690e000360281006021000014439001c80a0401808020e0382a4010502810060200838000a9004100a0401808020e0682a400050200c046200838000a9000000a1101808020e0002a0000c0200c04010700014909
  | 9, 0, 8 => 0x740a0401808020e0016e400050200c040110838000a9000e80a04018081c00052ee4002f0200c042007000144390042c0a0401808020e0002a4010a0d0140803010041c0a9001c40a0401808021f0702a400050200c042d0987c1c0a9000140824010041c002202a4010902810060200838000a9000000a0415008020e0002a0003a0281006020f838820a9000006c3a0281006020002a0001a1b2140a0401808020a9000003a1a1d01408030103a000000d23c0a03010041c0a8
  | 9, 0, 9 => 0x300803010041c001482a400050200c0401073a800299000740a0401808031007002400050243c200200838000a9004380a0401808020e0002a4001d0281006020083800419000300803010041c0005436400050200c04010f83a180a90023074050200c040e0022e400050200c04200700014909003983a36028100602008024001a1b014080301004000a90001408030104c020e003de4001d0d0680a0401808020e900014080301020000a8416e4003a0281006020f900000a9
  | 9, 0, 10 => 0x140803010041c000508a4003a1d014080301038000a9000148a030104c1c000517e400050200c04010700015139000006c050200c04010382a0001a02810060200839520a9004480a04018082601070024001a6f8140803010041c0a9000142203010041c000516e400050200c0401200380e0a9000140824010041c000510e400050200c04010701c00299000140803010041c008882a400001d0bc080301038000a80006874050200c04130702a400e418014080301004000a9
  | 9, 0, 11 => 0xe80a0401c64020e0002a4003602810060200a18000a90007556050200c0401070024011802810060200838000a9004106c050200c04010002a40005020a8040107000145b9000d874050200c04000516e4000042814080301004820a8004103a1a0281006020083a4001a02810066d00838149090045c0a0401808020e0002a400050200c0401072dc000a9004586c050200c04010002a4011502810060200838000a900014080301005f21f2082a4000502450200200838000a9
  | 9, 0, 12 => 0x4e0502008020e0002a00075028100602008381a0a9000140803010041c001490e400050200caa1300838000a90001408030104c0240003ba4001a1d0140803010396e0a90046c0a0401808020e0002a4000002810200200854000a8000e80a0401808020e0382a4003602810200200800144390001408038d0041c0005252400361d014080301000820a9000bc080301004f60e0002a4003a0281006020700014ad9000680a0401808020e7d02a400050200c04200700014e89
  | 9, 0, 13 => 0x746c050200c0408008024001a6e0140803010041c0a9000bc0810010041c000510e4003a02810060207034000a9004100a0401808020e7d02a4005a028100602098041c009000746c050200c04012c802400050200c040107000151e900075c83a02810060207002400050200c320107474000a90001408240104c020e0002a400050200c040107000151c9000e80a04018081c0e0002a400360281006020081c145b90000074052280c040e0002a0003a02810060207001b60a9
  | 9, 0, 14 => 0x75701a0281006020083a4000522914060200838000a90001408030104c1c009197e400050200c051007000145f900014080301188260e0002a4002f0200c04010a80014439000140803010041c000548a400050200c04010700052ff9000e80a04018081d210002a4000502480480200838000a9003300a0401808020e0002a4001d318d80a040180802009000140810010041c0005242400050200c0401200023e0a9000680a4501808020e0002a4001a0281006020083815009
  | 9, 0, 15 => 0x3f00a04018085a0e0002a400050200c0401070005c949001d46c050200c04010002a40000028100602100381a438002ac0a04018081c000517e400750e8680a0401808020e9000000a0401808400e0002a000050200c04010f8380e0a90000182050200c04010f82a0003a02810060207002480a9000740a4501808020e0002a400050200c04017c8381a439000140803010041c7f054024005a870140803010041c009000140803010042a0005242400050200c04017c838000a9
  | 9, 1, 0 => 0xc00a04018081c000516e4007517810060200838000a90009d560502008020e0002a4001d0281006020083824009000140803010041c00054a6400050200c040194038000a9000140803010f01c0005242400050200c04010a80014e89003980a0401808024000242400001d0150e0301038000a800014092708008020e0002a4000c0200c040107000145b9000764c050200c0401070024003602810060292804000a9000740a0401808020e00252400050200c04010700014749
  | 9, 1, 1 => 0x140803010041c00053de400050200c04010f90414909002300a04018081c000517e400360281006020081c000a9000017a0401808020e0002a000050200c04012000014909000140803010b41c008302a4007502810060200839f40a9000743a3a028100602070024001a1d01408030103814749000d80a04018085a010f82a400001b01408030104c005f8000140803010041c0d0510e400cc0281006020700014439000e80a04018081ca90002a400050200c040107000140a9
  | 9, 1, 2 => 0x691e050180802f00702a400050200c04010f904150d9003900a04018081c000516e400050200c0408008381a4390001408030c8041c00054b2400050200c040800838000a9000140810010041c00054ae400050200c040107000143e9000e80a0401808260e0017e4003602810060216838880a9000d80a04018080200053b24001d0d0140803010041cec9000740a8701808020e0002a4000033010060216838880a800014092a010041c008302a40000550140803010041c748
  | 9, 1, 3 => 0x3f0e2050200c040e0002a4001a0281006025e0041c0a9000003a36028100602008020001a1b0140803010043e0a9000140803010041c00054c24000002810060200838002280001408e212008020e0002a4001a1d8140803010041c0a90000008030134c020e0002a000001b810060200838000a8000148a0301004020e0002a4012f02810060200838000a9000140803368041c00054ba4012d0e8140803010041c0090001408030102010000516e400000281006020087d080a8
  | 9, 1, 4 => 0x140803014c8020e0002a400660200c042d00838000a9000140803010041c001116e4003602810060241800145b90006874050200c040e052424010e02810060200c401c00900000ea050200c0401070360004c1b014080301004000a9000d80a0401808020005422400370200c040107000145b9000003a2f0200c040107002000001b014220301004000a800014080301004800048242400360281006020080015029000000a0401808780e0002a0003a0281006020700015319
  | 9, 1, 5 => 0x3980a0401808020e0028a4001a02870060200838145b9000746c050200c040100106400050200c042d16838880a9000e80a1101808020e0002a4001a180140803010041c0a9000bc08030104c020e0002a400050200c04010703486e89000140803010041c001482a4010a0d0d80a0401808020a9000000a0401808021f2082a0000502090040800838000a9000140803010041c00054364000002810361900838000a8000000a1c0d808020e0002a0000002870061900838000a8
  | 9, 1, 6 => 0xa0401808020e0690e000361d014080301034000a9000000a0401808020e0002a0000902810060200838000a9000e80a04018081c000517e4003a02810060f00838000a9000146403010041c0005436400361d014080301038000a9004d00a0401808020e0002a4003602810060200802660a9002a80a0401808020e0002a4000501809140107000145f9000150e03010041c00053b2400c102810480200838000a900014080301020020e000a6400050e00c320107000145b9
  | 9, 1, 7 => 0x2ac0a0401808020e0002a4003a02810060210038000a9000140803010041c00148a64001d02810066d0083800909004286c3a0281006020002a4001d0d0140803010041c749003986c050200c04010002a4001d0281006029b0041c009000580a0401808400e0002a4001a02810060200adc820a9000006c050200c04200002a000001d014380301038000a80018c0a0401808020e0028a4003602810060200be4000a9001d40a040180802bf0002a401350281006020080014439
  | 9, 1, 8 => 0x74b00401808020e003b2400050200c040107000525b9000e80a040180802150002a400050200c0401074e8000a900069183a0281006020702a400050200c04010700015399000140803013b41c009982a400050200cda0107000153890018c6c050200c04010002a400050200cda0107000880a90039074050200c040e0002a400050200c0413009001c009000740a0401808020e00402400050200c04019b838000a9000d80a040180802008f82a4000002810480200838000a8
  | 9, 1, 9 => 0xd874300281006020002a4003a02810060204000145b90007434050200c04010716e4003a028100602008381a4390001408030100442000510e4003a02810060200838000a90006874050200c04400702a400001d8140803010041c438001c80a040180810000516e4001a0281006020083814439000143803010041c002202a4007202810060200838000a90000012050200c040107002000050200c040107002760a9000140803010041c0d4202a400e41d0140803012a4000a9
  | 9, 1, 10 => 0x50200c053f00838000a9000140803010041c000f02a400050200c0401070027c0a9000140803010041c00054f6400050200c04e100838000a9000ec0a0401808020e0690e4003b02810060200838000a90007434050200c040107036400050200c040107002780a9000686c3a0281006020002a4010a02810060200838000a9
  | 10, 0, 0 => 0x28100602098041c00053ba800050200c040107000144390281006027684c020e0002a80a0401808020e03800145ba000d80a04018085a010002a40a04018085a0120038000aa0281006020087c1c000517e876050200c040107034000aa1b0140803010043e0e0002a80a0401808020e06800145fa1b0140803010041c0d0002a800050200c040107000880a9028100602008041c000516e800050200c04010700014ec9000148a03010041c000517e46c050200c040107038000aa
  | 10, 0, 1 => 0x42834050200c04010702a400001b0e80a0401808000a8001300a0401808020e0002a400050200c040107000150890001408030104c020e0002a5c83a02810060200838000aa02810060200838000a2d90e800050200c046200838000a9000000a1101808020e0002a00a0401808020e00104880aa850d80a0401808020e0002a800000e8140803010041c008000680a0401808021f0702a40a0401808020e00110145ba000680a0401808020e0682a434050200c040178038000aa
  | 10, 0, 2 => 0xd0e80a0401808020e0002a80a0401808020e000281490a02810060204020020e0002a800050200c0401072dc000a9028100602310041c002082a80a0401808260107000145ba000e874050200c040e0002a40a04018085a010f838000aa000740a040180803100700240a04018085a0107034000aa004380a0401808020e0002a4001d0281006020083800419730140803010041c00052428001a1b014080301004000a90d014080301004800e0002a8001d02810060200838005b9
  | 10, 0, 3 => 0x140803010041c0d0510e4003a028100602072a4000a9000140803010041c000502a40a04018094c0800838000aa000300803010041c000516e40a0401808020e000292090a000140803010041c00051d24000002810060210038000a802810060200838000a21a52800050200c04017c838000a91b014080301005060e0002a834050200c040107034000aa000e80a04018081c0d0002a556050200c041300838000aa02810060200838000a2fc029b83602810060200838000aa
  | 10, 0, 4 => 0x2a80a0401808020e0002a40a0401808021f07000880aa000140803010041c001482a400000281006020087c820a8000140803010041c0005436474050200c0401070001443a000003a360281006020080200a0401808100107000145ba1d0140803010041c002202a874050200c04010700014eca00014080301020020e0002a46c050200c040107000145fa000d80a04018080200053b246c3602810060200838000aa000140803010041c00053de400050200c04012000014909
  | 10, 0, 5 => 0x140803010041c001496e40a04018080240070001490a028100602008381a000502a800631b014080301004000a90039074050200c040e0002a400050200c0413009001c00902810060200838000a2d96e8000002810480200838000a8002ac0a0401808020e0002a40a0401808020e06802660aa028100602009001c000502a80a04018085a2d00838000aa000000a0401808020e0690e0000002810060200838000a8000e80a04018081c000517e400361d014080301038000a9
  | 10, 0, 6 => 0xa0401808020e00104145fa000ec0a0401808020e0002a4010a02810060200838000a9028100602008381a000516e874050200c040107000145ba000e80a0401808020e0002a4e4050200c040107000145ba000680a0401808020e0510e4007202810060200838000a90e8680a0401808020e0002a80a0401808100107034000aa
  | 11, 0, 0 => 0xe80a0401808020e0002a400050200c040107000150050200c040800838000a9028100602098041c000548003a050200c04010700200a0401808020e00028872050200c040107000880a9
  | 12, 0, 0 => 0x2810060200838000a8
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 7 => 67
  | 8 => 76
  | 9 => 94
  | 10 => 94
  | 11 => 85
  | 12 => 76
  | _ => 0

def idWidth : Nat := 9

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 193 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xfffffffffff0000000000000fffffffffff, 44)], [(0x55555440aa40a555440aa40a55555440aa40a555440aa40a, 1), (0x60006000000600060000000060006000000600060, 2), (0x200000000002000000000000200000000002000000, 3)], [(0x550000000000000000000000550000000000000000000000, 1), (0x10000000000000000000000010000000, 41), (0x1800180000000000000000001800180, 42), (0xaaa881548140000000000000aaa88154814, 43), (0x20001201000000000000000020001201, 44), (0x555440aa40a0000000000000555440aa40a, 45), (0x600060000000000000000000600060, 46), (0x2000000000000000000000002000000, 47)], [(0x220008022208844020000000220008022208844020, 1), (0x400000000002000000000000400000000002, 2), (0x1110002200000000000000001110002200000000000000, 3), (0x2000000000000000000000002000000000000000000, 22), (0x120000000000000000000000120000000000000, 37), (0x110000000000000000000000110, 41), (0x88800110000000000000000088800110000, 42), (0x80000080000000000000000080000080, 43), (0x100000400404000000000000100000400404, 45), (0x11106022000000000000000011106022000, 46), (0x200000000000000000000000200000, 47), (0x20000000000000000000000020000000, 65), (0x1000000000000000000000001000, 80), (0x200000000000000000000000200, 82), (0x1000000000000000000000001, 88)], [(0x2220884402000002200080002220884402000002200080, 1), (0x200000000004000000000000200000000004, 2), (0x11100022000000000000000011100022000, 3), (0x2000000000000000000000002000000000000000000, 21), (0x100000000000000000000000100000000000000, 36), (0x20000000000000000000000020000000000000, 38), (0x1000000000000000000000001000000, 41), (0x44418088000000000000000044418088000, 42), (0x800808000000000000000000800808, 43), (0x100000000000000000000000100000000000, 44), (0x40000040000000000000000040000040, 45), (0x22200044000000000000000022200044000, 46), (0x22000000000000000000000022, 47), (0x20000000000000000000000020000000, 66), (0x1200000000000000000000001200, 81), (0x1000000000000000000000001, 89)], [(0x40040000000400404000000040040000000400404, 1), (0x2220604400011106022000002220604400011106022000, 2), (0x20000200000200000000000020000200000200000, 3), (0x2000000000000000000000002000000000000000000, 22), (0x120000000000000000000000120000000000000, 37), (0x88800110000000000000000088800110000, 41), (0x10000000000000000000000010, 42), (0x140000000000000000000000140, 43), (0xc00000000000000000000000c0000000, 44), (0x1222000440a00000000000001222000440a0, 45), (0x2000000000000000000000002, 46), (0x20000000000000000000000020000000, 65), (0x1000000000000000000000001000, 80), (0x200000000000000000000000200, 82), (0x1000000000000000000000001, 88), (0x550000000000000000000000550000000000000000000000, 1), (0x10000000000000000000000010000000, 41), (0x1800180000000000000000001800180, 42), (0x88888110810000000000000088888110810, 43), (0x44400088008000000000000044400088008, 45)], [(0x4000004400040000040000004000004400040000040, 1), (0x1110002200022200044000001110002200022200044000, 2), (0x2000000000022000000000002000000000022, 3), (0x2000000000000000000000002000000000000000000, 21), (0x100000000000000000000000100000000000000, 36), (0x20000000000000000000000020000000000000, 38), (0x8000000000000000000000008, 42), (0x44415488000000000000000044415488000, 43), (0x100000000c00000000000000100000000c00, 44), (0xaa0000000000000000000000aa00000, 45), (0x4000000000000000000000004, 46), (0x11100022000000000000000011100022000, 47), (0x20000000000000000000000020000000, 66), (0x1200000000000000000000001200, 81), (0x1000000000000000000000001, 89), (0x550000000000000000000000550000000000000000000000, 1), (0x10000000000000000000000010000000, 41), (0x1800180000000000000000001800180, 42), (0x88888110810000000000000088888110810, 43), (0x44400088008000000000000044400088008, 45)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 96)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 3000009 zs symsG zs (hk 3000009 zs)

theorem ori_ok {u ys} (h : NatRunT 96 true (goal 96) u ys) :
    NatRunT 96 true (goal 96) u (ori ys) :=
  pickMin_runT 3000009 ys h symsG ys (hk 3000009 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 3000009 zs) 10 0 (NN s)

def poolG : List Nat := [12398102926429281, 61936604687732832, 14649902713901154, 59685901164491919, 59682649824919651, 60809604194471008, 61983925515420856, 12395903904265400, 15775802619694177, 10146307363670116, 59682603702258784, 11272203020636258, 61934405679157344]

def Z (s : Nat) := bar 96 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 40 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_40 : ∀ i, 40 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 54 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 48 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 54 → Z 7 i = true := (range_split (range_split z7_0 (range_split z7_8 z7_16)) (range_split (range_split z7_24 z7_32) (range_split z7_40 z7_48)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_40 : ∀ i, 40 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 56 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_56 : ∀ i, 56 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_72 : ∀ i, 72 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 88 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_88 : ∀ i, 88 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 104 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_104 : ∀ i, 104 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_120 : ∀ i, 120 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 136 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_136 : ∀ i, 136 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 152 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_152 : ∀ i, 152 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 168 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_168 : ∀ i, 168 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 184 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_184 : ∀ i, 184 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 200 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_200 : ∀ i, 200 ≤ i → i < 208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_208 : ∀ i, 208 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_216 : ∀ i, 216 ≤ i → i < 224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_224 : ∀ i, 224 ≤ i → i < 232 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_232 : ∀ i, 232 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_240 : ∀ i, 240 ≤ i → i < 248 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_248 : ∀ i, 248 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_264 : ∀ i, 264 ≤ i → i < 272 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_272 : ∀ i, 272 ≤ i → i < 280 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_280 : ∀ i, 280 ≤ i → i < 288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_288 : ∀ i, 288 ≤ i → i < 296 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_296 : ∀ i, 296 ≤ i → i < 304 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_304 : ∀ i, 304 ≤ i → i < 312 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_312 : ∀ i, 312 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 328 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_328 : ∀ i, 328 ≤ i → i < 336 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_336 : ∀ i, 336 ≤ i → i < 344 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_344 : ∀ i, 344 ≤ i → i < 352 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_352 : ∀ i, 352 ≤ i → i < 360 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_360 : ∀ i, 360 ≤ i → i < 368 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_368 : ∀ i, 368 ≤ i → i < 376 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_376 : ∀ i, 376 ≤ i → i < 382 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 376 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 382 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 (range_split z8_8 z8_16)) (range_split z8_24 (range_split z8_32 z8_40))) (range_split (range_split z8_48 (range_split z8_56 z8_64)) (range_split z8_72 (range_split z8_80 z8_88)))) (range_split (range_split (range_split z8_96 (range_split z8_104 z8_112)) (range_split z8_120 (range_split z8_128 z8_136))) (range_split (range_split z8_144 (range_split z8_152 z8_160)) (range_split z8_168 (range_split z8_176 z8_184))))) (range_split (range_split (range_split (range_split z8_192 (range_split z8_200 z8_208)) (range_split z8_216 (range_split z8_224 z8_232))) (range_split (range_split z8_240 (range_split z8_248 z8_256)) (range_split z8_264 (range_split z8_272 z8_280)))) (range_split (range_split (range_split z8_288 (range_split z8_296 z8_304)) (range_split z8_312 (range_split z8_320 z8_328))) (range_split (range_split z8_336 (range_split z8_344 z8_352)) (range_split z8_360 (range_split z8_368 z8_376))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_8 : ∀ i, 8 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_24 : ∀ i, 24 ≤ i → i < 32 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_32 : ∀ i, 32 ≤ i → i < 40 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_40 : ∀ i, 40 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 56 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_56 : ∀ i, 56 ≤ i → i < 64 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_64 : ∀ i, 64 ≤ i → i < 72 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_72 : ∀ i, 72 ≤ i → i < 80 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_80 : ∀ i, 80 ≤ i → i < 88 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_88 : ∀ i, 88 ≤ i → i < 96 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_96 : ∀ i, 96 ≤ i → i < 104 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_104 : ∀ i, 104 ≤ i → i < 112 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_112 : ∀ i, 112 ≤ i → i < 120 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_120 : ∀ i, 120 ≤ i → i < 128 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_128 : ∀ i, 128 ≤ i → i < 136 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_136 : ∀ i, 136 ≤ i → i < 144 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_144 : ∀ i, 144 ≤ i → i < 152 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_152 : ∀ i, 152 ≤ i → i < 160 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_160 : ∀ i, 160 ≤ i → i < 168 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_168 : ∀ i, 168 ≤ i → i < 176 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_176 : ∀ i, 176 ≤ i → i < 184 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_184 : ∀ i, 184 ≤ i → i < 192 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_192 : ∀ i, 192 ≤ i → i < 200 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_200 : ∀ i, 200 ≤ i → i < 208 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_208 : ∀ i, 208 ≤ i → i < 216 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_216 : ∀ i, 216 ≤ i → i < 224 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_224 : ∀ i, 224 ≤ i → i < 232 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_232 : ∀ i, 232 ≤ i → i < 240 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_240 : ∀ i, 240 ≤ i → i < 248 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_248 : ∀ i, 248 ≤ i → i < 256 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_256 : ∀ i, 256 ≤ i → i < 264 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_264 : ∀ i, 264 ≤ i → i < 272 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_272 : ∀ i, 272 ≤ i → i < 280 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_280 : ∀ i, 280 ≤ i → i < 288 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_288 : ∀ i, 288 ≤ i → i < 296 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_296 : ∀ i, 296 ≤ i → i < 304 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_304 : ∀ i, 304 ≤ i → i < 312 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_312 : ∀ i, 312 ≤ i → i < 320 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_320 : ∀ i, 320 ≤ i → i < 328 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_328 : ∀ i, 328 ≤ i → i < 336 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_336 : ∀ i, 336 ≤ i → i < 344 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_344 : ∀ i, 344 ≤ i → i < 352 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_352 : ∀ i, 352 ≤ i → i < 360 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_360 : ∀ i, 360 ≤ i → i < 368 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_368 : ∀ i, 368 ≤ i → i < 376 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_376 : ∀ i, 376 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_384 : ∀ i, 384 ≤ i → i < 392 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_392 : ∀ i, 392 ≤ i → i < 400 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_400 : ∀ i, 400 ≤ i → i < 408 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_408 : ∀ i, 408 ≤ i → i < 416 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_416 : ∀ i, 416 ≤ i → i < 424 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_424 : ∀ i, 424 ≤ i → i < 427 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 424 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 427 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split z9_0 (range_split z9_8 z9_16)) (range_split z9_24 (range_split z9_32 z9_40))) (range_split (range_split z9_48 (range_split z9_56 z9_64)) (range_split (range_split z9_72 z9_80) (range_split z9_88 z9_96)))) (range_split (range_split (range_split z9_104 (range_split z9_112 z9_120)) (range_split (range_split z9_128 z9_136) (range_split z9_144 z9_152))) (range_split (range_split z9_160 (range_split z9_168 z9_176)) (range_split (range_split z9_184 z9_192) (range_split z9_200 z9_208))))) (range_split (range_split (range_split (range_split z9_216 (range_split z9_224 z9_232)) (range_split z9_240 (range_split z9_248 z9_256))) (range_split (range_split z9_264 (range_split z9_272 z9_280)) (range_split (range_split z9_288 z9_296) (range_split z9_304 z9_312)))) (range_split (range_split (range_split z9_320 (range_split z9_328 z9_336)) (range_split (range_split z9_344 z9_352) (range_split z9_360 z9_368))) (range_split (range_split z9_376 (range_split z9_384 z9_392)) (range_split (range_split z9_400 z9_408) (range_split z9_416 z9_424))))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_8 : ∀ i, 8 ≤ i → i < 16 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_16 : ∀ i, 16 ≤ i → i < 24 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_24 : ∀ i, 24 ≤ i → i < 32 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_32 : ∀ i, 32 ≤ i → i < 40 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_40 : ∀ i, 40 ≤ i → i < 48 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_48 : ∀ i, 48 ≤ i → i < 56 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_56 : ∀ i, 56 ≤ i → i < 64 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_64 : ∀ i, 64 ≤ i → i < 72 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_72 : ∀ i, 72 ≤ i → i < 80 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_80 : ∀ i, 80 ≤ i → i < 88 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_88 : ∀ i, 88 ≤ i → i < 96 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_96 : ∀ i, 96 ≤ i → i < 104 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_104 : ∀ i, 104 ≤ i → i < 107 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 104 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 107 → Z 10 i = true := (range_split (range_split (range_split z10_0 (range_split z10_8 z10_16)) (range_split (range_split z10_24 z10_32) (range_split z10_40 z10_48))) (range_split (range_split z10_56 (range_split z10_64 z10_72)) (range_split (range_split z10_80 z10_88) (range_split z10_96 z10_104))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 7 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 12) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z12 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 96 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 12) (h : NatRunT 96 true (goal 96) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := runT_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 8 fG 12 := mainG noRunFull

end Main

end PEqualNP.Outside.L_meta_8443_aux

theorem PEqualNP.Outside.L_meta_8443 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_8443_aux.Main.noCircuit
  exact ⟨C, hfan, by omega, hev⟩
