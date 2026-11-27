import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10662_aux

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
abbrev fG : BFn 9 := fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8)

def cSub_0 : Fin 9 → Sum Bool (Fin 8) := (fun i : Fin 9 => match i with
  | ⟨0, _⟩ => Sum.inl false
  | ⟨1, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩
  | ⟨8, _⟩ => Sum.inr ⟨7, by omega⟩)

namespace Sub_0
abbrev fG : BFn 8 := fun y : Fin 8 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.cSub_0 y)

def cSub_0 : Fin 8 → Sum Bool (Fin 7) := (fun i : Fin 8 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inl false
  | ⟨2, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩)

namespace Sub_0
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.cSub_0 y)

def cSub_0 : Fin 7 → Sum Bool (Fin 6) := (fun i : Fin 7 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨4, _⟩ => Sum.inl false
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩)

namespace Sub_0
abbrev fG : BFn 6 := fun y : Fin 6 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 7) (_ : SCleanL 6 gs)
    (_ : ∀ p, p < gs.length → 6 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 6 + p ∈ g.inputs)
    (_ : ∀ x, val gs 6 o x = fG x) :
    ∀ a, a < 6 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 1, 4, 4, 32, 33, 33, 33, 33, 7, 7, 7, 14, 3, 3, 3, 5, 5, 5, 6, 6, 12, 16, 16, 8, 8, 32, 48, 48, 48, 48, 26, 26, 26, 14, 18, 18, 18, 24, 24, 24, 10, 10, 12, 2, 32, 14, 12, 9, 17, 20, 36, 36, 35, 37, 41, 49, 15, 23, 39, 15, 11, 19, 35, 13, 21, 37, 22, 38, 13, 20, 17, 9, 40, 40, 50, 56, 52, 49, 30, 27, 58, 30, 22, 19, 50, 28, 25, 56, 11, 42, 28, 34, 34, 46, 44]

def xsG : List ℕ := [0x29141a7ffe300000007efe3, 0x763f8818fe20563f8018fe00, 0xc84ca07f1e5cc804003f1e0c, 0xcfc797213281cfc783201000, 0x9fff8ca450601fbf8c00000, 0xf5227e1489f820007c0001f0]

theorem rowsG_len : rowsG.length = 96 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => ((fun x : Fin 6 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 48 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 48 false (fG, false) = goal 48 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 48 zs &&& lo 48) ≠ lo 48 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 7, ¬ NatRunT 48 false (goal 48) s xsG) :
    ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 48 false (goal 48) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 7, ¬ NatRunT 48 false (goal 48) s xsG) :
    ¬ HasCircuitSize 6 fG 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 48 false (encT rowsG 48 false (fG, false)) s'
      (ws.map (encT rowsG 48 false)) :=
    RunT.map (encT rowsG 48 false)
      (fun a => encT_inv rowsG 48 rowsG_len false a)
      (fun a b => encT_and rowsG 48 rowsG_len false a b)
      (fun a b => encT_or rowsG 48 rowsG_len false a b)
      (fun a => encT_tag rowsG 48 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x4ee8810
  | 6, 0 => 0xfb73b432b0513d145dff4e9a40c414e625be566e1a0a8cad17cd0c28
  | 7, 0 => 0x25be566e
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xf6000735baf9fe04073fffffc84ca07f1e5cc804003f1e0c763f8818fe20563f8018fe00cfc797213281cfc783201000fc6ea87f9e7cc804003f1e0cf5227e1489f820007c0001f009fff8ca450601fbf8c00000029141a7ffe300000007efe3
  | 0, 1 => 0xadd81eb7607dfff83fffe0f74220810882000000000000089c077e701dfa9c07fe701fffe7fa87ffe7cde3f803ffe0c303868decd7e30387cdfefff
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105
  | 6, 0, 0 => 0xc46510646210b646a21069462106465210665821067465206
  | 7, 0, 0 => 0x4652106
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 28
  | _ => 0

def idWidth : Nat := 4

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 96 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3fffff0000003fffff, 22)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 48)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 48 false (goal 48) u ys) :
    NatRunT 48 false (goal 48) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 4 0 (NN s)

def poolG : List Nat := [34912805654151217, 5642703390949449, 5639428501456947, 23649424669459504, 34912798139008050]

def Z (s : Nat) := bar 48 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 48 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : NatRunT 48 false (goal 48) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := runT_len h
    change 6 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 6 fG 7 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 4)

def perm_4 : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩

def cu_4 : Fin 7 → Sum Bool (Fin 6) := fun i => cSub_0 (perm_4 i)

theorem hperm_4 : ∀ y : Fin 6 → Bool, fG (substIn cu_4 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_4 : ∃ y y' : Fin 6 → Bool, fG (substIn cu_4 y) ≠ fG (substIn cu_4 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 7, ∃ y : Fin 7 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 9) (hcl : SCleanL 7 gs)
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
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 1, 4, 4, 64, 7, 7, 7, 7, 14, 21, 21, 21, 21, 28, 81, 81, 81, 81, 3, 3, 3, 3, 5, 5, 5, 6, 6, 6, 12, 17, 17, 17, 20, 20, 20, 65, 65, 65, 65, 80, 32, 32, 8, 8, 64, 42, 42, 42, 42, 14, 56, 56, 56, 56, 28, 112, 112, 112, 112, 34, 34, 34, 34, 40, 40, 40, 10, 10, 10, 12, 48, 48, 48, 24, 24, 24, 96, 96, 96, 96, 80, 2, 2, 16, 64, 14, 14, 28, 28, 12, 80, 9, 33, 36, 68, 68, 15, 23, 39, 71, 15, 23, 29, 53, 85, 29, 83, 85, 89, 113, 11, 19, 35, 67, 13, 37, 69, 22, 38, 70, 13, 19, 25, 49, 22, 52, 84, 67, 69, 73, 97, 84, 36, 33, 9, 72, 72, 46, 58, 43, 106, 46, 58, 60, 57, 120, 60, 114, 120, 116, 113, 38, 50, 35, 98, 44, 41, 104, 26, 11, 74, 44, 50, 52, 49, 26, 25, 88, 98, 104, 100, 97, 88, 18, 66, 18, 66, 30, 78, 30, 92, 76, 82]

def xsG : List ℕ := [0x10a1248210cf1e3ffffe30000000000000f1c3ffbde3, 0x9fc24b8f10fc0125c7887e00cc0038f007c0001c7803e0, 0x7c081411494432e3f817ffc7c000400084000e3f807fec, 0x7c25c7f02fff840a08a4a217c01c7f00ffd80020004200, 0x1b561f882ff8810fc417fc40b121f800ff8010fc007fc00, 0x1e3c7ffffc68509241086001e387ff7bc60000000000, 0xeabf0248f4231f81247a118823e0000f0021f000078010]

theorem rowsG_len : rowsG.length = 184 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 92 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 92 true (fG, false) = goal 92 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 92 zs &&& lo 92) ≠ lo 92 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 92 true (goal 92) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 92 true (goal 92) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 92 true (goal 92) s xsG) :
    ¬ HasCircuitSize 7 fG 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 92 true (encT rowsG 92 true (fG, false)) s'
      (ws.map (encT rowsG 92 true)) :=
    RunT.map (encT rowsG 92 true)
      (fun a => encT_inv rowsG 92 rowsG_len true a)
      (fun a b => encT_and rowsG 92 rowsG_len true a b)
      (fun a b => encT_or rowsG 92 rowsG_len true a b)
      (fun a => encT_tag rowsG 92 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 3
  | 6 => 10
  | 7 => 56
  | 8 => 28
  | 9 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x9f9296438c0c5c9566b1ff72
  | 6, 0 => 0xc9e3db1a97969a138110cf2c74d48ebb36966ba3361013a634ddd62a1f1c643f1905bf3315838405
  | 7, 0 => 0xfe8c5db3f922c04df4125de5ec8b4e83ebfbf30eea435d95e84f060adc87f7f6d9c86e28d4e076c9cddbf15fcae90b70c3554725a9bc2226a4793ea1a38481679bd23cc79b11bf01894fec9181e8f1757bc781a07ad11635784c1874748412296d38d6ff5bdb843659d1c9bc51c206d150109b504fef076d4e0147784cfc217e451886904259bb873c8132113b548ab2391978de36c3ffe434ddd62a3316698331aa598e2f9ef1bd2a3a1626283b39e31ce90b2819bf26b917a2d2a4154bcab311cb4e400e5e02dc0e0a31ca06b7e74d05ded1770533dc7602ebeb88024b1535
  | 8, 0 => 0xf922c04deaf7a9e0ea435d95d9c86e28d30d0546ccae4168b728979a8db3d0f3761e44f575ee05ff73e45deb65affa3860f2a7415bdb8436533b47c74df0285b4ceb6a41391978de2c0906a12ae6320821aad4611dffdf601511387113cfd60211cb4e4010e5f2850ead47290b8e3e57
  | 9, 0 => 0xf922c04d
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x7fe52f4dacf619f3fe8fffe3e00020004200071fc03ff600078f1fffff1a14249042180078e1ffdef1800000000000021424904219e3c7ffffc60000000000001e387ff7bc6eabf0248f4231f81247a118823e0000f0021f0000780103e12e3f817ffc2050452510be00e3f807fec00100021001f02050452510cb8fe05fff1f00010002100038fe01ffb13fbcfdfffff8d2ebae92b8c003c70ffef78c00000000009fd2ebae92b8cf3f7ffffe30000000000000f1c3ffbde3
  | 0, 1 => 0x4fe125c7887e0092e3c43f0066001c7803e0000e3c01f005503f6dc2f7381fb6e17b9df707fffc3ff783fffe1ffbdfffe979fe9fe3f4bcff4ff11dfc071fe0fc3e038ff07e0603db575ef57fedabaf7abffffffffffffffffffffffff41fbf5f75b5de68e03f4001c1fffdfffbdfff8e03fc009a7f092a2842a00495142150000000000000000000000001ffcf9ff47fff0a5e9b59ec2f8038fe01ffb00040008400ffff4acaf4ab1fa5657a558823e0000f0021f000078010
  | 0, 2 => 0x7f53e3fc1fffc2858656590be00e3f807fec001000210020f68e03f4001efd7dd6d77a0ff8e03fc009fff7ffef7fdeafbf9e5ff17fdfcf2ff8bfe67ff8e1ff07fffc70ff83e603db470ef03feda387781ff33ffc70ff83fffe387fc1f7ffffd657fd58ffeb2bfeac599ffc007fc10ffe003fe083ff870e00000e5ebdb6fbde7ff871e00210e7ffffffffff6ac3f105ff1021f882ff8816243f001ff0021f800ff800ffef5edb7def30e1c00001cfffffffffffff0e3c00421c
  | 0, 3 => 0xf5ebffffe77af5fffff3800f1c3ffbde378e1ffdef1800408092084120404904208000000000000000000000013fbcfffffff8d2ebaf92fcc19bc77ffeff8c0038f007c00002080f10fc000082000800000000f003c000000000003e044a98a5aa5b75fc5bffebe00020004200071fc03ff60007af5fffff3b16a6b96a9c0078e1ffdef1800000000016ae3f14dff30b1f8a6ff9856243f001ff0021f800ff8007c081515495433e7ff9fffc7c000400084000e3ff87fec
  | 0, 4 => 0x454f1f3ffffe34a8cb248c3000f1c3ffbde300000000002d5ffe32bfea063f105ff102c4ffe003fe0043f001ff000f85b8fe0dfff2d16516d672f8038fe01ffb00040008400fd69f882ff8812fd617fd58b121f800ff8010fc007fc003e1ffffffffff62d4d72d53be0ffffffffef00100021000001011c0bff000000000000000001c01ef000000000001d57f06d1ec673f1659fd673047c0001e0043e0000f0020683f3e7fffff6c509261086001e387ff7bc60000000000
  | 0, 5 => 0xc1a1ae5aa342849208430000000000000000000000022a08082040800404102040000000000000000000000001fd7e2cb3face7fc7f8ffff9fc7c0801f0843fc7f0ffff868080000400012812012118000000000000000000000007ff3e7ff9fffc297e7d67f0be60e3ff87fec001e3c21f0070010e0003f00000020088030000e0001f0000000008016ad3f927ff9861f9a2ff9896243f001ff0021f800ff800ffe74bcf34ff0525c7a87e00cc0038f007c0001c7803e0
  | 0, 6 => 0x3e1af3fa57ffe60d0d72d51be00e3f807fec00100021002ff8fea2bfea047f515ff502c487e003fe0043f001ff000d06b46c94c679e3c7ffffc60000000000001e387ff7bc67c35e7f4afffcf1e3ffffe37c01c7f00ffd8f1e3ffffe300004090010842050452510800000000000000000000001a0960d8098ce1028229288400000000000000000000001d57e7cfffffeffa36cf633d047c70ffef7cfe0000f0020001e0048f42008000040000001e0000f00000000000000
  | 0, 7 => 0x1011c0bff000000000000000001c01ef03aafe8db3d8cf7e7cfffffee08f80003c0087c70ffef7ccf85bafe2dfff6dd7f16fffaf8038fe01ffb01c7f00ffd87c000410094400020804a207c0004000840000200042000000029a802a70014d40153a66003ff803ef001ffc01f7a7f49aebe4bf124d75f25f8833000e3c01f000071e00f81d57e44d9ec66bf226cf6335047c0001e0043e0000f00209fca5f9f59fc2165d7897e40cc0038f007c0001c7803e0
  | 0, 8 => 0x7c18b535cb54fffffffffff7c00040008400ffffffffef3e0f1e3ffffe3d79fd2bfff3e0f1e3ffffe3071fc03ff61a0940900908c10000080000000000000000000000000013fa5d75f25f99e7ffffffc61980071e00f81e3bfff7fc60008141149442040900108400000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x104820c0144030e182a8406080805
  | 6, 0, 0 => 0x100c1060a298804060830a6100c10f0c158703041828a61a0c1060a298203040428a6080c1060a29860406083056080c3860a298584061828a6
  | 7, 0, 0 => 0x22101821e802b91080c10f3e79c98e06087860ae442030474e057221019b1e182b91163818f0c15c884060879a0ae64203043c3057284420304182b91080cc0f0c15c203043c30514e44217043c30572844b0404182b9528101820c15ca13080c1060ae40911080c10f7
  | 7, 0, 1 => 0x52101821e182b9022101821e19c88406094060ae5088e0608305722101821e9c2b9022582021e19d30406087860ae409840608786722112821e182ba4080c10f0c15c811161018f0ce44223043d105722381821e182b91420c10f0c15c004060830514c4c203041828a7
  | 7, 0, 2 => 0x222c2031e182b91080c1380c15c88b2c107860ae4c584063c30572211b821e182bb6080c10f0c15c88406087866ae44234043c33372044703043c339108087860ac9c8b106087b00ae44203043c2af722341820c1573ad220c7860ab1c88456095060ae40a11080c1067
  | 7, 0, 3 => 0x2211ebc1e182b91080c10f0c15c20304ec7860ae54203043c305726341821e182b93080c10f0c15c8840609d060ae45c83043c3057
  | 8, 0, 0 => 0x2210182823c305800408840608786722101821e182ae822101821e182c082210703043c30580044703043c3057222c203043c30585a44203043c305822101821e1829e822101821ea8305822101821e182bf822101821e7c305800508840608305722f8203043c30582234203043c305822101821e18e058
  | 8, 0, 1 => 0x44203043c30572844203043c3058004c203043c30570044584063c305722101c4043c30582211583043c30582212183043c305822101821e182c282210182783c305822101821e1980582211e83043c30582444203043c3058
  | 9, 0, 0 => 0x44203043c3057
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 39
  | 6 => 46
  | 7 => 53
  | 8 => 60
  | 9 => 53
  | _ => 0

def idWidth : Nat := 7

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 185 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x1ffffffffff0000000000001ffffffffff, 41)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 92)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 92 true (goal 92) u ys) :
    NatRunT 92 true (goal 92) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 7 0 (NN s)

def poolG : List Nat := [16903902602555528, 51796909478736990, 51807943332602031, 51796903035236445, 16894007080746159, 10138656991966300, 16899548622452831]

def Z (s : Nat) := bar 92 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 48 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 56 → Z 7 i = true := (range_split z7_0 (range_split z7_24 z7_48))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 28 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 24 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 28 → Z 8 i = true := (range_split z8_0 z8_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 92 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRunT 92 true (goal 92) s xsG) : False := by
  have hmin : 6 ≤ s := by
    have hl := runT_len h
    change 7 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 7 fG 9 := mainG noRunFull

end Sub_0

def cSub_1 : Fin 8 → Sum Bool (Fin 7) := (fun i : Fin 8 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inl false
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩)

namespace Sub_1
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.cSub_1 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 9) (_ : SCleanL 7 gs)
    (_ : ∀ p, p < gs.length → 7 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 7 + p ∈ g.inputs)
    (_ : ∀ x, val gs 7 o x = fG x) :
    ∀ a, a < 7 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 2, 2, 4, 4, 8, 8, 7, 7, 14, 14, 44, 44, 67, 7, 7, 14, 14, 44, 44, 67, 3, 6, 12, 3, 3, 6, 6, 12, 12, 40, 5, 5, 10, 10, 24, 24, 66, 5, 5, 10, 10, 24, 24, 66, 1, 64, 64, 16, 16, 32, 32, 81, 81, 112, 112, 56, 56, 67, 81, 81, 112, 112, 56, 56, 67, 65, 80, 48, 65, 65, 80, 80, 48, 48, 40, 17, 17, 96, 96, 36, 36, 66, 17, 17, 96, 96, 36, 36, 66, 40, 9, 18, 34, 20, 68, 9, 72, 15, 71, 15, 46, 46, 60, 71, 23, 39, 30, 78, 45, 108, 75, 35, 22, 76, 11, 19, 38, 70, 13, 28, 42, 13, 69, 11, 42, 28, 88, 70, 21, 37, 26, 74, 25, 26, 74, 33, 68, 72, 20, 18, 33, 34, 113, 83, 113, 120, 120, 60, 83, 85, 89, 116, 114, 57, 58, 99, 73, 84, 50, 97, 69, 88, 82, 49, 52, 104, 49, 19, 97, 104, 52, 38, 82, 21, 25, 100, 98, 37, 100, 98, 41]

def xsG : List ℕ := [0x24c39334e3a1261c99a71d081830661c3020c18330e181, 0x1231089a2150d9327b9f7c32040002040013260f73e786, 0xd582241500a074de67ffcc1830000000000c1bccfdf98, 0x2084442c9c04f8f78cf8f70c00080183000f1e708f1e60, 0xe9bccfff986ac1120a8050183799fbf30c1800000000, 0x3f1ef19f1ee104222164e025e3ce11e3cc0000400c1800, 0x1b264f73ef86918844d10a8264c1ee7cf0d02000102000]

theorem rowsG_len : rowsG.length = 182 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 91 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 91 false (fG, false) = goal 91 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 91 zs &&& lo 91) ≠ lo 91 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 91 false (goal 91) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 91 false (goal 91) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 91 false (goal 91) s xsG) :
    ¬ HasCircuitSize 7 fG 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 91 false (encT rowsG 91 false (fG, false)) s'
      (ws.map (encT rowsG 91 false)) :=
    RunT.map (encT rowsG 91 false)
      (fun a => encT_inv rowsG 91 rowsG_len false a)
      (fun a b => encT_and rowsG 91 rowsG_len false a b)
      (fun a b => encT_or rowsG 91 rowsG_len false a b)
      (fun a => encT_tag rowsG 91 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 7 => 13
  | 8 => 9
  | 9 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 7, 0 => 0x3dec5716384e16a533fbae0f20997a471bf60b0119af0922159891db1251a8f80ef79ef50eb36e930eacf12f04d13c6e04338978
  | 8, 0 => 0x4df0366f3f33678f3641912133fbae0f2f867f212121e6691bf60b0107ab5ab705a50612
  | 9, 0 => 0x33fbae0f
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x9366c23041e5b9deecbbd5f66cf8460c3cbf7fffbf7ffff1ef19f1ee104222164e025e3ce11e3cc0000400c1800821110b27013e3de33e3dc300020060c003c79c23c7981b264f73ef86918844d10a8264c1ee7cf0d0200010200048c42268854364c9ee7df0c810000810004c983dcf9e18d582241500a074de67ffcc1830000000000c1bccfdf9827a6fb3ffe69af25596e234060de67efcc3060000000024c39334e3a1261c99a71d081830661c3020c18330e181
  | 0, 1 => 0x1a4a32dc4612904482a014000000000000000000000024c7d73cffa5feff9dffff0c1838679f302fdff3bfffe18200009200008052228054200000000000000000000002dcef765deaf26cd846083cdfbfffdfbffecd9f08c187903843983847bef777a6c7f6870c7b870cffffeffcf9ffc0e9bccfff986ac1120a8050183799fbf30c18000000007deeef4d8fec1c21cc1c23cfffdff9f3ffc3863dc3867ff1643300067953eedf57fafe7c866040cf3e7ffffffff
  | 0, 2 => 0x40000000000401887df00000000000000000310f1e03f1ef5bf9ee594a225f4e225e3ce11e3cc0000400c18006fbffffffe7bef255b6e2b49f3dfffffcf70e0004080000200c43ef8000800000000000018878f000000000000048d532eab55366c9ff7df8c810000810004c983dcf9e1b6e39b36e3a1b71cd9b71d0a1c30661c3030e18330e181cad532faf553e7dffffffcf810200e1c007cf9ffffff9800000080000d832089874000000000000030600030600
  | 0, 3 => 0xca9f76fabfd7e2c866000cf9f3fffffffffcf90cc0819ff5ef3df5eeb076fe77ffce5e3ce11e3cc00c1fccfdf9800111082301242001340080000000000000000000000012200812210091004091080204000204001020001020004be6f37fff63efcdee7ff1c870de6fffcc7cf83dcf9e1b6f39bbee3f1ff3efbbf7d3a1c30661c3033e78f73e787
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x58a4189407316a31028e629062501cc524c4a03b0c5209407314921894f13104a041cc520c407b99c41894d76148b1280e832483101d06394620398a4188207
  | 8, 0, 0 => 0xe98a4189408e18a4189408314831281b8018a418940731483d0940831499189408030c52094073149818940831483128178
  | 9, 0, 0 => 0x18a4189407
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 7 => 39
  | 8 => 44
  | 9 => 39
  | _ => 0

def idWidth : Nat := 5

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 182 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xfffffffffff800000000001fffffffffff, 45)], [(0x204200408202040080000084084008104040801000001, 1), (0x102000000000000000000002040000000000000000000, 3), (0x8000008000000000000000100000100, 5), (0x200000200000000000000004000004000, 6), (0x8000000000000000000000100000000000000000, 22), (0x10210050228000000000000204200a0450, 42), (0x26000c020000000000000004c001804, 43), (0x810862811400000000000010210c50228, 44), (0x400000400000000000000008000008000, 50), (0x4000004000000000000000080000080, 51)], [(0x408010000011021002041008100200000220420040820, 1), (0x810000000000000000000010200000000, 3), (0x1000001000000000000000020000020000000000000, 5), (0x40000040000000000000000800000800000000000000, 6), (0x100000100000000000000002000002000, 39), (0x8000008000000000000000100000100000, 40), (0x408431408a00000000000008108628114, 46), (0x980030080000000000000013000601, 47), (0x204200a0450000000000000408401408a, 48), (0x40000000000000000000000800000, 67)], [(0x100004000204110204100002000080004082204082, 1), (0x300180000000000000000006003000000000000, 2), (0x2001000081000000000000040020001020000, 3), (0xc1840000000010000010081830800000000200000201, 4), (0x4000000000000000000000080000000000000000, 23), (0x1000080000000000000000020001000, 40), (0x60030000000000000000000c0060, 41), (0x2800040400000000000000050000808, 42), (0x60c00400000000000000000c1800800000, 43), (0x20000020000000000000000400000400, 48), (0x800000800000000000000010000010000, 49)], [(0x40822040820000800020000810440810400010000400, 1), (0x1800c00000000000000000030018, 2), (0x200010200000000000010004000204000000000000200, 3), (0x200000201060c20000000004000004020c184000000, 4), (0x8000008000000000000000100000100000, 41), (0x100000100000000000000002000002000, 42), (0x1830010000000000000000030600200000, 47), (0x50000808000000000000000a000101, 48), (0x60030000000000000000000c006, 49), (0x80004000000000000000001000080, 50), (0x20000000000000000000000400000, 68)], [(0x902004102080000200000012040082041000004000000, 1), (0x80c000000060c01264c30010180000000c18024c986, 2), (0x80040000000000000000001000800000000000, 3), (0x1800000180000000000000030000003000000, 4), (0x40020000000000080000000800400000000001, 5), (0x10000000000000000000000200000000000000000, 6), (0x2000000000000000000000040000000000000000, 24), (0x2000000000000000000000040, 39), (0x4082000000000000000000081040000000, 40), (0x2040000000000000000000040800000000, 42), (0x8000000000000000000000100000000000, 43), (0x100000000000000000000002000000000, 44), (0x4080000000000000000000081000, 46)], [(0x40000004810020810400000800000090200410208, 1), (0xc18024c9860040600000001830049930c0080c000000, 2), (0x400200000000000000000008004, 3), (0x3000000000000000c000000600000000000000180, 4), (0x10000000200100000000000200000004002, 5), (0x80000000000000000000001000000, 6), (0x8100000000000000000000102000, 44), (0x80000000000000000000001000000000, 46), (0x2000000000000000000000040000000000, 47), (0x408000000000000000000008100000000, 48), (0x204100000000000000000004082000000, 50), (0x80000000000000000000001, 51), (0x10000000000000000000000200000, 69)], [(0x800000000000000000000010000000, 2), (0x400000000000000000000008, 3), (0x54a80054a88000000000000a95000a9510, 44), (0x2a55132a55100000000000054aa2654aa2, 46), (0x60000000000000000000000c000000, 47), (0x80000200000000000000001000004, 48), (0x80000000000000000000001, 49), (0x40000000000000000000000800000, 67), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)], [(0x3060000000000000000000060c0000000000000000000, 2), (0x400000400000000000000008000008000, 5), (0x4000004000000000000000080000080, 6), (0x80000000000000000000001000, 42), (0x18300078318000000000000306000f0630, 43), (0x150004010000000000000002a000802, 44), (0x70000000000000000000000e00000, 45), (0xa80000080000000000000015000001, 46), (0x60000000000000000000000c, 47), (0x8000008000000000000000100000100, 50), (0x200000200000000000000004000004000, 51), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)], [(0x10000000000408014488000200000000008100289100, 1), (0x400000000000000180000088000000000000003000001, 2), (0x80001000204000204100001000020004080004082, 3), (0xc0040000000000000000001800800000000000, 4), (0x800000000000000000000010000000000000, 5), (0x4000000000000000000000080000000000000000, 23), (0x1000000000000000000000020, 40), (0x60c38000000000000000000c1870000000, 41), (0x100040002400000000000002000800048, 43), (0x8000000000000000000000100000000000, 44), (0x2040000000000000000000040800, 47), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)], [(0x81084891140080000000001021091222801000000000, 1), (0x2000010000000000000000040000200000, 2), (0x40840040800000100008080810800810000002000101, 3), (0x60010000000000000000000c002, 4), (0x20000000000080004000000400000000001000080, 5), (0x10000000000000000000000200000000000, 6), (0x2000000000000000000000040000000000000000, 24), (0x2000000000000000000000040000000, 39), (0x2000000000000000000000040, 40), (0x8100000000000000000000102000, 43), (0x4000000000000000000000080000000000, 46), (0x40000000000000000000000800000000, 47), (0x60c00000000000000000000c180000000, 49), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)], [(0x2000000000000000000000040000000000000000, 1), (0x30000011830000000000000600000230600000000, 2), (0x20000400000000000000000400008000000, 3), (0x200000000000000000000004, 4), (0x80000080000000000000001000001000000000000000, 5), (0x800000800000000000000010000010000000000000, 6), (0x8000008000000000000000100000100000, 39), (0x100000100000000000000002000002000, 40), (0x20000000000000000000000400, 46), (0x60c011e0c90000000000000c18023c192, 47), (0x10000000000000000000000200, 48), (0x380000000000000000000007000000, 49), (0x80000000000000000000001, 50), (0x20000000000000000000000400000, 68), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)], [(0x421000a00000000000000008420014, 1), (0x2000000000000030000000040000000000000600, 2), (0x4020004010408200800000080400080208104010000, 3), (0x100000100020000000000002000002000400000000000, 4), (0x10000000204100000000000200000004082000000, 5), (0x80000000000000000000001, 6), (0x100000100000000000000002000002000, 41), (0x8000008000000000000000100000100000, 42), (0x1020000000000000000000020400000000, 46), (0x810000400000000000000010200008000, 48), (0xc000000000000000000000180, 49), (0x200100000000000000000004002, 50), (0x80000000000000000000001000000, 51), (0x10000000000000000000000200000, 69), (0x200000000000000000000004000000000000000, 1), (0x1000060000000000000000020000c0000000000000, 2), (0x81000100080020000020001020002001000400000400, 3), (0x800000800000000000000010000010000, 4), (0x40800000000000000000000810000000000000000000, 5), (0x8000000000000000000000100000000000000000, 22), (0x4000000000000000000000080000, 40), (0xc0800000000000000000001810, 41), (0x4080402001000000000000081008040020, 42), (0x1800000000000000000000030000000, 43), (0x2042260002200000000000040844c00044, 44), (0x400000000000000000000008, 46), (0x1000001000000000000000020000020000, 48), (0x10000010000000000000000200000200, 49)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 91)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 91 false (goal 91) u ys) :
    NatRunT 91 false (goal 91) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 5 0 (NN s)

def poolG : List Nat := [12392605317950600, 58554505795563614, 14646602009504865, 58554503647032412, 37169048733229147]

def Z (s : Nat) := bar 91 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 13 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 9 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 9 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 91 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRunT 91 false (goal 91) s xsG) : False := by
  have hmin : 6 ≤ s := by
    have hl := runT_len h
    change 7 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 7 fG 9 := mainG noRunFull

end Sub_1

def taggedFn (a : ℕ) : Bool := (a == 1) || (a == 2) || (a == 3)

def perm_1 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_1 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_1 i)

theorem hperm_1 : ∀ y : Fin 7 → Bool, fG (substIn cu_1 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_1 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_1 y) ≠ fG (substIn cu_1 y') := by decide +kernel

def perm_2 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨4, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨0, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨6, by omega⟩

def cu_2 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_2 i)

theorem hperm_2 : ∀ y : Fin 7 → Bool, fG (substIn cu_2 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_2 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_2 y) ≠ fG (substIn cu_2 y') := by decide +kernel

def perm_3 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_3 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_1 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 7 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_1 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 8, ∃ y : Fin 8 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 11) (hcl : SCleanL 8 gs)
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
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_1.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 1, 2, 2, 8, 32, 64, 64, 64, 41, 41, 41, 41, 41, 84, 84, 84, 84, 84, 112, 112, 112, 112, 112, 224, 224, 15, 15, 15, 15, 3, 3, 3, 5, 5, 5, 5, 6, 9, 9, 9, 10, 10, 10, 33, 33, 33, 33, 40, 40, 68, 68, 68, 68, 16, 16, 4, 4, 8, 32, 128, 128, 128, 56, 56, 56, 56, 56, 131, 131, 131, 131, 131, 161, 161, 161, 161, 161, 224, 224, 30, 30, 30, 30, 20, 20, 20, 18, 18, 18, 18, 6, 24, 24, 24, 12, 12, 12, 48, 48, 48, 48, 40, 40, 130, 130, 130, 130, 224, 6, 192, 14, 17, 65, 34, 66, 72, 34, 65, 66, 72, 43, 45, 57, 105, 169, 85, 86, 92, 116, 212, 113, 114, 116, 120, 240, 225, 226, 31, 47, 79, 143, 19, 35, 67, 21, 37, 69, 133, 70, 25, 73, 137, 42, 74, 138, 35, 37, 49, 97, 42, 104, 69, 70, 76, 100, 17, 144, 36, 132, 136, 36, 144, 132, 136, 60, 58, 57, 184, 120, 147, 135, 139, 163, 195, 177, 165, 163, 169, 225, 240, 228, 31, 62, 158, 94, 21, 52, 148, 19, 50, 146, 82, 134, 25, 152, 88, 44, 140, 76, 52, 50, 49, 176, 44, 168, 146, 134, 138, 162, 232, 38, 200, 46]

def xsG : List ℕ := [0x1010913ff20044f1dffd087e43000000003ff00000f1dffc003e03, 0x1af080f8f09f100091e21fe1082acaf000f8f01f000000e21fc00000c, 0x1a247887f8420ab3c203e3c27c400a003887f0000033c003e3c07c000, 0x1d4c3f00f104fc4130fc03c413f1080c3f00f000f84030fc03c003e10, 0x13c77ff421f90c0404244ffc801003c77ff000f80c0000000ffc000, 0xb8fc8122fe8f8923f2048bfa3e2410fc0000fe0f8803f00003f83e20, 0x50024408e108003e84a913ffd1da50000000c000003c000003ffc1c0, 0x5fa12a44fff476800910238420005f000000fff07000000003000000]

theorem rowsG_len : rowsG.length = 224 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => ((fun x : Fin 8 → Bool => x i), taggedFn i.val)).map
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
    ¬ HasCircuitSize 8 fG 11 := by
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
  | 6 => 2
  | 7 => 43
  | 8 => 275
  | 9 => 247
  | 10 => 19
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0x917835cf8928178c
  | 7, 0 => 0xf4d40070dea195aeda0ecc0dd8e32848c696e465bf12d9b4beccdfd9be4f55dbba92fd4ab4f004d2aabc429fa4f671d49ecda29d7e2896617dcc75707485c68f71c3fd406e2098a16973defd6281412d6055b1205ea6c3225e341e355c2f55225b84597853b7aa7f4ec8ffdd4895862e4682c683427268483a0d182234da1a1d2dcc7aae2c406b351f3e5e7a1f15d11d1bb07d0d197d353118e3cd871092f70d0a60f377069de7b20272b0da
  | 8, 0 => 0x1b53e7981b0ef6991ae0e65a1ad5f96f1a8e59c019ecb2cb196d28fa18d387961895a0a017eba34617e7baff17da454b179c5fda173d91b61723cf8f16e8816a1677999616255ac315ff9b7f15a6d754158eb62b14f1e05014cc31fc14a0f4071492b79313df6a701345cfc712dcd18312d0374112c4dd9b12809fff11edc75c1128823510755617104bd5c90f452cbe0e4d0a9c0dcd151e0dc9cead0d37288b0d2ca7bd0ce8e1b00ce557830caf659a0b0341d309c541d5095b42da0942d22106b068b70697d19005df01fe056e853e0550031d04de4933040db23d03be6ed1039a6d1602e6280a02cb261401c8e64b00f9873a004b6c9700359bca001b928a
  | 8, 1 => 0x41b03ae54136b301409293e43f3719123eb09b863eaf1aaf3e8ea5113d3061a13d14277d3ce334d63c7b1c933c3c8c363c1bc2f03b7ee23b38f28f8f38345c80378347d136f2d7813627cec4360a1f4735c04d3035959f1a338edcaf32a1bfe4325db96231e8971630ee71a42fb2757a2eece7a22e63adc12e3974142df8c8192d4a63e32cd9a2cc2cd662452c003be22b96bd9a2b1b82bf2ae8e7912ac207202a520da4299209802936367429060f1928e0fd652870a89c27829d9e269561972687f891265b34f626146b7025f6a5e223e1ea5b2293eb252221c49b210a98c620451a581f7a66dc1eb33fd21da332de1cb7fbd91ca0a8ea1c2470f61b7653df
  | 8, 2 => 0x6b5fb1336ad0e5b96a9bc5c36a92886f69c1fd3b693b57d667fde59567add9cc6606d1e0653df76665384ae864a078696454d64c641390215fad9e6b5eb549415d9d73ee5d7d62575d64bc295d43730e5d30d66c5cfda1045ce216375cda5d445cb976e75c4209285adaabdd5ab2cf745908f86158a4cdb6589c1c4857d698e55794e89e577fae1556e500b456cdd262565e1e3e54fb546854ee5b0654bb1c4e544f8c0a541b731353c362cb510fb1d050c5915c5068c1ae504d45f64ff9b3f94f6124324effc75b4ea1b0c04e6c60124d511d714c210dd64c124d894c0556a94be1d5b3487bcf6246d4de6b466d3d2e45d918e8457f85be456596ad428672d2
  | 8, 3 => 0xc46cb996c3c59b82c02598acbe0a7ea3bcc30b1ebb75dbc9bb6d7209b9b4b189b81b7899b2fcf8afb1061af3b0a8cca0b0282fc7af2536d9ad938cedacd767bdaad2130aa2c67dc49f5f17dc9d8861f69b339d7a9aa8e7dc9a6387b79750e34e961e604d94b9f418939ac44792e8bc90908fb7bc902ebf9c8febd1f38fc662878f59d0ef8e3d6ab08dfef0908d6ac3d28cc249938c91842a8c91259e8c2983c68968702788bcae4a8706d2e384e539fe839c80b7834c55f8829b257c7f2f739b7ce49d6879248407787e697277f130f777a7bd85750de19d74b618d473bd405c7126cf4c70cfeb4a6f82eb656f39d30b6f1834526d8a19e16c8d8e016be631f9
  | 8, 4 => 0xf62b6361f25b0b59f100582aef93f551e6570791e35e59dfe32df6ace1ef4e7cdc6eb472da053a56d9841fead5be4040d4d0ef19cf4bbeafcf015b75ce788d55cc25f102c810ec1dc7970065
  | 9, 0 => 0x210144f020d85a83207640ab2028f083201c865f1fad122f1f7a66dc1ef2b0681de032471c7f7e981c3057951b7a35771b68f03a1b0ef6991a8e59c01a1c1c1119f1d5b41957a67018a87efa173d91b6171c9f5f170e24bc160273c8158342af1492b7931485af50143d224c1335bcd51125127b111b675d10f813060f0703a90e1b05be0d2ca7bd0d2229b60c9023b10c5c9bcf0c54a9b90bb9bb270a7bd40009ea26be09c541d509a54fbe097b64f10917fd9f08d8fae208992486082a3144081faeb606b068b7069b56fc065085770613e4ab05914ad3049f33f6040db23d03ca102602349a38021aaf9301b94f440124b4cd005f3143002663a3001b928a
  | 9, 1 => 0x424e7b91423680904232718f4194211c412179333fa0722c3f8a168f3f2412b63f06823f3edebc593e28f2383d8efbfc3c93fda33c3ade633c1bc2f03a8d188f3a25277b38a7d3b038345c80381838b53751b719374c39ea373ec5ae3730c825369b45f43644dde83599499c353a227734d4ce8d3409db0d33bf5cca32626de0323ec029320529d0316d68a530fc4ff130b4891f304ac6852eece7a22e67a9e22e588f872dfc58812bc281232ac584d42aa5ed57291324862870a89c283e157d28374fca27f08894276f1542273abe7326d188d325de4af625a5f1d924feee3b2365311e22e4f4b222d23a4322cce2832267fe2c21e06afa2195923d21781700
  | 9, 2 => 0x7b4ebb967a4d0ebd7a17d0a3796d2da2745050b773e68bb87391ffd97280003c726aa69c6ff774cc6fd6a20c6bcc899c6bbd0df36b5fb1336a9bc5c3694b76da67042c31666e01db64a07869640d6ad863ebfbf263ccbc4763c5a2eb6382486b62682dd6621db20c62169805621525f05fcc9fed5d1d45f25a2861f059cab250593caf565911f6fe58e86e47582a4af85663f0e8565e1e3e54d09229547d2fc1544f8c0a53c362cb52eb4fb351ea511151c3913d5068c1ae4f3af7164ec529794d3311ad4c877d614c85c4b94c4613144c06f0654bb044fb4af80ed248aeb09547228dac46d4de6b456596ad453405f5450900d744927a2844277f2843e14261
  | 9, 3 => 0xf83195cff575f2f1f5657d9ef16084f7f100582aed08ff40ea722159e81623e0e5f2448dd9c1552fd718605fd3b1a0d3d16a562ace41a9b7cd9e93d3c7970065c388074ec0929693be3bf101be0a7ea3bbd316feb5e0240ab54337bdb4e8b6bbb0a8cca0b0512fc1adae26e5a8ef5ce9a4a0d9b0a1f671d6a0ab07e19e7005069df12d319bdf661c965d5cd592c8b90591a0e86c908f7b2e908db62a908b79c38f2f42e78c489f398c1fc9e48b49b4cd8716803e8706d2e38510bbb68437598a83be999083077c158244dbfd81744eb57df25ff67b9ac48e7b6b899b
  | 10, 0 => 0xd16a562a9e70050691a0e86c81744eb5745050b76ff774cc5fcc9fed5d1d45f251c3913d38a7d3b030b4891f2e588f872bc281232870a89c1b0ef6991492b7930f0703a906b068b70613e4ab
  | 11, 0 => 0x1492b793
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x6a61f80798a7e20bc7e49ea4bfa94061f8078007c20187e01e001f08004c0cb550858430101091231200400000000000000000000000000035e101f1e13e200123c43fc2105595e001f1e03e000001c43f8000019a247887f8420ab3c203e3c27c400a003887f0000033c003e3c07c000ea61f8078827e20987e01e209f884061f8078007c20187e01e001f0817e8db933fff1dafa36e4cfffc7697c000003ffc1c0f000000fff070171f90245fd1f1247e40917f47c4821f80001fc1f1007e00007f07c40013032d5631610c4c0cb558c58430000000000000000000000000000
  | 0, 1 => 0x2fd89d6afffb3b6024a933c63400af8000007ff83800000001800000140091023842000fa12a44fff476940000003000000f000000fff0700bf6275abffeced89f3bfff18fc86be000001ffe0e001e3bffe007c06013c77ff631f90c4c0cb55ffd843003c77ff000f80c0000000ffc0006af1f927a92fea4987e01e629f884061f8078007c20187e01e001f0817e84a913ffd1da0024408e1080017c000003ffc1c00000000c000000a024a933c63400fd89d6afffb3b6a000000180000078000007ff8380001010913ff20044f1dffd087e43000000003ff00000f1dffc003e03
  | 0, 2 => 0x9e3bffbfffc86278effeffff21801e3bff9fffc06078effe7fff0197ef5ffffffffdb0125499fffa0057cf1dfffffffc30000000fff0000026065aaffec2189e3bffb18fc86000000007fe00001e3bff8007c06513e77ffe31f90fec4eb57ffd9db503c77ffc00f80fc000003ffc1c051b3d53fe31a5dde101f1e53e2005001c43f8000019e001f1e03e000144c9db778c7843fb13ad5fff676d40000003000000f000000fff0701abe7e5bea4bfa9a69f84f99afe230187e01e001f08061f8078007c20a377baffc636bbfc607e7cafcc01a003887f0000033c003e3c07c000
  | 0, 3 => 0x512bcc7fd39955be707fbe97ee21d001c43f8000019e001f1e03e00017ec4eb57ffd9db13276dde31e10d7c000003ffc1c00000000c0000015d839810b9d0de02762951ffcc495f8710007fe0fe07fffff9fffc7ea247887fa520ab3ca0bf3d2fd442a003887f0000033c003e3c07c00028092a4cfffd003f7affffffffeda80000007ff8001e78efffffffe1ae3f2048bfe3e249fca366fe9f99843f00003f83e200fc0000fe0f8800278effe843f2180808489ff90020078effe001f0180000001ff8000a25798ff8632ab7c607e7c2fcc01a003887f0000033c003e3c07c000
  | 0, 4 => 0x5c7648d9e0bec4b381edbb792033887e000060ffc40180effffc00118004042448c480113032d5421610c0000000000000000000000000000a024a933bdf400f4eaedddef5f32a0000001ffe00079e3bfffffff86af282fcf4bf510891e21fe9482acaf000f8f01f000000e21fc00000c6a69f84f892fe229a7e13e24bf88c061f8078007c20187e01e001f0817e84a913ffd1da122664ce31c1097c000003ffc1c00000000c0000015e101f1e53e2001b3d53fe31a5dd5e001f1e03e000001c43f800001847136e4c3e827698fc24890dbf98ef03ffff3e0077fcfe200007ffdc
  | 0, 5 => 0x5c7e48d9ff4fc4b1f92367fd3f12887e00007f07c401f80001fc1f103a3fb14a87e1e2475dab66017bff903f00000f83e20ffc000001fff815fdb56cc420bff0b15122210a0cd5ffffffe001fff861c400000007818a25499fe84005c04eb5781e1dbb003fffffe0007fc0fffff07c1df009633b73ef6c84258cedcfbdb21001e3bff9fffc06078effe7fff01ae7f2cfdffa7e678fc91b3ff9f89443f00003f83e200fc0000fe0f88002404488842821000000010800000000000000000000000000000000513e33f7a31790fec4eb570019db503c77ffc00f80fc0000030001c0
  | 0, 6 => 0x7f61c4005ef0379fdfdedd801bff7fe1c4007ff83f9fffffff801fffbe3fb14abfe3e24ffdab66ffffff943f00003f83e20ffc0000fffff8020000001c0100045000007f420002000000180000000000007f00000affdbbf71ef7ffc17b56ec002e25afffffff3fffffc3fffffc003e3f07d1b7260f7e3b5f46dc983df8ed078000001ff8381e0000007fe0e03fb4e62460849bded3989182126f7ff0e20030001fcfc38800c0007f1e0b92367c2071282e48d9f081c4be1ffffff801f1f87fffffe007c7eaf383fdf4bf710c95e63fe9ccaadaf000f8f01f000000e21fc00000c
  | 0, 7 => 0x280122046004001d0210017bc0cc280000006000001e000001ffe0e03e3f2048bfe3e248fc8122ff8f89143f00003f83e200fc0000fe0f88000202122042400808084881090020000000000000000000000000000d4d3f09f104fc457ffcffc497f5380c3f00f000f8403ffdffc003e13578407c784f880048f10ff084156578007c780f800000710fe0000062817b56ec002e25ffdbbf71ef7ffe83fffffc003e3ffffffff3fffffc000000004200000901122210a08400000000000000000000000000000010109121020044f0cfdd085e430000000000000000f1dffc003e03
  | 0, 8 => 0x5c7e40917fc7c491f90245fd1f12087e00007f07c401f80001fc1f102e3f246cffffe259fcf7fffe9f99c43f00003fffe200fc77fffe0f88c002000007d040001e00912107c00000000007c000001e00000007c0047037edd017076dc0dfb7405c1dbef03ffff01f077fc0ffffc07c1df2fd095227ffa3b40448811c618002f8000007ff838000000018000003ffbfbdbb0037feec38800bde06f3ffffffff003ffffc38800fff07f0a244cc99c638217d095227ffa3b4a000000180000078000007ff8380ffefef6ee10dffbf8ea913ffd1feffffffffc00fffff0e2003ffc1fc
  | 0, 9 => 0x5768cc489ff937a2fdeffe843f33d7e1c4001ff83f81fffffe001f1f91c0db9300581da7036e4c016076bbc0ffffc07c1dff03ffff01f077d73f9effffd3f33c7e48d9ffffc4a21f8effffc1f1187e00007fffc40013c2366421f9080400000fe0800003c0000000f8000000000f8000000080848bff9002278effec63f21800000001ff8000078effe001f01804c1db7508784301010913ff20040000000000000000000003ff000142fdeffe843f33ffeddfb9ffbfff41fffffe001f1ffffffff9fffffe001c55bb000b80404042447bc801003c77ff000f80c0000000ffc000
  | 0, 10 => 0x23889d6a9ff93b627ceffe863f21a78000001ff8380078effe001f01abc607e7c2fcc0125798ff8632ab6bc003e3c07c000003887f0000030bf7effffffffedfd9bf6effff3b6be78efffffffe1f8000007ff8380001010913f920044f0cfdd087e43000000003e000000f00000003e007f61c4005ef0379fdfdedd843bff7fe1c4007ff83f9fffffff801fffbfb0e20020001bcec3880080006f3ff0e20030001fcfc38800c0007f00020a93284340080808489ff90020000000000000000000001ff8000af280f8f4bf500091e21fe9082acaf000f8f01f000000e21fc00000c
  | 0, 11 => 0x502762950004c49fdb56cc39cbff507fffff8007c7fffffffe7fffff97a042002f7819812e676ec00d9097c000003ffc1c003c77ffc00f80dffdfdeddfbdbff7f7f7b77ef6ffdfffffffffffffffffffffffffffeb9fca366fe9f99a3f2048bfe3e2410fc0000fe0f8803f00003f83e207ffff7b77f47ffddff1245ffdfde7fffffffff07ffffff1001fffffe2e3b2048b0036248c08000bc8009043f00003003e200c00000fe00080a1cfc0c1e819ff6d433803ce6aa4a1ffe0e1fc1fffffe3bc07ffffe6a05ed5bb021b897ff6efdc7bdfffa0ffffff000f8ffffffffcffffff
  | 0, 12 => 0x5c7e40917f4fc491f90245fd1f12087e00007f07c401f80001fc1f102891e21fe1082acf080f8f0bf1002800e21fc00000cf000f8f01f0001ffdfdeddb9dbff767e6955ef4f79fffffffffffffffffffffffffffe000000003ff00000011021002000000000003ff000000000000000005c7640917e46c491d90245f91b12087e00007f07c401f80001fc1f102891e21fe1082acf080f8f09f1002800e21fc00000cf000f8f01f0001fffb56cdffffff47f62957fc7c48bff80001fffff007e00007f07c4019a02244fe94108000000384200010000000fe000000000003000000
  | 0, 13 => 0x547e40910f47c491f902443d1f12007e00001f07c401f800007c1f103ffffffff7bffffedfddbbbdebef7fffffffffffffffffffffffffffc31400001fd08000000000700400020000001fc000000000006000000b8fed5bbfe8f897ff6efdffbffffb0fffffffe0f8fffffffffffffff502e40910005c491f902443d0f12007e00000007c401f800007c1f10004f1dffd087e4301010913de200400f1dffc003e0300000003ff00008e26fdba7fe4edb9fbfffa1bffb7de07fffe7fe0eff9fffff80fffbe000010910170004401db740040430000000001f0000001dffc000003
  | 0, 14 => 0x159607b076d01dd6581ec1db40773f9e07f87ff83dfe781fe1ffe0f7800404244fa480103c11b3421f80400000000f8000003c0000000f801fda731237fe4defffffffe10ffffff871001ffe0fe7ffffffe007ffe000000003de00004b19db9003642000000003ff00000f1dffc003e037cfe51b37fcfccd1f90245ff1f12287e00007f07c401f80001fc1f102817b56ec002e25edd99b31ce3ef683fffffc003e3ffffffff3fffffc8e06fdba42e0edb91bf6ea1ba3b7de07fffe03e0eff81ffff80f83be50000000e100000000000384000050000000c0000000000003000000
  | 0, 15 => 0x502762950004c49d83100039c0de507fffff8007c7ff8710007fe0fe004f0cfdd087e4301010913e8200400f1dffc003e0300000003e00001a987e01e609f88271f807a927e210187e01e001f08061f8078007c20affdffff5effffc17b56ecffee25afffffff3fffffc3fffffcfffe3f009e19fb810bc860202122000400801e3bff8007c0600000000000002895e21fe188aacf180f8f0bf3002800e21fc00000cf000f8f01f00015ffb77eebdefff82f6add9085c4b5ffffffe7fffff87fffff8007c7e5fa36e4ce10c76be8ca913ffd1da5f000000c000703c000003ffc1c0
  | 1, 0 => 0x2800000070800002404489c6282128000000600000000000018000001404910238c2800fb12a44fff676940000003000000f000000fff0701a987e01e209f88261f8078827e210187e01e001f08061f8078007c20ef092fcf09f176891f31fe1482acef000f8f01f070000e21fc00000c57840fcf84f880268ffdff086177d78007c780f8000007fffe000007bffbfbdbbfff7feec3cc08fde86f3fffffffffffffffc38800fff07f0bf4254898008ed00100005080000be0000018000e00000000600000050000000e1080022800003fe100050000000c0000000000003f80000
  | 1, 1 => 0x6a61f80798a7e20987e01ea09f884061f8078007c20187e01e001f080000952640000017013ad5007076e800ffffc00001ff03ffff01f077dffffffff801ffffffddfbdffbfffffffffff801ffffffffffffffffefec388009ce06f3b3f34aa0027bcffc38800fff07f3fffffff003fff009e3bffbfffc86020a932fff400801e3bff9fffc0600000007fe00011c4dfb740dc9db7137edd037276fbc0ffffc07c1dff03ffff01f077ca1efe0e1ac1dffe4c2ac01ce5a22a1ffe0e1fc1fffffe3bc07ffffe6012022447ff41080011021842000000000003ff00000000000000000
  | 1, 2 => 0x57849fef84f8bb648fb9ff084156d781ffff80f83be007fffe00000f81c0dfb7401c1db7037edd007076ebc0ffffc07c1dff03ffff01f077c0278effec43f218180848bffb0020078effe001f0180000001ff80000fb13ad53ff676c4f9dffd087e430f0000003ff07000f1dffc003e036a69f84f99afe22be7e5bea4bfa9c061f8078007c20187e01e001f083530fc03c497f104c3f00f104fc42030fc03c003e100c3f00f000f8400240cc9884382100000001ff80000000000000000000000001ff800050024408e318003e84a913ffd1da50000000c000003c000003ffc1c0
  | 1, 3 => 0x5123c43fd290559e101f1e93e2005001c43f8000019e001f1e03e0003fff6efdfffdfff05ed5bbe10b897ffffffffffffff0ffffffc00f8fc1f4254883de8ed001220400040001e0000007fe0e000000000000000b8fc8122de8f892372048af22e2410fc0000fe0f8803f00003f83e2057f6d5b30002ffc085000000001257ffffff8007ffe187100000001e2bc203e3ca7c400267887fc624ab2bc003e3c07c000003887f0000031cebffffe02f7fffffffff8ffbfffdffffffe03fffffffffff9fffffe2a1c0db0ada02b6cf03fc33ac0ef7f3c0ff0fff07bfcf03fc3ffc1ef
  | 1, 4 => 0x9f3bffa10fc87f6275aa7feced801e3bff8007c07e0000007fe0e0140091023842000fa12a44fde476940000003000000f000000fff070000780244841f0000800001f4100000780000001f0000000001f00000afffffff1efffffffffffc7bffffafffffff3ffffffffffffcffffff578407c794f880048f10ff884156578007c780f800000710fe00000611c0db9300001da60308000160663bc0ffffc0001dff03880001f07701f425488bde8ed001220410840001e0000007fe0e00000000000000057037edde17076dc0dfb7785c1dbff03ffffc1f077fc0fffff07c1df
  | 1, 5 => 0x2301ae4c80b0332e06fdba00e0edf781ffff80f83bfe07fffe03e0efa817246cc000e2505c91b3000389683fffffc003e3f0ffffff000f8fc000488104210007d095222f7a3b40000000000000078000001ff8380d4d3f00f124fc4134fc03c493f1080c3f00f000f84030fc03c003e102fd1bf6efffa3b6e06fdbbc2f0edff81fffffff83bfe07ffff83e0ef91c04a91005c1da002440801000013c00000007c1c000000000000001ffdfffff82fbfffe1ff6edef83ffffffffff83fffffe1fffffff83fe50d7d030b40aef76e1de016b7d5350fff070fe0ffffff1de03fffff3
  | 1, 6 => 0x280922047fc5001f7a56cdffffed280000007f00001e780001ffffe000001102100200000000003ff00000000000000000000000003ff0000bf66fdbbfffcedfdfbffffffffb6be000001ffe0e079e3bfffffff86513c77ffe31f90c0404247ffc801503c77ffc00f80c0000003ffc0002301840000b0330e06dc980000ed7781c40000f83b9e07fffe0000ef97e84a9137bd1da0024408a1080017c000003ffc1c00000000c000001448f10ff0c615678407c784f8801400710fe00000678007c780f8000f4dff1bf104fcd537fc6fc413f35a0ffffff000f8fc3fffffc003e3f
  | 1, 7 => 0x281f22957187c01f625489ffeced281e00006007c01e000001ffe0e00400110238020008a00000fff4000400000030000000000000fff00002278efffc43f21c580848fffb0022078efff801f0180000007ff8000feff8922ffefef3fffbdbbfa3ffeffff8800ffffff3ffffffff83fff7ffefffffffffff1fdab77ffff12affe3bfffffffc61f80001ffff10000f046cd087e0101010913e9200400f00000003e0000000003e000015ffb77ee7fefff8bf7bffa10fccf5ffffffe7fffff87fffff8007c7e00000000000000000000000840000000000000000000000000000000
  | 1, 8 => 0x3809d6a80383b6004a932000000d781ffff80f83be007fffe00000f840400003fa28008bc0122fe8f80040000003f8000003c0000fe0f80000780244fd1f0001e00913f47c00007800007c1f0001e00001f07c00ffe3aa44fff47fbfbfbdbb8437feffc38800fff07f3fffffff003fff502140000000049fdb56cc000bff5061c4000000079ffffffe001fff800f046cdfffe0113c77ff7e9f90c00f00000fffe0003c77ff3e0f80d7181000179001247640916006c4821800001fc001007e00006007c40000244080008003e84a9107bd1da000000000000003c000000ffc1c0
  | 1, 9 => 0x7f61e6047ef4379fdfdeddfffbff7fe1c4007ff83f9fffffffffffff840f0048b883e008b00000fe8600040f00003003e000000000fe00000002000007fe40001e22952107c00000000007fe00001e00000007c0000000000000000000000000000000000000000000000000000000000289f3bffffffc87f7affffffffeda81e3bffffffc07e78efffffffe1800404244ffc8010105499421a00400000000ffc00000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffe50000000fff0000001102384200050000000fff00000000003000000
  | 1, 10 => 0x108000000000008000000000000000000000000000000000140080002840000fa12a44c00476940000003000000f000000c000701f3fdefffff3f33ffeddfbffffffea1f8effffc1f11ffe00007ffffc0ffffbbf7bff7ffffffffff003fffffffffffffffffffffffff003fff00803b6e8008086000212202e00080003bff8000006000000003e0002a3f204887a1e2405c8122000b89003f00000f83e200fc0000000f8800258cedc801b2100000001ef00000078effe001f0180000001ff8000000000003e800000000001002000000000003e000000000000000000
  | 1, 11 => 0x2fd0b7267ffe3b40048811fff0002f8000007ff83800000001ffe000066f1dffffa7e430101091fffa00440f1dffff83e030000000fff0000bf425489fff8ed45122047fc6000be000001ffe0e000000007f00000ffffffffc21ffffb4e6246ffc9bdffffffffc00fffff0e2003ffc1fc000800000101000020000004040000000000000000000000000000002817b56ecffee25ffdffff5effffe83fffffcfffe3ffffffff3fffffd73f9efffffff33cfe7bffffffcce21f8efffffff1187e3bffffffc46001010911ef200407156ec002e01000000003ff00000f1dffc003e03
  | 1, 12 => 0x400000038000000000000e000000400000030000000000000c00000031400001fd180045000007f4600020000001fc000000000007f00000ffffef6effffffbfffbdbbfffffe5ffc0000fffff83ff00003ffffe05760c4000e7037809d8a5400131257e1c4001ff83f81fffffe001f1f800800001081000000000020000000000000000000000000000000001e0bdab77c21712ffeddfbfffbfffe1ffffff801f1ffffffffffffffeb8fc8122ffff8923f314abfa3e2410fc0000ffff8803f00003f83e20
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x5040702010660504030201006
  | 7, 0, 0 => 0x200504030a0e1970504030f0901177051f031e0e011971d0504030a010870504030a0901157051c030a1b1a1970518030f0e0117705040b160e011570504110a120108705040b0214010870513030f0e010870510030a12010870504110f0e010870510030f0e01087050403020d010c705040b0a0901087
  | 7, 0, 1 => 0x50407221b011970504030a0e012b705040b0f0e010870510030a0e2a0872104030a1b1a1970504070a0e010670504030201292670504030a0e010070504030a28010870504030a0e271970513030a0e012670504030a25011972404030214010870504230f0e01177051c03221b011972104030f0e01197
  | 7, 0, 2 => 0x50403013319087320504030a0e017310504030119087050403221b010c73004030a0e2a0870504030a12011570518030a0e2f1770504030a2e19087051303160e011572d0504030a011972c0504030e19087
  | 8, 0, 0 => 0x440504030a0e1908842051c030a0e01198050403430e0119088420504030a4101198400504030a3f01198053a04033e0e190880504030a0e01173d805043c0a0e01190883b3a04030e0119088370504030a0901088050403020d01193980504030a0e0119388340504230a0119088370504030a3635088340504030a0119158051c030a0e0119088
  | 8, 0, 1 => 0x370504030a0e2f0885004030a0e01190884f0504030a0e011984e0504030a0e19088342404030a01190880504030a0e4d4c0880504030a0e01194b83004030a0e011908842440504030a0e1980504030a0e01084a8054904030e01480880504030a0e4719088051c030a0e1a190880504030a0e4619458440504030a0e192680504030f0e0108298
  | 8, 0, 2 => 0x4030a590e0119088055804030e0119088440504030a0e57198053a04030e0119388375604030a0e010880504030a1b010c398050403550e01082980504030a0e01195480504030a0e01190880504030f090119088051303160e0108298530504030a0e01088053a0403410119088520504030a0e013d80504030a140108518050403020a010c088
  | 8, 0, 3 => 0x440562030a0e19088420504030a0e01198340504030a010c088050403610e601908844053a04030e19088055f04030e01190880504035e0a0e010880513030a0e01083d85d0504030a0e01178053a04030e01173d8370504230a0e01088340504030a5c19088053a043c0e01190880504030a0e0119268370504030a0e011585b0504030a0e5a198
  | 8, 0, 4 => 0x5604030f0e01190880504031e0e0119088690504030a0e19688420504030a0e1a1980504030a0e570119805040b0a4101190880504030f0e2f190884244053a04030e1980504030a0e67190880504030a0e1a190880566030a0e0119088053a04030e4619458650504030a0e01198340504030d01196480504030a0e63190880504030a0e2a08068
  | 8, 0, 5 => 0x57204030e0119088710504030a0e19088050403023e70190880504030a0e6f190880518030a0e01173d8053a04030e01192686e0504030a1b0119834050403616d190884405040b0a0e190880513030a0e01191580562030a0e01190880504031e0e01192680504230f0e0119088053a04030e01190886c0504030e6b190880504030a0e016a088
  | 8, 0, 6 => 0x44050403220e19088057a030a0e011908805040b160a0e01088790504030a01190880504030a7801190880504770a0e0119088370504030d0e016480504030a0e4619768211c030a0e0119088750504030a0e01748051c03220e0119088420562030a0e0119842053a04030e011980504030a140e01158440518030a0e190880504030a730e19088
  | 8, 0, 7 => 0x37050403610e6d0880513030a0e5c190880504030a0e01150680504030a0e017e0884205040b0a0e01198050403164101082980504030a09011708805047d0a0e0119088053a62030e0119088051c070a0e01190882404030a140e01088420504030a78011980518030a0e01190887c0504030a017b088442104030a0e1908805040b0a0e0119088
  | 8, 0, 8 => 0x448404030a0e19088448304030a0e1908882050403810e011980504030a0e0129268422104030a0e011980504030a368019088053a040b0e0119088057f04030e011964842050403220e01198440504030a09190882104030a0e011908844050403160e082980504030a0901173d80504030a0e2a19088050403220e011908844050403027019088
  | 8, 0, 9 => 0x8a0504030a0e1908804030a890e0119088420504030270011980504030d0e01198880504030a0901190880504030a410119158050403028701190880504030a860119088050403160e01082980504030a0e2f173d80504030a363519088340504850a0119088370504030a1b0139805040302700119088050403220e1a19088053a18030e0119088
  | 8, 0, 10 => 0x504030a1b010c088440504230a0e190888c0504030a0e010888404030a0e01190884237340504030a0180504030d0e01640688304030a0e0119088420504030a0901198440504030a0e191580504070a0e1a190880504230a0e01173d8213a04030e01190880504030a0901192680504070a0e01193d80504030d0e018b198420504070a0e01198
  | 8, 0, 11 => 0x504230a0e0119088442404030a0e190880504030a0e01191583734053a0403010880504030a0e01941980504930a0e0119088370504850a0e01088340504030f01190880504920a0e01190880504030a140108918053a04070e01190880504030a0e2f190880504030a90011908805048f0a0e0119088058e04030e6d190888d0504030d0e01198
  | 8, 0, 12 => 0x563a04030e0119088440504030d0e19648053a04030e2f1908805040b160e0108298210403220e01190889b0504030a01193989a04030a0e011908899050403610e190880504980a0e0119088051c030a0e010c088425604030a0e011989704030a0e0119088050403020e0108068960504030a0e190880504030a0e01950880504930a0e0119268
  | 8, 0, 13 => 0xa20504030a0e1945805040b0a0e01191583405040301a119088a00504030a0e19088051c03020a01190880504030a0e010c3d8243a04030e01190880518030a0e2f190880504030f0e0119398420504030a0e5c1980504030d0e0119648059f030a0e01190882104070a0e01190889e050403019d190880504030a0e9c19088422404030a0e01198
  | 8, 0, 14 => 0x5604030a0901190884244340504030a198340504030a4619458370504030a3e0e0880504030aa60119088420504030a0e4da580510030a0e01080680513030a140e01088053a04030e5c190880504030a0e0117068a40504030201190880518230a0e01190885618030a0e01190880504030a0e1a0c088a304030a0e0119088051c030a1b0119398
  | 8, 0, 15 => 0x510030a0e0119088370504030a0e0126804030aa80e011908834053a0403011908805040b020e01190880504850a0e01190880504230a0e2f190884237440504030a0e8053a04031b01193980504070d0a0e01198053a04030e01a708842340504030a011984434053a0403190880504030a1b1a19398440504850a0e19088340504030a0119268
  | 8, 1, 0 => 0x504030a1b011926805b1030a0e011908805b0040a0e01190883004030a0e0108068af0504030a0e19088342104030a0119088420513030a0e0119805ae0403700119088370562030a0e01088340504030a017e0880504030a011908ad80504ac0a0e01190882104030a1b0e01198ab0504030eaa19088a90504030a0e4619842370504030a0e018
  | 8, 1, 1 => 0x440504030a0e173d8050403b20e01190880504030a3e0e19088
  | 9, 0, 0 => 0x6e0504030a0e011908900440504030a0e190880504030ab70e01190890504030a0e011908919050403020a0e0119089340504030a011908b69050403b50a0e0119089000504030a0e01173d80504030ab40e01190890504030a0e4d4619089050403610a0e6d190890504030d0a0e010806944340504030a0e190896c0504030a0e0119089b30504030a0e011908900051c030a0e0119088
  | 9, 0, 1 => 0x50403020a0119083990042440504030a0e1980504030a3e0e701908942050403020a0e011990504030a0e01197b089370504030a0e01350890504030a0e4d19a50890504030a0e3f0119089340504030a011719089000504030a0e4619458370504030a0e01084590504030a0e0119ba0890504030a1b0e0119399b9340504030a01190890504030a0e0108293d90504030a0e011908b89
  | 9, 0, 2 => 0x53a0403020e01190890504030a0e0119152990504030a3e0e0119089000504030a0e011926869440504030a0e19089340504030a0119083990504030a0e01bd1908942340504030a0e01199000504030a0e0119088440504030a0eaa190896c053a04030e01190890504030a090119083d9bc370504030a0e01089050403bb0a0e0119089420504030a0e3f01199340504030a0e0119089
  | 9, 0, 3 => 0x504030a0e0119c2089370504030a0e011708944440504030a0e190890504030a0e0119150897c0504030a0e011908934050403160a0119089000504030a0e1a19088370504030a0e01c1089440504030d0a0e19089370504030a0e0108b690504030a0e011908c090504030abf0e0119089a90504030a0e011908900420504030a0e011980044053a04030e190880504030a0e01be19089
  | 9, 0, 4 => 0x504230a0e0119083d9340504030a0119086492404030a0e01190829934050403610a0119089c70504030a0e01190895604030a0e0119083d90504030a0e01c619089690504030a0e01190890504030a0e0119c508934053a04030e0119089440504030a0e7019089c40504030a0e01190890504030a0eaa011908905c304030a0e01190890504030a0e01194c0890504030a0e2f19083d9
  | 9, 0, 5 => 0x420504030d0a0e011990504030ac80e01190890504030a0e4601194590504030a0e5c19082990504030a0e70011908940420504030a0e011990042053a04030e01198054904030a0e0119089440504030a0e0119089370504030a0e01083990504030d0a0e011908937440504030a0e19089340504030a360119089340504030a019d1908900053a04030e01190880504030a141b0119089
  | 9, 0, 6 => 0x504030a0e011908cd9370504030a0e01190890005040b0a0e01190880504030a140e0117089440504030a0e1908cc90504030acb0e01190890504030a0e011908ca9420504030a0e700119937050403160a0e01089c9340504030a0119089340504030a4d01190890504030a0e87011908942440504030a0e01199340504030a4601190890504030a140e0108b690504030a0e016019089
  | 9, 0, 7 => 0x340504030a016d1908944053a04030e01190890504030a0e0119d1089370504030a360e010890504030a0e011908d09053a04030d0e0119089cf370504030a0e0108942370504030a0e011990504030f0a0e0119089370504030a0e010864937050403610a0e01089340504030a0119a50890504030d0e0119086490504030a0e010119089000518030a0e01190880504030a0e01ce19089
  | 9, 0, 8 => 0xc9370504030a0e01089370504030a0e4d0108937053a04030e0119089440504030a0e19d308975370504030a0e01089420504030a0e0119cc9370504030a0e4601089420504030a0e0119d190504030a0e1a0119089002104030a0e011908800050403220e01190880504030a0e011908cc9ab440504030a0e19089053a04030e7001190890504030a0e01d219089440504030a1b0e19089
  | 9, 0, 9 => 0x370504030a0e016d089053a04030e011908cc9340504030a0119082990504030a0e800119089420504030a140e01199000504030a0901190880504030ad50e0119089370504030a0e01a508900050403160e0108298000504030a363519088ab0504030a0e0119089440504030a0e35190890504030a1b0e01190890005040302700119088440504030a0e1908459d40504030a0e0119089
  | 9, 0, 10 => 0x340504030a0119083d9440504030a0e1719089000504030a0e2f190880504030a0e011908d790504030a0e018b190890504030a410e0119089053a0403140e01190895b0504030a0e0119089370504030a0ed6010890504030a0e0119088890504030a0e011908069440504030a0e1908b690504030a0e0135190890504030a0e0119084590504030a0e0119d30890504030a1b011908399
  | 9, 0, 11 => 0xdc0504030a0e01190890504030a0e011908db905da3a04030e01190890504030a0e0e01190890504030a0e011719089a40504030a0e0119089440504030a0e19083990504030a0ed901190890504030a0e01c1190890504030a0e011908b69370504030a0e01082999e340504030a01190890504030a140e01a5089000504230a0e0119088000504030a0e0119158340504030a011908d89
  | 9, 0, 12 => 0x820504030a0e011908905ae04030a0e01190890504030a0e2f01190890504030a0e011919089990504030a0e01190890504030a140e0108299000504030d0e01196480504030a0e01de19089050403dd0a0e011908944050403610a0e19089520504030a0e01190890513030a0e0119082990504030a0e011908399370504030a0e01083d90504030a0e0117193d90504030a36013519089
  | 9, 0, 13 => 0xe10504030a0e01190890042340504030a01198050403020d0e01190890504030a410119082990504030a0ee0011908934340504030a0119089340504030a01197b089c90504030a0e01190890504030a0e460119089053a0403160e011908942053a04030a0e01199050403df0a0e0119089c9440504030a0e19089050403610a0e011908942050403160a0e01199440504030a0e4619089
  | 9, 0, 14 => 0xe30504030a0e01190895d0504030a0e0119089340504030a01d21908942420504030a0e011990504030a0e011908d890504030a0e0119083d937340504030a01190890504030a0e011908e290042370504030a0e018440504030a0e19083d9053a04030e016d190890504070a0e0119083990034053a04030119088053a04030e0119a50890504030a0ed60119089050403020e700119089
  | 9, 0, 15 => 0x44050403020a0e190890504030a0e01e619089050403610a0e4d190890504030a0e01e519089000504030a3e0e19088050403e40a0e0119089050403610a360e19089
  | 10, 0, 0 => 0x504030a0e0119083990504030a0e0117190890504030a0e011908b690504030a0e0135190890504030a0e0119084590504030a1b0e0119089370504030a0e01190890504030a0e700119089440504030a0e01190890504030d0a0e011908900053a04030e011908800420504030a0e01198000504030a0e0119088340504030a0e011908900440504030a0e19088050403020a0e0119089
  | 10, 0, 1 => 0x504030a0e0119083d90504030a0e460119089050403610a0e0119089
  | 11, 0, 0 => 0x504030a0e0119088
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 52
  | 7 => 60
  | 8 => 68
  | 9 => 76
  | 10 => 76
  | 11 => 68
  | _ => 0

def idWidth : Nat := 8

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 225 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3fffffffffffff000000000000003fffffffffffff, 54)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 112 true (goal 112) u ys) :
    NatRunT 112 true (goal 112) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 10 0 (NN s)

def poolG : List Nat := [21480074368896114, 15772572861973620, 27050194908651689, 90100605761256560, 15850627393505395, 10161701708305522, 21420711525598320, 15791195828635763, 15791272109391985, 15791211909596272, 27109586789056679]

def Z (s : Nat) := bar 112 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 2 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 43 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 19 24 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 43 → Z 7 i = true := (range_split z7_0 z7_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_72 : ∀ i, 72 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_120 : ∀ i, 120 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 168 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_168 : ∀ i, 168 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_216 : ∀ i, 216 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_240 : ∀ i, 240 ≤ i → i < 264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_264 : ∀ i, 264 ≤ i → i < 275 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 11 264 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 275 → Z 8 i = true := (range_split (range_split (range_split z8_0 (range_split z8_24 z8_48)) (range_split z8_72 (range_split z8_96 z8_120))) (range_split (range_split z8_144 (range_split z8_168 z8_192)) (range_split z8_216 (range_split z8_240 z8_264))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_24 : ∀ i, 24 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 72 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_72 : ∀ i, 72 ≤ i → i < 96 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_96 : ∀ i, 96 ≤ i → i < 120 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_120 : ∀ i, 120 ≤ i → i < 144 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_144 : ∀ i, 144 ≤ i → i < 168 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_168 : ∀ i, 168 ≤ i → i < 192 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_192 : ∀ i, 192 ≤ i → i < 216 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_216 : ∀ i, 216 ≤ i → i < 240 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_240 : ∀ i, 240 ≤ i → i < 247 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 240 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 247 → Z 9 i = true := (range_split (range_split (range_split z9_0 z9_24) (range_split z9_48 (range_split z9_72 z9_96))) (range_split (range_split z9_120 (range_split z9_144 z9_168)) (range_split z9_192 (range_split z9_216 z9_240))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 19 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 19 0 = true)

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
theorem rootChecked : span RootG 5 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRunT 112 true (goal 112) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := runT_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 8 fG 11 := mainG noRunFull

end Sub_0

def cSub_1 : Fin 9 → Sum Bool (Fin 8) := (fun i : Fin 9 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inl false
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩
  | ⟨8, _⟩ => Sum.inr ⟨7, by omega⟩)

namespace Sub_1
abbrev fG : BFn 8 := fun y : Fin 8 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.cSub_1 y)

def cSub_0 : Fin 8 → Sum Bool (Fin 7) := (fun i : Fin 8 => match i with
  | ⟨0, _⟩ => Sum.inl false
  | ⟨1, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩
  | ⟨7, _⟩ => Sum.inr ⟨6, by omega⟩)

namespace Sub_0
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.cSub_0 y)

def cSub_0 : Fin 7 → Sum Bool (Fin 6) := (fun i : Fin 7 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨4, _⟩ => Sum.inl false
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩)

namespace Sub_0
abbrev fG : BFn 6 := fun y : Fin 6 → Bool => PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.fG (substIn PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 7) (_ : SCleanL 6 gs)
    (_ : ∀ p, p < gs.length → 6 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 6 + p ∈ g.inputs)
    (_ : ∀ x, val gs 6 o x = fG x) :
    ∀ a, a < 6 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 1, 4, 4, 32, 33, 33, 33, 33, 7, 7, 7, 14, 3, 3, 3, 5, 5, 5, 6, 6, 12, 16, 16, 8, 8, 32, 48, 48, 48, 48, 26, 26, 26, 14, 18, 18, 18, 24, 24, 24, 10, 10, 12, 2, 32, 14, 12, 9, 17, 20, 36, 36, 35, 37, 41, 49, 15, 23, 39, 15, 11, 19, 35, 13, 21, 37, 22, 38, 13, 20, 17, 9, 40, 40, 50, 56, 52, 49, 30, 27, 58, 30, 22, 19, 50, 28, 25, 56, 11, 42, 28, 34, 34, 46, 44]

def xsG : List ℕ := [0x29141a7ffe300000007efe3, 0x763f8818fe20563f8018fe00, 0xc84ca07f1e5cc804003f1e0c, 0xcfc797213281cfc783201000, 0x9fff8ca450601fbf8c00000, 0xf5227e1489f820007c0001f0]

theorem rowsG_len : rowsG.length = 96 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => ((fun x : Fin 6 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 48 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 48 false (fG, false) = goal 48 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 48 zs &&& lo 48) ≠ lo 48 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 7, ¬ NatRunT 48 false (goal 48) s xsG) :
    ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 48 false (goal 48) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 7, ¬ NatRunT 48 false (goal 48) s xsG) :
    ¬ HasCircuitSize 6 fG 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 48 false (encT rowsG 48 false (fG, false)) s'
      (ws.map (encT rowsG 48 false)) :=
    RunT.map (encT rowsG 48 false)
      (fun a => encT_inv rowsG 48 rowsG_len false a)
      (fun a b => encT_and rowsG 48 rowsG_len false a b)
      (fun a b => encT_or rowsG 48 rowsG_len false a b)
      (fun a => encT_tag rowsG 48 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x4ee8810
  | 6, 0 => 0xfb73b432b0513d145dff4e9a40c414e625be566e1a0a8cad17cd0c28
  | 7, 0 => 0x25be566e
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xf6000735baf9fe04073fffffc84ca07f1e5cc804003f1e0c763f8818fe20563f8018fe00cfc797213281cfc783201000fc6ea87f9e7cc804003f1e0cf5227e1489f820007c0001f009fff8ca450601fbf8c00000029141a7ffe300000007efe3
  | 0, 1 => 0xadd81eb7607dfff83fffe0f74220810882000000000000089c077e701dfa9c07fe701fffe7fa87ffe7cde3f803ffe0c303868decd7e30387cdfefff
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105
  | 6, 0, 0 => 0xc46510646210b646a21069462106465210665821067465206
  | 7, 0, 0 => 0x4652106
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 28
  | _ => 0

def idWidth : Nat := 4

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 96 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3fffff0000003fffff, 22)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 48)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 48 false (goal 48) u ys) :
    NatRunT 48 false (goal 48) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 4 0 (NN s)

def poolG : List Nat := [34912805654151217, 5642703390949449, 5639428501456947, 23649424669459504, 34912798139008050]

def Z (s : Nat) := bar 48 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 48 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : NatRunT 48 false (goal 48) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := runT_len h
    change 6 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 6 fG 7 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 4)

def perm_4 : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩

def cu_4 : Fin 7 → Sum Bool (Fin 6) := fun i => cSub_0 (perm_4 i)

theorem hperm_4 : ∀ y : Fin 6 → Bool, fG (substIn cu_4 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_4 : ∃ y y' : Fin 6 → Bool, fG (substIn cu_4 y) ≠ fG (substIn cu_4 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 7, ∃ y : Fin 7 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 9) (hcl : SCleanL 7 gs)
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
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 1, 4, 4, 64, 7, 7, 7, 7, 14, 21, 21, 21, 21, 28, 81, 81, 81, 81, 3, 3, 3, 3, 5, 5, 5, 6, 6, 6, 12, 17, 17, 17, 20, 20, 20, 65, 65, 65, 65, 80, 32, 32, 8, 8, 64, 42, 42, 42, 42, 14, 56, 56, 56, 56, 28, 112, 112, 112, 112, 34, 34, 34, 34, 40, 40, 40, 10, 10, 10, 12, 48, 48, 48, 24, 24, 24, 96, 96, 96, 96, 80, 2, 2, 16, 64, 14, 14, 28, 28, 12, 80, 9, 33, 36, 68, 68, 15, 23, 39, 71, 15, 23, 29, 53, 85, 29, 83, 85, 89, 113, 11, 19, 35, 67, 13, 37, 69, 22, 38, 70, 13, 19, 25, 49, 22, 52, 84, 67, 69, 73, 97, 84, 36, 33, 9, 72, 72, 46, 58, 43, 106, 46, 58, 60, 57, 120, 60, 114, 120, 116, 113, 38, 50, 35, 98, 44, 41, 104, 26, 11, 74, 44, 50, 52, 49, 26, 25, 88, 98, 104, 100, 97, 88, 18, 66, 18, 66, 30, 78, 30, 92, 76, 82]

def xsG : List ℕ := [0x10a1248210cf1e3ffffe30000000000000f1c3ffbde3, 0x9fc24b8f10fc0125c7887e00cc0038f007c0001c7803e0, 0x7c081411494432e3f817ffc7c000400084000e3f807fec, 0x7c25c7f02fff840a08a4a217c01c7f00ffd80020004200, 0x1b561f882ff8810fc417fc40b121f800ff8010fc007fc00, 0x1e3c7ffffc68509241086001e387ff7bc60000000000, 0xeabf0248f4231f81247a118823e0000f0021f000078010]

theorem rowsG_len : rowsG.length = 184 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 92 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 92 true (fG, false) = goal 92 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 92 zs &&& lo 92) ≠ lo 92 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 92 true (goal 92) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 92 true (goal 92) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 92 true (goal 92) s xsG) :
    ¬ HasCircuitSize 7 fG 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 92 true (encT rowsG 92 true (fG, false)) s'
      (ws.map (encT rowsG 92 true)) :=
    RunT.map (encT rowsG 92 true)
      (fun a => encT_inv rowsG 92 rowsG_len true a)
      (fun a b => encT_and rowsG 92 rowsG_len true a b)
      (fun a b => encT_or rowsG 92 rowsG_len true a b)
      (fun a => encT_tag rowsG 92 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 3
  | 6 => 10
  | 7 => 56
  | 8 => 28
  | 9 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x9f9296438c0c5c9566b1ff72
  | 6, 0 => 0xc9e3db1a97969a138110cf2c74d48ebb36966ba3361013a634ddd62a1f1c643f1905bf3315838405
  | 7, 0 => 0xfe8c5db3f922c04df4125de5ec8b4e83ebfbf30eea435d95e84f060adc87f7f6d9c86e28d4e076c9cddbf15fcae90b70c3554725a9bc2226a4793ea1a38481679bd23cc79b11bf01894fec9181e8f1757bc781a07ad11635784c1874748412296d38d6ff5bdb843659d1c9bc51c206d150109b504fef076d4e0147784cfc217e451886904259bb873c8132113b548ab2391978de36c3ffe434ddd62a3316698331aa598e2f9ef1bd2a3a1626283b39e31ce90b2819bf26b917a2d2a4154bcab311cb4e400e5e02dc0e0a31ca06b7e74d05ded1770533dc7602ebeb88024b1535
  | 8, 0 => 0xf922c04deaf7a9e0ea435d95d9c86e28d30d0546ccae4168b728979a8db3d0f3761e44f575ee05ff73e45deb65affa3860f2a7415bdb8436533b47c74df0285b4ceb6a41391978de2c0906a12ae6320821aad4611dffdf601511387113cfd60211cb4e4010e5f2850ead47290b8e3e57
  | 9, 0 => 0xf922c04d
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x7fe52f4dacf619f3fe8fffe3e00020004200071fc03ff600078f1fffff1a14249042180078e1ffdef1800000000000021424904219e3c7ffffc60000000000001e387ff7bc6eabf0248f4231f81247a118823e0000f0021f0000780103e12e3f817ffc2050452510be00e3f807fec00100021001f02050452510cb8fe05fff1f00010002100038fe01ffb13fbcfdfffff8d2ebae92b8c003c70ffef78c00000000009fd2ebae92b8cf3f7ffffe30000000000000f1c3ffbde3
  | 0, 1 => 0x4fe125c7887e0092e3c43f0066001c7803e0000e3c01f005503f6dc2f7381fb6e17b9df707fffc3ff783fffe1ffbdfffe979fe9fe3f4bcff4ff11dfc071fe0fc3e038ff07e0603db575ef57fedabaf7abffffffffffffffffffffffff41fbf5f75b5de68e03f4001c1fffdfffbdfff8e03fc009a7f092a2842a00495142150000000000000000000000001ffcf9ff47fff0a5e9b59ec2f8038fe01ffb00040008400ffff4acaf4ab1fa5657a558823e0000f0021f000078010
  | 0, 2 => 0x7f53e3fc1fffc2858656590be00e3f807fec001000210020f68e03f4001efd7dd6d77a0ff8e03fc009fff7ffef7fdeafbf9e5ff17fdfcf2ff8bfe67ff8e1ff07fffc70ff83e603db470ef03feda387781ff33ffc70ff83fffe387fc1f7ffffd657fd58ffeb2bfeac599ffc007fc10ffe003fe083ff870e00000e5ebdb6fbde7ff871e00210e7ffffffffff6ac3f105ff1021f882ff8816243f001ff0021f800ff800ffef5edb7def30e1c00001cfffffffffffff0e3c00421c
  | 0, 3 => 0xf5ebffffe77af5fffff3800f1c3ffbde378e1ffdef1800408092084120404904208000000000000000000000013fbcfffffff8d2ebaf92fcc19bc77ffeff8c0038f007c00002080f10fc000082000800000000f003c000000000003e044a98a5aa5b75fc5bffebe00020004200071fc03ff60007af5fffff3b16a6b96a9c0078e1ffdef1800000000016ae3f14dff30b1f8a6ff9856243f001ff0021f800ff8007c081515495433e7ff9fffc7c000400084000e3ff87fec
  | 0, 4 => 0x454f1f3ffffe34a8cb248c3000f1c3ffbde300000000002d5ffe32bfea063f105ff102c4ffe003fe0043f001ff000f85b8fe0dfff2d16516d672f8038fe01ffb00040008400fd69f882ff8812fd617fd58b121f800ff8010fc007fc003e1ffffffffff62d4d72d53be0ffffffffef00100021000001011c0bff000000000000000001c01ef000000000001d57f06d1ec673f1659fd673047c0001e0043e0000f0020683f3e7fffff6c509261086001e387ff7bc60000000000
  | 0, 5 => 0xc1a1ae5aa342849208430000000000000000000000022a08082040800404102040000000000000000000000001fd7e2cb3face7fc7f8ffff9fc7c0801f0843fc7f0ffff868080000400012812012118000000000000000000000007ff3e7ff9fffc297e7d67f0be60e3ff87fec001e3c21f0070010e0003f00000020088030000e0001f0000000008016ad3f927ff9861f9a2ff9896243f001ff0021f800ff800ffe74bcf34ff0525c7a87e00cc0038f007c0001c7803e0
  | 0, 6 => 0x3e1af3fa57ffe60d0d72d51be00e3f807fec00100021002ff8fea2bfea047f515ff502c487e003fe0043f001ff000d06b46c94c679e3c7ffffc60000000000001e387ff7bc67c35e7f4afffcf1e3ffffe37c01c7f00ffd8f1e3ffffe300004090010842050452510800000000000000000000001a0960d8098ce1028229288400000000000000000000001d57e7cfffffeffa36cf633d047c70ffef7cfe0000f0020001e0048f42008000040000001e0000f00000000000000
  | 0, 7 => 0x1011c0bff000000000000000001c01ef03aafe8db3d8cf7e7cfffffee08f80003c0087c70ffef7ccf85bafe2dfff6dd7f16fffaf8038fe01ffb01c7f00ffd87c000410094400020804a207c0004000840000200042000000029a802a70014d40153a66003ff803ef001ffc01f7a7f49aebe4bf124d75f25f8833000e3c01f000071e00f81d57e44d9ec66bf226cf6335047c0001e0043e0000f00209fca5f9f59fc2165d7897e40cc0038f007c0001c7803e0
  | 0, 8 => 0x7c18b535cb54fffffffffff7c00040008400ffffffffef3e0f1e3ffffe3d79fd2bfff3e0f1e3ffffe3071fc03ff61a0940900908c10000080000000000000000000000000013fa5d75f25f99e7ffffffc61980071e00f81e3bfff7fc60008141149442040900108400000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x104820c0144030e182a8406080805
  | 6, 0, 0 => 0x100c1060a298804060830a6100c10f0c158703041828a61a0c1060a298203040428a6080c1060a29860406083056080c3860a298584061828a6
  | 7, 0, 0 => 0x22101821e802b91080c10f3e79c98e06087860ae442030474e057221019b1e182b91163818f0c15c884060879a0ae64203043c3057284420304182b91080cc0f0c15c203043c30514e44217043c30572844b0404182b9528101820c15ca13080c1060ae40911080c10f7
  | 7, 0, 1 => 0x52101821e182b9022101821e19c88406094060ae5088e0608305722101821e9c2b9022582021e19d30406087860ae409840608786722112821e182ba4080c10f0c15c811161018f0ce44223043d105722381821e182b91420c10f0c15c004060830514c4c203041828a7
  | 7, 0, 2 => 0x222c2031e182b91080c1380c15c88b2c107860ae4c584063c30572211b821e182bb6080c10f0c15c88406087866ae44234043c33372044703043c339108087860ac9c8b106087b00ae44203043c2af722341820c1573ad220c7860ab1c88456095060ae40a11080c1067
  | 7, 0, 3 => 0x2211ebc1e182b91080c10f0c15c20304ec7860ae54203043c305726341821e182b93080c10f0c15c8840609d060ae45c83043c3057
  | 8, 0, 0 => 0x2210182823c305800408840608786722101821e182ae822101821e182c082210703043c30580044703043c3057222c203043c30585a44203043c305822101821e1829e822101821ea8305822101821e182bf822101821e7c305800508840608305722f8203043c30582234203043c305822101821e18e058
  | 8, 0, 1 => 0x44203043c30572844203043c3058004c203043c30570044584063c305722101c4043c30582211583043c30582212183043c305822101821e182c282210182783c305822101821e1980582211e83043c30582444203043c3058
  | 9, 0, 0 => 0x44203043c3057
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 39
  | 6 => 46
  | 7 => 53
  | 8 => 60
  | 9 => 53
  | _ => 0

def idWidth : Nat := 7

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 185 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x1ffffffffff0000000000001ffffffffff, 41)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 92)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 92 true (goal 92) u ys) :
    NatRunT 92 true (goal 92) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 7 0 (NN s)

def poolG : List Nat := [16903902602555528, 51796909478736990, 51807943332602031, 51796903035236445, 16894007080746159, 10138656991966300, 16899548622452831]

def Z (s : Nat) := bar 92 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 48 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 56 → Z 7 i = true := (range_split z7_0 (range_split z7_24 z7_48))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 28 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 24 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 28 → Z 8 i = true := (range_split z8_0 z8_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 92 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRunT 92 true (goal 92) s xsG) : False := by
  have hmin : 6 ≤ s := by
    have hl := runT_len h
    change 7 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 7 fG 9 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 0) || (a == 1) || (a == 2) || (a == 3)

def perm_0 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_0 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_0 i)

theorem hperm_0 : ∀ y : Fin 7 → Bool, fG (substIn cu_0 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_0 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_0 y) ≠ fG (substIn cu_0 y') := by decide +kernel

def perm_1 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩
  | ⟨3, _⟩ => ⟨2, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨6, by omega⟩
  | ⟨6, _⟩ => ⟨5, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_1 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_1 i)

theorem hperm_1 : ∀ y : Fin 7 → Bool, fG (substIn cu_1 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_1 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_1 y) ≠ fG (substIn cu_1 y') := by decide +kernel

def perm_2 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩ => ⟨3, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩
  | ⟨3, _⟩ => ⟨1, by omega⟩
  | ⟨4, _⟩ => ⟨7, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨4, by omega⟩

def cu_2 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_2 i)

theorem hperm_2 : ∀ y : Fin 7 → Bool, fG (substIn cu_2 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_2 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_2 y) ≠ fG (substIn cu_2 y') := by decide +kernel

def perm_3 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨3, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩
  | ⟨3, _⟩ => ⟨0, by omega⟩
  | ⟨4, _⟩ => ⟨7, by omega⟩
  | ⟨5, _⟩ => ⟨6, by omega⟩
  | ⟨6, _⟩ => ⟨5, by omega⟩
  | ⟨7, _⟩ => ⟨4, by omega⟩

def cu_3 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 7 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 8, ∃ y : Fin 8 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 11) (hcl : SCleanL 8 gs)
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
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [1, 4, 1, 4, 16, 128, 32, 32, 42, 15, 28, 131, 28, 131, 42, 42, 42, 42, 56, 162, 56, 162, 56, 162, 56, 162, 56, 162, 112, 224, 112, 224, 5, 3, 12, 5, 5, 6, 6, 6, 6, 20, 129, 20, 129, 20, 129, 20, 129, 34, 40, 2, 8, 2, 8, 16, 128, 64, 64, 69, 15, 28, 131, 28, 131, 69, 69, 69, 69, 84, 193, 84, 193, 84, 193, 84, 193, 84, 193, 112, 224, 112, 224, 10, 3, 12, 10, 10, 9, 9, 9, 9, 24, 130, 24, 130, 24, 130, 24, 130, 65, 68, 16, 128, 28, 131, 112, 224, 15, 15, 3, 12, 17, 132, 33, 36, 17, 132, 33, 36, 106, 47, 29, 135, 60, 163, 43, 46, 58, 170, 57, 166, 58, 170, 60, 163, 120, 226, 184, 178, 113, 228, 116, 225, 37, 35, 44, 21, 133, 22, 134, 38, 70, 21, 133, 22, 137, 52, 161, 148, 145, 35, 44, 18, 136, 66, 72, 18, 136, 66, 72, 101, 79, 30, 139, 92, 195, 71, 77, 85, 197, 86, 201, 85, 197, 92, 195, 116, 225, 212, 209, 114, 232, 120, 226, 74, 67, 76, 26, 138, 25, 137, 73, 41, 26, 138, 25, 134, 88, 194, 152, 146, 67, 76, 144, 144, 156, 147, 240, 240, 31, 143, 19, 140]

def xsG : List ℕ := [0x172104f1055df5803561b90846e5572100f10555f5801541b00002a05, 0x1721ab0dc842372aa09e20abbeb00720aa0d80001502a01e20aabeb00, 0x1b12080202bbeb804affd60489eaab12000202abeb800abfd0000160a, 0x1b1257feb0244f55410040577d700b1055fe80000b05400040557d700, 0x5fcd5142eaa8a089aa285d55141105455002aaa0a080aa0055541410, 0xc000807980008066087fffff3cc0c000007800000060000ffffc1c0, 0xc33043fffff9e600100f30001000c300007fffe0e000000f0000000, 0xafcea28575514111d450aeaa28220a8aa005554141015400aaa82820]

theorem rowsG_len : rowsG.length = 224 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => ((fun x : Fin 8 → Bool => x i), taggedFn i.val)).map
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
    ¬ HasCircuitSize 8 fG 11 := by
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
  | 7 => 9
  | 8 => 58
  | 9 => 90
  | 10 => 11
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 7, 0 => 0x7d87fdbe6f09e92667eff1235c7b9a5a4ed729df2c14f29f18da8958102cdbd7034c7507
  | 8, 0 => 0xfa4709f1f5e83cbcefa210bfeb6a6b00d0844f92ce73c5ebc58428b3bc0b93e4ba0b1062b7335176b1880875acf84905a90581d29cbec18374c035aa73f5096d6ccb19c36b7b40505ca8c9b05c28bfeb3e8e9ba73be6be643a59ae3438ea95f138ddb96d36220875325cf6142bd60c9d2b22387329b892ff26772fad24ded35c230109f320de2e08206dcf8d1afaeac61af32afa1ad3f30719b4c87819914552196dda96181a5a1c180435221579556c153634d714c2d1d013cc8f63130bffbe0d373b9f0b152d7608ddf8cd0520032004de64de0356a09302e37ecc01566e9c0012b81d000bbfe0
  | 9, 0 => 0x667c51a5624e036160f2a4345fd7b23a5e8e7f1f5d5017f85d0c8d045b3d976959a2654458d4e74558ab924f55f1b2a654e6cd0e4adbbbbc4ac7d4e24a0f28f8467ebea4466c5597447811554446ef724320ae5d3fe56c203dda46ac3d0f87e03a59ae34375fa068346f02d332e5d4ca32a19fd5325cf61431f7bcfe2d2b49bc2cb992b52c25e8cf2bd60c9d2b2238732b1b03372af6b4ea294e29e32670f983235c774820435f211e581a5b1d274e341ace68d019e1b1dc196dda96189e56cb1804352217f20d6f15c12eca158ca77414dfcc72129fcddd0e459bf80d458ed00d1a148c0cbc4abe09609748091a0af307b9c9bf063daf9203b1704201566e9c
  | 9, 1 => 0xefa210bfeb6a6b00d813acbfced6658ace1a6fe5bc0b93e4ba0b1062b89fde1babb7c441a83e026ea6a085b3a116db0e9df3fd8394739f598ede76088d234c6b89db8c84878b075086d856db82ecc5157e313c9d7bba610d71a4bb8971741ed871547fe16d3414d2
  | 10, 0 => 0xefa210bfced6658ab89fde1ba83e026e5d0c8d042c25e8cf1d274e34196dda96091a0af3063daf9201566e9c
  | 11, 0 => 0xefa210bf
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x29e6aca2b9545447e557d15573ee84a2a8029550504355005555eae86c4820080aefae012bff581227aaac4800080aafae002aff4000058297fdaffd6c489eaab20081aefae01620abfd0000160a800080aafae0172104f1055df5803561b90846e5572100f10555f5801541b00002a053fef586e7211b955c4f1075df5803905506c0000a81500f10555f5803ff3fcf1fffe78667f9e3fffcf0cc3f3fc01fff878607f803fff0f0c01866087fffff3cc00201e60002001860000ffffc1c000001e00000000c000807980008066087fffff3cc0c000007800000060000ffffc1c0
  | 0, 1 => 0x5600d5417554608b2a6ba8d575777b4557fd5550a8bfaaffad55f5f7bc00fcf1e7fe78661f9e3cffcf0cc3f3fc01fff878607f803fff0f0c01ffe087fffff3cc30201fe0002001860000ffffc1c000001e0000000ffccf3c7980069999e78f3000d33ffcfffff8001f1f9fffff0003e3f2fe6a8a175545044d5142eaa8a0882a2a8015550504055002aaa0a086c495ffac0913d550401015df5c02c4157fa00002c1500010155f5c02e43561b90846e55413c41577d600e41541b00002a05403c41557d600afcea28575514111d450aeaa28220a8aa005554141015400aaa82820
  | 0, 2 => 0x2009400a4edd855537fdf944147fa77d500bffffa7d5fffdfd54147fbcf33ef000001867ffbfc33fffbffcf3fffe00007c7fffffc3ffffffde7fffff5dfffffff7ffea2abbfffeffffff5fffffffffffeaaaffffeafceaa87fd514917f4d7fffffbee0e8aa007d54141075400ffffe9e03fee27883aefac01eb0dce42372ab90807882aafac00aa0d8000150283ff030e18018799e061c30030f33c0c03fe0007879f807fc000f0f3c00661870cfff2cccc30e19ffe59800600000fffc1c0c00001fff8380bfec80206bbeb805affd6c489eaab12000202abeb800abfd0000160a
  | 0, 3 => 0x6010002baa8800000005100000004000002aaa000000000500000003ffffdff5dfffdfe77de2baa8b0cfeffffff5ffffffe7fffeaaa0f8fd479d4500caa2822328a00000104405154000aa828202a800000050407e1ab0dc842372aa09e20ebbeb00720aa0d80001502a01e20aabeb007892bff581227aef1d5782bbebeef8a2affc0000587f55ff82abebefbcfffdfe19fffdfe67de0000030cfcfffffe1ffffffe7fffc0000f8fce4209e20abbeb006ac372108dcaae4201e20aabeb002a8360000540aa032aebd15575f7655d7a2aaebeefabaaffd555f5f7f55ffaaabebef
  | 0, 4 => 0x7ffffbfffffffffccfbc79800699fffffffffffffffcfffff8001f1f800cc10e19ffe598004000000000000c00001fff838000000000000000066087f3fff3cc00201e60002001860000ffffc1c000001e000000050315d7a8aaebeee2baf5155d7ddf5755ffaaabebefeabff5557d7df5890401015df5c0257feb0244f5558900010155f5c0055fe80000b0503f30201fe000201f821fffffcf303000001e000000180003ffff07001f980000c00000030000180000000000000000000000000000000000afffa6bfffffdf71d550ffaa29220ebaa007ffff4f015400faa82820
  | 0, 5 => 0x619861fffffcf3330c3fffff9e606180003ffff070300007fffe0e0030000014400000010002baa8800020000014000000000002aaa000017a410040577d70095ffad8913d5562400040557d700157fa00002c140fcc000570000001c000aeaa200008000005000000000000aaa800000619821fffffcf3000807f80008006180003ffff07000000780000003cf33cf000001866679e0000030cfcf3fffe00007c7e7fffc0000f8fc1800000f300010000001e60002001800000f000000000001e0000000500059400000208e2aaf0055d6ddf1455ff80000b0feabff0557d7df
  | 0, 6 => 0x7819fbfc03fffbfc0fbc00000619f9fffffc3ffffffcffff80001f1f800c030e000187998061c00030f33c0c03fe0007879f807fc000f0f3de7fffff0cfffeffffffe19fffdffe7fffff0fffffffffffe1ffffffef3ed7feb0244f5ddba2c0d77d711b1455fe80000b0d4aa040557d7105892bff581227aaa080202bbeb805882aff40000582a000202abeb802b0cebaffffff7dd9575fceabafbbfaeabffffffd7dfd57ffeaafafbc0064087a2aae3cc00201440002001060000aaabc1c00000140000000f3edd1606bbeb88daffd60489ebbb16550202abeb880abfd0000161a
  | 0, 7 => 0x7ffffbfd77fffbfcdfbc2eaa8e19fbfffffd7ffffffcffffaaaa1f1f8300000018000000000000000000000000000000000000000000000015f9d450ffaa29223a8a1ff5452441d15400faa828202a801f55050405fcd5947faa8a88feaaffffff7dd0d455007aaa0a086aa00ffffd5d07fe67de0300030cfff7f867fff7ff9e7fffc0000f8ffffff87ffffffbc0cffffe7ffffff9ffffcffffffffffffffffffffffffffffffffffcbffabaf5d55d7ddf575ebaabafbbeaeabff5557d7dfd57feaaafafbe500151428aa8a0882a285155141105455002aaa0a080aa0055541410
  | 0, 8 => 0x60080017554400010002eaa8800020000015550000000002aaa0000030cc10fffffe79810403fea8840030c0001ffff838000003eaa000001800000f30000000c001fffe60001800000f000000000001fff800000c0000028800000000005100000004000002800000000000500000007fe6fde1755470cfff7faeffff7ffbe7fffd5550f8ffffffafffffff800000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffe0c010002eaa8800000005100000004000002aaa00000000050000000
  | 0, 9 => 0x7fe67de3cc0034cfff7fffffffffffe7ffffc000f8ffffffffffffff83000001e600020010003fea884003000001e000000000003eaa000015fff5d7fffffbeefebaffffff7dc1d75400ffffe9e0ea801ffffd3c05c335d7fffffbeee2baff355d7ddfd755ffffffebefeabfff557d7df07e70002baa88000c0005700000004000002aaa000000000500000002800a8a145545044151428aa8a0882a2a8015550504055002aaa0a081ff9ff78ffff3d33ffdfffffffffe1f9fe00fffc3c30ffc01fffffbe00031043a8aae9e6001005100010004300002aabe0e00000050000000
  | 0, 10 => 0x29e628a000001044d514062a8a0880a2a80000005040550002aa0a0800000200000000019821c33ffcb30000000000000001800003fff07015f9f450ffff38223a8a1ff5450441d15400fffc28202a801f550504053cd514062a8a0898a2800000411014550002aa0a080aa0000001410
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x4830a082408070c28209102c8b9014101820201c786141048010e18504123808070c282030434038c0c28209102dc30a08240880ee1828406080807
  | 8, 0, 0 => 0xc28209040402180c282094a0040b84818504120510b84628209020040b80c282090405121834185041280f8b83c18504120459d80c2821c020040b83618209020040b83418519120440b83018504060400880c10497020040b82c18513120040b82c18504120040b82a18504125008b80c289891a0040b8
  | 8, 0, 1 => 0xc282095ea440b80c28209280570b8485830a082400b82c18504120802182c8c504120040b85a28209020040b80c28989040400b80c28209280560b82014209020040b84818513120400b80c28209560040b8541850412a440b850185041200f8b80c28989040402184818504120400b84e1850412205a68
  | 8, 0, 2 => 0x6e18504120440b82028203020040b86c18504120402186a1850412bc40b83090d06141048182c18504060040b82cd0304120040b83019984120400883068b0614104888481850412bd48b8488c504120400b82028989020040b82028209020040b86418504120043186028209020040b82028209028840b8
  | 8, 0, 3 => 0xc282091a8840b87618504120040b80c28209020040b80c28209028840b8741850412080808301850412500ae8721850412040388309030a08240808345830a082440b83418504123440b8
  | 9, 0, 0 => 0x1850412080804305830a0825e00102e4d061410481102d0cba0c28209020040b9301850412040085d2d430a0824080102e5906141048100205c980c28209280400893418504120441f17218504120400816fa430a0825e8100205c980c28209020040b90c28209400041f1721850412f0080102e430a082408000205c802c18504120040b8
  | 9, 0, 1 => 0x4e1850412040081725830a0824080102e4006141049402b85c00485830a082400b8721850412040081726830a08240885c2e430a082468100205cc30c28209020040b934185041250088172185041204008170a60980c2820902004486141048100205c09305830a0824008172185041204008169a40240c2820902005c3f3418504120440b9
  | 9, 0, 2 => 0x2a1850412040081721850412bc029102e430a082648100205c86141048100205c890c14209020040b4321850412500805c2e4b160c2820900205c86141048100205c7900405041204008170185041318080102e609a0c2820902205c984818504120400b90c2820902022881720030a08257a9102e0b061410480102e1486141048100205c49
  | 9, 0, 3 => 0xc28209020040b17218504120404e102e4d06141048152205cb60c28209020040b930185041204008632185041334080102e430a0824080102d0c980c282095e040089989030a08240801721850412051081686430a0824080112c5ca42c18504120400b9729030a08240801726030a08240805222430a082408011285ca40c2820902005c29
  | 9, 0, 4 => 0xc28209020040ba72a830a0824080102e4b061410480102e94a40c28209280400b90c28209040400b432a030a0824080102e430a082688100205c9a0c28209040440b94818504120400b4326830a0824088174252061410481007c5cc10c28209020040b99e5830a08240081726030a082410100224d0614104af02205c861410494780440b9
  | 9, 0, 5 => 0x6141048100205c000c28209028840b84818504120400b712185041208080102e4d160c2820900205c80309030a082408080068b0614104881701850412bc080102e4c180c2820902004486141048100a440b9
  | 10, 0, 0 => 0x30a0824080102e030a082410100205c8614104af020040b90c28209020148817218504120400816864b06141048100205c86141048100205c09009030a08240801706030a0824080102e430a0825e0100205c802c18504120040b8
  | 11, 0, 0 => 0xc28209020040b8
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 7 => 53
  | 8 => 60
  | 9 => 67
  | 10 => 67
  | 11 => 60
  | _ => 0

def idWidth : Nat := 7

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 225 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x7ffffffffffff0000000000000007ffffffffffff, 51)], [(0x55555052aaaaa2aaaa0a5555545555555052aaaaa2aaaa0a55555455, 1), (0x140000000000000000000000000014000000000, 50), (0xa000000000000000000000000000a000000000, 52)], [(0x554005000000000000a000000000554005000000000000a000000000, 1), (0x55414aaaaa8aa00000000000000055414aaaaa8aa, 50), (0x1000003000000000000000000000100000300, 51), (0x2aa0a555554550000000000000002aa0a55555455, 52)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 112 true (goal 112) u ys) :
    NatRunT 112 true (goal 112) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 8 0 (NN s)

def poolG : List Nat := [12395914658483312, 12394803305237617, 12395913590983793, 11267826524525731, 9017105717510258]

def Z (s : Nat) := bar 112 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 58 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 48 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 58 → Z 8 i = true := (range_split z8_0 (range_split z8_24 z8_48))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_24 : ∀ i, 24 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 72 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_72 : ∀ i, 72 ≤ i → i < 90 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 18 72 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 90 → Z 9 i = true := (range_split (range_split z9_0 z9_24) (range_split z9_48 z9_72))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 11 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 11 0 = true)

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
theorem rootChecked : span RootG 5 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRunT 112 true (goal 112) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := runT_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 8 fG 11 := mainG noRunFull

end Sub_1

def taggedFn (a : ℕ) : Bool := (a == 0) || (a == 1) || (a == 2) || (a == 3) || (a == 4)

def perm_0 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨8, by omega⟩

def cu_0 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_0 i)

theorem hperm_0 : ∀ y : Fin 8 → Bool, fG (substIn cu_0 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_0 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_0 y) ≠ fG (substIn cu_0 y') := by decide +kernel

def perm_1 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨4, by omega⟩
  | ⟨4, _⟩ => ⟨3, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨6, by omega⟩
  | ⟨8, _⟩ => ⟨8, by omega⟩

def cu_1 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_1 i)

theorem hperm_1 : ∀ y : Fin 8 → Bool, fG (substIn cu_1 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_1 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_1 y) ≠ fG (substIn cu_1 y') := by decide +kernel

def perm_2 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨8, by omega⟩

def cu_2 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_1 (perm_2 i)

theorem hperm_2 : ∀ y : Fin 8 → Bool, fG (substIn cu_2 y) = fG (substIn cSub_1 y) := by decide +kernel

theorem hnc_u_2 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_2 y) ≠ fG (substIn cu_2 y') := by decide +kernel

def perm_3 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨3, by omega⟩
  | ⟨1, _⟩ => ⟨4, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨0, by omega⟩
  | ⟨4, _⟩ => ⟨1, by omega⟩
  | ⟨5, _⟩ => ⟨8, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨5, by omega⟩

def cu_3 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 8 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

def perm_4 : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨4, by omega⟩
  | ⟨1, _⟩ => ⟨3, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨1, by omega⟩
  | ⟨4, _⟩ => ⟨0, by omega⟩
  | ⟨5, _⟩ => ⟨8, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨6, by omega⟩
  | ⟨8, _⟩ => ⟨5, by omega⟩

def cu_4 : Fin 9 → Sum Bool (Fin 8) := fun i => cSub_0 (perm_4 i)

theorem hperm_4 : ∀ y : Fin 8 → Bool, fG (substIn cu_4 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_4 : ∃ y y' : Fin 8 → Bool, fG (substIn cu_4 y) ≠ fG (substIn cu_4 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 9, ∃ y : Fin 9 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 13) (hcl : SCleanL 9 gs)
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
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_0 ⟨0, by omega⟩ rfl hnc_u_0 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_0 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_1 ⟨1, by omega⟩ rfl hnc_u_1 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_1 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_2 ⟨2, by omega⟩ rfl hnc_u_2 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_2 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hev
      dsimp only at hsz
      apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply PEqualNP.Outside.L_meta_10662_aux.Main.Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [4, 64, 1, 8, 1, 8, 32, 256, 64, 64, 82, 82, 31, 82, 82, 82, 82, 112, 322, 112, 322, 112, 322, 112, 322, 112, 322, 112, 322, 224, 448, 224, 448, 60, 263, 60, 263, 9, 13, 13, 27, 3, 24, 5, 12, 4, 128, 2, 16, 2, 16, 32, 256, 128, 128, 137, 137, 31, 137, 137, 137, 137, 168, 385, 168, 385, 168, 385, 168, 385, 168, 385, 168, 385, 224, 448, 224, 448, 60, 263, 60, 263, 18, 22, 22, 27, 3, 24, 6, 20, 32, 256, 224, 448, 224, 448, 60, 263, 31, 31, 192, 3, 24, 36, 260, 7, 28, 56, 259, 27, 27, 68, 68, 33, 264, 65, 72, 33, 264, 65, 72, 86, 210, 95, 83, 90, 114, 338, 113, 330, 114, 338, 116, 326, 120, 323, 240, 450, 368, 354, 225, 456, 232, 449, 61, 271, 124, 327, 73, 77, 141, 91, 67, 88, 37, 268, 132, 132, 34, 272, 130, 144, 34, 272, 130, 144, 141, 201, 159, 139, 153, 169, 393, 170, 401, 169, 393, 172, 389, 184, 387, 232, 449, 424, 417, 226, 464, 240, 450, 62, 279, 188, 391, 146, 150, 86, 155, 131, 152, 38, 276, 288, 288, 228, 452, 480, 480, 316, 295, 63, 287, 196, 35, 280, 292, 292, 39, 284, 312, 291, 59, 283]

def xsG : List ℕ := [0x791700314155dfc005fb908118aa722e006282aabf800bf400001014, 0x791700bf72102315418a0aaefe00722e017e8000020283141555fc00, 0x43cf998de00601403c6f00300a01878f031bc000020038de00001001, 0x76268050a0abbfc00af7604229546c4d00a141557f8015ea00001028, 0x7626815eec08452a8285055dfe006c4d02bd40000205050a0aabfc00, 0x1dd3ee80abaaa80444055d5540220881540155554008000aaaaa0040, 0x878081e60008003bcffffff998010f0003c0000000001ffffef02, 0x878779ffffff33040f30004000010f0003ffffde04001e0000000, 0x2ee5f70155d55008880aaeaa80441102a802aaaa8010001555540080]

theorem rowsG_len : rowsG.length = 222 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 9) => ((fun x : Fin 9 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 111 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 111 true (fG, false) = goal 111 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 111 zs &&& lo 111) ≠ lo 111 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 13, ¬ NatRunT 111 true (goal 111) s xsG) :
    ∀ s ≤ 13, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 111 true (goal 111) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 13, ¬ NatRunT 111 true (goal 111) s xsG) :
    ¬ HasCircuitSize 9 fG 13 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 111 true (encT rowsG 111 true (fG, false)) s'
      (ws.map (encT rowsG 111 true)) :=
    RunT.map (encT rowsG 111 true)
      (fun a => encT_inv rowsG 111 rowsG_len true a)
      (fun a b => encT_and rowsG 111 rowsG_len true a b)
      (fun a b => encT_or rowsG 111 rowsG_len true a b)
      (fun a => encT_tag rowsG 111 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 8 => 65
  | 9 => 471
  | 10 => 673
  | 11 => 187
  | 12 => 11
  | 13 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 8, 0 => 0xe0214d45d63770d7d358c389d0dac9e2cf61912fbdcdd5febbf41316b9374680ae8e075e9f6db2509bb393459a9961fd952903f69280a3848a89ea708063fd7779081cc67376eeab7225a7ed6aa5831e69990dcc64a4508763bd0ce1609f98e65c69a26a4b9ec88a4b9bce454a8f58f3461bb09743e0e62943b1085a3dcc88353b5957353b3834a938a5136230c5c4c33059041f2f1921192c75c38b28fc41a228026e162711fbbe2695660624a7538123b565371f6385131d6628421678eaed1419f41c1365782a110160320f9bdef00dc2f3b40d6c0eb20d48678e0b1fe4cc0addbf510acce5b60ab760c008b1121e0834da380820f2bb080b5a15027b2b0c
  | 8, 1 => 0xfbfd9591
  | 9, 0 => 0xd6298400d2db67b0d1b85770d0f19b60cda298e0cba90840c9c27360b2f6a2b0b143f4f0a84ef100a69b2c60a5c79b80a1d5cf80a13bf1a0a05d9de09d41b4e09bea10e097bf97508b759e708b513f608b0b1ce08a5f8800833e6e407bf8b9907b5991407a9065706e61c5d068cabe40687636c0685320906714a8c065816dd06366e3505b2a1ae0531bd77051f1b4d0456cd300415837703fb1c0403f9bc1703e291c303b87241039ee5500385067802dcc80602a8e28902a49d240241f0440233d1b8020d131e01ce349601bd953701859e71017540780128e9fb0123e81200d1322a00bc72a200a6a9430091ed450070ec1300397a63001236e000103daf
  | 9, 1 => 0x1bb339761b1301481aaefbd31a380d021a19924f1905638018e217141895688d1893c49b1858e401183a746717e7a4c817e513621791f0f6177b82a817646b4117315b3116ed15f516a0c4da16664c8016189523157cfc8b156dd13f14ba149a146ed31a1433663314214ee7141f2b3c1419f41c13fb3dd713b87a2713b6eb7613b60e9e137dff08137031de135b8f46133b3b581339eb471321457b12e0f3eb12c3218c12c02ff512bde69f12a1eb03124ed29612494ded12211511120ddd6111ea9eb1116c50411151e8281101603210f9420810ccb9d21052985f104f7b030fb77cfb0f72a78f0ef8fcb50e7941130e6ee4110e3932ad0e087f980df985bd
  | 9, 2 => 0x2ec131d42eb1513e2e6896622d54413d2cb728682c084ed92c07a0a92ad8a3c02aacac54299c518d2935d9212920f651291ed11528fda9e528d0d4f82890e7fb27815265277f26072779fe132702ee2e26fcb75526ea975426bda43f26a5c8842665801726486cae25b12eed255d243825292d7324a47eb5248cbed423e9bdac23d85ec623cdde9623759b3823058b6e2197c189218bb6e2217f690d21604d2e214400932118282720fc342020e84ca320e73c04207ef5512051da25203adebc202896721fe148901fbd9fed1effa0e71ea0282a1e50bf011dcfcdde1d7955741d66651d1d186b201cfcccc01cbf66001c5fab5a1c06af631c01dabd1bffeb32
  | 9, 3 => 0x42063b954201602b41df84254154975b41465cbb40917c67408636e9400e29dd3ff2017c3fe81e523fc626813f4493953f200e073ef8858e3eb4a0ac3e85c96b3e56144b3e33efeb3e0d372a3dfc5e773db3bddf3d9fa61e3d1f9c403d0eb5443d0e72df3d0805b33ce6c2363c9006153c78bdfc3c4d604c3c3461603bf66b243bebbecb3bc16ee03b792c553b6bb8bb3b0346ac3aa886263a36497b3a113bd739f430f4399093b63909c86038a67ba5382d26fe3766897736fa188e353cd16e3304f2b032c92e4a32c22f0032ae77c8323a9fe031eaa8c431bff8063117c6f13117b90730c5c4c330b178b33071966d2ff3e02a2fdd6b782fc738282f4950ea
  | 9, 4 => 0x5e9fa4f35e4fd2995d9a3af85d1a7fa25c7862425c0cad6e5b99baee5b85d3715b6fa34b5b2392dc5abca5ea59bb95ac58b36e35575dc44d56ebfcf45602d90454f8275e53860e7353766bd5521cf2fc51585de95129115a50e0abdf50de8f1c50456cbf50217bca4f6026664f029bc54e98c4a54e5600f54e449de04d3b2f114d0c49ff4c8e8fb44c515d054bdd33204bb88c9c4b6a40a04b62e7c24b1caac14a8f58f349e70e9949e0b52b49ab4e7c48dfb0c448ceed40486271f54836bea64801dfb847bc998247b752d347aca08447aaf21e469386de452d3e544523ae6b450c8d1f44a66f9c443fccc843e0e62943b7d35043a077b04320858142f77394
  | 9, 5 => 0x89af748b88e0dd5688de31a78885a6a787ca93fe879bb4868703ff6c868d00ef85d4412983a6b436834c301983244a00826f8c5b826067b480a59c71800cb6337f2f58ee7a76dc74787c31587804f86e7718e81e76bbc0037693f1f2767789dc75e6a56275b8b304758d69f9754f67a1747415fa73dbd74972d5212f729fe685700ed6816fe5e05b6fc6cf266f4990576f3872746e1ec4186d40a6846d137b1f6bb54dbf6b80a53f6b1bb2ce69ac6ade69990dcc67e9659d67834c16652840be647485ac62fd808762f8d18f62b60ddf62b3aa56623565be61de5f0561d51fa76174921f616b4683610a88f5606848ae602aac795fca4d8a5f6226575ef22f26
  | 9, 6 => 0xc8c60a11c7a33122c52ba2adc45d0523c44cfb59c41a4173c23026a9c12e811ebeb07b61be52a87cbdcdd5febdbcfcccbcfdee82bc4c7e20bafb77c6b70a5f82b2544693b0842c30afa8d174af7dbe13ae94e890ae8e075ead150d7fac401ebbab620e7daab4a096aa909d30a8b92964a8a541e7a88fa941a816173ba5d2dcaba4cd16bca345fab5a2dc7cb2a220d2e4a14a5d839f60920b9eec16d09e74ffb19df439a99c2d43e49bb393459b756f6b9980914d98edfa0998eb9cd19889af169819b0119800aaa997dd447c9715e9109551ed5c94f05a3b94591c7a939ed37491fb4b1b908840ee8f851c1c8f3989d58f27da0d8c2b743f8be6adfc89e84c2f
  | 9, 7 => 0xffc9297bff470a28fbfd9591f8ce7e12f5ccfeaff09dbd69eba49991eb13a81fe88de4ace769a563e73874bde6fe3e61df2d48d3df276b72d87a0f91d63794c7d4b8b21ed487c8a8d3623cf4d14a13efd09ca608ce77aeb3c974702c
  | 10, 0 => 0x86e33ac086420d1083b222e081a5ccc07cd70f107bf8b9907b599140733fd9406cd78b10691fd5b05e5a47205b2a1ae057e6b58055c262304f3999d04ecbf3f04e3ce9a04b2ac5a04751ba504370ae00427b4f00407bc2203fc141b03f66b4403e291c303db71a103d291c903b9dd6803897c4f03850678035adb9f03559f6d0354ed4e03541d31034d11e4031c5d5902f7525202f43f1e02d50c2102b88c2302a36efc029b8e94027e3cd30254fa5e020c117c0209ec8301fe2f2001e47cfa01d22ea201ce349601bd9537014dd8bc014c9916014c22290133384300f4f4f500c8423c0086f1930082ba7f005bbc40004c5d75004a0269003519e4002cbb6a
  | 10, 1 => 0x13b853b9139c43e81362af281358bca7133b3b5812f4e8dd12bde69f125f6d67117d5012116c5041113a4b26113799261127ef1c11180fd1110569c610dc33af10add36a109c786910988ea9104c8598104b5af41048dc730fe586a80fcddf830f6c34910f5c064c0f3a1ab10f23957b0f1acbf60ec81eb60ea867c10ea0141e0e8081110e7def840e6ee4110e061a050df985bd0df5a19b0d6aab4b0cea00ed0cda298e0cc9deb30ca8a9a00c6d71d00c6d712c0c399ceb0c2009460c0a6b6b0bd60e200b999e9f0b935fad0a70f3d20a2112eb0a1d5cf80a0f2b3609dc4e4b09cb47a809a2bc3c099d30b6093e8d8c093dd8d50938721108e2529d086e4ba2
  | 10, 2 => 0x1d197a9f1d11d8041cfceeaf1cee02661ce571841c9551dc1c88c6ea1c6169951c5fab5a1c4ebda61c280fb11c1662651c01dabd1be7ae831b8a350b1b84178d1b5f3a711b45e5711b3c316d1b1c5a111ac155a91a7f82211a67097f1a5bece41a19924f1a1531d019ee14b619a1f2ca1963c33f17eea7c517e5136217d9c31f17a3e029172e35261718411e16f5e60916b79f11169d110b169a014b169537ea167042e3162913981609eb911606f29b15d3b6cd15cdafb115cb983d15c0e98515ade5a61559c38b155677fe15442d90153101ee151abaff14f8652614f1b9fc14cee7af149b2fd514982f39148fcc3f1439f8cb142769d613e1076213b87a27
  | 10, 3 => 0x29ce7774299a4037297f56102960260929148f242909c82929008e4828df604f28df57c428a5997928a452ea2895de412890e7fb2878aac3283606ef27f0ef85279cfd3a27884e98270edb08270d9feb26e1970726ce14b826833244266cbb4e26486cae262293b925ef3f6325eaaab525cd53c825b12eed25793a5924cec081248cbed424769f69246ab71a240186be23d5fec523bd7526238346eb2346399c2333bf3e23058b6e22ccd60222a5c17e228a68ca21e7663521169bdf20ca4c85205d7362204584652036d5b1202896721ff67ee11f53fd641f09ba4c1ec50e141ec0b8f01e6d61bc1e4f3b461e15a28e1dd534e91daa58881da2eff61d6b5d49
  | 10, 4 => 0x39578479391da1e138ae8804387cd60a382f435f3824e025379a383c377c0866371c964d36f27aa236bbf4b4369243173669fe4f3663dfb03653f01035d7914735d63c883518978134f7953434dd6ba634bb18f1343dfe0f343df475333023f3332f2d5b3323c9c532f5f47132ed270f32c22f00327f9a47327338c83265a9dc320a6572317987893136441c3116954830e8d3d430ac2051308c34fa30429a542fd7149b2f8f43942f57b44a2f1496922f0406342e95c8a82e3b2c172ddcf8682dcc61f32da4fe7d2cbb10692cb728682c8eadd92c8e43442c4057f42c1e43b92becfca22bdef0472b6babbb2b513c7d2ad8a3c02a676c2d29efb01d29e2c672
  | 10, 5 => 0x4a8c383d49c35d0a498b98a9496c360a4957a21e494969de490e59da48dfb0c448df8a5648ceed4048a857f5489d9e89488661c4486271f5480cc0a04774abf046ae1d314626b7184580aed045729191448fad2b44439a5943b7d35043a5262142e924c842a52210429e16324273caaf4226e23d41cfb3f541473fe3410e18ad407cf58c4067923a3fcdc6033f0384e83ed473383eb4a0ac3ea2df733e9ad41f3e7888d53dfa49023d9d8d123d956a493d9388123d907f463d7d0a333d4161c83cea7d973ccdb3443c85d96a3c842c123c2c5eef3c195b583c1780543bfc5dc93aaf0a723aa886263a7884613a368ec33a36497b3a113bd739b5b0453981bae1
  | 10, 6 => 0x5f60c6bc5f32af6d5ee243175e6d3e655d823dae5d554dba5d32014e5c4e4a8f5c3611a55c2ee7fa5c1b8b305b9c8eb25b6fa34b5b2392dc5972181458fd483057920417578f2d9156c34adb56097dda558110db54f20d6854dff16153ec44b1538a26e252ca2693521539035204f8115175f443512a13c85129115a51087b5c508a3b89502ed014502d20a0502983fd4f8e401c4f4c4f2d4f3c686d4f240c074f21f9594ef8af6d4ecd0e984ec765c14e6d47324e6b12214e5600f54e1e0c614e0f417d4e08c01a4ded01534db831e44d0c49ff4d00f9bc4cfd41e34cfd37664ca3291f4c8e8fb44c6969d44bd4c4e84bcf1bf14b62e7c24b50dc1e4ae8a520
  | 10, 7 => 0x7e7ed8bb7e7511a17c86c5697b4dedb57adc83ff7a8ca5a0796ad0f679160fa37903c0577804f86e77c54ccf7718e81e76caf99176883488758d69f974eccc4774e8f4ff7412a3ef739fbf727384743c732280a372a63452729bccba71ad1007713db5cb70e74cc87073c3566e4e34816e1ec4186d5007706cc3e9db6c93126d6c19b13f6c1024636bc9902d6b9134ec6b3bbf696ae021226a49b00769a8356068459efc67f069a767e9659d67b153ac679a6f6566100a7165f9710664fb843264d14a8564ace7f4647eeae7643b93df63f4d1c263b7bfd063704510636262b462b60ddf6248c173623565be61beacfa60b6c0a4604cfc715feadb355f67e1fe
  | 10, 8 => 0xa04d78a79fcb59549f60920b9eb404a59e570a2c9df439a99dbcc1949d17a0449ce201c39b756f6b9b6709579b20a7a39a2a70f198ded2c698ca4c1c98977bad9858f620980e6c4897dd447c97ce31e39635529a95d36723951211d29487fd59939ed37493575c4192a9744b92526b45924d07689218e8b9920abbaf9175812c9050ab598f73ce738f2f94f88d761c8d8cd652978c24121e8a1944058a17393b89dcde57879c4c1e872c2eae870fef0886ba687f85d441298554573d85319ba38528605984d3d04083e3408783cac2e3835246608336781a82a35d7a826067b482268b8782246e03821703aa8205fe068024ec847fb36eda7f5a81487e887407
  | 10, 9 => 0xcd2dc3c1ccd6f883cafd848fca20a0b9c87e92dec7743e05c6c198ecc6357e19c5b503edc5aaa774c59fc773c59e704bc5962f18c45d0523c41a4173c29d532ac18ef1f7c14f0ec9c12e811ec0ce09ecc04ffe62bf1eaff1bf0414f4bed50e2dbed0835ebecc3639bd9331ccbcfdee82b93425cab8c35a5eb73e2cdeb72038a3b6758f8bb5d6bd34b5b2fd37b56b3ab2b43ec368b39be58bb32b98abb2913ef5b2835c99b2544693b14a9a8ab031422cafa8d174aefeff70ad207662acba6378abed7b3dab6f4474ab570b8aab2dc6f7aabbd5b2a8bcdf57a8ad685fa854e253a3e19133a37bac34a3756b1ea2c5071ca237a6b8a1a330c5a0f0c6caa07350fe
  | 10, 10 => 0xfe6f2157f504b55af4bb8fd5f09dbd69eeda5021ec045c79eb13a81fe99c863ee92804a9e73874bde6fe3e61e617d957e55878c9e3a8f73ee1eb401ce139e29edda7b046dd145541dc40b793db21a5d6da68e022d79cee4ad64d2893d4c7f7bfd4755122d4529588d2734045d14a13efd1320a1fd09ca608cf4115caced468bfce77aeb3
  | 11, 0 => 0x26486cae24ad6ea3244c60a7240186be238346eb23276da920ca4c851da2eff61cfa2bb61cee02661b1c5a111a67097f1a1531d019e08fd0199a5ecf194fb1e7191c1efc18befe32189ddf29189a8faa17eea7c517e5136217b1aac8177d039d16f5e6091609eb9115ee946115ade5a614dcc056148fcc3f13b87a2713b853b91368bf8a1341d619133b3b5812e113a812589e8310f81282104b5af4102e1f67101da8920fa381580e8081110e7def840d877fd60d0940030c2009460b64704e0b46dc9a0ae6307b0ab89f5f09dc4e4b086e33ac05553366053b774604f3999d04a8adbd04751ba503f66b440254fa5e01e47cfa01bf3d880174a0dd011a05e2
  | 11, 1 => 0x636b8a27636262b462b60ddf607fcd5d5feadb355f60c6bc5d823dae5c4e4a8f54f20d68541dc9bd53760e785204f811502d20a04ef8af6d4ec765c14e5600f54e1e0c614e0f417d4c8e8fb44c459b5a4b77c7754a8c383d4a40492a49fc66ab4957a21e490e59da486271f54626b718460dbe9146025afb4544df2f44439a59435dacf4429e16323fc7b7163e7888d53d9d8d123d7d0a333c85d96a3b842aaf3a7884613824e02537b79b7c3661d82135a315be3568fa0032c22f0032b00287327338c8319f4a26312dcc7c30e8d3d42fd7149b2fc07e772f1496922e3b2c172d9fe6df2d938cb12bd316442b6babbb2b5896c029e2c672279cfd3a270edb08
  | 11, 2 => 0xfaa74c05f4bb8fd5eeda5021e92804a9e5d2bd86dc40b793db21a5d6d876eedbd7cc5eb3d64d2893d0fe2f07d088ccd0cd5da55fcd2dc3c1ccd6f883c9690567c7743e05c6357e19c41a4173c2f7d034c2ee55cabe924f0fbd0d1616b78d6bafb711ae2ab4f17161b031422cad80d1d2aabbd5b2a7668e8fa153e8159b756f6b9b6089b697dd447c97ce31e39487fd5993575c41924d07688d761c8d8ca280f08a20d56a89dcde57848ba13d7fb36eda7cc506bf7b5dddee7aed2f4e7a79009b793a7e4878ee9ba7754c46eb7258f7ec71ad10076f58b7eb6e4e34816daad4266745e8186600f7d863704510
  | 12, 0 => 0xeeda5021c41a4173aabbd5b2924d076862b60ddf5f60c6bc4ec765c14a8c383d3c85d96a16f5e609133b3b58
  | 13, 0 => 0xc41a4173
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x7fef0f10c00000199f7e19fff7ffffde1fff8000043f7ffc3fffffffe45c02fdc8408c5506282abbf801c8b805fa0000080a0c505557f003c8b8018a0aaefe002fdc8408c553917003141555fc005fa0000080a7626815eec08452a8285055dfe006c4d02bd40000205050a0aabfc00ec4d00a141577f8015eec08452a8d89a014282aaff002bd400002050ffdffe07ffffe033303fffff0198660ff00fffff0060007ffff803007e7ffc6f0c300a01e3786180500c3c7818de00001001c6f000008008cc9fe081fe0008003bcffffff998010f0003c0000000001ffffef02
  | 0, 1 => 0x7dcfcebddb108a55050a1abbfc00d89a057a8000040a0a141557f800f75f98c507577f0017ee720462a9c8b8018a0aaafe002fd000004051f73f32850d5dfe0057bb62114aa36268050a0aabfc00af50000081443cf998de00601403c6f00300a01878f031bc000020038de000010011993fcef3fffffe66081fe0008000021e0007ffffbc08003c00000000021e020798002000ef3fffffe660043c000f00000000007ffffbc081e7fcc6f00300a01e3786180500c3c7818de00001001c6f00000800800878779ffffff33040f30004000010f0003ffffde04001e0000000
  | 0, 2 => 0x5ddbfe12bfeaa111177dffffffbb2225f0057d550020002bffffdf04774ffa02ffaaa0111037ffff00882207d005f5550020002ffff80101112348465d5540445dd28d55deefbb72dff4aaaa10bdffa5aaaffdfbb3701bf7210231dcbba0aaeffddf76e0bfe80000217bff41555ffbf5dcbee02abaaa01110155d5500882205500555550020002aaaa8010088b045fd51555feeefea8aaaff77ddfaaffaaaaaffdfffd55557fefd776c7bb651557fddc252ed5422208892c014aaabef8200a5aaa00403ff787f7e19fff7ffc43000000667fef0fffc3fffffffffe000010fd
  | 0, 3 => 0x3ba7dd0157555008880abaaa80441102a802aaaa8010001555540080e45d80c505577f0017ee720462a9c8b8018a0aaafe002fd000004051772ff80effffc0444057fd5402208817c015fffe008000afaaa00401ddbfef7bffffff77445ff5544220891f4017ffffde8400beaaa0040001000fc00000fe667e000007f33ccf807f800007fcfffc00003fe7eccd86607f9ffe033303fcfff0198660ff00fffff0060007ffff803000040c040f30004001de79ffffccc00878001e0000000000fffff7813626e050a0abbfc00af76c4229546c4d00a141557f8015ea00001028
  | 0, 4 => 0x5ddbfeefbffffff76081fe1108000021e0007ffffbc08003c0000000bb97fc057fd54022203bffff0110440be00afaaa00400057fff80200eedff445ff5544223deffffffddc448fa00beaaa0040005fffff7a11dd3e60001c0888005b99c8118aa00000000000000000000000000007bafcd7ee720462a83141d5dfc00e45c02fd0000040506282aabf800776e5a22d72aa2111ee68aaafeee22469005a5550020002d5557bd09fffffc03f3000466601f98002333ffffffffe00010fdffff000087ebfff9f8de006014cfc6f00300a67ffef0fffc000021fbffe000010fd
  | 0, 5 => 0x230314224ef75aafaf5e54403ff2765fa857ffffbf5f5ebeaa807fe332799f806001fcccfc03000fe6799f00ff00000ff9fff800007fcfdffbf35fb9c8998aa4c517577f22391700bf40000101418a0aaafe003ff7e7bf7790631dc18a0eaefe00722e017e8000020283141555fc000450328118dfb9d57cebe2a203ff1ba3fd02fffffbfaf9d7d55407fe08a0673af8a880ffe8118dfb9d563747fe75f55501ffd02fffffbfad11234bba51aabbddc232eaaa0223bb72dff4b555ffbfffa5555085e911a08feaa2aaff777f551557fbbeefd57fd55557fefffeaaaabff7f
  | 0, 6 => 0x5ddbfeffbffffff777fdffffffbb2225f0057ffffbe0802bffffdf040021e000798002000023feaa10000043c000f00000000007d550000000038008aeaa80000005100000000005000155540000000a0000000373681deec08452ec685055dfe226ccd06bd4000020d050a0aabfc40606000e43cf3fd7f8721e79febfcf0e1f9c87ffffbff8e43ffffdffc000001fe067ffdcccff033ffee66000000000ffff78100007fffbc0999b00c43000000667df807ffdfffff787ffe000010fdfff0fffffff911270f6b44aaf777449aeaa80226eeda7fd69557fefffeb5554107d
  | 0, 7 => 0xe0002880000000115d55000000014000500000000002aaa800000f3fe63781180700f7fe72c46a261e3c0c6f00000800e37800004005ffbf3fbf0cfffbffe21860000333ff787ffe1ffffffffff0000087eb73681deec08452ec7b5055dffbbeeed07fd4000020fbfea0aabff7f722e006282abbf800bf721023154e45c00c505557f0017e800002028d89a057bb02114aa0a141577f801b1340af50000081414282aaff001c8bb05fb9c8118aa0c505577f00391700bf40000101418a0aaafe002eedff77dffffffbb84affaa84441112f802bffffdf04015f5540080
  | 0, 8 => 0x1983ec022baaa00000015c0000000001400055550000000280000000ffde1f7bb02114bb1a143577f889b3341af50000083414282aaff1003744fa046f7ee755f3af8a880ffc6e8ff40bffffefebe75f55501ffbdd7863141d5dfc005fb908118aa722e006282aabf800bf4000010141983cc00030000000000180000000000000000000000000000000000d89a014286aeff002bdd8108a551b13402850555fe0057a8000040a000034000510000000022eaaa000000028000a000000000055550000391760bf72102315418a0eaefe00722e017e8000020283141555fc00
  | 0, 9 => 0xc0e43ff3fd660721ff9feb300021e0007ffffbc08003ffffde04fb9e194282aeff002bddb108a551b13402850555fe0057a8000040a1b1340285055dfe0057bb02114aa36268050a0aabfc00af5000008143626e050a1abbfc00af7604229546c4d00a141557f8015ea000010280010f0ef3fffffe665e9fe845a200021e0007ffffbc08003c0000000ffdf98c507577f0037eef20c63b9c8b8018a0aaafe002fd0000040504ec8f50893bdd6abebd7d5100ffc9d97ea15ffffefd7d7afaaa01ffb62e8076a0abbff33af760422d546c5d00a141557fe055ea00001028
  | 0, 10 => 0x10f0811bdfb9c46cebe2a2037719a3ed02fffffbdaf9d7d55406fee45c02fdc8408c5506282abbf801c8b805fa0000080a0c505557f0001e7ccc6f00300a01e3780180500c3c7818de00001001c6f00000800bff7ef88ebaaa80ccfbf5dfffbffffef5fffd555421fbffebfffffff3ba70d0040000008880a18aa80441102080280000010001415540080ffdf9e21860000333efc33ffefffffbc3fff0000087efff87ffffffc0040c3bcf3ffff9982079800200000878001ffffef02000f00000003626e15eec08452a82850d5dfe006c4d02bd40000205050a0aabfc00
  | 0, 11 => 0x766e02ee82abbff77bf7210231dceedc17fd05557fefffe80000217adcda03da82aeffddfbdd8108a5d9bbb41ff50555ffbfffa8000041f5b177caff6c722b5596282aeff003626815ea000010282850555fe0009d97faf5f54403ff5089fbdd6ab93b2ff5ebeaa807fea15ffffefd713b2fd4227ef75aafaf5f54403ff2765fa857ffffbf5f5ebeaa807feffdf9efdce408c7726283abbf911ccb825fa0000084a0c505557f2000043c3fcffffff999fe7fffffccc00878001ffffef02000fffff781000878001fe000800000f30004000010f0003c0000000001e0000000
  | 0, 12 => 0x1192fe12bea8801102113f7bad132225f0057d550020002bffffdf04e45d80c507577f0017ee720462a9c8b8018a0aaafe002fd000004051ffbc3c0300000066601800000333ff787ffe000010fdfff0000087e800878001e6000800000f30004000010f0003c0000000001e00000005dcbcc00030220001004580400880000000000000000000000000000046066bd795100ffd4224ef75aae4ecbfd7afaaa01ffa857ffffbf5db1370af76c42295414282aeff003626815ea000010282850555fe00000878779ffffff33040ff0004000010f0003ffffde04001e0000000
  | 0, 13 => 0x7bbffdffffffffeee395ff5dfc00e47de2fd7fffffc5862beaabf800000180dc4e408c440000080010000000000000000000000000000001ffbc36850d5dfe2277bb02114bb36668250a0aabfc40af5000008341ddbee80abaaa88444055d5544220891540155554008000aaaaa00400000e0022baaa00000015c00000000014000555500000002800000004469e3faf9aabfdddff7fffffeefbbf7dff5f555ffbfffaffffffdfc00404040510004001da28aabfccc00828000a00000000005555f781000068008baaa80000005100000000005000155540000000a0000000
  | 0, 14 => 0x7dcfeebffbbaaa55151f5ffffc88fa9f557fd555042a0a3ebffff900bb979c01160100220000302200000000000000000000000000000000ee9ff40dffffc022202ffaaa0110440fa00bfffe0040005f55500201ddbfe80bfeaa8844405ff5544220891f4017d554008000beaaa00401993fcff3fffffe667f9ffffff330021e0007ffffbc08003ffffde04ffdfbfdfaefffdfff11d75550199ffbd7fff5ffffffffffaaaa843f4ee9c34050c5540222008000001104408200a0aaa0040005000000201ddbeefeabaaaff777f55d557fbbeefd57fd55557fefffeaaaabff7f
  | 0, 15 => 0x44480210800000111774015577bbeedc17fd0000042f7fe82aabff7e8890440551554022202a8aaa0110440aa00aaaaa00400055555002008890440551554022202a8aaa0110440aa00aaaaa00400055555002000081077145557f33040a20004000010a0002aaabde04001400000000010f0ef3fffffe66091ff5508000021e0007ffffbc08003eaa800000001c0005100000000028800000000028000a00000000005000000000043c040ff0004001de7fffffccc00878001e0000000000fffff7813dd7e6b163d5ffc445fb9c8558aa722e006282aabf800bf400001014
  | 1, 0 => 0x4458f2ffbffffff777f5e7557fbbeefdf7fd7fffffefffebeaabff7ee45c02fdc8408c550ee82abbfe67d9b80ffa0000081effd05557fcfcfefcfc6f00300a23e3780180511c7c7838de00001041c6f00000820b917603141d5dfc005fb908118aa722e006282aabf800bf4000010140000c000000000000000180000000000000000000000000000000000f3c799c87fe7faff0e43ff3fd7f9e1c3f390fffff7ff1c87ffffbff8664ff040f30004001de7fffffccc00878001e0000000000fffff781391700774155dff335fb908118aa722e006282aabfe04bf400001014
  | 1, 1 => 0x222401ed40155eeee88200000044ddda0ffa82aaffdfffd4000020fa774f9a0086000011101431550088220410050000002000282aa80100eedcb7b9a2aabfbba22d72aa2110448d200b5555ef42005a55500201dd3ee80abeaa88445bdddd558aa0881540155554008000aaaaa00404458f2febceaaff777fdffffffbbeefdf7fd7d557fefffebffffff7ed8bbe15686beff00ebdd8108a551b13402850555fe0057a8000040a199f0cffff3ffffffffff9ffffffffffffffffffffffffffffffffffbff787deec08452ec685055dfe226ccd06bd4000020d050a0aabfc40
  | 1, 2 => 0x6c4dc2ffff30ce77050a0ebbfc00d89a057a8000040a0a141557f8000001800006000000000000000000000000000000000000000000000088900441000000223da802abdddf77683fea0000107dff50555ffbfbfff97ff745557ffffffaeffffffffffafffeaaabfffffff5fffffff001030103cc001000779ffffff330021e000780000000003ffffde047f7ffe37861a2500f1bc70c4288e1e3c0c6f00000800e37800004005772f30000d08840055b362114aa00000000000000000000000000003ff7e6d0a1abbfc44ef76c4229766ccd04a141557f8815ea00001068
  | 1, 3 => 0x7fffff10fcc001199f7ffffffffffffffffff800043f7ffffffffffee45c00c507577f0017ee420462a9c8b8018a0aaafe002fd0000040507e7cfc6f0c300a01e3780180500c3c7818de00001001c6f00000800b626e056adabffe20af761422d546c4d00a141557f8015ea000010286e6d01a141577f889deec08452ecddda0ffa82aaff1f7fd4000020faffffffdffffffffff10fcc001199ffffffffffffffffffff800043f4000003bc0cfffb99820000000000000000001fffef0200000000000191300000140888005b9908118aa0000000000000000000000000000
  | 1, 4 => 0x7fefefefebbffefff8975d5500ccffdf5fffd7fffffffffeaaa821fabb961c05065540222008000001104408200a0aaa0040005000000201ffbc3dfb908118ee4c507577f22399704bf40000109418a0aaafe403fff97fff5dffffffffba2aabfffffffafffebffffffffff5555ffff0010f01b030c028060d81860140300000000000000000000000000000021e000798002000003fc0010000043c000f0000000000780000001ffffffbfffffffffe27ffffe2330cc9fe01fffffefc200fffff00600cc1ee008baaa80000005d00000000005000155540000000a0000000
  | 1, 5 => 0x5fdfff1bebaea29178df5d75148b2f1f5637d555042071beaaa821023b17dc05061000002028308000000408000a000000000050000000001e7fcc6f0c300a01e3780180500c3c7818de00001001c6f000008008dd9ffaf5fd4403ff5089fbdd6ab93b2ff5ebeaa807fea15ffffefd77fff1fffd77fffffffeea2aafffffffebfffaffffffffffd5557fffebb97dc055755422226eafaae6330440aa00aaaaa0040005555500200eedff4455d554022216aebaa511c440aa00aaaaa0040005555500203ff787886000000ccfbf00fffbffffef0fffc000021fbffe1fffffff
  | 1, 6 => 0xdd1fe811bdfb9d57cebeaa203ff1ba3fd02fffffbfaf9d7d55407fe0021e1de79ffffccc103cc0010000043c000fffff7810007800000007e7ffc6fff300e01fffffffffccc3cff98dfe0001001c6fffffff818008780800000000002c0c300a018000000000000000000000000000444802ee802aaef7708400000088eedc17fd05557fefffe80000217a3307b8002e80000000117555000000014000500000000002aaa8000000038008aeaa80000045755400000005000155540000000aaaa00003c3066721ff9febfc390ffcff5fe7870fce43ffffdffc721ffffeffe
  | 1, 7 => 0x6c4dc2bdd8108a55050a0abbfc00d89a057a8000040a0a141557f8004f7e663780180511f1bc00c0288fbfbc1fff0000083efff8000041f4664ff3bcffffff9982079800200000878001ffffef02000f000000003cff98de00601403c6f00300a01878f031bc000020038de000010015dcbce02832aa011101419550088220410050555002000282aa80100bbb7dc0557554222202abaaa1110444aa00aaaaa0040005555500201ffbc398a0eaefe446fdc8408c773997043141555fc805fa0000084a1112708935d5500447b5a2557bbbeeeda7fd6aaa820fbfeb4aabff7f
  | 1, 8 => 0x7fefcebddb119a550d0a3abbfc44d89a057a8000040a0a141557f800bbb7fc217f8102220ef3fffffe660043c000f00000000007ffffbc08eedff7bdffffffbb8207f822200000878001ffffef02000f00000003ee7875eec08452a82850d5dfe006c4d02bd40000205050a0aabfc005ddb1e12976aa111176ca2aaffbb2224b0052d55002000295557df04ff9fbb4286aeff003bddb148a551b33402850555fe0057a8000040a1ffbf7ef77d576976342aeaeff113666ab5eaaaaa10682855555fe201cc3e600a988000000050d5540000801000140000000000a0aaa0000
  | 1, 9 => 0x5ddbeefeabaaaff777f55d557fbbeefd57fd55557fefffeaaaabff7e0f3fe63786180500f1bc30c028061e3c0c6f00000800e37800004005b1370af762422d541deceeeff443626815ea000010282850555fe00000078019ffff8000000f30000000000f0003fffc0000001e00000007fefdf01df55d019880ababb80441102a802aaaa8010001555540080ffde1fff867ffdfffffc33ffefffffbc3fff0ffffffffff87ffffffd776ff80affaa84444057fd5422208897c015f554008000afaaa0040030e198de00601403c6f00300a01878f031bc000020038de00001001
  | 1, 10 => 0x7fefcf10c00000199f7e19fff7ffffde1fff8000043f7ffc3ffffffe0020603600180500c1b000c02806000000000000000000000000000000000040000000001de067ffdccc00000000000000000000ffff7810fcf9f8de00601403c6f0c300a01878f031bc000020038de00001001667c13fdd4555ffffffea3fffffffffebfffaaaafffffffd7ffffffe0021e1fe7fffffccc1b3fcc038060043c000fffff78100078000000191300af76042295414280aeff003626815ea000010282850555fe000cc9fe001fe000800000ff0004000010f0003c0000000001e0000000
  | 1, 11 => 0x10f0fe3ceaafe667f9ffffff330021e0007d557bc08003ffffde04fffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000003fff8ffeea2aafffffff5dffffffffff5fffd5557ffffffebfffffff7fffff03fffff119981fffff88cc3327f807ffff8030003ffffc0180f0c019c879e7faff0e43ff3fd7f9e1c3f390fffff7ff1c87ffffbff9f77ffaf7ff422d541deffffffccf62ef95ebe0001028285ffffff81000060080c00000002840d5dfe00000000000000000000000aabec00
  | 1, 12 => 0x10f0ef3fffffe66099ffff88000021e0007ffffbc08003fffc0000ffdfde25d75540333efebbffefffffbebfffaaaa087efffd7ffffffd776ffbbeffffffddc277fffe22208897c015ffffef8200affff00400cc1ee008baaa80000045d55400000005000155540000000aaaa00000000d001175550000008baaa80000000a0002aaa8000000155540000002021da28aabfccc10144001000004140005555f78100028000000199b00fbf00fffbffe21800000333ff787ffe1ffffffffff0000087e911a78ffbffffff777f5f3557fbbeefdf7fd7fffffefffebeaabff7f
  | 1, 13 => 0x4458e2fea8aaaff777f55d557fbbeefd57fd55557fefffeaaaabff7e0001a1de2efffdccc10144000000000140005ffff7810002800000000003c008ffaa80000027faaa000000078001f5540000000f5550000000068008baaa80000005d00000000005000155540000000a00000005ddbfe10bcc00111177dffffffbb2225f00578000020002bffffdf04774fba00a88000111015755500882205500550000020002aaaa80101772c380200000044405065540220881040140000008000a0aaa00402eedff7f5ff557fbbbfeffffffddf77efbfebeaabff7fff5ffffffbf
  | 1, 14 => 0x5dcb2e02a8aaa01110155d5500882205500555550020002aaaa80100ffde1e07867fe033300c00000198660c300f0fff0060007800000301eefff5fbff811caa1df7fffffccf91f78bf5e000101418affffff811dd386882000000447bd0cfffbbb8881040140000008000a1fffef420000f0003cc000000019ffff80000001e000780000000003fffc00003307d800570000000022baaa000000028000a00000000005555000000043c044ff5544001de7fffffccc00878001eaaa0000000fffff781000060568d8845220000010004000000000000000000000000000000
  | 1, 15 => 0x7fef0fffc33ffefffff6015577ffffde1fff87fffffffffc2aabfffe002041de577fffccc1028800100000428000affff781000500000000ee9c34050c554022202862aa01104408200a0aaa004000505550020111a78f7bffffff77441f30004226efdf7fd7fffffefffebe000107d5dcbee12abaaa011177d5dfff7bb2205500555550020002abfffdf04f77ff8e57fd77f001ffffffffeefc8fbc18afaaafe002fd7fffffc58000003b400557b99820000000000000000000aabef02000000000003ff7ff89fffff80ccfbffffffbffffefffffffffc21fbfffffffffff
  | 2, 0 => 0x3ba7cd01431550088802180000441102080282aa8010001400000080776ffbfeffffffdddff7fffffeee2247d005fffff7a1002fffffbd080043c004ff55440000079800200000878001eaaa0000000f0000000000878001e6000800004ff5544000010f0003c0000000001eaaa00001993fc113fd551000779ffffff330021e0007aaa80000003ffffde0488b1e5df7fffffeee12bceaa1110444be00afffff7c10057d55002007e7fffffffffff99e37ff980700c3cff98dfffffff03c6ff0000800800810081440008003b8a2aabf998010a0002800000000015555ef02
  | 2, 1 => 0x7fffff12ffeaa1199f7ffffffffffffffffffd55043f7ffffffffffe730f980286aaa0000015310000002004000505550000002800000000889344055d554022202a8aaa0110440aa00aaaaa004000555550020222c1109545550888bbaa2aabfdd9112a802aaaa801000155555ef827fffff13fffff1199f7fffffffff3327f807ffff8030003fffffdf84bb97fc077fffe022203bffff0110440be00affff00400057fff80201ffbc3c43000000667db802abdfffff787ffe000010fdfff0555ffff800878779ffffff33044ff5544000010f0003ffffde04001eaaa0000
  | 2, 2 => 0x7fefef10e88000199f7f5dfff7ffffdf5fffd000043f7ffebffffffe0021e020798002000ee3ceaafe660043c000f00000000007d557bc08004040005100040000028800200000828000a000000000050000000111a00fea00aaff777f100003fbbeefd07fd41557fefffea0001ff7f7fefefffebbffeffffff5dfff7ffffdf5fffd7fffffffffebffffffe0001a0002880000000014400000000014000500000000002800000008893440551554022202aeaaa0110440aa00aaaaa0040005555500201ddbfe80bfeaa884440dffffc4220891f4017d554008000bfffe0040
  | 2, 3 => 0x1993fc023feaa1000009feaa88000021e0007d5500000003d5540000bbb7dc25575542222eeabaaaff76444aa00aaaaa004000555557be08000003b000003b9982000000000333601fe00001ff3fff00000081e800078001e6000000000f30000000000f0003c0000000001e00000000000d000144000000000ba0000000000a000280000000001400000000021c1dc57555fccc1028800100000428000aaaaf7810005000000000043c000f30004000067fffe200000878001e0000000000ffff000000001000144000000008a2aa80000000a00028000000000155540000
  | 2, 4 => 0x10f0fc3cc00fe667f9ffffff33ccf9e7f878007fcfffc3fffffe7e3307d800570000000002b800000000028000a0000000000500000001ffffffffffffffffffdf9d55ffffffffffffffffffffffffaaaffff8cc186000180000000000000000000000000000000000000000000007fffffeffffffffff897ff5508ccffffffffffffffffffffeaa821fa000020002880000000114555000000014000500000000002aaa8000088d3c445f35544223deffffffddc448fa00beaaa0040005fffff7a1111a68feabaaaff777f551557fbbeefd57fd55557fefffeaaaabff7f
  | 2, 5 => 0x7fffffffffffffffffffffffffff3327f807fffffbf0803fffffdf84776ffbfeffffffdddfd7fd55feefbbf7dff5ffffffbfffafaaaffdfc0043c008ffaa840000079800200000878001f5540000000f00000000000707795dfff733040a20000000000a0002bfffde04001400000000000f0003cc000000011ff5500000001e000780000000003eaa800000021e1fe7fffffcccfd3cd55fe660043c000fffff7810007aaafbc08eedff441f30004223deffffffddc448fa00be0000040005fffff7a111120080a00aa8044401000000220881040141554008000a00000040
  | 2, 6 => 0xc00000000000000000000000000000000000000000000000000088b1e5fd79d55feeefebceaaff77ddfbeffafaaaffdfffd7d557fefc660c3000000000000000600000000000000000000000000000000003ff7eff7ebbfff7ffc43510000667fef5fffd7fffffffffea00010fd5dcb0e1080000011177c19fff7bb220410050000002000283fffdf0400000002062aa00000000000000000000000055500000000000000000043c048ffaa84001de7fffffccc00878001f5540000000fffff7811dd3eef7abbfff7774455d5540220881540157fffde8400aaaaa0040
  | 2, 7 => 0x2234f1ff7fffffeeeffbffffff77ddfbeffaffffffdfffd7fffffefe774e1a00800000111004000000882204100500000020002800000101772fb84aaeaa80445dd57555deefbb755ff5555410bdffaaaaaffdfbfff9ffffffffffffffff3ffffffffffffffffffffffffffffffffff5dcbce0083000011101419550088220410050000002000282aa801000001e0067fffe0000033ffff00000003c000ffff00000007fff80001ffbf7c0f5dffc066603aeaaa0330cc1ae01ebffe00c000f555500600008107f145557f333f8a2aabf998010a0002aaabde040015555ef02
  | 2, 8 => 0x5dcbfe02bfeaa0111015ff5500882205f0057d550020002beaa80100ffdfde05d7554033302ebaaa0199ffbebfffaaaa087efffd555043f5fffc7fff5dfffffffffaeffffffffffafffebffffffffff5fffffffbffff7fff5dffffffffbaeaabfffffffafffebffffffffff5555ffff7fff1ffdd4555fffffeea2aafffffffebfffaaaafffffffd5557fffeccf9e7ffffffffffffffcffffffffffffffffffffffffffffffffffc00408000a20004000005100020000085000140000000000a0000000000878769e6aaff33040f30004000010f0003d557de04001e0000000
  | 2, 9 => 0x200020000002000ec00000fe66004000000000000000000007bc09ffbf7c075d554066607aeffe0330cc1ae01eaaaa00c000f5fff0060111200fea00aaf7777f500557bbbeeed07fd41557fefffea0aabff7f7fff0fffc33fffffffe600007ffffffe1fff87fffffffffc0003fffe0000000000000000002032aa000000000000000000000000555000011120080200000044401000000223bb705ff4000010bdffa0000085e800060000180000000000c0000000000000000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 8, 0, 0 => 0x301408030988818088108800c050200c261f8030381e0301030100a80307808030103010008030141e030e870180a80301408030d004100a803038080d0d830100a80301408030d0301019803038080d01030100080301408180b858180880a8500a040184c180a8090180a0401844180a8080180a0f01808180b803038080d01030160a80301408030102410008038180a040180802008
  | 8, 0, 1 => 0x16814080d01030100a8160141e0301030100a811814080d01030160a803038080d01030100a80283c060215830100a80301006021503010008030141e030d030100a811838080301030160a8148180a280200c180880301408030d804160a8030141e03010304e0a8030140803010041600803014080d0b85818088030140803130941208803010060206020142480388c0a0406808180a8
  | 8, 0, 2 => 0x108480c050200c260c8188180a0401808020a8080180a04018443e0c8030141e0317030100a8030141e0301030160a80301408031309402088038180a300200c3e0c8030381e0301004100a8080180a04018681808803038060217830100a803014080317004100a803014080301004160a8030141e030d830160a8108180a040184c3e0c8030141e03010301600811814080d0d830100a8
  | 8, 0, 3 => 0x808c0a0f0180818088198180a0401808160a803014080317030160a8090180a040184c18328080181c0406808180880301408030d030100a8030141e030100410008030141e0301004160a80301460040187c18088030381e0d01030100a80301408030987c18328080180a04018b8180880301408030d030160a8188180a0f01808180a8030140818130941808803038080d01004100a8
  | 8, 0, 4 => 0x3014080317030100a8
  | 9, 0, 0 => 0x301408030d830160a21c8400c0502108261f060224460502034261f060201520703014080309894184192001408030b87c18081fc8400c0514010061f0082240c0e0200c261f1f020152060703c06130f804100a9080140803098ac3e0c0448f40c0502034261f0602240c0e1403c061f06020152070301478030987c180a908018763a0184c3e0c0448e40a04018e03e0c050d640c050200c6e1f060d86b206028d006130f830100a9
  | 9, 0, 1 => 0x11814084c0987c18080548180a281d00c3e0c0402a40c050200c261f0602065206028101a130f830960a903128080d0987c18080548180a032484c3e0c0402a40c0524010261f0602015206028101a130f830160090301408031c07c180a23c81c0c0514118061f0602a42406028100613048201520703014080301030144390281006132287c180805481c46050200c261f0600240c050780c041f0602c152062201006130f830100a9
  | 9, 0, 2 => 0x80180a28021343e0c0449680a040184c3e0c0402a40c050200c261f06164b12070281006132b87c180a91181408030107018080549580a280200c3e550402a4a80602918061329830152520301408030987c180a9038180a040684c3e0c0548181c040184c3e0c2882a420060294006130f830112060281006130f93c100a9038180a042704c3e0c05484024060283c06130602242406070101a130602015207090180a042684c180a9
  | 9, 0, 3 => 0x3014080d01030100a31c8480c0514010060c2882a40c0e02188261f06020152060298406130f804100a9030141e030987c18080048400c050200c261f0618240c050780c0401040288721203078080309830100a92f818080309894180820c84046050200c041f0602240e060297808130f83015210038180a3a0184c3e0c9030141e030987c180b0548180a5d0184c3e010402a40c0502170261f060201521203014065b09830100a9
  | 9, 0, 4 => 0x30140803099b018080548180a040184c3e0c0406640c050200c701f06028d7200030381e0301030100a80301408180987c180b0548180a0f0684c3e010402a40e06029a808030f830d3206028a01e0d0f830100a903014080309870020a3448180a043384c3e0c0402a40c660200c261f0602015206028e89a130f830100a9090180a040185c18081fc880ca060281006130f992466060283c06130f82015210030ec08030987c18089
  | 9, 0, 5 => 0x301408180987c18080048c40c0514010061f0602a472053080c261f060201527703014061f06020147690301450040187c18080548180a0f0184cea0c0402a40c050200c040c28828872060281006133a004100a90301408030987c18733248181c04018083e0c0582a4e4060281006133883011223029c008030f830100a903014a0030987c18600549bc0a040184c3e0c051ba4460514010061f008201521203014da0409830100a9
  | 9, 0, 6 => 0x3f8180a280200c180a3448180a04019f8fa0c0402a4201203038080309830112061d8a0084d0f830100a91c814080309870180a3448181c04018083e0c0400240c050200c265306028f92060281006170f830f67a9090500a040184c18080548180a0f0184c3e0c041e6446780200c261f06020152060281006130f830b2329000180a040184c440c0440c40c050200c261f0082a40c050200c261f00820152230281006020602c100a9
  | 9, 0, 7 => 0x3014080309a143e0805481908040184c3e0c0582a42456028a00803060201520602810060206020008391c81408030987c18080548180a0f0184c2c0c0402a40c050780c701f060286b2820301408030987c100a903014080231030100a21c8180a040184c3e0c0420640c051403c067d060201520607010061b0f830100a90801c0c050200c261f06488c0a500184c3e0c0402a40c800200c261f06020152070281006131587c180a9
  | 9, 0, 8 => 0x30141e030104c18080548180a040c04c2c0c0402a42406028a008030602c15272458180a040184c1808903014088a0987c0208054a240c050780c040c0402a40c840200c261f060200120703014a0030987c180a91181408030987c186005481c24060283c06130602a40c054400c261f060201528703014500401830147c9090180a040184caa080549500c051401006530602a40c0502134261f06020152860281006130f830100a9
  | 9, 0, 9 => 0x80180a900204c3e0c0448180a280196c3e0c0402a42456028109a13060201520602a3c08030f830103f91e88c0a040184c3e0c0449500c050200c268e0602a4244002810061306020152060281006130e234180a903038080309a30180805481c46050200c041f0602a420060283c06130f80411206070101a130f804100a9148180a040184c18080548400c051403c061f0602240e06028a0084d0f8301521203014080309804160a9
  | 9, 0, 10 => 0x80180a040184c3e0c28c8f40e060281006130f83242056028e806130f83011206028f12a030f830143594a0180a280200c380c0548180a040184c3e0c0424e40c050200c5c0c04028872060701006130fa48100a90301408030887c180a1ac8180a040184c3e0c2c99240c050200c040c058288721503014080309870180a90307850040187c18080548180a040987c18080524640e061d81006130f830152060281006131283016419
  | 9, 0, 11 => 0x30141e0309870180a3448180a9b0204c3e0c0402a4280514010061f06020152153f8180a040184c180a94d0180a040184c3e0c4cc81808030987c18080526240c05141b4081f060201520602810061b0602014439090180803098a818080548cc0c050200c04080510e446054b80c261f06020152060701006130b030100a90301408030e870180a4b48181c04018e03e0c050d640c05140e8061f2a820152071181408030987c180a9
  | 9, 0, 12 => 0x188180a0f0184c3e0c0548180a0401a84180a1aa8240c050780c261f0602015206028100638128306a419080800c050200c261f0448180a0f0184ce80c0402a5349f0301408030987c192100303808030987c020890801876040184c3e550448000c0e02034040c0402a0200703014da040987c192064f01006130f830100a90301408030987d3a0805488c0a04019f83e0c0402a40c050200c040c041e4872060283d38130f830100a9
  | 9, 0, 13 => 0x540180a040184c3e0c0548181c0f0180818080510e4800514010061f06020152a7038180a0401a983e0c90801c0c050200c261f2aca940a040184c3e0c0402a5480602810061312830112100301408030987c180b90301408030987c100a51c8140803098ac3e0c0582a42406028100638060288f206028101a380f830143591181408030987c18510548180a042604cea0c0402a40c050200c261f06190652060281006130f830e6a29
  | 9, 0, 14 => 0x80180a950200c3e0c1ac8181c0401aa83e0c0402a40e56028e806130f83015210198180a040184c3e08903014080309aa4020805488c0a043104c3e0c0402a40c050780c261f04820152060281098380f8301435903210c2030987c18080548180a04018443e0c0402a4a412030140803098301521003014080301004104390301460040184c3e0c0448140803098ac3e0c0400240c0e3080c261f06020152400281006130f804100a9
  | 9, 0, 15 => 0x30380803099d018080548480c050780c260c040025660602810061306021652060281006370f830c8b191183850040187c1808054ac00c050200c261f0402a40c050200d5e1f57020152390281006130fab4100a9030381e0d0987c18080548180a045604c3e0c0402a40c050200c4c250602087212030141e0309830160a903014084d0987caa0805481d4a0514010061f0602a4ca060281006130f830c92ab030151e040187c18089
  | 9, 1, 0 => 0x301570040187c180a1ac8400a040184d6e1f0602240c050200c261f062d81520602984060206020144390381876040184c3e550548480c050200c260c0406640e0602810061312831652060200c262a0f804100a90301408030987d6a085a48185004018a83e0c0402a40c050200c041a0602015200108180a040184c3e0c80321008030987c18080548480c051d134260c0402a462060701006130f8301521003014505e0207c18089
  | 9, 1, 1 => 0x801c24060281006130648180a040184c4a0c0410640c050200d761f0602015206029841a130f830100a90301408030d04c18080548180a0f0680818080510e40c051e00c261f06020152120301408035d030100a9000180a0401808020b0540180a04018983e090402a5120602810061a060201523d0301408030987c180b9090180a040184c020805484172060200c261f0602242406028a0080306020152060281006130f830c0009
  | 9, 1, 2 => 0x30157e030987c180805481408030995c3e0c0402a40c055f01006130f82015212030380803098301000903014084e0987c18080548480c0502134260c0402a420060281006130f8317b207030145004018941841903014c24c0987c18080548400c0e0780c261f06022424060701006130602c152060281006130faf0100a9188180a0401808180a21c8180a040180818080510e5121003014080301030112060701006130f824100a9
  | 9, 1, 3 => 0x301584040987c020805481c0a040184d6e1f0602a40c05140e89a1f0602015210030ec50040187c18089030141e030987c02080048400c053080c261f06022420060283c06020602087206070101a020602014439090180a040184c18593248180a6a0200c3e0c041a640a0401808561f06020152060283c06130f804160a903014080301024100a21c9480c050200c261f0082a40c050200c2625048208320602b04061360030100a9
  | 9, 1, 4 => 0x3078080d0987c18080548180a040184c3e0c28802420310301408030987c192100301408030987c18089030141e030987c18086348140803098ac3e0c0402a5341203014080309831332061d8e806130f830100a90301408030884c3e0c05488c0a040184c3e0c6282a40c050200c261f00820332070301588030987c180a9558180a0401b0c3e0c0448400c0507834261f0602240eb90301006130f8301520602810062e0d830100a9
  | 9, 1, 5 => 0x301408030987d90080548400c0e02034261f0602240c050780c04130082015206028a01e0301030100a9080480c050200c260c05c8180a040184c3e0c3002a40c0e6380c261f06020152100301408030987c12089080181c0401808180821c8480c051401006550402a4800e0200c261f06020152064201006130fab4100a9000180a0f01808180b0540480c050780c260c0402a420070301408030987c0320602984061d0f830100a9
  | 9, 1, 6 => 0x30141e0309b2c18080548180a040186c02080510e40c050200c261f049801521203038080309830100a9650180a040184c3e0c2cc8cc0c050200c261f0582a480050200c040c0402887294080180a040184c380c90301408030987c0259324ac024060281006130402a40c050200c261f0602c012060281006020082c14439448180a0401808185105499424060281006130619240c050200d921f06164f520703014c2030987c180a9
  | 9, 1, 7 => 0x80180a040184c3e0105c8181c0f0184c3e0c0582a4ac051d00c261f06020152060281006130fb38100a9650180a040184c3e0c1948181ccd0184c3e0c0402a512060281006020602c15210038180a0f0184c3e0c9080180a040184c3e5504481c0c050200c261f0482a40c050200c2e1f061807f2060281006a106029984390301408031700818080548180a0f0184c3e010402a420230283c06130f830112060f01006130f830c00a9
  | 9, 1, 8 => 0x301408030987c18596848480c051401006010402a4201203014080309830112060283c060206020004390301408030100410000548180a0f0184c3e0c2c99240c050780c040c05828872200301408030987c100a9290180a0401808180a21c9000a500184c3e0c0402a594650301408030987c19210678180a04019f8180890301408031307c0208054a240c050200c360c0402a442060281006130f8301520602810062e09830100a9
  | 9, 1, 9 => 0x1181006131507c18080548480c050200c260c3002a40e060281006130fb5015210038180a040180818439698180a04018e03e0c0548cc0c050200c261f0402a40c0e0780c041306020152310301408030987c1800903014080301004100a21c8400e1203014500401832400060281006130f830650060281006130f830160a9030141e030d830100a21c8180a040184c3e016902a40c056880c261f06020152060283c1a130f830160a9
  | 9, 1, 10 => 0x80180a040184c3e010448180a040180818593210e5120602810060206020152060281006130f82014d69030141e0d0104c18080548000c0518010061f0602202006028e89a130f830112ca090180a040184c1859903038080d0987c18080048480c050200c260c0580242406028a0080306164c9210030141e030987c180b903038080d0987c180b0548180a040184c3e090400240c050200c261f06265ab2060281006130f824160a9
  | 9, 1, 11 => 0x100480c050200c26080548480c0e0200c26010402a40c050200c261f0082c012310301408030987c180a9080180a0401808180b21c8180a040184c3e0c0402a40c056c80c261f06021b12060283c1a130f830100a903038080d0104c1808054b5c0c050200c261f0602a4000602810061a06020150060281006130f804c00a9030141e0301030100a21c8840c050200c261f0616642012030140803099541121203014500f01830100a9
  | 9, 1, 12 => 0x301408030987c020b0548180a040186818080510e42007100180a040184c3f2060281006130f954100a9080480c0514010060c04484160060281006130f822442060281006130f830c920602810060209804160a90301408030987c18510cc884ca060281006130f8324661203014080309820152cf03014e00401830100a903038080d0987c18080548480c050200c260c0582a40c050200c261f04820152100301408030d83010439
  | 9, 1, 13 => 0x180a0401808180b0010e51206028100602008201520003014080317030100a80301408036d830100a21c8800c050200c261f2c99259e0602810067e06020152da0301408030987c100a9
  | 10, 0, 0 => 0x38180a042684c3e0c0537680023028101a130f830100a90001c0c050200c26250610640c050200c040c040288243a1181408030984c3e0c0402a80e12030140803098301435a6e0400c050200c261f06022824060283c06130f830100aa0307808030987c18080510e80c050200c701f060286aa0a0301408030b87c1808051a680c050200c261f061cc160aa0804966060281006130602280c1e0200c261f06020143fa030140803508e03e0c050d680e060281006135307c180aa
  | 10, 0, 1 => 0x30145004018703e0c0538a80c051401006130f830b264a038180a040184c3e0c0525a80c050200c2625128301041a708180a040184c3e0c040028240602b80080309830100aa558180a0401a983e0c0402a82406028100613060201469a080180a042684c3e0c0402a8240602810062609830100aa038180a040184c3e0c050da99e1203014080309830100aa080180a04018dc261f060228240602810061306021be0aa6f0402406028100613060228fe060281006130f830100aa
  | 10, 0, 2 => 0x301408030109418080510e82006028a008030f8301035a2a01c0c050200c261f0602a80c050783c06130f830100aa038180a040184c3e0c051ea80c050200c2e1f060207e43a650400e060281006130f83280e060281006380987c180aa000180a04018e03e0c0511e4240602a3c080309830100aa038180a040184c3e0c0538e80c0e0200c2e130f830100aa0301408030b87c18081f8fe8000703014080301030144390822c0c050200c261f06022948100301408030987c1808a
  | 10, 0, 3 => 0x301408030987c187b0402a9d01203014080309830100aa538180a040185c3e0c0402a80c050200c261f0639c100aa0301408030104c180805282800520301408030987c180a90001c0c0502034261f0602a40e060281006130987c180aa730180a040184c381f0602a80c050200dca130f830100aa038180a040184c3e550402a80006028a074030f830100a903014080d0987c180805106912070301408030987c180aa0301408030987c180b0402a80c050200c261f0602014e4a
  | 10, 0, 4 => 0x301408030987c1808053b69c2060281006130f8301043a0303808030987c1808051a294e1203014080309830100aa039940c050200c261f0602a800060283c06130f830160a90301408030987c1808053b2956060281006130f830100aa038180a0401bac261f0602a80c0514010061f0602014b2a0301408030987dd40c0402a82406028a008030b830100aa7301c0c050200dd21f0602a80c054a810061f060201435a2001408030987c18080520e91612030140803098941808a
  | 10, 0, 5 => 0x30140803099f83e0c0402a934060281006130f830100aa000480c050200c2e0c040fe5a6060281006130f830100aa000400c3b0200c261f06022420060281006130f83010eea0301408030b84c4a0c04106820060281006130f830b264a000180a0f0184c3e0c04002446050780c261f060201443a448180a04019f83e0c0402a846050200c261f0f830100aa0321008030987c1808051a2820060701006130f8301043a0301408030987c18080502a840060281006130f964100aa
  | 10, 0, 6 => 0x301408030987de80c0402a80c054a81006130e07c180aa030140803098703e530602a80c053080c261f060201435a0301408030987c1808053ce8201203014080309830b208a080180a6d0204c3e710602280c051403c06130f830100aa0301408030987c1808003ca820060281006130f83010f1a080180a040184c3e0c0411e80c050780c261f0602014f0a0301408030b8703e0c040fe928060281006130f830147ca1181408030987c1808051929de060281006130f830100aa
  | 10, 0, 7 => 0x301408031c07c1808050d69f0070301408030987c180aa03014080d0b84c3e0c0402a934100301408030987c1899a000180a280200c3e0c0402a40c050200c261c060286a68a001c80c050200c267106022594060281006130f830b264a038180a040184ce81f0602a800060281006130f8301019903014080309bdc3e0c0402a820060281006f60987c1808a0301408036484c3e0c2c99282406028a00803060201468a080180a040184ce20c041069ea230281006130f830100aa
  | 10, 0, 8 => 0x80180a040184c3e0c0410682006029a850040187c1808a0301450040187c180b0510e80c050200c262506020d041a03015f8040184c3e0c0402a828050200c261c0f830100aa448180a040184c3e0c2882a80c050200df6130f830100aa0301408030987d5a080510e8e4070301408030987c180aa7d0181c040184c3e0c0402a80e060281006130f8301464a0301408030987c1808053e694e060281006135307c1808a0301408030987c18590582a800060281006130f804100a9
  | 10, 0, 9 => 0x301408030987c18088182a80c050200e04130f830100aa2001408030987c18080510e80c050200c261f060201435a0301408030987e02010402a93e060281006130f83010d5a2001408030987c1808050fe8241203014500401830100aa650180a040184c3e0c052668ac0514010061f0602014dda090180a040184c1808054029fe060281006130f830100aa0301408030987c020b0510e80c050200c261f0602014fea090180a040184c18080520e80c050200c261f7e830100aa
  | 10, 0, 10 => 0x90180a040184c18080002a80e06028a008030f8301435a03014080d0987c1808051a280c050200c70130e07c180aa090180a040184c4a0c04106820060281006130fc1c1808a0301408030987c18080528280c050200c27060f8320a0aa000e40a040184c3e0c0402a40c050200d42130f830100aa03a2c0c050200c261f0602a80c050200c261c0602a0868a080180a0f0184c3e0c0402a80e1203014080309830100aa000400e060281006130f83240c050200c261f2a82014dda
  | 10, 0, 11 => 0x3014080301030100a6610e8287f0281006130f830100aa0301408038504c3e0c0402a80c05700a008030f830100aa1183808030987c18080510e80c051401006260f830100aa090180a040180818080510e80e060281006170987c183fa000480c050200c26550402a59e06028a008030f830100aa848180a040184c3e0c0402a82406028a0080306020147ca000180a042684c3e0c0402a40c050200c261f060200058a390400c050200c26250602280c050200c2625064201041a
  | 10, 0, 12 => 0x301450040187c180a710d680c040184c541f060201443a03014080309c184a0c04106800060283c060209830100a903014080d0987e1c0c0402a80c0514010061f86830100aa558180a040185c3e0c040fe80c050200e18130f830100aa080480c050200c26a6060228ee060283c06130f830100aa080480c050200c04130602280e060291806130f830100aa03014508f0200c3e0c0402a80c050200e1602060201443a0301408030987c180805412934060281006130f830b20aa
  | 10, 0, 13 => 0x1c0c3b0200c261f0602a440650301408030987c100aa538180a280200c3e0c0402a82406028100613060201443a730180a040184c3e0c050d680c050200c70750f8301435a090180a040184c1808050fe80c050200c27100f830100aa8781c0c050200c261f0602a8000602a3c08030f830103f9038181c040184c3e0c0510e80c050200c701f061641435a080480c050200c70130602280c050200c04130f830160aa0301408030987c18600510680e060281006137487c180aa
  | 10, 0, 14 => 0x3014d4040184c3e0c0402a912060281006130f830160aa0301408030d84c3e0c0402a80c0514010061f060201515a0301628040184c3e0c0402aa26060281006130f830100aa090180a040184c18080544a8a4070301408030987c180aa000180a040184c3e0c2c99240c050200c70130f830160aa038180a040184c3e0c7882a80c050200c261f88830100aa038180a040184c3e0c0511e800060281006020602c144390301408030987c180b0525a9cc07090180a040184c180aa
  | 10, 0, 15 => 0x301408030987c187b051ea80c05140100613128301041a080181c040184c3e0c0402a80c050200c26130f830160aa538400e060281006130f83280c050200c26250f83010b2a0301408030987c18730402a80c050200c70130f8301000a708180a040184c3e0c0402a82406028100617098941808a090180a040184cfa0c0402a94e720301408030987c1808a0001c46050200c261f0602a420060281006130f83010d5a0301408030987c18080025a82406028100613060201516a
  | 10, 1, 0 => 0x3014e0280200c040c0402a80c054a81006130f8301435a730180a950200c3e0c0402a8009a0301408030987c18999090180a040184c1808054628460502034261f060201443a080480c050200c26710602290e06028100613060201468a038180a6a14010061f0602a80c050200c0413008201443a080180a040184c3e0c041a2a2e060281006130f830100aa000180a040186c18080510e40c054a81006380f8301435a118140803098943e0c0402a824060281006130602014dda
  | 10, 1, 1 => 0x80180a0401c2c261f06022820060281006130f83010cca0301408030987c18080546e972060200c26a60f830100aa080480c050200c261f0602280c050200c04380f8301435a0301408037487c1808050d680c050200c261f008201483a038180a040184c4a1f0602a80c050200c261f06020f296a0301408030987c18080546a824060281006130e030100aa080480c0514010060c0402a80c050200c2675060201496a6f0180a040184c3e0c0402a80c050200c261f060201519a
  | 10, 1, 2 => 0x301408030987c02080002a80c050200c701f060286a7aa080180a040180818080510e80c050780c261f0602c1443a030145004018943e0c04106846050200c2e130f830100aa0301408031c07c180a1aa5a82006028100613128301041a3904024060281006130602282012030140803098301064a0301408038e84c3e0c0402a80c050200c261f06020151ca000180a0f0184c3e0c0402a4a4060281006130f8301443a080180a040184c3e0c0426680e060281006130f804100aa
  | 10, 1, 3 => 0x301408030987c18088f82a80e120301408031c04c180aa0301408035087c18080511e94810090180a040184c1808a03014d4280200c3e0c041a680c050200c70130f8301435a030141e030987c18080010e93e100301408030987c1808a438180a040184c1808051f280c050200e3c130f830100aa0301408030987c180b0519282007038180a040184c3e0ca080180a040184c3e0c041f28a80602810061329830100aa03014503a0187c180805376934650301408030987c180aa
  | 10, 1, 4 => 0x301408030987d5a08050d6956060281006170f830100aa0301408030987c18590402a82006028a008031c07c1808a0301408030987c18080c90e80c050200c26250f8301069a1181408030987c1808051a280c050200c4c131287c1808a038180a042684c3e0c0402a800a50281006130f830100a9730180a040184c3e0c0402a80c050200c261f061ec1464a002900c050200c262506022400100301408030987c180b90301408031c0703e0c0511e916060281006130f8301100a
  | 10, 1, 5 => 0x301450040187c18080544a80c050200c261f060201522a03015820f0184c3e0c0402a9561203014080309830100aa030141e031784c3e0c0402a800650301408030987c1864903014500401c843e0c0402a820061d81006130f83010dda0301408030987c02080510e80c050200c261f00820143fa030140803099d43e0c0402a82406028100613061ec100aa448180a0401808260c0402a824061d81006130f830100aa0301450040187c1808050fe80c05900a008030f830100aa
  | 10, 1, 6 => 0x301408030987c18080549a80c050200c261f0602014b1a0301408031c07c180a320d6824060281006130602014f3a928180a040184c3e0c0402a80c050200c261f29830100aa0001908040184c3e0c0402a5341203014080309830100aa0301408031c07c1808052c6820070301408030987c1843a0301450040187cfa0c0402a80c050200c261f060201524a0801c0c050200c261f060fe80c050200c261f060201458a090180a040184c18080502aa46060281006130f830100aa
  | 10, 1, 7 => 0x301408030104c3e0c0402a80e06028100613128301441a030140803098703e010402a80c050200c27290f830100aa080400c050200c261f0602280c050200c261f94030100aa030145004018703e0c0402a8001203014080309804100a9090180a04018e01808050d6800105c81808030987c180890301408039384c3e0c0402a80e0602810070b0987c180aa0801c0c050200c261f063768001203014500401830100a9038180a040184c3e0c0533280c053080c261f060201496a
  | 10, 1, 8 => 0x4f81c0c050200c261f0602a80c050200c261f061641104a0301408030987c192a0402a82007030140803098703e0ca000400e1203014080309832424060281006132a82014dda030141e030987c18080536280e060281006130f830147ca03014084d0987c180805376800060281006131283010419030ec50040184c3e0c0402a80c050200c261f060220041a0301408036487c18080510e80006028f006130f830100a90301408036487c1808050fe80c050780c0413060201443a
  | 10, 1, 9 => 0x301408030987c1859320fe80c059701006130f830100aa448180a040184c3e0c0402a80e060281006130f8325a0aa090180a040184c18080528280c050780c261f060201483a090180a0401a84260c0402a80c050200c261f06020152ca0301408030987c1808054ae80c050200c261f06020147aa650400c050200c261f0602280c050200c70130f830100aa0301408030987c180b0510682012030140803098941808a000180a040180818080510e40c050200c261f060201496a
  | 10, 1, 10 => 0x301408031b87c1808052c680c0514010061f061ec100aa080180a040184e601f0602280c050780c041f060201443a0301408039784c3e0c0402a8ca060281006130f830100aa030141e030987c18080002a8240602810070c09830100aa0301408030987c18593244a82406028100613060201504a090180ae014010060c0402a80c050200c26130f830100aa678480c0514010060c0402a80c050200c261f060200041a000480c0502134260c0402a40c050200c261f06164c843a
  | 10, 1, 11 => 0x301408030987c18080519280c050200c261c0f83014cca678180a040184c18080510e9f0060281006130f830100aa030141e030987c18080510e80c050200c2616060201441a0301408031c07c180a1a90680c050200c26740f830100aa090180a040186c260c0402a820060281006130f8301132a030140803098703e0c2c99280c050200c261f06022623fa000480c050200c260c2c99240006029a808030f830106990301408030987c18080506695606028a008030f830100aa
  | 10, 1, 12 => 0x80180a040184c3e0c0590e80e060281006130f8301535a090180a040184c18080546a820060281006130f830c899a0301408031c05c3e0c040fea68100301408030987c1808a0301408031b84c3e0c0402a9bc1203014080309830100aa000400c050200c261f0602253410038180a040184c3e0ca000140803098ac3e0c0402a534060281006130f8301064a038180a040184e661f0602a80c050200d5e130f804100aa0801c0c050200c261f0602a80c0e0200c261f060201483a
  | 10, 1, 13 => 0x90180a0401c78260c0402a820060281006260987c1808a0833c0c050200c261f060228201203014080309830107ca038180a040184c4a0c0410680c050200c040c040288683a0301408031307c18080510e824060281006130f830160aa0301408030b87c1808053ca80c050200c261f060201538a000480c050780c260c0402a40c050200c261f060201537a080480c050200c260c0426682012090180a040184c1808a9b0180a040184c3e0c0402a80c0e0200c261f06020000aa
  | 10, 1, 14 => 0x80480c051401006130602280c050200c261f568201496a090180a040184c02080510e80c050200c261f06020153aa090180a280200c18080510e820060281007390987c1808a0301408037b04c3e0c0402a8240602810061306164100aa290180a040184c3e0c0402a928060281006130e07c180aa0301408030103010000510e80c050200c261f061641464a000180a040184c3e0c3002a4200602a3c08030987c1808a0301450040187c18080541280c050200c261f00ab8100aa
  | 10, 1, 15 => 0x804024060281006130602293e070301408030987c1859a030140803098703e0c8282a824060281006130602014b1a080180a0401808260c0410e82006028a008030f8301068a090180a040184ca60c0402a80c050200c040c040288643a090180a280200c1808053768001203038080309830100a9090180a280200cfa0c0402a800ca0301408030987c185999e8180a040184c3e0c0402aa78060281006130f830100aa000180a040184c3e0c0580240c050200c273b0f830100aa
  | 10, 2, 0 => 0x45acc0c050200c261f06022820060281006130f8301000a038180a8f0200c261f0602a824060281006130602014e3a030167e040184c3e0c0402a93e07090180a040184c180aa038180a0401898261f0602a800060283c06130f804100a90301408030987e7c0c0402a80e1203014080309830147ca080180a040184c3e0c0582a9bc10038180a040184c3e0ca090180a040184d4c0c0402a8240602810060209830100aa0301408035084c3e0c0533299e060281006133f030100aa
  | 10, 2, 1 => 0x801c0c050200c261f06166a84060281006130f830100aa0301408030987c180805506820060281006130f8301043a0301408030987c1808a002a80c050200c261f00964100aa328480c050200c260c0402a866060281006130f804100aa0301408030987c18080535680c053801006133e830100aa090180a040184c260c0402a80c050780c261f060201476a328180a040184c3e0c05192800100301408030987caa089448480c050200c260c0402a80c050200c267d060201443a
  | 10, 2, 2 => 0xa28180a040184c3e0c0402a820070301408030987ca60ca0004024060281006130602240c050200c261f06020147ca4d0180a040184c3e0c0426680e060281006130f8301483a0801c24060281006130602a82406028100613060201464a000800c050200c261f0402a420060281006130f83010dda090180a0f0184c18080510ea88060281006130f830100aa090180a040184c3e0c0402a820060281006130f9f41808aa18180a040184c3e0c0402a824060281006133a030100aa
  | 10, 2, 3 => 0x301408030987c180b0010e912060281006130f804100aa000cc0c050200c261f0402a40c050200c261f06164b264a0801c0c050200c04130f832800060281006020082014439030140803a384c3e0c0402a82406028100613060201538aa30180a040184c3e0c0402a800060281006130f830160a9038180a040184c3e0c0002aa6c1203014080309830100aa0301408030104c3e010402a80c050200c261f061801443a0301408030987c1859053568240602810063709830100aa
  | 10, 2, 4 => 0x301408036487c1808051ea80c051401006740f830100aa090180a280200c360c0402a80c050780c261f06164100aa080180a040184c3e0c0402a82007328180a040184c3e0ca038180a040185c26250f83280c050200c261f06164c8b1aa48180a040184c3e0c0402a80c050200c261f060201548a090180a040184c18590519282406070100613060201443a678180a040186c3e0c0402a80c050200c26130f804100aa0833c24060281006130602280c053501006170987c1808a
  | 10, 2, 5 => 0x80180a040184c3e550437680c050200c261f0082014b4a0301408030987c18080552a824060281006130f954100aa0301408031c04c3e0c8402a80c050200c04130602c1443a0801c0c050200c261f0619280c051401006370f830100aa6f0480c0514010060c0402a800100301408030987c020890301408030d80818080510e994060281006130f830100aa002240c050200c040c0402a40c050200c261f008201464a030141e030987c02080510e80c050200c04130f830b264a
  | 10, 2, 6 => 0x301408030987c18593219280e060281006130f830140aa000180a0f0684c3e0c0402a42406028a0080306164100aa0301408030987c180800002994060281006130f830b20aa090180a040184c180805356912060283c06130f830100aa678480c050200cfc0c0402a80e060281006130fba8180aa0301408030987c180b0002a800060283c06020602014439030141e030104c3e0c0402a80c050200c3613060201443aa58180a040184c3e0c0402a8ca060281006130f830b264a
  | 10, 2, 7 => 0x678180a040184c3e0c0402a9bc100301408030987c1808a030140803a684c3e0c0402a866060281006130f8201443a080480c050200c260c043768241203014080309830100aa03014080301030b2080510e80c050200c261f0602c1443a678180a04018083e0c0402a8200602810061b0987c1808a0301408030987c180a3226680c050200c6e130f830b264a0301698040184c3e0c0402a800310301408030987c180a9000180a040184c3e0c0402a42012030140803098301043a
  | 10, 2, 8 => 0x80180a040184c3e010410e80c050200c0413060201443a080180a040184c3e0c2c82291206028100602060201443a0301408030987c18600402a82406028a0080309830100aa0301408030100818080510e9121203014500401830100aa030145004019f418080510e80c059f8a008030f830100aa000181c040684c3e0c0402a40c050200c261f0602014d0a000480c050200c260c0582a40c050200c261f06020154ea090180a280200c040c0402a800060281006130f824100a9
  | 10, 2, 9 => 0x301408036d84c3e0c0402a80c050200c261f0602014dda0033c0c050200cfc0c0402a40c050200c261f060201443a0301408030107cfa0c0402a800060281006130f804160a903014080301030100a3210e820060281006020987c1808a000180a040184c3e550402a40010090180a280200c180890801c24060281006130f8329941203014080309830100aa090180a280200c180805192824060281006130f804100aa080180a280200c3e7d06022820070301408030987c18d5a
  | 10, 2, 10 => 0xc050200c261f00804100aa
  | 11, 0, 0 => 0x6f0180a280200c261f06020156060281006130f830100a1fa0ec24060281006130f830b20805580156060281006130f830100aa000180a040184c3e0c3d82015406028100638098943e0c0402ac0c050200c261f06164100a3458000c050200c261f0602c100aa03014d4280200c261f06020156002a01c0c050200c261f0602a800070301408031c04c3e0c0550019e1203014080309830100aa001fc0c050200c261f06020154060281006380987c180805106c0e070301408030987c18080558180a040180826250f830100ab
  | 11, 0, 1 => 0x38180a040184c3e0c04029bb6060281006020987c1808051a2c00000301450040187c18080548180a040185c26130f830100ab0301408030987c180805190836060281006130f83010000510ec00060281006130f830100a79d0180a040184e0c1f06164100ab0301408030987c3e0c04028836060281006380b84c3e0c0402ac00060281006133f07c180805500134060281006130f830100aa038180a040184c3e0c04028876070301408030987c1808050fec00060281006130f830100a0550180a040184c3e0c040288683b
  | 11, 0, 2 => 0x301408030987c1808050fc876120301408030104c3e0c0402ac0c050200c261f06020143f1fd81c0c050200c261c0f830100ab0001c24060281006130602015400000400e060281006130f832548060281006130f830100a20d8180a04018e0261f060201468b000180a040184c3e0c040286b400090180a040184c18080540280c050200c26250f830100a32580020060281006130f8301041a6f0400c050200c261f0602015600038180a040184c3e0c05192800000301408030987c02080548000c050200c701f060201435a
  | 11, 0, 3 => 0xc050200c261f06164c92060281006130e07c18080510ec0c050200c6e170987c18080558002406028100613060201443a000480c050200c260c040287f4100301408030987c18590402ac000703014080309ba43e0c0550000c050200c261f060201504a090180a04018e0261f060201560003015c0280200c3e0c0402a80006028100638098703e0c0550000c050200c261f0602014a0a000180a0401a84261f060201540602810070b0104c3e0c0402ac0c050200c261f06020144321d8180a0401808261f0602014ccb
  | 11, 0, 4 => 0x400c050200c261f060213341003014080309a983e0c0402ac20060281006020987c180805580020120301408030987c1808a0001c0c050200c26250f830154060281006130e0703e0c0402ac0012030140803098701808055001bc060281006130f830100aa030140803098943e0c04028836120301408030987c180805192c0c051401006380987c180805580020060281006130f8301068a090180a040184c3e1f0602015600090180a040184c18080537680006029a808030987c18080550000c050200c36130f830100aa
  | 11, 0, 5 => 0x30140803098943e0c04028d16000301450040187cfa0c0402a80c050200c261f06020146820d8000c050200c261f008201443a000180a040184cea1f06020154000301450040187c1808050fe800060281006130f830b2080550180a040185c26250f830100ab003980c050200c261f06020154000301408031c04c3e0c050d68fe060281006130e07c18080558180a040184c3e0c04028143fb038180a040184c3e0c040286b6100301408031c04c3e0c0402ac0000030141e030987c18080548180a040184c3e0c3d820143fb
  | 11, 0, 6 => 0x180a040184c3e0c040292d4004f81c0c050200c261f0602a8000003014080309894180820c81c0c050200c261f06020100ab650180a040184c3e0c04028c96000301408030104c3e0c0402a80c050200d92130f830100a3258180a0401c2c26250f830100ab0004020060281006130f83011400030145004018703e0c0402a80000090180a280200c18080548000c050200c261f0602014b1a390400c050200c261f06020156100301408030987c180805192c24060281006130f830100a20d8000c050200c261f29830100aa
  | 11, 0, 7 => 0x30140803098703e0c04020156006f0480c050200c260c0402a80000080180a040184c3e0c04484824060281006130f830100ab000400e060281006130f830154000301408030987c180805192800060283c06130f830100a21d0000c050200c26740f830100aa001940c050200c261f0602015406028a008030987c180805106c0c050200c261c0f830100a8258000c050200c26130f830100aa002240c050200c261f06020154000301408030987c1808051ea800060281006380987c180805500000060281006020602014439
  | 11, 0, 8 => 0x480c050200c041306020154060281006130987c18080510ec0c050200c2e130f830100a595a240c050200c261f060201443b080180a040184c3e0c04029336060281006130f830100a1f9eac20120301408030987c18080558180a0401808261f060201443b030140803098703e0c2c82015600090180a040184c18590402a82406028a008030987c18080558000c050200c261f061641464a030140803098583e0c040287f6060281006130f830b2080510ec24060281006130f830100a3e58000c050200c6e130f830100aa
  | 11, 0, 9 => 0x301408030d808261f0602015600080180a040184c3e0c0402a80c050200c261f06020140a3258180a040184c3e0c040287e41b000000c050200c261f0602c152cf090180a040184c3e0c0402ac0000080480c050200c260c0448000c050200c261f06020147ca000480c050200c260c04028c9400080180a040184c3e0c04376800120301408030987c180805500020060281006130f8301043a0301408030987c180805192256060281006130f830100a3210ec00060281006130f830100a6ad0180a040184c3e0c2c820140ab
  | 11, 0, 10 => 0x301450040184c3e7d06020156650301408030987c18590402ac00cf0301408030987c1808055001bc100301408030987c1808a0801c0c050200c261f0602015600090480c050200c260c0402a800060281006130f830160a21d00000060281006130f830100a90301408030104c3e0c2c820156120301408030987c180805376c0c050200c261f06164100a58d8480c050200c261f060201443b4f81c0c050200c261f06020156060281006130f830100a1f9a2c0c050200c261f06164b20805580194060281006130f830100aa
  | 11, 0, 11 => 0x60281006130f830100a32192c00060281006130f830100a6ed0000c050200c261f060201443a000400c050200c04130f830114060281006020987c180805192c000602810060209830100a21d00020060281006130f830b208a0301408030104c261f06020156060281006130f830b20805192c00120301450040184c18080550180a040180804130f830100ab
  | 12, 0, 0 => 0xc050200c261f060201443a000180a040184c3e0c0402a420060281006130f830100aa090180a040184c3e0c0402a800100301408030987c180890301408030987c18080519280c050200c70130f830100aa0301408030104c3e0c0402a80c050200c261f06164100aa0301408030987c1808050d680006028a008030f830100a9
  | 13, 0, 0 => 0x60281006130f830100a9
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 8 => 76
  | 9 => 85
  | 10 => 94
  | 11 => 103
  | 12 => 94
  | 13 => 85
  | _ => 0

def idWidth : Nat := 9

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 223 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xfffffffffff80000000000000001fffffffffff, 45)], [(0x1552aaa0aaaaaa154505555550aa2aa555415555542a8a0aaaaaa154, 1)], [(0x1552aa00000000000000000000002aa5540000000000000000000000, 1), (0xa0aaaaaa15400000000000000001415555542a8, 44), (0xf000000e01800000000000000001e000001c03, 45), (0x505555550aa00000000000000000a0aaaaaa154, 46)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 111)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 111 true (goal 111) u ys) :
    NatRunT 111 true (goal 111) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 11 0 (NN s)

def poolG : List Nat := [38316900185438321, 11295349687832687, 38293801842888818, 11296450273201263, 11295315375325342, 42816141516721263, 11272252439031919, 61961889175949426, 37167901934996593, 61960811183197297, 19184289784646769, 19153559291547759]

def Z (s : Nat) := bar 111 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega

private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 65 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 17 48 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 65 → Z 8 i = true := (range_split z8_0 (range_split z8_24 z8_48))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_24 : ∀ i, 24 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 72 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_72 : ∀ i, 72 ≤ i → i < 96 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_96 : ∀ i, 96 ≤ i → i < 120 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_120 : ∀ i, 120 ≤ i → i < 144 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_144 : ∀ i, 144 ≤ i → i < 168 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_168 : ∀ i, 168 ≤ i → i < 192 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_192 : ∀ i, 192 ≤ i → i < 216 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_216 : ∀ i, 216 ≤ i → i < 240 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_240 : ∀ i, 240 ≤ i → i < 264 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_264 : ∀ i, 264 ≤ i → i < 288 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_288 : ∀ i, 288 ≤ i → i < 312 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_312 : ∀ i, 312 ≤ i → i < 336 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_336 : ∀ i, 336 ≤ i → i < 360 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_360 : ∀ i, 360 ≤ i → i < 384 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_384 : ∀ i, 384 ≤ i → i < 408 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_408 : ∀ i, 408 ≤ i → i < 432 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_432 : ∀ i, 432 ≤ i → i < 456 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 24 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_456 : ∀ i, 456 ≤ i → i < 471 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 15 456 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 471 → Z 9 i = true := (range_split (range_split (range_split (range_split z9_0 z9_24) (range_split z9_48 (range_split z9_72 z9_96))) (range_split (range_split z9_120 z9_144) (range_split z9_168 (range_split z9_192 z9_216)))) (range_split (range_split (range_split z9_240 z9_264) (range_split z9_288 (range_split z9_312 z9_336))) (range_split (range_split z9_360 z9_384) (range_split z9_408 (range_split z9_432 z9_456)))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 24 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_24 : ∀ i, 24 ≤ i → i < 48 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_48 : ∀ i, 48 ≤ i → i < 72 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_72 : ∀ i, 72 ≤ i → i < 96 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_96 : ∀ i, 96 ≤ i → i < 120 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_120 : ∀ i, 120 ≤ i → i < 144 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_144 : ∀ i, 144 ≤ i → i < 168 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_168 : ∀ i, 168 ≤ i → i < 192 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_192 : ∀ i, 192 ≤ i → i < 216 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_216 : ∀ i, 216 ≤ i → i < 240 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_240 : ∀ i, 240 ≤ i → i < 264 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_264 : ∀ i, 264 ≤ i → i < 288 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_288 : ∀ i, 288 ≤ i → i < 312 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_312 : ∀ i, 312 ≤ i → i < 336 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_336 : ∀ i, 336 ≤ i → i < 360 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_360 : ∀ i, 360 ≤ i → i < 384 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_384 : ∀ i, 384 ≤ i → i < 408 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_408 : ∀ i, 408 ≤ i → i < 432 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_432 : ∀ i, 432 ≤ i → i < 456 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_456 : ∀ i, 456 ≤ i → i < 480 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_480 : ∀ i, 480 ≤ i → i < 504 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_504 : ∀ i, 504 ≤ i → i < 528 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_528 : ∀ i, 528 ≤ i → i < 552 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_552 : ∀ i, 552 ≤ i → i < 576 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_576 : ∀ i, 576 ≤ i → i < 600 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_600 : ∀ i, 600 ≤ i → i < 624 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_624 : ∀ i, 624 ≤ i → i < 648 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_648 : ∀ i, 648 ≤ i → i < 672 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 24 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_672 : ∀ i, 672 ≤ i → i < 673 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 672 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 673 → Z 10 i = true := (range_split (range_split (range_split (range_split z10_0 (range_split z10_24 z10_48)) (range_split (range_split z10_72 z10_96) (range_split z10_120 z10_144))) (range_split (range_split z10_168 (range_split z10_192 z10_216)) (range_split (range_split z10_240 z10_264) (range_split z10_288 z10_312)))) (range_split (range_split (range_split z10_336 (range_split z10_360 z10_384)) (range_split (range_split z10_408 z10_432) (range_split z10_456 z10_480))) (range_split (range_split (range_split z10_504 z10_528) (range_split z10_552 z10_576)) (range_split (range_split z10_600 z10_624) (range_split z10_648 z10_672)))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_0 : ∀ i, 0 ≤ i → i < 24 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_24 : ∀ i, 24 ≤ i → i < 48 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_48 : ∀ i, 48 ≤ i → i < 72 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_72 : ∀ i, 72 ≤ i → i < 96 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_96 : ∀ i, 96 ≤ i → i < 120 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_120 : ∀ i, 120 ≤ i → i < 144 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_144 : ∀ i, 144 ≤ i → i < 168 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 24 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_168 : ∀ i, 168 ≤ i → i < 187 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 19 168 = true)
private theorem z11 : ∀ i, 0 ≤ i → i < 187 → Z 11 i = true := (range_split (range_split (range_split z11_0 z11_24) (range_split z11_48 z11_72)) (range_split (range_split z11_96 z11_120) (range_split z11_144 z11_168)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z12 : ∀ i, 0 ≤ i → i < 11 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 11 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z13 : ∀ i, 0 ≤ i → i < 1 → Z 13 i = true := span_ok (by decide +kernel : span (Z 13) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 13) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z13 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 111 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 8 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 13) (h : NatRunT 111 true (goal 111) s xsG) : False := by
  have hmin : 8 ≤ s := by
    have hl := runT_len h
    change 9 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 9 fG 13 := mainG noRunFull

end Main

end PEqualNP.Outside.L_meta_10662_aux

theorem PEqualNP.Outside.L_meta_10662 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 3 && x 8) || (x 4 && x 8) || (x 5 && x 8)) t → 14 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_10662_aux.Main.noCircuit
  exact ⟨C, hfan, by omega, hev⟩
