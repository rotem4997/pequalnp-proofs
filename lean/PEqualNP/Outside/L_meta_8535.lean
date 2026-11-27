import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8535_aux

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
abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)

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
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_8535_aux.Main.fG (substIn PEqualNP.Outside.L_meta_8535_aux.Main.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 10) (_ : SCleanL 7 gs)
    (_ : ∀ p, p < gs.length → 7 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 7 + p ∈ g.inputs)
    (_ : ∀ x, val gs 7 o x = fG x) :
    ∀ a, a < 7 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 1, 4, 4, 16, 16, 16, 64, 18, 18, 18, 18, 18, 25, 25, 25, 25, 70, 70, 70, 70, 76, 76, 6, 6, 6, 12, 12, 17, 17, 17, 17, 24, 24, 24, 24, 65, 65, 65, 65, 68, 68, 68, 2, 2, 8, 8, 32, 32, 32, 64, 33, 33, 33, 33, 33, 38, 38, 38, 38, 73, 73, 73, 73, 76, 76, 9, 9, 9, 12, 12, 34, 34, 34, 34, 36, 36, 36, 36, 66, 66, 66, 66, 72, 72, 72, 3, 5, 5, 20, 20, 48, 80, 80, 19, 22, 26, 50, 82, 27, 29, 57, 89, 71, 78, 86, 102, 77, 92, 7, 14, 22, 13, 28, 19, 21, 49, 81, 26, 28, 56, 88, 67, 69, 81, 97, 69, 84, 100, 3, 10, 10, 40, 40, 48, 96, 96, 35, 41, 37, 49, 97, 39, 46, 54, 102, 75, 77, 105, 89, 78, 108, 11, 13, 41, 14, 44, 35, 42, 50, 98, 37, 44, 52, 100, 67, 74, 98, 82, 74, 104, 88]

def xsG : List ℕ := [0x22273c7e027c3d28f841c0001cf0f800f0f001e003, 0x3e1e947c20e0444e78fc04787800f001800039e1f00, 0x1e1acbc801c88bff90878078630f0007000ffe000c, 0xe445ffc843c03c359790038007ff000600f0c61e000, 0x9088021104093fe927ffe0000000000000ff001ff70, 0x49ff493fff12110042208007f800ffb800000000000, 0xff100fe2181fe201fc4303f8003f00407f0007e0080]

theorem rowsG_len : rowsG.length = 172 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 86 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 86 false (fG, false) = goal 86 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 86 zs &&& lo 86) ≠ lo 86 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 86 false (goal 86) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 86 false (goal 86) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 86 false (goal 86) s xsG) :
    ¬ HasCircuitSize 7 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 86 false (encT rowsG 86 false (fG, false)) s'
      (ws.map (encT rowsG 86 false)) :=
    RunT.map (encT rowsG 86 false)
      (fun a => encT_inv rowsG 86 rowsG_len false a)
      (fun a b => encT_and rowsG 86 rowsG_len false a b)
      (fun a b => encT_or rowsG 86 rowsG_len false a b)
      (fun a => encT_tag rowsG 86 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 1
  | 6 => 104
  | 7 => 737
  | 8 => 610
  | 9 => 33
  | 10 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0xc9d979a0
  | 6, 0 => 0x537475a9533c194e531ad38352ba05a44d27b1b647dae75947da13c84727c59945e15cb2456569ac42d7e70142cce9a13cc49a553a2c40ac38f54ce037e77b033541ae633472b49133d339ff33a4d98a3371f83d33505fbb328475ac322bd2223058408e2ecfea292e6ea3af2d9208772ba7bbec2a2c570a26fe512e24f0c7d224ee731724d36788227360d32241a0f921674a142097e47620311c6a1f4825201e2a13691df122551da6ce621d7f7b3f1a4ef49c183c6a5b17c366d11790e3ca157e8a5f1557050e155182be12974bca10743711100b93e60fc6cae10ee2c2430d32b57a0adedb0e09f6914b09d7522c07e471e807c120f6062ee04800ceb70b
  | 6, 1 => 0xfa809fc0f1f954a4f021ee36e969104fe80dd446d5deb23dd4958b87d1c9039ecb7e71f8c08cdd6bbdc74f87bd8ea2b9b666e9a2af3ff0b5ada83645a364e4a09ccb0bfe9bda426c9b14dc9a9195919e8edbe669891d7d2484652fc9840bdf947f46e4b67cc0b445786b493076a43c77728f96ff71a1c4546ef8fdb36d83694b69c2b61368e89846677332cf64f6d82c6286658c623aa30660704b9d54b5ea54
  | 7, 0 => 0xa75d25f0a759fa40a2b171409d8449c09263f5a08f77c7708d7ed8708acd8580895182a087544ba08297150081090ab080d260407f5ce2d07d6296207cef17b07850729074a658707451199073da21a0732a3c907105dc606ea04f406dd5c6b06dcdb6506ad2a74064423f30614cea6054ab4c00524bf2304b1e3470490cd60047e4c440438e8070433075e0427222a039d116003893e6c0382b84a037f9ace035c9a4f035b94ea02faedb702f4452502f17ed402c2794a02b3771302afc04b0207216501fa5bbb01ec380601db2a0b01b3b60e019d6e590189c19401353857012672fd011cccac00dcb10f00ca63af00be1459009092e6004b1d290012f6d1
  | 7, 1 => 0x16e214d416dddd4f1637efaa1625bbd7161d4a3115ba8fd715a7e16c15a4310515a17bbd1588aaf11539b46614e6e72114d8c5b014c2cc221491fc791488ab291476dba5146ded9f142ce518136e3144135ea07412ff1acb12f5375312c643a812b04ba11290d98112766b131267a0e6124657a811d5b44411c1a0ba11acfb27118fb74d11816aa5117e4de2115daa35113c2be81069c307105101f2104a3337101c90700f4113c60f24db5c0ebffbf20ead86640e74b5150e4d86310e4b98650e1c76590df4e7180da792110d8643210cffe5440cdbddf90cdab1dd0c7ece980c0f29e30bc2b7550bc287750b88b5640b6bd9cf0ab0a6fa0aa75afa0a8a6afe
  | 7, 2 => 0x235776602346b5dc2311a8ca22e802e821f9d7e121d21df5219a09bb217169f521674a14210f0bb320d5a8a52084e96d207716e2202ebd4d2005012b200159e91ff49b9a1f9711dc1f90788e1ecd8cec1e4314541dffd9861d93007d1d71de621d55dab81cea53111cd7a7ae1cd4a19e1cce992c1c9aaf361c7d2fdc1c771d511c3a02471c3298771c20d8391c0e7c0b1bfbc15f1bdc1bc31bd67ab41baa4c3c1b59719b1b1387371abfecd71a73a5a51a4b7d711a1e8e9d1a1ad35919ee738319cba5be199b16dd19404f6f19306824192ca85218f8b40318cde16118cc570418c87fb318b6167d18298fef18159c2a1795b3c71737d19c172c599416f5c7af
  | 7, 3 => 0x315452153100c3e530b2b34530af31c030591db8303cc9f330097f1c2fe9c8052fbac7d62fb4b1962f66db5f2f2ab9982f0b83832e52573a2df90ece2de5767e2ddfd0172d9403522d8ead432d813fc22d7db59c2d5109aa2d4f0fbd2d153ed02d0a8d442c81f2f72c2d22c12bc659332bc478252b522d3e2b3367b22b301ce82b27410e2aec84612a6a7f8529e1b60b29ad7ed529ab816c29a4db7628f5f7d928d0f54628b3355528191ba827ad0d9527a7f658276f9a642724a17126f5fd8726d55f8226c0d90c26b7e8f0268a6622265d8a09265b75ce25f97c3025c77f76254f99d524ce845b249397482447bc832435bf37241bd58b240d0e4c23d6c984
  | 7, 4 => 0x3f92eb313eae8f263dfed9333d8753e33d4699f43d08a04a3cfdacb83c914c313c7e2e7f3c507bcb3c4d22923bb7f3083b8600553b75c9f83aff47733a07c19939fe013e39b34cd3396f1a743957f58039058cb6389f9afe3823b26c37df7b8637d8c24537d8b31237d63fa636f747d136e4fcf236e3633336c4ee0c36381e1b35f1b40d35ef20a135d7bcd335a20be2353f42163532adc9351f414134fefdc0349c2dc5349388c23472533733cbdc2933bf570f33631182333a158133391392331def09330ba8df32eac37932cd1cd2329487ce3291ec683272012d322d231431f84a1431f4f01b31ba913b31aa5eb331a4cdb331a3ae13318b90533154c47b
  | 7, 5 => 0x4ead8fc44e8da8d54e79ffe14e2eb9c24e001ffc4d5741c24d4b07e44d27b1b64ce5711e4c5c14cf4c4cbdde4b7b22404b67aae54b4a68024b216cbb4b09dcf44ada16a64ad79ca749c1b7b4489cb249482ed60647008dc846e2e74946de45f446cf3c1a46a99c9146949da745a3e07044dc0753447dd8554470a334446f5c8d44597b36442d12c54429397c4422a25d440a81e643ee39d243c4c2934373355743698c474360033243479f8a4336070f4327b3a243256efb4300356842d1ca5842c0bc1f42b84cb742ac62cc428ecd6c421ba70241d7bba141c975554123533440d472f8408fc1e7405837ae402dd7823fc1722f3fb061023fab40893faacb17
  | 7, 6 => 0x60520f44601c3f9c600a864c5fc7b0ef5fb764f55f701f315ed496b15eb36b4e5e889e575e81d4375ddf6f6c5d400fbb5d1bfc0d5cbc232b5c7f15705c0b4daa5c051abd5bc8ce875b7a3e3d5aefc8dc5acc9c955a8f33145a61c7245a2012dc59fe1df05920b3bc58ddde5f58daa29858827f45585ebbc3585956e057be4ec457b46173579801a75796b1fd5675ccd956314a7d5626a4ab55e97c6955a770cb5585f14b554ea74e5504d88f54a929ce548ca037543912075434da74542c84e153c1318353a56084538dc738528ee7435246026952321bad51302e4951121c945106da8e50428afb501200124fc2aea34faa2f864f370fb44efbafcb4ecad218
  | 7, 7 => 0x74649bc0735ca6747355867e72d76d4771d8bfb471cf022871af439071823af0717ae515714e3b92714126f07125faec70c715957070369c702a48b4701634466fd6fd166ec4bc8a6e44c30f6e105a846e0f78636d8e70296bf5322c6bc23dbd6b9f4fa16b44297a6a836ea46a8031376a6143e46a0a360b69920630693504966909a8596900b09568e96f2b68c3b7f468b6cad9685f5223684f21c168145575679d2f7a670add9a66bdbaac66a451ab668be14d6683633465b7f7b965b00b68657c6bee6572407f653e238e65313d0964d24a4c64c67bf063e3e5c663bccd3b6377122262ad70d762a2f78261e3abc061746b586137f95b611f15c360b45516
  | 7, 8 => 0x8a297c8288a5430b8844d96487c79b3b879332b0862d6e5c859f39ba857beae7852e87c68501ee0c83cac331834fc3f583199c438317bf3f82e8decd827b7792824e1f4a81d8d02581b3bcaa80ef201d800d1f1f7f71a8fe7f297fd27f1418b47e95b0c67e3c647b7df7dfa17d8e0e937d6feb227d6457227d25c96e7d18e0d17cfa96cc7cf2646b7c616cbc7c2fc9b37c2f914b7c2bb7117ba01f3e7b0bf2bc7ae65e8e796e901778ecf2ca78a9dd1278a06e8278994c0877d4f84277bdfccd779d249b776d2896774fb7047735cd5876c2e7e7769a5b967691e9787657dda67616aa0f75ea858975dcdfa375bad517758f940274fc375874bc7b9e747e856c
  | 7, 9 => 0xa634a3b7a611403fa5cc59e5a5bd1425a3541940a3422081a304f9aaa2b519b5a2ab52f9a28be7aba23b4544a21d7ed8a18f8858a0d1e879a0c65cb59fb046889f1e57cf9edf5dbf9e86bc729e07128e9d8a0dc39d4e731b9ccb867d9c9a976b9c82d73d9bfe4fbe9bc6373b9b5bd2419b2ad39c9b00ff6b9aa2fff79a27159299e815e99944aabe992c338398fb7e10985d52ec985b259a9697092b966a8abd94e3363394abd36c94a2416b9479b7dc9454d4ab940414d793ee09b2936fa5dd9367a781926fcaf69235fcd191642a4490f000c2908b587b8fd7e8088fc13cf18f1509038e8448a98e7f0f848e473a218ce151fa8bfdbd6f8b84eb518ac5b88b
  | 7, 10 => 0xd018d9fbcf44e698cf0b944ccdb8b157cd97bf6bcd2a9dd3ca13a420c9dcdfb4c9d4b9d5c9c8e576c94740aec935b8ffc817e3dcc75f0e4dc70bae1cc5ce21b8c58c53a2c3a56ca9c1cdda7dc1492cdbc114aa09c0e4723cc00c91fbbf54cc97be824949bdef2bf4bd3541f3bc9ba529bc406fffb9be23a7b99d0a08b925e60ab91ba55fb8237e4ab809949eb79f6f72b794b25db73ebe55b7181439b586e9c3b536cf3cb533005bb4afef77b435a8f6b2a3ec16b22c71f5b1cf6807b05a0788b02847aead8c0388ad88d5f0ad40696aacc7dba5ac5fd702ac4d0209ac0d454eabbb68f9ab388f11a9560be6a8c5d4f2a840bee1a7c9d693a74aa6f0a6642a26
  | 7, 11 => 0xff8bbf89fe54b3cbf92be2a1f8dbc81af662c8bbf5edea19f57460e5f4465719f431373eeedd87efecb23289ea42b0ebe9b60fade98ce265e4ee69cee3b9feefdf70fd72dec3477fddb1a33ddcbf864bdc0e3febdb28940edaf8f443dacc0507d8ecbb1ed8882f11d6ad3752d6a37a26d415b3c5d39e2015d345897fd316a8cad0c1b9cf
  | 8, 0 => 0xec96a7d0e92efc40e4dc0b10dc7833b0d2c01920cdab1dd0c4a5aee0bc2b7550ba855d60ba781040b8aa6360b8220880adaf2b20ab0a6fa0a7e89200a543adf0a319ae10a1727330a063be009d8449c09cd4e900973120109707a6909609b530926c84508fb24b708c6a95f08b37baf0889c0cb084dc5f70825806a07f12c7507c02893074a6587073bd034072535400717ffdf07051e9006e0c1a106b955ef066e6b0b06422f02062d42eb062d029e0589e0060583f4c404a2ce8104889581047053a60422e43b040fe9fd038d0a21038c124b032b8d9f02e2909c02893f710279c50a026ea72501a907ef017c65fb00ea2684006a090900271c9100140713
  | 8, 1 => 0x1ce43de41cd58ab81cbb27301c9d07681c93f5d41c771d511c3298771bf1b8cf1be7c1101b398cbf1ac53a421aba90721a3d327819d1c07319b6bdfd19a9f4bd1972af05191dca3a18ee9eb318cf88211878881d182ca629182b73991824c62717de4b3a17d05b9416e1efcd16ad0c52168684ff168280bb164d1831162fc99816044ccb15d154a015a7e16c15a778001569731915556f981539c0a11507e63f14ffceb314991e941457d5c514403b61138fc1d7135ea074133576b6131a91811309dcd9130345d612500da5123d9aa61204cc2311f80ab3115daa3511064fb210f00e7010b60d8410aaf91d1021991d0fadf1300fa7932e0f9cb26f0f6345a1
  | 8, 2 => 0x3039abb12fbac7d62f2ab9982f24ccd12ece4d7d2e755b2c2e45224f2e30c55d2e22958d2cab60232c8cb5052c8abece2c81f2f72c222a842bb5e2d22b89f1722b3af7082a189d5d29c1a989291ce11f28d6c4fe28d0f54628894d5c27f73dfd2783e5e6276b8703274a5b67272f039726ec3dda26e8b9c326c4606d26931dee2692a093265d8a09264bd3972628e73126011dee25fdb14d25f000dd2537fea224e583d624a9072d2451247823b6eedd22e8b343227dfce321da25fa21cf1d30210a88a82081b4731fdbcdde1fd4a3741f72d89f1f6027d71f29bf581ecd8cec1ebbe6fa1e7cdd051e2e95431e229f271e1b8a341d5c00c01d3a47601ce74227
  | 8, 3 => 0x42925a344280c95141a7539441a3892f4153067e40cf2d0440c3b5b7405837ae401f6a633ff375523f5e60413f2a06f13ec9abd83e6ba6583e6184143e0355663d5cffce3cda1cad3cb7dcc03c387a9d3c26ecd53c1ab4773be166923b8186833b51f55c3b2d39433b1f67153af0d1b23a8d60d43a86a5743a44f6e53a07c19939f77a4339e5968f39d9e32739bed32139b596a0398566533973459c3957f58038aee004384c6b1c37bcd569378ec5083776001836e6b5e036a1f1e035f04a1d3556d7cc34cb5afc344a4b9d335b2455331def0932f421c332e9d14532cd1cd2326549c631d0dfa931aa5eb3317d112b3132947d30c46d8c30af31c0305a530c
  | 8, 4 => 0x5341ab4d53224ff653083e7f5302377752f61dc852f1da7e52649c1951fd184b51a30a51513e9647512e6f6250b02ee9507736a94ebdb6de4dab34be4da47df84d9e85234d6b71a34cf925bc4cd88c804c6fb8034c5edc644bed3eae4bc46e054b7b22404b1801bb4aed55214ad79ca74aa3d5254a831f0749801f7b495e8da248c4822148ba7523483cd90e48399814476ad84d474048aa4729e385470f132a4704d68347008dc846f80f81467582064672187a462e384f45d7d05e4557ef4044d74e69447d6e84446f5c8d4448dca2440c922143d0c03543c98d6543c5cf84437f295b4327b3a242fa3b8e42f73e7642d001b342c8d66742af25fd429875f9
  | 8, 5 => 0x695817cd6901175e680e8bdd67ff844c675e913f6716750166f7dee966496fcb6636b21f65eabdce65bacd7665940aef654bbb5c64c14b376426ad5163fc03d963d872df63b45f2d6396fa74637fef5f6368a3b46257a6f8614f15e75fe614745fd5ceee5fcc07fa5f7d377f5f0773725ed728085ebcc9f25ea02d155d7d45075d400fbb5ce740555bf004145b8d2b615b62a0bd5a7a61165a5205305a4a10fd59b18278599259be598d7ff959764d7e595f3b18592a766e591ba9f158bb498f58acdf1d583e177258106ece5808eec858066fb9580302f257af223f57461f7f57022c4755a9c5015524fc6a549220535490fb39546b177f5398b7ab534325c1
  | 8, 6 => 0x842f35f883fe586283c4634183a30065834fc3f583380fdd82c050a382624ef18248acf78238dab9822b0f7a8219a5de809560c37f61423c7ecc17ce7e2159ca7df0601c7dad206e7d7edc057b6f3be77a23d79f79bd0a427994442879935036791f8b33785d4a8c785c9bdb7844020077e7043c77bbbdeb77af5c20774c7a2c77001d3376c2e7e7763e1d2775fee83f75c08112757625d6753f3ccd745f0c937459c22c73b21d547323207c70b91f4a70b7137b70b50f6e6ec57d0f6eb5218e6e80e8126e4678eb6e0f78636dbb6d296d9f60956d5099866d4d48d76cc4c5d96c1982096bf2c3456b7527306aa84aed6a418b156a0a360b6a00077b69f4e6a0
  | 8, 7 => 0xa6f343d1a6642a26a58b16aea4f40ec5a457a15ea260dbc2a20f6c52a1f8eea3a0029de29fba43149fb046889f953af79f7146509e376f489e1f59f49c9ef99d9c9a976b9c82d73d9c32a91c9c2ab6339c17801e9bfe4fbe9bade7a69b7a2fd199a26e0f97b39e829764892697371f769707ee4f955c0fb5953cac4794abd36c93aaee279367a7819311c4a2926fcaf690f000c290a2ce569052ee158f990e8c8ec6ba0e8e903dd08e7f0f848e51fc2f8db036288da5f8d68cbb4df48bdb5aed8b31692f8acf6ba989f6f6998920efba890fa2918903786e88a0bfef87c79b3b879332b086cb75f4860193ac85bc35aa84f7ff5c84d0aa7684b359da849c81c8
  | 8, 8 => 0xd39e2015d308f33ed1b10666d06046d2cee538d6ced89200cd991491ccced44fcc86a505cbce9a7dca00b848c9dcdfb4c8a56210c7ad9f78c787b36cc70bae1cc68afef8c3c2a304c2c9722dc2996c92c0fdd5a3c0a0f1d4c082111cbfe81143bec9b586bcc48411bc174c5aba9accb9ba722647ba4ef708b9900156b94af3aab8237e4ab809949eb7084250b65a3556b6305ea9b60393abb602227fb5f968cdb55977dfb504880bb4cd85a9b3c8b594b2de1759b12743dbb057674bafff3feaaea59538ae1b72d8ad88d5f0ac597986ac4ebb36abc9eee2abb857f3aba0398cab3e2e03aa5cddefa9efae0fa97211faa931f39ca8ddb68aa7cba62fa7643649
  | 8, 9 => 0xff1f0f72fcfab283f9a88c89f92be2a1f8dbc81af865a4b0f7acfc7ef73faf78f6e867f6f57460e5f2995af0eedd87efed9a88e3ed87b07de7e85999e76861fbe5a783e8e589aa6bded90405dd10d4e3dc469019db589760dacc0507d9c75a6dd97d9fa1d91e3cbad8882f11d69d42aad65aeafbd504d919d48bd011d488b3f2d4278d0ad3b18f41
  | 9, 0 => 0xf9a88c89db589760c70bae1cbcc48411a4f40ec59e1f59f49bade7a684f7ff5c83c463417d7edc0577001d3376c2e7e76426ad515a52053058acdf1d55a9c5015341ab4d53083e7f4dab34be462e384f3a8d60d42f2ab9982c8cb505274a5b67265d8a09227dfce319a9f4bd0c4a5aee0ab0a6fa0a543adf073bd03404a2ce81026ea725
  | 10, 0 => 0xab0a6fa
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xe445ffc843c03c359790038007ff000600f0c61e0003e1e947c20e0444e78fc04787800f001800039e1f00022273c7e027c3d28f841c0001cf0f800f0f001e003ff100fe2181fe201fc4303f8003f00407f0007e008049ff493fff12110042208007f800ffb80000000000001e1acbc801c88bff90878078630f0007000ffe000c9088021104093fe927ffe0000000000000ff001ff706667fdcce3e4d4d69b941c000000000000000000000
  | 0, 1 => 0xd9980b331c1b3fe967ffe0000000000000ff001ff7049ff493fff1a19a96328e007f800ffb800000000000022230c4a024c0d289841c000000000000000000000ff980ff31c1fffe9ffffe3f8003f00407fff07ffff0f445ffc843c93e35b7d3038007ff000600f0c61e000be1e967c20e9664f7cff04787800f001800039e1f002667f4cce3e4c01698001fffffffffffff00ffe008fffff4fffff1ff301fe6383fff83ffff87f0007e0080
  | 0, 2 => 0xedffffffffd23d35d7b08387ffffffbe00f0c61e00041e5edbcc31c98bffb0878078630f0007000ffe000c42677bcfe327d3d28f841c0001cf0f800f0f001e00303e3bcfca03cc8fff98c7c078630f0007000ffe000c2626f7cfe0e7c7d69f941c0001cf0f800f0f001e003da5b6bb46320787bef6c07f87ffff00780f0fffff00fef1a35e98036abe054b7bff860ff0400f00f80008cc1e16b83df1fbbb18703fb8787ff0ffe7fffc61e0ff
  | 0, 3 => 0xfe5ffffc63e07c7ffffc07f87ffff00780f0fffff006dffdd7fffd2150452b08007f800ffb800000000000b48c965904c93fed37ffe0000000000000ff001ff70ff900ff2181feaa9fd4b63f8003f00407f0007e00803e3eb4fca0e4c4def9fc1c787800f001800039e1f002606944c20e0444618940400000000000000000000000a02094800c88bba90878000000000000000000000d9774b2efb1b2ee965df6007f800ffb800ff001ff70
  | 0, 4 => 0x7e5fdd7c63e0544e7afc04787800f001800039e1f00e465ffccc3c4bcb79f901b8007ff000600f0c61e00003e3ffffe03fcbffff8c7c0787ffff807f0ffffe00fed55ffea5bd23c35d790038007ff000600f0c61e0007f1e9d7e38f2444e78fc04787800f001800039e1f006667ffcfe3e7d7d69f941c0001cf0f800f0f001e003f4cddf5947c93fed37ffe0000000000000ff001ff70d0cd4b1947093fe927ffe0000000000000ff001ff70
  | 0, 5 => 0x90a82295840dbffbaffff8000000000000ff001ff70fd55ffea5bdb3e35f7d3038007ff000600f0c61e000ff1e9f7e38fb664f7cff04787800f001800039e1f003fff38c0a0fcccf181f47c7ffe300001f000c601f0cd9ff4b3fff1b3fe967ffe007f800ffb800ff001ff7001e9acbd841c99bffb28f8078630f0007000ffe000c02aa73d7e427d3d28fa49c0001cf0f800f0f001e00392aa32d5a42dfffbaffffc000000000000ff001ff70
  | 0, 6 => 0xe667ffcce3e4fcf79f941f8007ff000600f0c61e0004bff79ffff36d1d2cba49c07f800ffb8000000000000067f00ce3e0001600001c07ffc0ffbf8000f80000fd9ff4b3fff1b330166638007f800ffb80000000000065e5fdfcc3dc9cbffb9878078630f0007000ffe000cff169fee38ffe647fcd707f8003f00407f0007e0080b68e965d24e97fef3fffe4000000000000ff001ff70d9ff4b3fff1b3ba9676be007f800ffb800000000000
  | 0, 7 => 0xff323fe6b83fe2d3fdc71ff8003f00407f0007e008052454908432dd2ca2a4f7c7800000041ff0f39e1fff3c3ce7bbc0c7879cf778187879cfff818f0f39fff03c10e9b9e38ffa64f84bf0780783ff041ff003e01f804bdd3af81f35d2d2cda49c07f9cff0380f0f001e003ff55dfea5bdff605fed303f8003f00407f0007e0080481ee5837f0e99bfbb28f8007e300fb87000ffe000cff554fea5b1ff201fe4303f8003f00407f0007e0080
  | 0, 8 => 0x6445dd4843c01404129000000000000000000000000fe1e53437fe3774006f787f879cf0fff8fff001fff31a5bac8b3c234b75916784787e300ff98f0fc601ff3ff302fe6981fe293fd431bf8003f00407f0007e008049ff69bfff169192cb209807f800ffb80000000000077e1dd43dff2554e3adc847f80000fb9800039e1f008b320226b836fc234f901c7ff800fff9fff039fe08fff980ff31c1ff301fe6383f8003f00407f0007e0080
  | 0, 9 => 0xc000c73f5f03330e7e0b838001cffffe0fff39fe0f391e1aebc801daabffd4b78078630f0007000ffe000cffdd4ffb5f1ff301fe6383f8003f00407f0007e00804b327be7f837c3d2cf841c0001cf0f800f0f001e003db327be7f83fe3d3efc71c0001cf0f800f0f001e0032626b4cca0e4c4d699941c000000000000000000000010e5ca167fc9541fab4840079f00fbff0ff07fff73b422c507e0ca2d2d325b63f806300fc7f0f0ffe1ffc
  | 0, 10 => 0x922273c7e02fe3d3afc71c0001cf0f800f0f001e00302a230d4a02cc8fba98c7c0000000000000000000000067f00ce3e00cfe019c7c07ffc0ffbf80fff81ff7f6d558e291bd103c4578403fffe30f07ff00ffffe08c4910b92218f20cfe419c7c0007c0000780fff81ff7f2600b4c000e4c01698001ff807ff0047ff00ffe008f3e3ef7ffe0e7c7defffc1c7879cfff818f0f39fff03928a125524297feb2fffe4000000000000ff001ff70
  | 0, 11 => 0x6f980df31c16dde8dbbce3f8003f00407fff07ffff0d9980b331c1b33016663800000000000000000000006fffdd7ffff255465ab48407f800ffb80000000000027e7bcfca0fcccfff99c7c078630f0007000ffe000cff121fe6383fe243fcc707f8003f00407f0007e00804bff597fff3251424aa48407f800ffb8000000000003e9e947d24e0554e7afc84787800f001800039e1f00e647ffcc63e07c779f94078007ff000600f0c61e000
  | 0, 12 => 0xe5a45374c3dcb48a6e987b8781cff00670f039fe00cadbab6f7bcd22d35d5b08387ffffffbe00f0c61e00002cd83da07c7de2c8c38e007fe0ff03f8ff0f801f7cd9f1afbe981faabffd4b78078630f0007000ffe000c25a4944b9cdf87841093f80780000ff87f0f00000ffe4e5ffdcc3ccbcbfbf987b8007ff000600f0c61e000ffb02ff6981feabbfd4b7bf8003f00407f0007e008049ff69bfff1e99bbeb28f807f800ffb800000000000
  | 0, 13 => 0xb600b6c000edeeffbddf7ff807ff0047fffffffffffe667ffcfe3e7fff79f941f8007ff0f860fffc61e003fdf1acbc981ca8bff94b7bff8630f0407000ffe008c0202104420204042088404000000000000000000000e4cdffd947c03d3597b0838007ff000600f0c61e000c3c318443f3878630887e7878630007e70f0c6000fc2688b4d104e4d1169a209ff807ff0047ff00ffe008f49f1adbe981e88bff90878078630f0007000ffe000c
  | 0, 14 => 0x2021245202143c20f84040000000000000f001e000ff100362181fe2006c4303f8000f00407f0001e0080fddd8c381fd83cad717be3fffe30f07ff0f0ffe1ffc6445fdc843c01c349390038007ff000600f0c61e00092aa73d7e42ffffbaffffc0001cf0f800fff001ff7300202285800583d28f84180000000000000f001e00049ffedbfff1e99bffb28f807fe30ffb87000ffe000c00eff01de7e01dfe03bcfc07ffc0ffbf80fff81ff7f
  | 0, 15 => 0x2226387e027c3d28f041c0001cf0f800f0f001e0036f77fdeefbf6c016d8001fffffffffffff00ffe008f3ff1acfc801cc8bff948787f8630f0007000ffe000cffff8c3fbfffffef787ffffffe30ffffffffffe1fff00000201000103c00784000000000000000f001e0002404944800c00404109000000000000000000000000404549084300100002000000000000000000000000049f1093e98120000400000078000f00000000000000
  | 1, 0 => 0x4910092218120000400000000000000000000000000e645ffca43c7fe359f90038007ff00060ff0c61e0001bba0037bc3fc3ca686ffc7ff800fff9ff0f39e1fff1a1a00033c2343400067847878000ff98f0f0001ff30041ac880000083591000000063000000000c6000002e1e947c20e0444e58bc04787800f001800039e1f0009ffacbda41c99bffb28f807fe30f0007000ffe000c0020208480048092890018000000000000000000000
  | 1, 1 => 0x2a273d7e02fcbfbaf8c7c0001cf0f800f0f001e003fddd8e381fd93e2d747be3fffe30f07ff0f0ffe1ffcfddd8c381fd83c2d707be3fffe30f07ff0f0ffe1ffc022a73d7e027c3d28fa41c0001cf0f800f0f001e00302a273d7e027c3d28f841c0001cf0f800f0f001e0033e1e947c20e04c6f79fc04787800f001800039e1f00ff10afe2181feabffd4b7bf8063f00407f00ffe008c40cd491947001100022080000000000000000000000
  | 1, 2 => 0x73c0400000108780000001cf00000000001e000822273c7e027fff38f941c0001cf0f800fff001e003fff1affe981feabffd4b7bff863ff0407f00ffe008c01000ca0001c8001f800000000300000700007e0000d9100b22181b220164430000000000000000000000041e1adbc801c88bff90878078630f0007000ffe000cff55ffea5bdfe215fc4303f807ff00467f00c7e00806f77fdeefbf6c056d8841fffffffffffff00ffe008f
  | 1, 3 => 0xe465ffccc3c03c359790038007ff000600f0c61e00025e5bcfc80dc8cbff99878078630f0007000ffe000cff55ffea5bdffe35ffd303f807ff00467ff0c7fe080f4000fc000092201b4430380003f00000000060000002222087a027c3d289041c0000000f800f0f00000039000020000092201244300000000000000000000000020273c4602040528f84040001cf00000000001e000e645ffcb43c7fff59f94038007ff00060fffc61e000
  | 1, 4 => 0x3fffbcfca0fcccfff9fc7c7ffe30f001f000ffe1f0c91e9aebd841dbffffffff8078630f00070fffffff7cc3e37bc7ff3ffbf38f87ff8787ff0ffe7fffc61e0ff00206383c00783908700180001cf0f800f0f001e00340eff91de7e01dfe03bcfc07ffc0ffbf80fff81ff7f0020a484800c88bfb9087800063000007000ffe000c6f77fdeefbf6c096d9001fffffffffffff00ffe008fe445df4843c03c251690038007ff000600f0c61e000
  | 1, 5 => 0x6e1651427be24000000007f879cf0fff8f00000008300800010000808a921086000000000000000000000001e1ac80801c88bfb9087807863000007000ffe000c7fffdd7ffff2554e7afc847ff800ffb9800039e1f00491e093e38120000402000007800f000000000000003e1e944820e0444410f404787800000180000001f004955492a5b1210004200000000000000000000000000088001104001100022080000000000000000000000
  | 1, 6 => 0xff300fe6981fe201fc4303f8003f00407f0007e008049fdacbc9f1c98bff928f807fe30f0387000ffe000c1bba0037bc3fd3ca6a6ffc7ff800fff9ff0f39e1fff6445ffc843c014149790000001cf00000000001e0003fff9c7ca0f0444e78fc047ff800f001800039e1f003e9e947d24e85def7bfce4787800f001800039e1f004bff7bffff37d3d2cfa49c07f9cfffb80f0f001e00300226187e00681928b00180000000f8000000000000
  | 1, 7 => 0xe645ffc843e5fef79f941f8007ff00060fffc61e0032dffbcfca0dc8cbff9b87807fe30f0007000ffe000c3602944420e0444e38dc047800000001800039e1f00360e945c20e0444e38fc04787800f001800039e1f00e5e5fffcc3dcbcbfff987b8787fff00670f0fffe00c3e100460000040007840007800000000000001e000000e16001c70019b00300f80787c00fbe00ffc01e07f6d75edaadbd68014d0001bffffffffffff00ffe008f
  | 1, 8 => 0xfdddcf3b5fdb3f2d767be3fffffffffffffffffffff9898023104093fe967ffe0000000000000ff001ff70e445dfc843c0340596900380003f00000000060000009ffacbca01c88bff9287807fe30f0007000ffe000c9088021104093be9276fe0000000000000ff001ff70ff100fe6181fe203fc4303f8003f00407f0007e0080e445ffc843c034149690038007ff000600f0c61e0001bba20b7bc3fc3dae96ffc7ff800fff9ff0f39e1fff
  | 1, 9 => 0xe4c5ffd843c83cbdb798638007ff000600f0c61e00000224107e00201000200000000000f8000000000000ff327fe7f83fe3d3ffc71ff801ff0fc07f0f07fe0834b100be21817c200cc000000000f00000f000000000ff5fdf6b7ff3774456f787fffffffffffffffffffffbe9e967d24e97fef7fffe4787800f00180ff39fff70100800100000044820fc00000000000000000001f00e4c5ffd843c03c359790038007ff000600f0c61e000
  | 1, 10 => 0x481e41037f0211000220800078000fb8000000000009b100222181fe2016c430078000000407f0001e0080f4cdffd947c93ffdb7ffe38007ff000600ffc61ff70c0454b0843003c21079000000000000000f0001e00049fb4937ff12110042208007f800ffb800000000000fddd9c781fd83c2d70fbe3fffe30f07ff0f0ffe1ffce545ffca5bdfbe359793038007ff00467ff0c61e0809088021104093301266380000000000000000000000
  | 1, 11 => 0x1e18c3c8010000e780800078000f000000039e000000e1a09c800488be890878078600f0000000f80000ca626f7cfe0e7fff79f941c0001cf0f800fff001e003be1a12433ce3674004f787f879cf0fff8fff001fff3fdfdefbbdfdfbfbdf77bfbfffffffffffffffffffff6df5acbc9bdc88bff9087bfffe30f07ff000ffe008ced100fe218122001d4000380003f000000000600000ffff5b7ffff3774046f787fff9cfffff8fff001fff3
  | 1, 12 => 0xfe9e53537feb7fe927ffe7f879cf0fff8fff001fff3900802010401374006f780000000000000ff001ff70ff149fea18dfe605fcd303f8003f00407f0007e0080081e003c20000000402000007800f000000000000008000020100013fe1079400000000000000ff001e000020073c24007c2108f80000001cf00000f00001e00000aa4117e40211000220800000000f8000000000000ffd1affa181feabdfd4b63f8063f00407f00c7e0080
  | 1, 13 => 0xbfbab6f7bcffeffffdfffffffffffffffffffffffffe4000fc00000200194000380003f00000000060000000aa0015a42001ca002cfc07f800ffb9800f3801f7fe445ffc943c13ff59794038007ff000600ffc61e0003e9e947c20e84cef79fc64787800f001800039e1f00c9ff6bbfff1fbbb1c723fb87fffffffe7fffc61e0ff41e14903df1211000200800780000fb80000000000041ededbdc71c99bffb28f8078630f0007000ffe000c
  | 1, 14 => 0xff108fea181fe205fc4303f8003f00407f0007e00808000020000003c21079000000000000000f0001e000fddd8d3a1fda3c2d707be3fffe30f07ff0f0ffe1ffce62673c7e3e7f7d28f941f8001cf0f860fff001e003ec55ffe843c03c35d790038007ff000600f0c61e0007ff1adfe981ec8bff948787f8630f0007000ffe000c01e1acb8801c88bdf10878078630f0007000ffe000c01e128bc801c88bbe90878078000f00000000000000
  | 1, 15 => 0x49ff49bfff169100ca208007f800ffb8000000000000020a4bc8004809ef90818000000f000000039e0000b6eff6dde7edffffbffffffffffffffffffffffffff3ddd8c3800d80c2d7078607ffe30f001f000ffe1f0c41e16983df1699b08300fb8787ff0ffe7fffc61e0ff3e1a947420e0444e78fc04787800f001800039e1f003e1e967c20e1464e7cfc04787800f001800039e1f00ff1e9ffe38ffe64ffcff07f8783ff041ff003fe1f80
  | 2, 0 => 0x1bba0237bc3fc3ca6feffc7ff800fff9ff0f39fffff02eff05de7e05dfe0bbcfc07ffc0ffbf80fff81ff7fe6000fc20007e2019c000380003f00000f0006000000000843c0000000e780800000000f000000039e000090c90a1904093fe927ffe0000000000000ff001ff70ff100ff2181fe209fc4b03f8003f00407f0007e0080c1c14b035f1b3b210603e38787ff0ffe7fffc61e0ff020003c20007c2008c000000000f00000f000000000
  | 2, 1 => 0x822273c7e027e3d38f841c0001cf0f800f0f001e003ff120fe6381fe201fc4303f8003f00407f0007e00804b7369a6fb36c012c8001fffffffffffff00ffe008ffe3e73c7ffe7f7d28ff79ff879cf0fff8fff001fff302025343602343400684040001cf0f800f0f001e00349ff69bfff121110c3208007f800ffb800000000000b680b6d000edeeffbddf7ff807ff0047fffffffffff022271c7e026c1d28b841c0000000f8000000000000
  | 2, 2 => 0xfdffcd3fffda3d2d727be3fffe30fffff0f0ffe1ffc49dd08381f10100040208007f800f03800000000000022023c68007c2928d001800000f00000f0000000009088021504093feb2fffe0000000000000ff001ff7001e3acbca01c88bff90878078630f0007000ffe000cfe5fffcb7fe37f7597f787f87fff0fff8fffc61fff3e404534043c034000690038001cf000600f0001e000be9e967c20e96eef7dff64787800f001800039e1f00
  | 2, 3 => 0x3ebeb4fca0ecccfff9fc7c787800f001800039e1f00e445ffcc43c03c379f90038007ff000600f0c61e0006f77fdeefbf6c416d8901fffffffffffff00ffe008f2ff7bcfca0fcc8bff9087c7ffe30f001f000ffe000c01e1aebd801d8bffff8c78078630f000700ffffe00c0061ac8c800488b799001800063000000000c600000b600b6c000e5e6569cd71ff807ff0047fffffffffff3ff5bcfc80dcccbff9d8787f8630f0007000ffe000c
  | 2, 4 => 0x22273c4e024c0d28f841c0001cf00000000001e0006d558c281bd00004500003fffe30f07ff000ffe008c8080021000083ca9279860000000000000f0001e000d9100fa2181fa201fc43000000300000700007e000081e1aebc801ca8bffd0878078630f0007000ffe000ca404964800c03c25179000000000000000f0001e0000222f7cfe027c3d69f841c0001cf0f800f0f001e003ff51afea181fea35fd4303f8063f00407f00c7e0080
  | 2, 5 => 0x3e1e94fc20e4c44ef8fc04787800f001800039e1f00c9ff4b3fff12310146208007f800ffb800000000000e445ffd843c03c3db798038007ff000600f0c61e000f7e1ffc3dfffffffbfdfffff87ff0fffffffffffffffe1e53437feb774126f787f879cf0fff8fff001fff3497f492fff12110042208007f800ffb800000000000022233c6a027c2d28d841c00000f00000f000000000022273c7e02fc3d3af841c0001cf0f800f0f001e003
  | 2, 6 => 0x3efff47de7e05dfe7bfcfc7fffc0ffbf80fff9fff7f000e901c20e0044e00bc04007800f00180003801f00fe1e53477fe377420ef787f879cf0fff8fff001fff349ff493fff12150042b08007f800ffb8000000000007fdf9c7c3ff0544e78fc847ff800f039800039e1f00ff100f62181b62017c43007800000000000001e000091e90a3d84193fe967ffe0078000f00000ff001ff70e445ffc843c4bc359f90038007ff000600f0c61e000
  | 2, 7 => 0x22232c5a025c3d28f841c0000000000000f001e0000b320026b836c00248001c7ff800fff9ff0039e008f022273c7e027d3d28f841c0001cf0f800f0f001e003922273c7e02ffff3afd71c0001cf0f800fff001e00349ffadbeb81e88bff9287807fe30f0007000ffe000c1b320026b83fc2ca684f7c7ff800fff9ff0f39e1fff01e1083c80100000400000078000f00000000000000e445ffc843c02c359590038007ff000600f0c61e000
  | 2, 8 => 0xf4cdffd947c93f35b7f3838007ff000600f0c61e0009bba0237bc3fe3cb6c6ffc7ff800fff9ff0f39e1ffff445ffc843c03c35b7d0038007ff000600f0c61e000ff100b6218136200444303f8000f00400f00000008001e9083d84101100422080078000f00000000000000fddd8e381fd83c2d77fbe3fffe30f07ff0f0ffffffcfdfdacbc9fdcbcbff97bfbfffe30f07ff0f0ffe1ffc01c18c380018082d700860078630f0007000ffe000c
  | 2, 9 => 0x6445fdc843c01c3593900000063000000000c6000000bffbcfca03cc8fff9ac7c07fe30f0007000ffe000c199800301c180008606be07ff800f079f00039e1ffc9088021104093ba9276be000000000000000000000001e12890801c88b9a1087807863000007000c60000c01a000039c1f83800003f80780000ff87f0f00000ffe4454fc84300300196000380003f00000000060000000eff09de7e49dfe8bbcfc07ffc0ffbf80fff81ff7f
  | 2, 10 => 0xe4c5ffd943c93ffdb79c638007ff000600ffc61e00049ff493fff12114042a48007f800ffb800000000000fdfffc3dfff83dff73fffffffff0fffff0fffffffffc00e53037fe3374006b7878079cf0fff8fff001fff3ef77ffeefbf6fc37df901ffffffffffffff0fffe08f6445fdc843c000149000038007ff00060000c6000009088431144093fe927ffe0000000000000ff001ff70fdddcd385fd83c2d727be3fffe30f07ff0f0ffe1ffc
  | 2, 11 => 0xe4efffdde7e03dff97bcff87ffffffbf80fffe1ff7f0045f00843c01c340390000007c0000600f0c01e0003e1ef7fc60e0445efffc047879cff001800039fff00e4049fc800c0240594900380003f000000000600000fe1ed77f7fe3774e7eff87f879cfffff8fff39ffff33e1e104020e0444000f404787800000180000001f0002225147e02241420a84040000000f80000000000000080021100090be9278c600000000000000f001e000
  | 2, 12 => 0x90880313040b3fe927ffe0000000000000ff001ff707ffffdffffffc3def86fffffffffffffff0fffe1fff022271c7e027c3d288041c0001cf0f800f0f00000033ff3bcfca03cc8fff9cc7c7f8630f0007000ffe000c49ff493fff1a110162208007f800ffb80000000000000880011040819a92328e0000000000000000000000ff10bfe218ffeefffddf7ff807ff0047fffffffffffb60006c0000de201bc4303f8003f00407f0007e0080
  | 2, 13 => 0x9f1acbc801c88bff90878078630f0007000ffe000c022673cfe027c3d28f841c0001cf0f800f0f001e0036ffffdfffff6d116da209fffffffffffff00ffe008f4977492efb12000040000007f800ffb80000000000049ff493fff12118043208007f800ffb80000000000041616982db16801080001b8787ff0ffe7f00c60008f3e1e946c20e0444658f404787800f001800039e1f00ff100fe2181fea21fd4303f8003f00407f0007e0080
  | 2, 14 => 0x81a022839c1fabb18503fb8787ff0ffe7fffc61e0ff089e003d24001100422080007800f00000000000000ffdfdf7b7ffb7f6d76ffe7fffffffffffffffffffffff1e5fe37ffff741fef787f879ff0fffffff07ffff3fe10034218036200044303f8000f00400f00000008040457bc8430010108780000001cf00000000001e000022273c7e027c7d28f941c0001cf0f800f0f001e003e4c5ffc947c93fb59793e38007ff000600ffc61e070
  | 2, 15 => 0x19b800339c1f8388606bf87ff800fff9ff0f39e1fff01e1a89c801c88bf810878078630f0007000fe0000c91880eb1041dbfe9ffffe0000030000070ff07fff70bd9884301cd82c2d707be3fffe30f07ff0f0ffe1ffc1bfff03fffffdffe6bfffc7fffc0fffffffff9fffff49fff93ffff21dfe43bcfc07ffc0ffbf80fff81ff7f00ef401de700110002208007f800ffb800000000000920003c2000fe201ac430000000f00000f000000000
  | 3, 0 => 0xc1e96b93df1fbbb18723fb8787ff0ffe7fffc61e0ffffdd8ffa1fdffe2dfc7be3fffe3ff07ffff0ffe1ffcfd100c2018182001704303f800300040700007e0080b622f7c7e0efefffbfdf7ff807ff0fc7fffffffffff020032c00025c2d28d841c0001cf00000f0f001e003e445ffca43c23c359790038007ff000600f0c61e000da1a43037f237340066787f879cf0fff8fff001fff3c22273c7ff27f3d28f879f8001cf0ffe0fff001e0f3
  | 3, 1 => 0xff77ffeefbffeefffddf7ffffffffffffffffffffff01e1acbc801488bed90878078630f0007000ffe000c3e1ed57c60e0444e7afc04787800f001800039e1f00be1eb6fc20edeefffdff7ff87ffff047fffffffffff3600944000e0444e38dc047800000001800039e1f0000c1ac98000808bdb1086000063000000000c60000091e9aebd841dbbbfff6bf8078630f0007000ffe000c2404947c00c0040e789800000000f000000039e0000
  | 3, 2 => 0x920a53436423774006f7840001cf0f800fff001ff73e445ffc843c03cb59790038007ff000600f0c61e0003fff9c7da4f0554e7afc847ff800f001800039e1f00ff55bfea18dfee35fdd303f8063f00407f00c7e0080ff140fea181fe201fc4303f8003f00407f0007e0080022273c6e027c2d28d841c0001cf0f800f0f001e003499809331c12110042208000000000000000000000000ef401de7001de803bce007f800ffb800ff001ff70
  | 3, 3 => 0x12aa0015a42dc3ca286ffc7ff800fff9ff0f39e1fff1bba03f7bc3fc3caec6ffc7ff80ffff9ff0f39e1fff1bba0037bc3fcbeb696ffc7ff800fff9ff0f39e1fff122273c7e027c3d2afc41c0001cf0f800f0f001e0036ff7fdfefbfec8bff9087fffffffffffff00ffe008f0161acac80148016d80018078630f0007000ffe000ce441afc80000283595000380063f00000000c6000007edfdd7d67e0554e7afc84787800f001800039e1f00
  | 3, 4 => 0xff900ff2181fe201fc4303f8003f00407f0007e0080be1e967c20e0644f7cfc04787800f001800039e1f00be9e967d24e9774f7eff84787800f001800039e1f00f4c5ffd843c93ebdb7db638007ff000600f0c61e00049ffcd3fff12110452208007f800ffb800000000000ff100fe3181fe301fe4303f8003f00407f0007e0080e447ffcc63c03c359790038007ff000600f0c61e0006dff4d7fff12110052208007f800ffb800000000000
  | 3, 5 => 0x92a273d7e02febfbafcf7c0001cf0f800f0f001e003020213c62027c2428c840400000f00000f000000000c1c108001f1838210003e3878630007e70f0c6000fce44dffd843c03c3597b0038007ff000600f0c61e000ff100f62181b6201744303f8003f00407f0007e0080eff7ffeffffffbb7df03fffffffffffffffffffe0ff9088021104093fa9277be0000000000000ff001ff704067490fe30211000200000000000f8000000000000
  | 3, 6 => 0xfd100fa2181fa201f44303f8003f00407f0007e0080908873d144093ff9a7ffe00001cf000000ff001ff7001e9acbc801c88bff92878078630f0007000ffe000c081e843c2000000e782800007800f000000039e0000ef55ffea5bd7fe35df90038007ff00060ff0c61e00000cfd01967e01d6c02bce407ffc0ffbf80fff81ff7f6f57dd6a7bf24004500007ffffffffffff00ffe008ffd558c281bd82c2d705b63fffe30f07ff0f0ffe1ffc
  | 3, 7 => 0xf60053435fe3774006d787f801cf0fff8fff001fff3c00063835f0fbbb18703fb8007ff0ffe7fffc61e0ff9288025104097fe92fffe0000000000000ff001ff70900802100009264924ff00000000000000000001f0042227bc7e027c3d28f841c0001cf0f800f0f001e00300ae5015e7e015ca02bcfc07f9c0ffbf80ff381ff7f03e1acfc801cc8bff90878078630f0007000ffe000cbf1006e2181fe201fc4303f8003f00407f0007e0080
  | 3, 8 => 0xfdddfff85fd83c3df7fbe3fffffff07ff0f0ffffffce4458c0803c03c25101003800630000600f0c60000000ede019c7c01dbc0338f807ffc0ffbf80fff81ff7f022273c7e027cbf38f841c0001cf0f800f0f001e00326eff4dde7e4ddfe9bbcfffffffffffffffffffffff3fff9c7ca0f84cef79fc647ff800f001800039e1f00006ff00de7e0155602b49c07ffc0ffbf80fff81ff7f7f9e9d7f3cf2554e7afc84787800f001800039e1f00
  | 3, 9 => 0x3e1e97fe20e7c64efcfc0478780ff0018f0039e1f0000effc9de7e01dff93bcfc07fff0ffbf80fffe1ff7f9088125104093fe927ffe0000000000000ff001ff7080e16281c70dbbb18703fb8787ff0ffe7fffc61e0ff7fffdd7ce3f0544e7afc047ff800f001800039e1f00ffbe5377fffff7ca6efffffff9cfffffffff39fffffff10bfe218ffe217fc431ff807ff0047ff00ffe008f0bba0037bc36c1ca482cfc7ff800fff9ff0f39e1fff
  | 3, 10 => 0x1effcbde7fc9dfffbbcfc07fff0ffbff0fffffff7f0000104000000000008000000000000000000000000ff108ffe181fe20ffc4b03f8003ff0407f003fe0080e545ffe843dcbc35ff90038007ff000670f0c7fe0000080001000000000000000000000000000000000000ff9e9fff3cffffefffffe7f8783ff041ffff3fffff01008843c0000044e78fc00000000f000000039e1f005bff493fff3fd3ca6a6ffc7ff800fff9ff0f39e1fff
  | 3, 11 => 0xf5edfffdc7ddbffffffffb8787fff00670fffffff7c1bba73f7fc3fc3daefeffc7ff9cffff9ff0f39fffff002000048000000000000000000000000000000000003227fe7e03fc3d3ff841c0001ff0f807f0f07fe003000000000008000120000000000000000000000000049ffcd3fff12110e7a288007f800ffb8000039e00003e1e047c20004000786000787800f000000001e00001b100022181fc20068430078000000407f0001e0080
  | 3, 12 => 0x2073c4c00480928f80180001cf00000000001e000ff77ffeefbffe217fc431fffffffffffff00ffe008fffffffffffffffffffffffffffffffffffffffffffffff5fffedbdffebfffdb7bff87fff0467ff0fffe08cdbfb6bb7ff3ffbfbef6ffffffffffffffffffffffffe7e7ffffe3ffffffff9c7f8787ffff867ffffffe00f0041ffc8400008359780000007ff00000000c61e0000080843c000808af790860000000f000000039e0000
  | 3, 13 => 0x6f100de21816c000d80003f8003f00407f0007e00800008001000000000002000000000000000000000000c1e1efbfdf1fbbbfff0bfb8787fffffe7ffffffe0ff0141aca8001c8835f9000000063000007000c7e000093ebffffe43ffffffffffc0787ffff807ffffffff7fffffdf7ffffb7fef7fffe47ff800ffb980ff39fff7000224307e00303c00784000000000f80000f001e0000100082000100000400000000000000000000000000
  | 3, 14 => 0xa3e73ffe027c3d2cfa41c0079cfff800f0f001e00301e3edbfe01e89bffb0878078630ff807000ffe000c01e1fffcc01c88bfff88780787fff0007000fffe00c00000000000000000000000000000000000000000003f100ce0001cc001f840007800300000700007e000000040008000000000000000000000000000000000000000020000010200040000000000000000000000000ff100fe2181ffe21ffd303f8003f00407ff007fe080
  | 3, 15 => 0x49ff7bffff121110c7a08007f9cfffb80000001e0009080021000092aa9254b60000000000000000000000f645ffc843edfeffbfdf7ff807ff0047fffffffffffe6227fc7e027e3d39f841f8001ff0f800f0f061e003fddd8e391fd93fed77ffe3fffe30f07ff0ffffffffc1a1a00342020404a686c04787800f001800039e1f000222f7ffe027c3deff8c1c0001cfff800f0f39fe0031bfbacbfbc3fcbfff96ffc7ffe30fff9ff0fffe1fff
  | 4, 0 => 0x1a00034801c808a680878078000f000700039e000c4bff4bffff17d300ce208007f80fffb80f00000000002eff3dfe7e7dffe8fbcfc07ffcfffbf8ffff81ff7f3fbe947fbcffc7ce78fffc7ff800fff9ff0f39e1ffffedffffd67e97fffffffe7f87ffff00780fffffff70022271c6e026c01288001c0001cf0f800f000000003c0416b80430038318700038007ff000600f0c61e000000e500167e0154002b4840079c00fbf80ff001ff73
  | 4, 1 => 0x1000000000000000204000000000000000000000000ffffbffeb8ffeefffdff7ffffe3ff041ff00ffe1f8cfc1c00001fc03400007383f87800007f80f00001ff011e9acbc801c8cfff9fc78078630f0007000ffe1f0c90c9ae9904093ffdb7ffe0000630000000ffc61ff702400044000000000100000000000000000000000000b400840000c82c2d305b63f806300047f0f0ffe1ffcffffffffffdfff35fff383fffffffffe7ff0c7fe080
  | 4, 2 => 0x22243c7e007c3008e000000000f0f800f000000000f4880fd104093fe9b7ffe380003f000000ff061ff7009ba0037bc12010040208007f800ffb8000000000007fff4d7fff1251007a60807ff800ffb8000001e00003e1007e20007c200fc400078000f00000f0001e0000bfffbefda4fdfffffffffc7ffe30f001f0fffffff7cfe100fe000006001fc4003f8003f0000000007e000001e1acbc80100835d10000078630f0000000c600000
  | 4, 3 => 0x2220007a027c3c208041c0000000f800f0f000000381e1aebc801cbcbfff9878078630f00070f0fffe00c9bba0237bc3fffeb6ffffc7ff800fff9ffff39fffff0000003c00000000400000000000f00000000000000ffff7bc3fffffff187f7ffffffff0fffffffc61fffff6efffdfe7efffffbfffff8007ff0f860fffc61ff730263ffcfe027cbf79f841c0007ff0f800f0fc61e003e4007fc0400020119780038001ff00000000061e000
  | 4, 4 => 0xe5000fe0001ca001fc000380003f0000700007e0000ff5ffffe7bfffe7fffff07f87ffff047fff0fffff803e10847c0000400e784800780000f000000039e000003e1affe801fcabffd087807863ff0007f00ffe000c3c1c843800c0040c707800787800f001800039e1f007f7ffdfefbf6c45ef8fc1fffffffffffff00ffe1f8fffba0ff7bc3fe3cbfc6ffffff83ffff9ff0f3fe1fff000003c00000000084000000000f000000000000000
  | 4, 5 => 0xff324fe7f81fe301fe4303f8003f0fc07f0007e0080b7e1befc80fdeefffddf7fff87fff047fffffffffffb688b6d104edffffbffffff807ff0047fffffffffff0200004000004000080000000000000000000000000d9ffefbfff1fbffffffff807fe30ffb870fffffff7c083e413fe0020100422000007800ff80000000000000041080800000000000000000000000000000000000e4000fc000003c2197900380003f000000f0061e000
  | 4, 6 => 0x1e3493fe0120100420000078000ff8000000000000ff7fffeffff7f756def79ffffffffffffffffffffff00227005e02001d203841c0001c00f80000f001e003b600124000e1664004d707f801cf00478fff001fff3be100660000962017c43007800000000000001e0000ffffdffffffff74ffeff87fff83ffff9ff003fe1f808080020104093ba10703e0000000000000ff001e0703fffffffe0ffcffffffc7c7fffffff81ff0ffffff0f
  | 4, 7 => 0xffdf9c7c3ff87c6f78ffe7fffe30f07ff0f0ffe1ffc59ff493fff12154862fc8007f800ffb800000001f00a400b6c000c02c359590038007ff000600f0c61e000bebef7ffe4effffffffffc7879cfff818fff39fff73edff4fffff123101d6208387f83fffb8000006000009088001004083c29207be0000000000000f00001f706f77ffeffbf7c3d6df841fffffffffffff0ffffe08f2e16946c20e04006580004787800f001800039e0000
  | 4, 8 => 0x2000420000000000000000000000000000000000ffffefffff1ffbbfff6bfbfffe3ffff87f00ffe008c00000c800000000190000000003000000000060000012000000002dc2ca284f7c7800000041ff0f39e1fff03e37bffe037c3d2cf841c0781cfff800f0f001e0030000840800000004100000000000000000000000000ff1e0ffe381fe201fc6303f8783ff0407f0007e008091000ea0001da201fc43000000300000700007e0000
  | 4, 9 => 0xff3efffff8ffe7dfffff1ff879ffffc1ff0f3ffff832c1e947c20c0040450b000007800f000000000000003e3ed57fe0e2454e7afc04787800ff81800039e1f009000020000092ee925df60000000000000ff001ff70000000100000000820080000000000000000000000049ff4b3fff1313c047a48007f800ffb8000f001e000ffff4fffff1fffe9ffffe3fff83ffff87fff07ffff0
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x400c02004005
  | 6, 0, 0 => 0x102606c030940160202408c020140160100600c02088216010170181601420607c04078020141d60700706c030140160100700c01068196010070181800805601017018160540160100700c1404c0160480400c0201401604407018030140160201001c020140f6010070180e0040d60300b028030080560240801c06008056
  | 6, 0, 1 => 0x10060780201420601037018360080160301001c3400805601c060d43400805602007018020140f60100600c330880160c80700c02014316030070183000805601007018030502f60b82d00c02014016010070b003014016010070182b0a829601007018030502860100600c0204c2060102700c020880160100707814014016
  | 6, 0, 2 => 0x10410180300805601007078020040d60101709c020142061001001c2b0080560fc0701803008286010060f8020140160102700c0204c016010070f4030080160f00700c02014016010070183b0080160101709c020540160e017018020142060e80600c02088016010070183600828601007018390140160e003008050041a6
  | 6, 0, 3 => 0x1c2d00c0212c0160100700c020044a60e8060780201401601c0600c49014016100070182b0080561200401c060080160e01709c0201401601003050050044760204601c060140f60103706c0300801601045018030140161100701843094016010060780201421601007108020140160e0060780201401601c060d0020140f6
  | 6, 0, 4 => 0x1058144030500160300701834008576010070180300456601c061542b00805611007018030942f61184001c060ac056100070182b0a80561500401c0600c02601c06008530140161484001c0600805601007144030505060100713c0301401601c0600c4e0140f6134070182b0080561180c01c060d00560200708c02130016
  | 6, 0, 5 => 0x10670180301401601066018020140160900600c4e01401601c061940300801602024018020140f60b80600c6401401601003008630140160106201860014016184070186001401617c070180300805607c040780204c01601c060ac020145e6010071745c01401616c071445a008016010071642b0082960102601843094016
  | 6, 0, 6 => 0x106b0182b0a80560106a01c030080160b8060d0020140160300702834008056010071445a008506100071642b0080561a40401c0600805602007018680140f6
  | 7, 0, 0 => 0x1180405c06014011e5c0401c061c4780140170100701803008731ddc7601c0600c020140170106e0180300805081c750100701803008017010580185a00805005c6f01007018020040d7010740180300805005c0401c0600c021cc727110070187100c05005c070187000c020140f71bc0401c0201401069c041b807018030041971b40401c0600c05005c0401c0600c011b0197
  | 7, 0, 1 => 0x10070180e01401201c041600600c02014507010070188100c05005c041600600c020048071f84401c0600c02015c46010070180313001701007018030087f005c7e010071f40600c0571bc041ac0600805005c070187000c020142f71f0041b80600c02005c040400700c021cc7b7100070182b00c02015c0401c03008011e80d7010070180305001035c040400700c05004197
  | 7, 0, 2 => 0x10070187100c050bdc0401c0600c0223c0170e00600c02014011e9c8e01007018030080172344601c061c003005c0401c0600c0223001701007018030088b005c0401c8a00c020140171bc8901c0600805005c0401c0600c4e15c017010070182b00805221c081180701805004877010102180300805005c042142300c02014017010062100320c05005c0401c8200c02014017
  | 7, 0, 3 => 0x108506c0300805005c04214060780201401716c070180305005005c3801c0600c020140170106e0180300899005c042600600c020140171bc041b80600897005c6f16c07018020140171bc0401c0600896005c8d25407018032500172140600c020140124dc6f010070180204c017010070180324805005c9101c0600c0201401701c061c00300857005c900100701803008057
  | 7, 0, 4 => 0x1f88d1180401c0600dc041600600c021cc017010070180300805085c0409c03008050047a7010071440305005005c042800600c02014017234040400700c02005c0427c0600c02014017010070181e27805005c4001c0600c020140171bc040900600805005c9d2700600c0201401701007018030089b005c0401c0600c02014017030070180300857269c8d0100701803058017
  | 7, 0, 5 => 0x184070180300805005c0401c0600cad0140172340401c0600c02081c0401c0600c020141d7010072b0022ac05005c46010072a8030140170101701802014012a5c0401c590ac02014a870100729c0300813005c3801c2700c0201401701007018032980223dc7e0100701803008577010a501c03008a4005c07018a300c020140171bc0401c0628805005ca10100701803008057
  | 7, 0, 6 => 0x1cba00cb900805005c08030070182b0080570106b0182b008052a1cb80100701803008057010580180300805005c040400700c2a0140172dc070180300805005c8d01007018b600c017010b50180300805005c0401c060d8020040d71bc07018020140124dc0401803008052d00172340401cb300c02005c0401cb200c0201401701007018b1008b0005caf0100701803014ae7
  | 7, 0, 7 => 0x308070180300805005c043040600c020140171f8040408500c02015c043000600c020140171bc042fc0600805005c381b80600c02014017118040400700c05005c0401c062f803014017010072f40300805005c0401cbc00c0201401716c0714403008011b1c460100701803054017234042ec0600c83005c6f0100706c020140170701001c0300805005c8d010070185a008017
  | 7, 0, 8 => 0x3340701803008cc005c6f040071c00201401732c0401c0600c05005c0801c060080503c0172340401cca00c02325c043200600c0201401701007018030084c03dc0401c0600c8f00419731c0401c0600c02005c0401c0600c02014c67010620180300805005c043140600c020140170100700c0204c011b1c8d01007018030085070101001cc400c05005c0401c0600c02014c37
  | 7, 0, 9 => 0x3600401c0635c05005c0401c0600c05004197214063580300805005c042140600c020a40170106e09c0300805005c043540600c02014d470fc070180300801035c0401c0634c0201401702007018020140f21dc46010072cc030140173480401c0600c02005c04040d100c020140171180401c0600c05081c0c01c0600c02014d072340433c0600c02005c4601007018b1338017
  | 7, 0, 10 => 0x106e01803008e2005c040981b00c0201401701007018b1008e1005c042180600c02014017380070180300805005c0401ca700cdf01401701c061c00337805005c0401c0600c023740171180401c0616805005cdc010070180301401701085018031a005005cdb01007144030080170100729c1e00805005cda0100701803014017274d90180300805005c0401c0600c021cc7b7
  | 7, 0, 11 => 0x394070180300813005c070182b0080524ca87184070180301401065c46010cf018030140171180401cca00c05325c1c33c0600c02014017010852b00239005005c0401c0600c250040d70000801c060080503d82401803008050049a7134070180300805005c7e1bc040400700805702007018020140124dc043540600c02014e371180401c0600c05141c041ac5900c02014017
  | 7, 0, 12 => 0x1101001c0300805005c041b803008970041a70101001c7d00c05005c0433ceb00c020140172340401c0600c02005c6f01007018020a40170100700c0204c01069c0401c1b00c25004807010ea01c023a405005c0401c0600ce801401739c0401c0600c05399c0401c1e008050046c71bc0401c0a00805005c6f0100b01802014017010070180329805065c090100701803008057
  | 7, 0, 13 => 0x10f30180300805005c040400700c020140f701c061c00327805005c0401c5100c020040d7010073c80600c05005c041880600c050041970101001c03298052b9c0401c0600cf1014017214061c00300805005c0401c0600cf00140173bc0405c0600805005cee018ed00c02014017010850180313805005c8d10007018030080171bc0401c061a005005cec0187000c02014017
  | 7, 0, 14 => 0x1f8043b00600c02015c4001c0600c2a01401725407018030084c005c0401cfa00c020140170101001c03008050bdc0401cf900c020140171f8f801cba00c02015c0433c06038020140172340401c0600c02075c0401c0600c2a0140173dc070180300805005c8d0100709c030080171180401c0600c8f005c6f010d501802014f673d40401c0600c02005c0401cf401803008017
  | 7, 0, 15 => 0x1f80401c0600c9e015c7e334070180300900701007018ff00805005c0401c06310030140170100729c03014fe005c461000701803014017394070181e00805005cfd02007018020140171f8042140600c02015c0401cfc01803008017010073ac030088f005c460100701803014017234041600600c02005c460e0070180301401701007018031cc7b065c043ec0700c02014017
  | 7, 1, 0 => 0x1bc070187000805005c0401c0600c024200172340401c0610c02005c0401ceb00c02014017011070180300805005c070190600c02014017020240180300805005c0401c0600c0212c0170101001c0300857005c6f010070184e014017275050180300805005c0401ca700c0541001701007018030080540dd0201c0600c020140170110101c0300805005c8d118040400700c017
  | 7, 1, 1 => 0x10070180e0088f005c6f03007018020149a71180401c0600c05075c0401d1000c0201401701c061540300805005c0401c0600c0243c017438070180300805005c0401c1b00c2501401701c061c00305005005c460100709c030140174340401c0600c02015d0c010070180342c017030070183400805005c0401c0642802014017010070180317005005d090100701802014017
  | 7, 1, 2 => 0x10070181e00813005c0401d1c01803014017010070180346c021cdc0401c0603802014017010bb0180346805005d190100701802014017010074600600c05005c8d010070180300419745c0401c0645802005c460105801803014017334070180300915005c070183400805004937010cf01803298052b9c0401c0600c02015147010070180344c05005d120111101803014017
  | 7, 1, 3 => 0x4980401c0600c021edc0401c0600c021cce37010d50180300805495c070180300805490017010070180348c05005c043540600c02015227010070180300921005d202140600c020140170100747c0300805005c044780600c02014017010072b00300801035c4601007018430140171f80401c0600c14015c1f01003278050047a74740401c0600c02015c7e1bc0401c06008057
  | 7, 1, 4 => 0x10070192e00805005c0401c0600c020143170112d0180300805005d2c010072b002014017010260187100c05005d2b0100701803014017010070192a00805005c9d01c060d00201401701085018030084c005c0401c0600c024a4017110070180300805005c0401c0600c024a001701007018032988f2b9c6f274ee01802014017010070180300927005c071447000c020046c7
  | 7, 1, 5 => 0x1bc04018020140111dc0401c064d00201401707c6f01002014011e9c070187000c25004807010074cc0300805005c07018700ac02014a8716c072b00300805005c070193200c0201401701007018714c405005c082140600805004877118042180600c05005c044c00600c020140170100701803298052b9c0401c0600c02014287010071640300829005c0401d2f00c02014017
  | 7, 1, 6 => 0x1c061c0714e405005c8d1180401c0600c0172341c01c0600c02005c0402c060d0020140172340401c0600c2a005c0401c0600c020142f70106b0180300829005c6f48007018020140172540401c0610c05005c044e00600c020140171f80401c5100c021b1c074dc03009360140171f8040980600c02015c8d214061c0030080174d40401c0600c05005c0401c0600c020140f7
  | 7, 1, 7 => 0x113e01803008053d9c952140600c052500172340401ceb00c02005c0401c0600c024f40170100747c0301401065c8d0100729c03410017118850187000c05005c00100070182b008056110070184300805005c8d01007018c400c01701007018030093c005c0401c0600c0215c0171f88d0108501803009c0401c064ec030140171bc0401c060084c005c044e80600c02014017
  | 7, 1, 8 => 0x100708c031a005005c6b0187000c020140170100701843008050bdc460700701803014017510070180300805005c042140600c02054017010070187150c05005c043540600c02258f6701c7000c0201401069d42010070180300801701024018031a005005c071647000c020140171180401cf401803005d4101007018035000170100701803008014fdc8d1bc0701870008017
  | 7, 1, 9 => 0x10030094a014011e9c461bc0701870014017010850180300805081c0401c060d04e014017070073ac0300805005c9d5240600c0201401701c065200300805005c0401c061c4030040d7011470180300805005c7e39407018030080572340401c0603802005c045180600c020140170101001c0327805005ccd0400700c024000171f8460108501803015c045140600c02014017
  | 7, 1, 10 => 0x2344401c0600c02005d5001007018030080170100600c0253c05005c6f0100701816014017010070194e00c05005c7e0106b01803008057010070180319005005c045340600c0225c017010070180300805531c6e0187000c0225c01701c061c00300896005c951bc070180525001701007018030142f065c04214b300c0201401701c061c00300813005c040400700d4b014017
  | 7, 1, 11 => 0x554cd01c0600c02005c8d01007018030080f71f8041b80600c0225dc7e01007018030089672340401d3300c02005c1f39403008050047a72340401c0600ca62b9c0455007018030140171f80401c060d002015c7e1186f0100701805754c045480600c02015c6f0101001c02014017010070180300805545c1c01c06038020140171bc0401c0600815005c240187000c02014017
  | 7, 1, 12 => 0x100b0280300805005c9d5700600c020140171bc042ec0620c05005c043b00600c021cc0171184401c0600c05005c070b4030080500493756c0401d5a00c05005c0401c062c402564017010070186001401065c8d01007018030082f7010070180300873561c6f0100701802014207010073ac0e00805005c0401c0600cde014017011570180300805005c0401c0655802014017
  | 7, 1, 13 => 0x10070180305001201d66010d5018030080571180401c0600c0503dc9d01003008050041a7010070180300965005c0401d6401803014017010070196300805005c040402600c020140171bc0401c0600805141c0401c0600ca60156275856001c0600805005c7e0100708c030080570700701803298052b9d5f018030095e0140170106e5740600c02005c0401c060ac2a014017
  | 7, 1, 14 => 0x5b40401c065b002015c0401c065ac020140170101001c0309401201c04040070ac02014a87010070180327805005c045a80700c02014c971f80401c0607802015c9d01c0600c4e014017010075a40300805005c0401ceb00ca6014ae75a0070180300805005c6f010cf0180201401701007018030080559dcf801cba00c020140171bc0401cca00805325c0401c1b1c403014017
  | 7, 1, 15 => 0x2c061c00300805005c6f010070180223c017010070280313805005c0401c0600c141cc0175d40401c0600c25005c0401c06038a6014ae7070070180329805005d745cc0701803014017010071445a008011b1c041b80600c025c8017010070180352c05005c0401c0600c025c4017011700180300805005c0401c0600d6f01401701007018030096e005c9d0100600c0204c017
  | 7, 2, 0 => 0x1007018030142f2b9c460101021403014017030070280300805269c0c02c0600c020149a71bc0401c0600805005c0809006008050048772540401c0600c050bdc070197a5e40201401707c0407802014011e9c6f0e00701802014017334070180300978005c045dc0700c02014017010072b0025d805005c04040071c539014017010070180327805075c070287000c02014017
  | 7, 2, 1 => 0x10076000600c02005c0401c06038a6014017010ec01803008731edc072b070008e40140170117f0180300805005c6f0100709c020140170101001c0300801035c0401c0600d7e01401725407018030157d005d7c01007018030080172346f0101001c02005c1f01007078020140172757b0180300805005c043540600c022580171bc4001c0600805005c0401c2300c02130017
  | 7, 2, 2 => 0x10bb0180362805005ccd2180600c024000171bc0401cbd00805005c041600600c14014017010070180362405005c0401ca700c056200170118701c0300805005d866140701803008017010070183000805005c042140600c021cc7b7010850180301401065c7e01007018030082971bc0401c0600805075d84010070180260c017011820180300805005d810100701803014017
  | 7, 2, 3 => 0x10070182b00805645c4001c060ac02014a871bc0401c0601401065c0401c0600c25004807010070182b008052a1c040402400c0201401701c066400300805005c0401ca700c020141d763c0401c060ac02015c0401c0600d8e014017010076340300805005c0401c5100c020046c71f80401cac008e4015c5b0400700c020140176300401d8b00805005c040400700c0204c017
  | 7, 2, 4 => 0x10071640300805005c8d1bc0401c06008017118cd01c0600d00005c3f01c0600c02014017118042140600c05005c0401d9500c02014017650070180300805005d9301c0600c02014017118043b00600c05005c463e0072e80301401701007018714e405005c042140600c2a0140170400700c020140124dc041605100c020046c7010070180300992005c5b01c0616802014017
  | 7, 2, 5 => 0x5c061c002014011e5c046740600c0201401701007018030099c005d9b01007018036680570b80600c020140124dc9d6640600c02014017010076600300805005c0401c0600d970140171bc850187000805005c0401c03008050041a70187000c020140111dc4001c5900c02014017010070184309401201c046580600c020140172340401c0600c14005c0429c8500c05410017
  | 7, 2, 6 => 0x10076980300805005c6f010073ac020140170101002c0300805005c0401da500c02014017011a40180300805005c0401c0668c02014017688070180300805005c5b01c0600c02014017010070180300896005c0401c0600c0204c017011a10180300805005c7e07c0400c020147a701007019a000805005c0467c0600c020140170119e0180300805005c6f0700701802014017
  | 7, 2, 7 => 0x1085018030080503dc4601026018030140176a80401cca00c02015c04040d500c02014f671480401c06008052a1c0401c0600c02015a9701007018b1009a8005c0401cac00c02014507010070180300813075da701c0600c02014017010070180328805005c442140600c020140170101001c031a005005c7e01017018020147970101001c0300829005c040900600c02014017
  | 7, 2, 8 => 0x1c060d40300805269ccd01c0600c026b8017040071c00300805005c042140600c0215c01701c061c00300815005c040400700c4e0140171bc0401c7d01805005c46010070182b014a87011ad01c03008011b1c070187000c16014017011ac0180300805005c042140600c020142f707c0400c020140111dc4601007144030046c76ac070180300805005c070180300805004937
  | 7, 2, 9 => 0x106b018030a805005c0401c0a00c020140170100b0180300805005c046cc0600c0201401701c066c80300805005c440980600c020140176c40401c0600c02015cbb0187000c8301401701c061c05a00805005c0433ca7018030140170200701802014012a5db001007018030080170100701803009af005c070187000c0201420701c061c0b1008ce005c0c0400700c020149a7
  | 7, 2, 10 => 0x101001c030084c005c070187000c0223c01701c066e80300805005d200400700c020140171185b01c0600c05005c0401c0600db9014017010030080500479069db801c0600c020140170200401c060080503ddb701c0600c020140170100700c5c01401069c041b80600c026d801701007018036d405005c0401ca700db40140171180401c0600c01035c460100700c050041a7
  | 7, 2, 11 => 0x10077000300805005dbf0100701803014017011be01c0300805005c070187000c020141d7010070180300828035c460100706c030140170100701803008056f5c0c01c0600c020149a70100732803008056f1c0401c0600c026ec017480bb0180320c05005c8d040071c0030080170201001c020140121dc04018030081300479701c061c00300805005c07018030080503c9a7
  | 7, 2, 12 => 0x1180401c0600c29005dc7011c60180300801701c067140300805005c0401c060d00215c017218061c00300805005c0401c0600c02710017480070180300805005c7e118040400700c0571bc042140600805005c6f010ec018020140171f8041600600c02015dc301c0600c02014017274ee0180300805005c950400700c05250017010077080300805005c07019c100c02014017
  | 7, 2, 13 => 0x10070180300805735c042ec0600c83014017010070185a00805005c7e1bc0701870008057011cc01c0300805005c0401c062c4023380170100709c0305805005c0401dcb00c02014017010070180305805005dca010bb018030140171000401c060ac02015c0401c0616802014507010850180309401201dc901c0600c02014017118043540600c053d9c047200600c02014017
  | 7, 2, 14 => 0x7019ce00c02014017
  | 8, 0, 0 => 0x10070180300805005d383340701803008054000187480401c0600c02014018010070197a00c020140181f80c010070180300805871c8d01007018030080185b40401c0600c0201401801c061c00300805004a880100701803008050040180100701803008053380180100701803009b40140183340401c062c403008018010070180300805744018010077400600c020140180101001c03008050047b80100773c0600c02014018
  | 8, 0, 1 => 0x1bc0401c06008730140180000401c0600c0223c017010073280600c020140183e00401cba00c0201401801007019d900c0201401801085019d800c0201401823446010070180300801801085018030080500479801007019d700c0201401801c061c0b100c02014018010077180600c020140180106b01c0600c02014018010070180300805005d687540401c0600c02014018010070180300805004878011d401c0600c02014018
  | 8, 0, 2 => 0x1bc0401c51018020140180100701803009dc014018274070187000c020140180003801c0600c020140170100729c0600c250140181f80401c0600c02014a88010070180300805005db8010070180600c020140180100701803008050740180101001c03008830140180102601803008050048081bc0401cee01802014018010075480600c020140180100701803008130047a801007019da00c020140180100729c0600c020040d8
  | 8, 0, 3 => 0x100709c0600c020140180102401c0600c020140181180401c0600c0542c0180101001c030080525c0181f80401c062c4030080580008d0101001c03008017010bb01c0600c020140180004001c0600c020140170106e01c0600c0225c018011df01c0600c0201401823404040070180300801845c0401c0600c02014018011de2140600c020140180000401c0600c02014017010070180300805005dd8010070180329802014018
  | 8, 0, 4 => 0x1bc040400700c020140182340401c0600c02004ae8010852b00600c020140180100729c5100c02014018354070187000c020140182349501007018030080180000401c0600c020141d71bc0401c06008050047981f89d010070180300805801007018030080578001801007018712c402014018010a501c0600c020140181184601007018030140180101001c03008050049a801c061c0030080540001801c061c00309402014018
  | 8, 0, 5 => 0x7280401c0600c02014018794070187000c02014018000460101001c030140177900401c0600c020140181480401c0600c020140182340401c060ac0300801878c0401c0600c02014018334070187000c02014018010070181e008050047a801c061c0030095e0140181180404007018030140180100701803008730047b8011e201c0600c02014018000041600600c020140170100701803009e10140182340401c0600c02004c98
  | 8, 0, 6 => 0x11ed01c0600c020140180100701803009ec0140181f804354070180300805801007018037ac02014018010077a80600c02014018010bb1b80600c020140180100701803008057a4018010070180300805005e8801007018030080579c018010070188400c0201401816c0701803008050046c801c061c003008052500181f80401c0600c020150087980401c0600c020140181f80401c0600c250080583e0042140600c02014018
  | 8, 0, 7 => 0x10070180300805005f187c00401c0600c020140187947e01007018030080581bc0401cac01802014018011ef01c0600c020140180000401c0600c021cc7b70000401c0600c050041971f8cd01007018030080581180401c0600c05004c98010070180300805005628254460100701803014018070070180300805004ae8010ea0400700c02014018010070180300805005ee80100714403008050046c80100701803008050047b8
  | 8, 0, 8 => 0x20040400700c0201401801c061c07000c020140180100701803008ab0140185040401c0600c02014018010073ac0300805004ae81f80401c062e803008058010075240600c02014018000042180600c020140170100701803008052c001836c0401c0600c020140180100701803094050048081180401c060ac030140182340401c0600c0233801801007018030080545401801007019f300c02014018010070180300805005f28
  | 8, 0, 9 => 0x10070183500c020140180008d010070180300801766c0401c0600c02014018011f82140600c020140182340401c0600ca6008018010070180e00805004ae80100701803009f701401801007018035b00201401801007018037d8020140180100729cac00c0201401805c070187000c0201401801007018037d4020140182340401cca018030080180100701803008830140182340401dc6018030080180101001c0300805005f48
  | 8, 0, 10 => 0x1f80405c0701803008058010070180327802014018274043540600c020140181180401c0600c050048782346f0100701802014018000850187000c0201401701007019fa00c02014018234042ec07018030080181f8042140600c020140181f80401c061c00300805801007018030080525c01845c8d01007018030080180100b01c0600c020140181180401c0600c05338018030040400700c020140180100701803009f9014018
  | 8, 0, 11 => 0x108501803008e40140180007e01085018030080570004601007018030140173940401c0600c020140181180401c0600ca6014018010075700600c020140180106e01c062c4030080187ec0401c0600c02014018010d501c0600c02014f680101001c0300805004a881bc0401c0600c020140180100701803008053840180000401c0600c2a014017010072b003008050046c81180401cca018030140180100701803008050040d8
  | 8, 0, 12 => 0x2340401c0600c020047b87f46f010070180201401801007018030500201401801c061c003008050047a80006f01c061c002014017010077f00600c020140180100701803008960140180000401ceb00c020140170100701803008130140181f86f01007018020140180000401ca700c05410017010073ac0600c0201401801007018030099a014018118042ec07018030140180000401c06310030140170100729c0600c05410018
  | 8, 0, 13 => 0x10072b0062c4020140182540401c0600ca601401801ca70187000c020140180101001c030080540001816c0401c0600c020140180101001c03094020140180101001e0100c020140180000401c0603802014017010070180300931014018010070180300a0001401801007019ff00c02014018010070180300805004d480300401c060ac03008058010070180300805005fe8010070180346c0201401801c061c00300805410018
  | 8, 0, 14 => 0x10070182b00c02014a881f80401c0600c02015048010850180300805004f6801007018030080503c018010103540700c020140181f80401c0600c02016028010070180300805004e385048d0100701803008018010070180300805005f4801007018030093601401807c042140600c02014018010070180329805004ae80200401c0600c020140181bc0401c06008e40140181f80401c0600c020147a80007e1bc0401c06008057
  | 8, 0, 15 => 0x10078100600c02014018274073b80600c0201401880c0401c0600c02014018010075ec0600c0201401801c061c003008050046c80101001c03008052500181f80401ca7018030080580004401c0600c0201401701c061c00300939014018794040400700c020140180100701803008d7014018334040400700c020140180100701803008050bc01839c46010070180301401801007018030080503c8780100729c061c403014018
  | 8, 1, 0 => 0x2340401c0600c020049a801007018b100c021cc0180000401c0600c020140f7010070187100d39014018010173540600c0201401801007018030940200480863c0401c0600c02014018010070180300a070140180100701803008050049380000401c0600ca6014ae70100701a0600c020140182340401c0600c0225c018010075340600c020140180117301c0600c020140180100701a0500c020140180101001cba00c02014018
  | 8, 1, 1 => 0x100701803008050059181f8041b807018030080581f80401c0600c020146c82346f01007018030080181bc0401c8501802014018100070180300805004a88010070180300805004478010070198b00c020140181bc0401c0600805004f680000401c0600c020142f71180401c0600c830140180100701803009430140188240401c0600c02014018010070180300805004a885540401c0600c020140188200401c0600c02014018
  | 8, 1, 2 => 0x100701803094021cc0180100701803008050060f8118042140600c02014018010d501c060ac030080580101701c06008050047988380401c0600c020140188340401c0600c020140181180401c0600c0525c0180000401c0600c0215c0172740401803008050047a80100701803830020140180008d1180401c0600c0170101001c7000c020140181f80401c061c403008058010070180300a0b0140180100701803008050060a8
  | 8, 1, 3 => 0x100701803008054000182540701803008050048780100701803094020140180100701a1300c02014018010078040600c020140183f40401c0600c02014018010070187100c050048086100401c0600c02014018010102140600c02014018010078480600c020140184b00401c0600c020140180100701803008290140180121101c0600c02014018010070180300a100140182740401c0600c020140181180401c0600c050049a8
  | 8, 1, 4 => 0x3340401c0600c0201401801007018030095e014018254042140600c0201401801c061c003008730140180101701cac018020140180121a01c0600c02014018010070180300a190140181186f0100701802014018010078600600c02014018010d501c0600c020140181f80401c0600c0201480801007018030080585c018010078580600c02014018010070180385402014018010078500600c020140183340401c0600c021cc018
  | 8, 1, 5 => 0x6f0101001c020140170121d2140600c020140181bc0404007018020140180100701803008058700180100701803008055e001801c510187000c020140180100701803008052500183e09d01c0600c020140180100701803008050052580118501c0600c02014018274041b80600c020140187940401c0600c020140183600401c0600c0201401886c0401c0600c02014018010850180300805004ae8010070180300805005228
  | 8, 1, 6 => 0x1180401c0600cd70140186180401c0600c020140188840401c0600c020140181bc0401c0600805004c981bc0401c0600805004ae801007018030091a01401801c061c003008050047981f80401cee018030080580100701803008050055881180401c0600c05005f4801007018030080588001802046010070180301401801007018032e40201401801007018030080587c0180100701803878020140180101001c03008050047a8
  | 8, 1, 7 => 0x2349d0100701803008018010853280600c02014018010bb01c0600c8301401801007018030a805004a880108601803008054000186306f01007018020140180300401c0600c020149a856c0401c0600c020140188887e01007018030080580100701803008df0140181bc0401c060ac020140182340401c062c4030080183e0cd01c0600c020140181180c0100701803014018010070187000c020140180101001ca700c02014018
  | 8, 1, 8 => 0x1bc0401c06008053380180100701a2500c020140180000401c0600c9e0140170101001c7100c02014018010070180389002014018010cf01c0600c0201401801d370187000c02014018010070180300896004f68010850180329802014018010101b80700c020140180101001c03008050046c81180401c0600c05004a880101001c0300939014018000f801cba00c020140170100701a2300c020140180100701803008570049a8
  | 8, 1, 9 => 0x100701803008050047a80006f01007018020140170106e01c0600c020048082340401c0600c022500180100701803008011b080801007018030084c014018234046140701803008018010078a00600c02014018234cd01007018030080180100789c0600c02014018010070185a008050046c8274043b80600c020140180100701803008055640181bc0401c06008050048788980401c0600c020140182340401c0600c25008018
  | 8, 1, 10 => 0x7944601007018030140180100701803008050747a80100729c0600c020140180108501803008050047b8118043540701803014018010070180300a2a014018010ec01803008050047b80100701c0600c02014018234070187000c020140180101001c03008050048081bc042ec07018020140180100701803008053f80184800401c0600c020140181180401c0600c054000181f8f80100701803008058010070180300805006298
  | 8, 1, 11 => 0x100701803009760140188b80401c0600c020140180100701803009390140182340405c07018030080180000401c5100c020046c70100701803458020140188b46f01007018020140180100701803008050062c801007018030080560c0180100701a2b00c020140180101001c03008730140181f8070187000c020140181180401c062e8030140186188d01007018030080181180401c0600c05250018010ac0180300805004478
  | 8, 1, 12 => 0x10078c00600c0201401801c061c003008e401401854c7e010070180300805801007018030580500479801085018030080525c0181f87e01007018030080581180401c061c0030140180000401c0600c250048070000401c060ac02014a878bc0401c0600c0201401801c0600c02014012688781bc0401c06008050047b80100701803008050046c80101001c03008052900185980401c0600c020140180101001c5100c02014018
  | 8, 1, 13 => 0x100701803008052640180000401c5900c020140170100701803008056b80180008d1bc0401c060080170004601085018030140170100701a3300c020140188c80401c0600c020140180101001c03008050063182540c01c0600c020140181bc0401c06008830140180000401c061c5390140171bc042140600c020140180108601c0600c020140180105801803008050046c801c061c0035e40201401801007018b100805338018
  | 8, 1, 14 => 0x5b01c0600c020140170000401c0600c0225801701c061c003008058d40182549d01c0600c020140188d00401c0600c020140180000401c0600c0204c0170100701803008730140181180401c0600c050047a801024018030080500487801c850187000c020140180200701803008050048780101001c03008e90140180101001cac00c0201401801c060ac03008050049381bc0401c06008050049a80000401c03008050041a7
  | 8, 1, 15 => 0xe00401c0600c02014018000070180300805004937010850180300a07014018010070180300805004798012042140600c020140180100600c02014011e47a80100708c0600c020140181180401ca701803014018010070180300a370140186a80401c0600c02014018000040900600c020140178d80401c0600c020140182340401c0600c024e40181f80401c0600c02014f68010071440600c020140181f81f0100701803008058
  | 8, 2, 0 => 0x10070185a00c020140180100729c0600c05004ae80001001c7000c020140171bc0c01007018020140184480401c0600c020140188e40401c0600c020140181180401c061c40301401801007018030098a01401801007018b100c023380180100709c0300805004798118041b807018030140181180401c0600c050046c81f80401c068e0030080581000401c0600c020140180100401c0600c020140181bc0401c0600805005f48
  | 8, 2, 1 => 0x401c0a00c020140170000402c0600c020140175d04601007018030140181180401c0600c0500480801085018038540201401801c061c02b00c02014018010078f00600c020140181bc0401c062c4020140180123b01c0600c0201401801007018031a00500487801085018030940201401801c061c00300805004c980100701803008730147b81bc0458007018020140180100701803008050063a80100701803008056a0018
  | 8, 2, 2 => 0x11ad01c0600c02014018010070180300805005bc801c0675c7000c020140181180401c510180301401801c061c003008050048782340401c0600c0200479801085018030080587c01801c065e87000c020140184980401c0600c020140182340401c0600c020140180108501803008052500188fc8d0100701803008018334042140600c020140180100701a3e00c020140181f89501007018030080581bc0401e3d01802014018
  | 8, 2, 3 => 0x9d3b80600c020140170200c01c0600c02014018118040400700c0201401801007018035e402014018010071640300805004a88010070180300a430140181f80401c0600ca6008058010bb01c061c4030140180100701803008050064281f80401d52018030080589040401c0600c020140180000c01c0600c020149a72ec070187000c02014018010070180300805900018110070180300805004808000070187000c02014017
  | 8, 2, 4 => 0x1c061c003008830140180100701a4900c020140189200401c0600c02014018010072140600c020140180012001c0600c020140177987e0100701803008058010ec01c0600c020140180100701803008050064780006f01085018020140170100702803008050049a8010100400700c020140181180401cac01803014018010072700600c020140189180401c0600c020140180100701803008059140180100701a4400c02014018
  | 8, 2, 5 => 0x10070182b00c02014018000042ec0600c830140170000401c0616802014017010070180300a4d01401801c061c00300805005f48010070180300878014018020070187000c020140180000401c062c4023380174800701803008830140180000401c0600c16014017010070180300805080018010079300600c020140181bc0401c06008050064b80100701803008050064a81bc0401c0600805410018010850180300939014018
  | 8, 2, 6 => 0x100701803008050047789380401c0600c02014018
  | 9, 0, 0 => 0x100701803094020140182740401c0600c02014018010070180300805004a880200401c0600c020140180004601007018030140171bc0401c0600c0201401801007018030080525c0180008d01007018030080170100701803008830140180100701803008050047b8010bb01c0600c020140180000401c0600c02014017010070180329802014018010073280600c02014018010070180300805004878010070180300805338018
  | 9, 0, 1 => 0x10072140600c02014018000070187000c020140172340401c0600c02014018010070180300805004798010071440600c020140180100701803008730140180100701803008050046c80100701803009390140180100729c0600c020140180100701803008050047a80006f0100701802014017010070187000c020140180100701803008052500183340401c0600c02014018010d501c0600c02014018010070180300805400018
  | 9, 0, 2 => 0x10070182b00c02014018
  | 10, 0, 0 => 0x401c0600c02014017
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 54
  | 6 => 64
  | 7 => 74
  | 8 => 84
  | 9 => 84
  | 10 => 74
  | _ => 0

def idWidth : Nat := 10

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 172 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x1ffffffffffc00000000007ffffffffff, 43)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 86)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 86 false (goal 86) u ys) :
    NatRunT 86 false (goal 86) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 11 0 (NN s)

def poolG : List Nat := [63073502922672260, 23658256215923801, 9021515628670038, 67568342964202588, 9068790301156443, 63064697160690820, 63069100536065159, 19154600757123159, 23662644646992002, 57435253463150683, 31534016150747222, 63064743290690649, 67572708793211990, 19154614731496534, 19154652338676828, 80004886747503702, 23658200384493655, 67577092838086743, 19154614790216790]

def Z (s : Nat) := bar 86 false S NN idx ori poolG s

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
private theorem z6_48 : ∀ i, 48 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_56 : ∀ i, 56 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_72 : ∀ i, 72 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 88 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_88 : ∀ i, 88 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 104 → Z 6 i = true := (range_split (range_split (range_split z6_0 (range_split z6_8 z6_16)) (range_split z6_24 (range_split z6_32 z6_40))) (range_split (range_split z6_48 (range_split z6_56 z6_64)) (range_split (range_split z6_72 z6_80) (range_split z6_88 z6_96))))

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
private theorem z7_400 : ∀ i, 400 ≤ i → i < 408 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_408 : ∀ i, 408 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_416 : ∀ i, 416 ≤ i → i < 424 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_424 : ∀ i, 424 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : ∀ i, 432 ≤ i → i < 440 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_440 : ∀ i, 440 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 456 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_456 : ∀ i, 456 ≤ i → i < 464 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_464 : ∀ i, 464 ≤ i → i < 472 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_472 : ∀ i, 472 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : ∀ i, 480 ≤ i → i < 488 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_488 : ∀ i, 488 ≤ i → i < 496 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_496 : ∀ i, 496 ≤ i → i < 504 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_504 : ∀ i, 504 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 520 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_520 : ∀ i, 520 ≤ i → i < 528 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_528 : ∀ i, 528 ≤ i → i < 536 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_536 : ∀ i, 536 ≤ i → i < 544 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_544 : ∀ i, 544 ≤ i → i < 552 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_552 : ∀ i, 552 ≤ i → i < 560 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_560 : ∀ i, 560 ≤ i → i < 568 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_568 : ∀ i, 568 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 584 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_584 : ∀ i, 584 ≤ i → i < 592 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_592 : ∀ i, 592 ≤ i → i < 600 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_600 : ∀ i, 600 ≤ i → i < 608 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_608 : ∀ i, 608 ≤ i → i < 616 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_616 : ∀ i, 616 ≤ i → i < 624 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_624 : ∀ i, 624 ≤ i → i < 632 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_632 : ∀ i, 632 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 648 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_648 : ∀ i, 648 ≤ i → i < 656 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_656 : ∀ i, 656 ≤ i → i < 664 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_664 : ∀ i, 664 ≤ i → i < 672 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_672 : ∀ i, 672 ≤ i → i < 680 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_680 : ∀ i, 680 ≤ i → i < 688 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_688 : ∀ i, 688 ≤ i → i < 696 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_696 : ∀ i, 696 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_704 : ∀ i, 704 ≤ i → i < 712 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_712 : ∀ i, 712 ≤ i → i < 720 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_720 : ∀ i, 720 ≤ i → i < 728 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_728 : ∀ i, 728 ≤ i → i < 736 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_736 : ∀ i, 736 ≤ i → i < 737 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 736 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 737 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 (range_split z7_24 z7_32))) (range_split (range_split z7_40 (range_split z7_48 z7_56)) (range_split z7_64 (range_split z7_72 z7_80)))) (range_split (range_split (range_split z7_88 (range_split z7_96 z7_104)) (range_split z7_112 (range_split z7_120 z7_128))) (range_split (range_split z7_136 (range_split z7_144 z7_152)) (range_split z7_160 (range_split z7_168 z7_176))))) (range_split (range_split (range_split (range_split z7_184 z7_192) (range_split z7_200 (range_split z7_208 z7_216))) (range_split (range_split z7_224 (range_split z7_232 z7_240)) (range_split z7_248 (range_split z7_256 z7_264)))) (range_split (range_split (range_split z7_272 (range_split z7_280 z7_288)) (range_split z7_296 (range_split z7_304 z7_312))) (range_split (range_split z7_320 (range_split z7_328 z7_336)) (range_split z7_344 (range_split z7_352 z7_360)))))) (range_split (range_split (range_split (range_split (range_split z7_368 z7_376) (range_split z7_384 (range_split z7_392 z7_400))) (range_split (range_split z7_408 (range_split z7_416 z7_424)) (range_split z7_432 (range_split z7_440 z7_448)))) (range_split (range_split (range_split z7_456 (range_split z7_464 z7_472)) (range_split z7_480 (range_split z7_488 z7_496))) (range_split (range_split z7_504 (range_split z7_512 z7_520)) (range_split z7_528 (range_split z7_536 z7_544))))) (range_split (range_split (range_split (range_split z7_552 (range_split z7_560 z7_568)) (range_split z7_576 (range_split z7_584 z7_592))) (range_split (range_split z7_600 (range_split z7_608 z7_616)) (range_split z7_624 (range_split z7_632 z7_640)))) (range_split (range_split (range_split z7_648 (range_split z7_656 z7_664)) (range_split z7_672 (range_split z7_680 z7_688))) (range_split (range_split z7_696 (range_split z7_704 z7_712)) (range_split z7_720 (range_split z7_728 z7_736)))))))

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
private theorem z8_376 : ∀ i, 376 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_384 : ∀ i, 384 ≤ i → i < 392 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_392 : ∀ i, 392 ≤ i → i < 400 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_400 : ∀ i, 400 ≤ i → i < 408 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_408 : ∀ i, 408 ≤ i → i < 416 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_416 : ∀ i, 416 ≤ i → i < 424 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_424 : ∀ i, 424 ≤ i → i < 432 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_432 : ∀ i, 432 ≤ i → i < 440 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_440 : ∀ i, 440 ≤ i → i < 448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_448 : ∀ i, 448 ≤ i → i < 456 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_456 : ∀ i, 456 ≤ i → i < 464 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_464 : ∀ i, 464 ≤ i → i < 472 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_472 : ∀ i, 472 ≤ i → i < 480 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_480 : ∀ i, 480 ≤ i → i < 488 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_488 : ∀ i, 488 ≤ i → i < 496 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_496 : ∀ i, 496 ≤ i → i < 504 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_504 : ∀ i, 504 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_512 : ∀ i, 512 ≤ i → i < 520 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_520 : ∀ i, 520 ≤ i → i < 528 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_528 : ∀ i, 528 ≤ i → i < 536 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_536 : ∀ i, 536 ≤ i → i < 544 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_544 : ∀ i, 544 ≤ i → i < 552 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_552 : ∀ i, 552 ≤ i → i < 560 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_560 : ∀ i, 560 ≤ i → i < 568 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_568 : ∀ i, 568 ≤ i → i < 576 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_576 : ∀ i, 576 ≤ i → i < 584 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_584 : ∀ i, 584 ≤ i → i < 592 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_592 : ∀ i, 592 ≤ i → i < 600 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_600 : ∀ i, 600 ≤ i → i < 608 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_608 : ∀ i, 608 ≤ i → i < 610 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 608 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 610 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 z8_24)) (range_split (range_split z8_32 z8_40) (range_split z8_48 (range_split z8_56 z8_64)))) (range_split (range_split (range_split z8_72 z8_80) (range_split z8_88 (range_split z8_96 z8_104))) (range_split (range_split z8_112 z8_120) (range_split z8_128 (range_split z8_136 z8_144))))) (range_split (range_split (range_split (range_split z8_152 z8_160) (range_split z8_168 z8_176)) (range_split (range_split z8_184 z8_192) (range_split z8_200 (range_split z8_208 z8_216)))) (range_split (range_split (range_split z8_224 z8_232) (range_split z8_240 (range_split z8_248 z8_256))) (range_split (range_split z8_264 z8_272) (range_split z8_280 (range_split z8_288 z8_296)))))) (range_split (range_split (range_split (range_split (range_split z8_304 z8_312) (range_split z8_320 z8_328)) (range_split (range_split z8_336 z8_344) (range_split z8_352 (range_split z8_360 z8_368)))) (range_split (range_split (range_split z8_376 z8_384) (range_split z8_392 (range_split z8_400 z8_408))) (range_split (range_split z8_416 z8_424) (range_split z8_432 (range_split z8_440 z8_448))))) (range_split (range_split (range_split (range_split z8_456 z8_464) (range_split z8_472 (range_split z8_480 z8_488))) (range_split (range_split z8_496 z8_504) (range_split z8_512 (range_split z8_520 z8_528)))) (range_split (range_split (range_split z8_536 z8_544) (range_split z8_552 (range_split z8_560 z8_568))) (range_split (range_split z8_576 z8_584) (range_split z8_592 (range_split z8_600 z8_608)))))))

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
private theorem z9_32 : ∀ i, 32 ≤ i → i < 33 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 32 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 33 → Z 9 i = true := (range_split (range_split z9_0 z9_8) (range_split z9_16 (range_split z9_24 z9_32)))

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
  scr 86 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRunT 86 false (goal 86) s xsG) : False := by
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
abbrev fG : BFn 7 := fun y : Fin 7 → Bool => PEqualNP.Outside.L_meta_8535_aux.Main.fG (substIn PEqualNP.Outside.L_meta_8535_aux.Main.cSub_1 y)

def cSub_0 : Fin 7 → Sum Bool (Fin 6) := (fun i : Fin 7 => match i with
  | ⟨0, _⟩ => Sum.inr ⟨0, by omega⟩
  | ⟨1, _⟩ => Sum.inr ⟨1, by omega⟩
  | ⟨2, _⟩ => Sum.inr ⟨2, by omega⟩
  | ⟨3, _⟩ => Sum.inl false
  | ⟨4, _⟩ => Sum.inr ⟨3, by omega⟩
  | ⟨5, _⟩ => Sum.inr ⟨4, by omega⟩
  | ⟨6, _⟩ => Sum.inr ⟨5, by omega⟩)

namespace Sub_0
abbrev fG : BFn 6 := fun y : Fin 6 → Bool => PEqualNP.Outside.L_meta_8535_aux.Main.Sub_1.fG (substIn PEqualNP.Outside.L_meta_8535_aux.Main.Sub_1.cSub_0 y)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 8) (_ : SCleanL 6 gs)
    (_ : ∀ p, p < gs.length → 6 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 6 + p ∈ g.inputs)
    (_ : ∀ x, val gs 6 o x = fG x) :
    ∀ a, a < 6 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [8, 16, 16, 9, 10, 12, 17, 17, 17, 17, 18, 18, 18, 18, 20, 20, 20, 20, 8, 32, 32, 9, 10, 12, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 1, 1, 2, 2, 4, 4, 9, 9, 10, 10, 12, 12, 24, 24, 48, 25, 26, 28, 19, 21, 25, 49, 19, 22, 26, 50, 21, 22, 28, 52, 40, 40, 48, 41, 42, 44, 35, 37, 41, 49, 35, 38, 42, 50, 37, 38, 44, 52, 3, 5, 3, 6, 5, 6, 11, 13, 11, 14, 13, 14]

def xsG : List ℕ := [0x5d711f2047c80c300f2003c8, 0xb6d2f140bc5030c0f0403c10, 0xebaf2283c8a0c30f0083c020, 0xfc0444ed113bfc0000e40039, 0x88813ffff00000003ffc6, 0xffffe2204000fff180000]

theorem rowsG_len : rowsG.length = 96 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => ((fun x : Fin 6 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 48 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 48 false (fG, false) = goal 48 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 48 zs &&& lo 48) ≠ lo 48 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 8, ¬ NatRunT 48 false (goal 48) s xsG) :
    ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 48 false (goal 48) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 8, ¬ NatRunT 48 false (goal 48) s xsG) :
    ¬ HasCircuitSize 6 fG 8 := by
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
  | 4 => 1
  | 5 => 4
  | 6 => 22
  | 7 => 16
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 4, 0 => 0x68a83186
  | 5, 0 => 0x931f2e0b60ecc16d2532bf5318885a05
  | 6, 0 => 0x8f587d5e8b193b96857991b875f5e2ab715fecc270cbed786cf2119a61c0ecfd5d2af7145a4b361b449b68a23ef1d6aa35557ec933972adc2db38804294da4aa16ac521d0feb09f70ebd8fc10965f038087db41908246ca9
  | 7, 0 => 0x8f587d5e75f5e2ab712a5dd061c0ecfd5d2af71453e49f6042947e4c3ffacea83636078024e985bb203ab4251c06d85c13cd06ad110d1f020864646d072328c8
  | 8, 0 => 0x61c0ecfd
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xb6d2f140bc5030c0f0403c105d711f2047c80c300f2003c800088813333f000000000000000444ec0000000000000000fc0444ed113bfc0000e40039000ffffe2204000fff18000000088813ffff00000003ffc6fff33300ccc0000000000000
  | 0, 1 => 0xfffff333f000fff180000b6d231008c40000000000000492102004080000000000000fc0fffff333ffc0ffffc0039000cccffffff00000003ffc6fffff3c3fcf0f3cff0c3fc30fff33f20cfc80c300f2003c8ebaf2283c8a0c30f0083c020
  | 0, 2 => 0xebaf66efc8a0c30f0083c020fff00001ddfbfff000e7ffffa28ee0dfb837f3cff0dffc37492d0ebf43afcf3f0fbfc3efebafffffeaa4c30fff9bc020000f22820000000f00000000fff777ec0000fffffffc00391450dd7c375f3cf0ff7c3fdf
  | 0, 3 => 0x3fbbb12eec403ffff1bffc65d799f33ffff0c300f23ffce0000080047c80000000003c0fc0cccff333ffc0000e40039ffff3fa3cfe8cf3f0fa3c3e8000fffffffff000fff1bffc6000888122204000000000000000cccfe2204000000000000
  | 0, 4 => 0xa28220008800000000000000ffaf66efd9bbff0f00e7c039e80400810020c000008000200002f14020000000f00000005d799f3267cc0c300f2003c8492ffffe6284000fff1800005d71130044c000000000000014589913ffff00000003ffc6
  | 0, 5 => 0xebafaa93ffffc30f0083ffe6fc0cccfffffffc0000e7fffffd755fed57fbfc300fe403f9
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xc20404
  | 5, 0, 0 => 0xc204e354c20718b50ca24205481c61445
  | 6, 0, 0 => 0xc81c60a060c81c6081620719f081644350818260c81de09d67081c608160db1c204d60c81c669960c81c605860d540708160d71c608165835481c160d440608160d31c6481644340718260c81c63c16
  | 6, 0, 1 => 0xd01c608160c81e308160c81c6881658320718165881c67c160c81c20616
  | 7, 0, 0 => 0x3407182058058320718160ea20718205c00c81c608160081c67c205a90c81c60817a0320718205c36c81c608170c81c608111c3207182067798320718205d10c81c608170c894718205c320718290170d420718205c32101c60817
  | 8, 0, 0 => 0xc81c60816
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 4 => 28
  | 5 => 34
  | 6 => 40
  | 7 => 46
  | 8 => 40
  | _ => 0

def idWidth : Nat := 6

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 96 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3ffff00000003ffff, 18)], [(0x41001400050041001400050, 1), (0x30c00000000030c000000000, 2), (0xf0003c000000f0003c00, 4)], [(0x410100204008410100204008, 1), (0xc30000000000c3000000000, 2), (0xf0003c000000f0003c0, 4)], [(0x41000000000041000000000, 1), (0x30c00000000030c000000000, 2), (0x3c00000000003c000, 14), (0xa00000000000a0, 17), (0x30f00000000030f, 18), (0x50000000000050, 19), (0x3c00000000003c00, 22)], [(0x410000000000410000000000, 1), (0xc30000000000c3000000000, 2), (0x3c00000000003c00, 14), (0x8010000000008010, 17), (0x30027000000030027, 18), (0x4008000000004008, 19), (0x3c00000000003c0, 22)], [(0x200008000000200008, 2), (0xc30000000000c3000000000, 4), (0xf0003c000000f0003c0, 8), (0x208000400010208000400010, 1), (0x104020000800104020000800, 3), (0xc00030000000c0003000, 4), (0x10000400000010000400, 5)], [(0x104010000400104010000400, 1), (0x200008000000200008, 2), (0x82000000000082000000000, 3), (0x41000000000041000000000, 5), (0x2000080000002000080, 7), (0xc00030000000c000300, 8), (0x1000040000001000040, 9)], [(0x82000200008082000200008, 1), (0x41002000080041002000080, 3), (0xc00030000000c000300, 4), (0x1000040000001000040, 5), (0x208000400010208000400010, 1), (0x104020000800104020000800, 3), (0xc00030000000c0003000, 4), (0x10000400000010000400, 5)], [(0xc30000000000c3000000000, 4), (0x3c00000000003c000, 10), (0x20000000000020, 16), (0x3c17000000003c17, 18), (0x8000000000008, 20), (0x3c00000000003c0, 26), (0x208000400010208000400010, 1), (0x104020000800104020000800, 3), (0xc00030000000c0003000, 4), (0x10000400000010000400, 5)], [(0x444080001000444080001, 1), (0x8000000000008, 5), (0x20000000000020000, 6), (0x10000000000010, 8), (0x2000000000002000, 9), (0x20000000000020, 11), (0x200000000000200, 12), (0x4000000000004, 16), (0xc00000000000c000, 32), (0xc00000000000c00, 34), (0xc00000000000c0, 36)], [(0x51102000000051102, 1), (0x200000000000200000, 5), (0x400000000000400000, 8), (0x800000000000800000, 11), (0x300000000000300000000, 14), (0x30000000000030000000, 16), (0x3000000000003000000, 18), (0x1000000000001, 20), (0x8000000000008, 24), (0x10000000000010, 27), (0x20000000000020, 30)], [(0x300800c10000300800c10, 2), (0x30000000000030000, 12), (0x80000000000080, 15), (0xc00000000000c000, 16), (0x40020000000040020, 19), (0xc00000000000c000000, 20), (0x180000000000180000, 21), (0x200000000000200000, 22), (0x301000000000301, 36), (0x6000000000006, 37), (0x8000000000008, 39)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 48)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 0 zs symsG zs (hk 0 zs)

theorem ori_ok {u ys} (h : NatRunT 48 false (goal 48) u ys) :
    NatRunT 48 false (goal 48) u (ori ys) :=
  pickMin_runT 0 ys h symsG ys (hk 0 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 0 zs) 6 0 (NN s)

def poolG : List Nat := [4506903622276180, 27024902794035266, 6758728109967408]

def Z (s : Nat) := bar 48 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 22 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 22 → Z 6 i = true := (range_split z6_0 (range_split z6_8 z6_16))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := (range_split z7_0 z7_8)

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
  scr 48 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : NatRunT 48 false (goal 48) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := runT_len h
    change 6 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 6 fG 8 := mainG noRunFull

end Sub_0

def taggedFn (a : ℕ) : Bool := (a == 3)

def perm_3 : Fin 7 → Fin 7
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩

def cu_3 : Fin 7 → Sum Bool (Fin 6) := fun i => cSub_0 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 6 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 6 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

theorem hno_projG : ∀ i : Fin 7, ∃ y : Fin 7 → Bool, fG y ≠ y i := by decide +kernel

theorem htag_fn (gs : List Gate) (o : ℕ) (hlen : gs.length ≤ 10) (hcl : SCleanL 7 gs)
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
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta

def rowsG : List ℕ := [16, 16, 32, 18, 18, 18, 34, 18, 18, 33, 36, 25, 25, 28, 28, 25, 25, 28, 28, 24, 24, 24, 17, 17, 20, 20, 17, 17, 20, 20, 64, 64, 32, 66, 66, 66, 34, 66, 66, 33, 36, 73, 73, 76, 76, 73, 73, 76, 76, 72, 72, 72, 65, 65, 68, 68, 65, 65, 68, 68, 2, 32, 8, 8, 1, 4, 1, 4, 2, 2, 34, 33, 36, 33, 36, 33, 36, 34, 34, 9, 12, 9, 12, 9, 12, 48, 80, 48, 26, 50, 82, 50, 19, 22, 49, 52, 27, 57, 30, 60, 29, 89, 29, 92, 56, 88, 26, 19, 49, 22, 52, 21, 81, 21, 84, 96, 80, 96, 74, 98, 82, 98, 67, 70, 97, 100, 75, 105, 78, 108, 77, 89, 77, 92, 104, 88, 74, 67, 97, 70, 100, 69, 81, 69, 84, 10, 40, 10, 40, 3, 6, 5, 5, 3, 6, 42, 41, 44, 35, 38, 37, 37, 35, 38, 11, 14, 13, 13, 41, 44]

def xsG : List ℕ := [0x1d753a0e61cd4039873500a8a85033066800cc19a00, 0x3cce6a0b014fc02c053f0060701000007e000001f8, 0x2eba5c1b8372806e0dca015150a0cc1990033066400, 0x7f0381e01ffc04007ff011f8000c00ffe00003ff800, 0x140a80117ffffffe00000000000003ffff9bb, 0x30ff8141442b2a8510acaa07fc02000019100000644, 0x1fffffffd02a0044000000ffffe6ec0000000]

theorem rowsG_len : rowsG.length = 170 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => ((fun x : Fin 7 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 85 true) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 85 true (fG, false) = goal 85 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 85 zs &&& lo 85) ≠ lo 85 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 85 true (goal 85) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 85 true (goal 85) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRunT 85 true (goal 85) s xsG) :
    ¬ HasCircuitSize 7 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged true fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 85 true (encT rowsG 85 true (fG, false)) s'
      (ws.map (encT rowsG 85 true)) :=
    RunT.map (encT rowsG 85 true)
      (fun a => encT_inv rowsG 85 rowsG_len true a)
      (fun a b => encT_and rowsG 85 rowsG_len true a b)
      (fun a b => encT_or rowsG 85 rowsG_len true a b)
      (fun a => encT_tag rowsG 85 rowsG_len true a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 2
  | 6 => 44
  | 7 => 199
  | 8 => 185
  | 9 => 15
  | 10 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0x4e100b3a034d98ab
  | 6, 0 => 0xf73c0c5fd6a7b3a09aeb42d091dfd5aa8c93064b8b6d161889cd8f58811579377dd6d20b7db04d9178be977e7345a5096ee294bc6eca44e96974a8b9685467df5fad4fa65c3f227d5c371eb859621e8443f6f816417ea0fa40a08fe83825ecb929cc941329ae1448253b6075216b0e2e1f86a1d71dd3d2b01a8a800518e2b6bd12450b680ebc368e0b99d5f30ad7c6e206490b1d0584106603d8299b0389c88c0318836802685dc001e814590150edd8
  | 7, 0 => 0x12cca79f12aa9871124a4bf8118d912f112cbb5210e801a31024bfce0fd4647d0f7814b60e6065920df824860df1a0da0dc0356e0d7fdb960d77cec40d35ba9f0d1915f20d0e3c350c7c603f0c6b28c30bec11a90bce57710abda0c90aa187bc09c67ba509c506c809b9d08509b7b7c509b1d5e709a429ff098d04350882e0c008649f41083bdfab07f84bf907cdceb00773d682075f179d0738932305cd04a3052db304051d4a430505cd6704e54d6c04a0de2d043dc390040b79280385faa80370dccb03675c92034a585102ee4a7a0295212e02375b4702337bcb01de344001b69d9901b4cf92014842360130c265010ed03d0104b20400f59d7200e84bc3
  | 7, 1 => 0x395cdbfb3786933936b9c54c3584547634cb2bfe34900dee339f57f1312beca83020b8632f24bdfc2eabe5e42de1fe022dd5847a2d9593572d68c7072d6431402c7515ed2c4062132c18d12a2a6110112a02caa1295d9bfc2937178228442abf28093af1271bc5cb26fce5f326e65b92266714bb250814572228035521acfe87215fcc3020f43054208136091ee53a971ebeb61d1da77d1c1d9b7e441d698f0b1d56713d1c9506501c8c57121bf849071bbdf42c1b017a2a1a5b236b1a349ef119e1efbc19bb6b4219702be7191402fd185a9d111767baca1728176816b0ce5d16a2b4bf169dd00b16533c5e1479e7ef13b8954a13b7cfad13b6590112df5bdd
  | 7, 2 => 0xb12299f8a9490181a84b8aeda73351939a5f10ab99e0775799b9f2dd98c55fad98198b0b916f1eae8c0e1d5587a995e98711004084b454aa7dd6d20b72f8737f6dc134156d1386356b6c1d7b6b2c99846a24dfd069b1fc316859d9b6685467df68325a8365db153b648d5fe962863f1861d737876108187f60615c0a5dc40e7d5d97422d5d812b565c6edd395c4858bf5c4120a35bb751f65a8060045a352a1a5a2bbf5858c906ea52d7a97e52567e7b522ffa014e1ce8e84de8f4854d84ec634d5e67e94cbad238486cb1d6468d766a4431ed5d42e0efef41dcea503f0ce7f33ed7babd3eabf75b3d7523f53d2bb2b13ccccd8d3c9fed043b8e486539b786eb
  | 7, 3 => 0xcc9fd483c6ea26b7c02190dfc00792b0bfaceca8be06362ebc6417ae
  | 8, 0 => 0x1d970edd1c83a86c1aba4f481a5b236b1a4f84c519e1efbc199a1e93197f32f519568e4918263e3e18230a04180b102517f9098c17d285121774895415df6fca15b8ec76155a786615444a73145a96ad1368bd54130111aa12febe7512da8d3012d5e3da1269496611dbdeba11895b7110e0c68b0e5c7c3c0dd8b86b0db147920d48f7950ce36eb60ca9a6de0c9abb650c8fa8540c3541010befda470be8a76d0a31ff860949ce6a092d3d990877db01082f1190076fe3f8075f179d073fab82072e24dd06cb3dff05e6bd6105da120e05a6ad8004db2f320370dccb02ba9c1002b81f7801ddd61c01b3d5f1015191b201123a48010ed03d009517f4006e937a
  | 8, 1 => 0x5439e74c540773f452567e7b522ffa01502796914ee161a64e71ef024dfafe904d84ec634d0189904c399d744b3002b04a9761e149adae1b499c6fca4864cd8248569f89441f7aab43045f004125a8a93ffbc4183f0ce7f33e5e97433c1e556d3bf7d0f33b504c263a6a117d39b2bceb392418953786933936c236af362bafde34de39d234adbf0433f2e28f339f57f13291aca131e25117318616b4305294753020b8632f86daab2e6bb1632e452ce92e1ea86f2d09006b2cf7ed922c7515ed2abee02a2a62127629c81717295d9bfc256455ce24c4c81c2467e383238feafe22722638222803551f74210d1f5150281ee53a971ec5695d1e8753651dd6d968
  | 8, 2 => 0xf439ccace96c7f9be02afa48c4097772bf890544bc6417aeba32f15bb84ae44bb419682dac8ad9fcab32a480aa609a11a84b8aeda2eb9f9ea2c51b249b057a8599e077579829b8a3963dbff495a9d6c9956241a38d41ef638a04763587a995e98574ff408435ef1a82f7ccdd82145f817e9a05877cf955387bcf3ce17b0fe9a3750d30c572bd2478715423cf6edebd1b6d9d55846d9888306d0024846c154e1d6b7ec74c6b5842d2681d2e1d673f05fe6543cd846440a65363dd6e1962d6a135613d0b575f47fad55dc40e7d5dba7ece5d97422d5c6edd39579404e75538e1de547240cb
  | 9, 0 => 0xa2eb9f9e9829b8a387a995e96c154e1d6b7ec74c52567e7b49adae1b43045f003c1e556d339f57f131e251172e452ce917f9098c130111aa009517f4
  | 10, 0 => 0x87a995e9
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x3fffffffa0540088000001ffffcdd80000000000000502a0045fffffff80000000000000ffffe6edf81c0f0afff9742bffe5dfc0006007ff00001ffc003f0381f55fff3fd57ffcfff8000c00ffe00003ff8005d74b83706e500dc1b9402a2a1419833200660cc80075d4e839873500e61cd402a2a140cc19a003306680187fc0aaa7559dea9d567703fe0100000c88000032203cce6a0b014fc02c053f0060701000007e000001f8
  | 0, 1 => 0x3aea743edfdef7f35e6a895150a0660cd00198334000f339ad7faffff4ba94fd0181c0400001f8000007e187fc0af5dea6aaa9d567703fe017ffffffe000032233cf6615e2bfc0578aff01f9f8f0ff1ff803fc7fe00fe0703c03ff80800ffe023f0001801ffc00007ff000fddeefa8fff110a3ffc447e0003003ff80000ffe00187fc0a0a215954288565503fe0100000c8800003220ffcfeaab154fc2ac553f0060701000007e000001f8
  | 0, 2 => 0x3aea743cd79aa2f35e6a895150a0660cd00198334000f339ad2ea53f54ba94fd0181c0400001f8000007e0000000fffffffffffffff0000007ffff377ffffcddbfffffebf57fee80000001fffffffffffffc00006445ffcfc3746ed80dd1bb602a2a1419833200660cc8007ff7fabbc777f0ef1ddfc2babd44cc19bf833066fe07fe3f0550aa601542a9800000000000000000000001d753a119e32bfe9ad3544a8a850ccf98eeccc19a00
  | 0, 3 => 0x5b15769e4bccd5792f33555ea8a4660ce2219833888000207807000fe01c003f8181c3c03801ff00e007fc7803f500000001562a988fc01fe80000001ffffcdd800000154eab3bfffffffe00000000000003ffff9bb200303c8b9127f22e449fd5d5ebe67ccdff99f337febae9706e0dca01bc77baad4542833066400cc19900187fc0aaa7559dffffffff03fe0100000c89fffffff83cce6a0b014fc07d0fffa060701000007e000001f8
  | 0, 4 => 0x7f9fcfc17ff98805ffe623f0001801ffc00007ff00030c06028050000a01400000000000000000000000007803f5558aa6202885655fc01fefffff37600000003fff7e1fe3ffc07f8fff01f9f8f0ff1ff803fc7fe007e6733d43ff80850ffe023f0001801ffc00007ff000f3fe652d15acaab456b2a81ff008000064400001910eba9d0730e6a01ecbded554542819833400660cd003f0381f55fff3fd07ff055f8000c00ffe00003ff800
  | 0, 5 => 0x799cd43e87ffd0580a7e00c0e0200000fc000003f0fd1e8f80fff11003ffc447e0003003ff80000ffe001f81c0f0afff97403ff808fc0006007ff00001ffc003c33195f4feb03fd3fac0ff9f8fefffff81fffffe070000003fffffffaa7559dc000001ffffcdd800000003c01fafaef5355ebbd4d57e00ff7ffff9bbffffe6ed75d2e0de3bdd57706e500a8a850660cc801983320030ff815fffffffd53aacee07fc02fffffffc0000644
  | 0, 6 => 0x3aea743cd79aa2fb7f7bdd5150a0660cd0019833400cccd9f87d0ff5a1f43fd6807ec0c00007bc00001ef06180c0ffffffffc1780220000007ffff37600000000c30181e0bc0117ffffffe00000000000003ffff9bb228b47f706e50083b06b755d5ebf983312219f337fe49d512c36866550da1995542aeb733e63bbccf98eed75d2e0fc5f948bf17e522a8a850660cc8019833200300301554eab03d53aac0ff9f8fefffff81fffffe07
  | 0, 7 => 0x7fffffe8150022a054008bfffffe000032200000c880f3198028053000a014c00000000000000000000000000000a054008aa9d56770000000000000000000002ffefebbb376fc6ecddbf15757a1cc1997e330665f865ff8a838877550e21dd540ff804000032200000c88ffffff80000000bf57feeffffffc0000644fffffffcffebf0770eee01dc3bb8054542819833400660cd002eba5c1f8bf2917f3feeef5150a0cc1990033066400
  | 0, 8 => 0x799cd7fffffffa5d4a7e80c0e03ffffcfd800003f000000002c053f00000010000000000001b800000000144220fffffffe91521220000007ffff3760000000328bc5f5debbbfd77aeefffffffffffffffffffffff5d74b83ffffffffc5f948aa2a141ffffedde60cc8000000007e2fca4540a80110000003306600000000000044000fffffffe81500220000007ffff37600000000ccc981e0bc029782f00a5fe04fcffffe10fffff843
  | 0, 9 => 0x798cc295529a2fffffffc00000000000007ffff376fcce67ee7ffa11a1ffc047e0003333ff80000ffe000018000a054008bfffffff00000000000001ffffcdd8144221fffffffd0aa1144000000ffffe6ec00000007dffbab78ef755de3bdd56aff9459833322660ccc88b2e8602c058800b0162000054000000040000001001f81c0f20ffe021efffeddfc0006007ff00067ffc00228ac5f19e32bfc678caff5757afccf997ff33e65ff
  | 0, 10 => 0x228b47c8f91aff23e46bfd5d5ebe67ccdff99f337fef5deef80000000b756f6effffffc0000644fffffffc6ba1d0f15e228bfffffff00000000000001ffffcdd9f45fffeffddfffbff77fffeafffffffefffffffbff417400020044000a21595402a000000020000000800ffffff80801100bf57feeffffffc0000644fffffffc0000000a21595400000000000000000000000000003f0381f01ffc046e7ffa11f8000c00ffe00333ff800
  | 0, 11 => 0x61ff02a28c56558a3159540ff804000032200000c8835d0e828851100a2144400000000000000000000001f81c0ffafff83e83ff80afc00067ffff00601ffc003c33194b456b02ad15ac0bf9f8fefffff81fffffe071e88fd7d77a9aaf5dea6abf007fbffffcddfffff37603f1f87f800fefea000d101fffcffc007ffff001ffc6ba1d0730e6a01c4388800000001983300000000000eb85c0a8150802a054200000000000000000000000
  | 0, 12 => 0x29152122fffffffc00000000000007ffff376ffffffffffffff40a80117fffffffffffff000019100000005fabff7400000000000007ffff37600000002eba5c1f8bf2917fffffff5150a0cc199003ffffdbb00000020040000de3bdd540000000000000660cc00005108850aa1145fffffff80000000000000ffffe6ec8a2d1ffffffffe8fd1aff5757affffff7fe67ccdff800000047c8d7f9022004400000033e666ec0000000
  | 0, 13 => 0x7e0703d43ff80800ffe023f0001801ffc00007ff0000a211002004200080108000000000000000000000018ffd1a0b217b542c85ed503fe0100000c8800003221d753a1e6bcd517ffffffea8a85033066803ffffbbb00000008010000730e6a000000000000000198330000510880080110002004400000000000000000000000eba9d0730e6a01c43888054542819833400660cd003f03bbee3ffc4438fff111f8005c33ffe000cfff800
  | 0, 14 => 0x7e0703c07ff88800ffe023f0001801ffc00007ff000c3fe050510acea1442b3a81ff0080000644000019117dd3f5fddfb6abf77edaafca9fefffffb77ffffedd8e005c1a8350806a0d42015000a0cc1980033066000679fcfebfd7fffaff5ffffffffffffffffffffffffe0000007fffffff40a80390000003ffff9bb000000007803f5ffffffffd77a9aafc01fefffff377ffffcdd8000001ebbd4d5502a0044000000ffffe6ec0000000
  | 0, 15 => 0x20040000dc1b94000000000000000660cc000f5deeffdffbdfff7fef7ffffffffffffffffffffffc1e67350580a7e03606df8030380800003f000000fc2eba5c0b8172802e05ca015150a0cc1990033066400617702828856550a2159540ff804000032200000c88cf3f9f87d0ffba00000007fffffffffffff00001911f81c0f00ffe02003ff808fc0006007ff00001ffc0003cce6a4b094fc12c253f0060701000007e000001f8
  | 1, 0 => 0x3aea743ffffffff35e6a895150a1ffffddd998334000000003987350040080000000000cc1980000000000066330af001fdebc007f703fff9ff800ffffe003ffa28ac5f59eb2bfd67acaff5757afccf997ff33e65ff05108829152122fffffffc00000000000007ffff376fc0e07807ff05001ffc147e0003003ff80000ffe0001e6735a5d4a7ebfffffff030380800003f1ffffcfd8000000000001002c053f00000000000000000001b8
  | 1, 1 => 0x3aea769cdb9a87736e6a1d5150bc67ccd0399f3340e82e800040088001002200005400000004000000100114562f00000000328655dababd78000088999f32ff900101444c89039132240ea8a85e33e6681ccf99a07000000000000000a215954000000000000000000000ffffffafd5ffba1442b2affffffffffffff0000191187fc0a0a215954000000003fe0100000c8800003223f0381ee7ffd44107ff011f8000c33ffe00003ff800
  | 1, 2 => 0x5998801002150040085400c08000000020000000803c01faaac55310ab154c47e00ff7ffff9bbffffe6edffffff00000001562a988ffffff80000c89fffffff8f307ebebbd4d57aef5355f803fdffffe6efffff9bb61ff0297eaffdd000000000ff805fffffff80000c88cbff17c778eeff1de3bbfd5ffebf33e67ffccf99ffd04540a08211154208445503aa0100000888000022200fc7e0fe003fb918005ee07fff3ff001ffccc007ff
  | 1, 3 => 0x786632800000005a2b5817f3f1fc00003027ffffc0e000000502a004540a80110000000000000000000000000000aff5fffe81500220000000000037000000000c00181e0bc001782f0005f800fcffffe00fffff80301990000000050000001400c0800000002000000080000000782f0045fffffff80000000000000ffffe6ec000000aa7559de815002200000000000000000000033ffe7e1f43ffe87d0fffa07ff0300001ff000007fc
  | 1, 4 => 0x1c00b97d37a12af4de84abf007fbffffcddfffff376fc0e07ee7ffa1101ffc047e0003333ff80000ffe0000000000fa1fff40000020000000000003700000000000000144a89117ffffffe00000000000003ffff9bb7e0703c03ff80800ffe163f0001801ffc00007ff000fc0e07d07ff05541ffc157e0003003ff80000ffe001f81c0f00ffe0202bffe5dfc0006007ff00001ffc003f0381ee7ffd4439fff511f8000c33ffe000cfff800
  | 1, 5 => 0x799cd416029d80580a7600c0e0200000fc000003f03f33fafaef53f5ebbd4fd7f81ff7ffff9fbffffe7ec1803350580a6a016029a80001808000037000000dc3f0399fe1ffc05787ff015f800fcffffe00fffff8030799cd43e87ffd0fa1fff40c0e0200000fc000003f0fccdffffffff5ffffffd7fe7effffffffbffffffefdffffff000000000000000ffffff80000c8800003223fffffeffdffff91f235fffffffffffffffccf99fff
  | 1, 6 => 0x786632bffffffffa7f589ff3f1fdfffffdffffffc0e00000039873500e61cd400000000cc19800330660000220000000000000000000000000000000000000003fffffeff5ffeeb9873501fffffffffffffccc19e447ffffff7feffff8cf195fffffffffffffffe67ccffe0332007fffffff40a80390181003ffff9fb0000010010022584d084aa134212aa801d6e67cc37799f30ddbfffffff4feb03ffffffbffffffffffff91ffffffff
  | 1, 7 => 0x20048000000000000000000000004ff79a83c077f00f01dfc01abc0400003f800000fe1ebb9dafb7f7a1fedfde87fcfc7f7ffffc0ffffff03bfff7e1febffd17ffffffff9f8f0ff1ff803fffffbb20ea00008012000200480001500000001000000040041d400398735004408900002a000cc19a0000000801effdda7b2f7b55ecbded557fe2919833c88660cf220f007eaab154c400000001f803fdffffe6ec0000000
  | 1, 8 => 0x297529fafffffffc00000000000dc7ffff3768f3b9fc6f8dbff1be36ffd5d5ebf33e65ffccf997fdffffffffffffffd77a9aafffffffffffffffffffffa0ba0001442b2a840088000150000000100000004005d74b83766edf8dc1b9482a2a14198332dc660cc800bffbfafffffffffbbf6fd55d5e87ffffdfbcc1997e08a291023046a008c11a8054542819833400660cd001f757ebefbddd57bef7755f8abfdffffeeefffffbbb
  | 1, 9 => 0x799cd400000000580a7600c0e020000020000003f00000007d3fac0f40a80010000003ffff803000000007803f5f5dea6abffffffffc01fefffff377ffffcddaebaddfb9f72bfee7dcaff5757afccf997ff33e65ff7ffffebfcfffd5ff3fff57fff9e5fe3ff227f8ffc88000000502a0045e6bcd510000000000000033066000000000f35e6a8bfffffff00000019833001ffffcddb0330141442b028510ac0a01f802000018100000604
  | 1, 10 => 0x5118941202178048085e00c0e0200000fc000003f003320002c053f00000038018100000001f80000010000000000000000000000000000000000000000000000000010020000400800000000000000000000000003862301c839200720e48015150a0660cd00198334000f339a92c253f0ef1ddfc0181c0400001f8330667e08a2d1f03a06b7400000005757af99f337fe00001220000001b83728040080000000000cc1980000000000
  | 1, 11 => 0x7ffffd7fe7fff8ff9fffe3ffffe3fe3fffc7f8ffff00000000510acaa1442b2a8000000000000000000001ffffffffffffffffffffffffffffffffffffffffffbcff995f4feb2bfd3facaffffcfefffff91fffffe477fffffdfebfffd7faffff55ffea6660cffe19833ff875d6efb9f735fee7dcd7fababd7ccf99bff33e66ffd87fc0a00000000288565503fe0100000c88000032230ff0001402b000500ac0001f800000018000000600
  | 1, 12 => 0xa054008a97529fa0000000000000000000dc0030000000000000000000000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x503020100504030201005
  | 6, 0, 0 => 0x24232200070660b1a211900076200302090e0660b031f00070660b091e08070661d0b0302001c60b1b1209070660b1a0219180760b03170916156140b1312090760b120907061160b031009000660b030f090e0660b03020d000660c0b0900070660a03090807066
  | 6, 0, 1 => 0xb030236070660b03020116156240b0900353460b030219002b60b330209000660b033200070660b3102010015630240b09070662d0302282f0662e030908070662d030228001c62c0b0302192b6242a0b08070660b290228001c62709000706266250b030200076
  | 6, 0, 2 => 0x24230908070660b09080706116400b0302070663f0b0302090060b090807063e62d030209003d60b090007061160b3c393b07066240b0908070663a240b09080660b390908070660b38370900076
  | 7, 0, 0 => 0x2c2a0b030207067140b030222000773a2c2a0b03020672e030209004c0670b4b02004a070674903020900070670b48030947460670b03020109001572c0b03020945067440b030900070670b43020900420672c0b031709070672303020900070670b03020900410670b03022809001c73a2303020900067
  | 7, 0, 1 => 0x2a0b020007065870b5702220007067560b030209000670b0302090007557540b4b0200070670b03020918070673a0b03020918067142d030209000770b4b02005307067520b030209000670b2902280006517142a0b4803000771450030209000770b03020900074f74e03020900070670b03020900074d7
  | 7, 0, 2 => 0xb030209004c6270b61020900600672357020900070670b03370900073d70b03120907063e70b03025f00070670b03393b00070672d57020900070670b13090007065e75d03020900070672a0b485700070675c0b030209070675b0b0302000706703025a0900070672a2e030200070670b0309000759067
  | 7, 0, 3 => 0xb57020918070670b02090807066e70b03026d004c0672a0b036c00076b72e03090007062672a0b031207066a70b03690900070672a68030200070670b03022200073470b0302010015067140b030209180770b0302090e070670b0302090007677660b030209006570b030228001c0670b6402090007637
  | 7, 0, 4 => 0xb31020900070673a0b310209000670b7c020900070670b03027b00070677a0b030209000777948030900070670b03020978070677703020900070670b0302760007067750b7402000706773240b0900070670b03020900720672303020900073472a0b03020007627710b030200700676f0302090007067
  | 7, 0, 5 => 0x820302090007067140b032109000772a0b030281078070b64020900077f73a0b640209007f70b03120907065e70b481a0900070670a03020900070672c240b0907062677e0b3c0209070672c79030209070672d03022800065170b0302097d070670b3c023b07066e70b03210900070673a0b03210900067
  | 7, 0, 6 => 0xb03020916070672c0b020907065870b31020100070670b8c020907066e72a0b033900070670b03021900078b73a0b030219008b72e48030900070678a0b030289000770b48090007065870503020900070678803870900860670302850900070670b84030900070672c0b480309070670b0339090007837
  | 7, 0, 7 => 0xa03090007065e70b0302094746067140b030209002b70b92039100070670b57021900078b70302900900070672a0b030200070672a0b03022f070670b030209002b0670b03020900153d70b038f0900070670b4b48008e070672a0b030200071c72c0b485709070672c2e030209070670b8d03090086067
  | 7, 0, 8 => 0x3a240b0900062677903020900070670b39090007062670b3c033909070670b0302090e069972e03026d00070670b03029897070672a0b57020007067960b030200070670b0302011607067950b03020900067940b030200070670b57170900070670b03029309000770b570209002b0670b12090706586a7
  | 7, 0, 9 => 0x2e0302090007067a003020900070670b02090007065873a0b020900065870b09000706263e79f0b030209460670b31020900159e70b03022819001570b030209009d067143a0b4803090079c0b03029b070670b48030900070673a0b480309000670b03020900079a7230302090807067240b09000706267
  | 7, 0, 10 => 0xa90b030209009e70b03020916159e7a80b64020900077a70b030200070672c0b030209073472c0b030201070672aa603020007067000b030219002b62aa2030200070670b03020947a50670b48030100070670b0302090007a47a30302090007067a20302091607067a103021909000770b4857090007067
  | 7, 0, 11 => 0xac03020900070670b02090807065870b0302989b070670b030209ab07067240b090807062670b03020100070673a0b03020100067a1030209002b0672c0b030209159e7aa0b030298070672ca2030209070670b0302090007067a648030900070670b3c390907066e700240b0908070660b4803989b07067
  | 7, 0, 12 => 0x2c0b030222070672423090007062670b03020900353470b030209af070670b09000706586a7ae0b0302ad07067a60302090007067
  | 8, 0, 0 => 0x140b43030209000780b4803190900070680b570209810007068b30b03020900070680b0302090097070680b03020900b207068002c2a0b0302070670b03b102090007068b00b03020900070680b5702090007460682c0b4b030209070680b030209000706638140b0302098100078002303020900070670b4303020900070683a0b4303020900068
  | 8, 0, 1 => 0xbd0b0302090007068bc0b03020900070680b0302090015069e80b03b90200bb070680b0302090007065e80b03020900ba070682c0b03021909070680b03b96c090007068b80b0302090007068b70b03020900070682a0b03020007065180b0302090007b60680b030209000706b580b0309000706266a8000b0302091807067b40b0302090007068
  | 8, 0, 2 => 0xbc303020900070680bc203020900070680b9248030900070680b4803980900070680b0302099100070680b0302090007067f80b0302190900150783a0b03020900067f82c0b0302098e070680b0302c1090007068c02a0b030200070680b030209000706bf80b030209be00070680b0339090007066e8b4140b030209000780b480309008e07068
  | 8, 0, 3 => 0x230302090007062680b0302090007c70680bc60302090007068000b03210900070670b480312090007068000b3102090007067140b03020900077f82c0b03029809070680b030222000706268c50b03020900070680b3c03120209070682a0b0302009b070680b0302090007066e83a0b03020900066e82a2a0b030200070680b03020900c407068
  | 8, 0, 4 => 0xb5702090007600680b3102090007069e82e0302090007066a8000b03021900078b70b0302090007c90680b0302090007a50680b1202090007065880b03020900c8070680b030209080007068002c0b480309070672c0b03120209070680b030209000760068000b64020900077f72a0b03020007860680b4803090007066a80b5702c1090007068
  | 8, 0, 5 => 0x143a0b030209000780b0302220900070680b0302090007626a8002a0b030200070670b03876c0900070680b4b03020900070680b0302980947070680bcc0302090007068000b030209002b067cb0b03020900070680b0302090007070683a0b03020900070683a3a0b030209000682c0b03020907065180b030209000706ca8000b0302091607067
  | 8, 0, 6 => 0x3a0b03020900cf0682a0b03020007069e80b030209008e070682c0b03020907ce0680b130302090007068002a0b57020007067cd2a0b030200070680b0302190900070683a0b03021909000682c2a0b030209070680b2903020900070683a0b57020900070680b03026d0007066a8000b03020947460670b480309009b070682a0b4803090007068
  | 8, 0, 7 => 0xb0302090035070682c0b0302d30907068000b4803090007067003a0b480309000672a0b03020007062682a0b03020015070680b570209008e070680b030209d2000706800240b090007062670b03d1020900070680b03023b0900070680b0302280007065180b9203020900070680b0302980900070680b4302090007d0068a90b0302090007068
  | 8, 0, 8 => 0x3a2a0b030209000680b48030900d7070682a0b48030200070680b03020900d6070682a0b0302000706d582c0b03020907068080b4803090007069e80b0302190900078b80b5702090007066a8000b48570900070670b4b03b9020007068002e0302090007067000b0209000706587a60302090007d0068aa0b03020900070680b030209000706d48
  | 8, 0, 9 => 0xb0302d30900070680b480309000706d582a0b030200ad07068142a0b030200070688a140b030209000780b03db020900070680bda57020900070680b030209d900070682c0b03020915070680b0302090007ce0680b4803090007062680b03020900d8070680b480309001507068730b03020900070680b030209009b070682a0b0302090007068
  | 8, 0, 10 => 0x2a0b43030200070680b030209000706e180b0302010007069e8000b0302989b070670b0302090015070683a0b03020900150680b030209000706e08000b03020100070670b0302090007069e8df0b03020900070680b030209000706de8dd2a0b030200070682c0b0302094707068dc2c0b03020907068000b03020900070670b030209470046068
  | 8, 0, 11 => 0x9c0b0302090007068dd0b03020900070680b030298099b07068140b03020947000780b03020909000706800a60302090007067dc0b03020900070680b030209000706d58dd0b4803090007068
  | 9, 0, 0 => 0xb0302090015070680b0302090007069e8000b03020900070670b030209009b070682a0b0302090007068000b48030900070670b0302980900070680b030209008e070680b030219090007068002a0b030200070670b4b03020900070683a0b03020900070680b0302090007066e80b0302090007067f80b430302090007068
  | 10, 0, 0 => 0xb0302090007067
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 44
  | 6 => 52
  | 7 => 60
  | 8 => 68
  | 9 => 68
  | 10 => 60
  | _ => 0

def idWidth : Nat := 8

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 171 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x7ffffffe00000000000003fffffff, 30)], [(0x15552a0000014000000500aaa95000000a000000280, 1), (0x660cc001983300000000033066000cc19800, 2)], [(0x15552a0000000000000000aaa950000000000000000, 1), (0x660cc000000000000000033066000, 28), (0xa00000000000000000000500, 29), (0x7000fe00000000000000038007f, 30), (0x500000000000000000000280, 31), (0x1983300000000000000000cc19800, 32)], [(0xa881100008811000000005440880004408800, 1), (0x8000000100000000000004000000080, 2), (0x44088800000000000000022044400, 27), (0x22044000000000000000011022000, 29), (0x4000000000200000000002000000000100, 31), (0x8000000000000000000004000000000000, 32), (0x10000000000000000000008000000000000, 33), (0x80000000000000000000040000000, 35), (0x100000000000000000000080000000, 36), (0x200000000000000000000100000000, 37), (0x400000000000000000000200000000, 39), (0x800000000000000000000400000000, 40), (0x1000000000000000000000800000000, 41), (0x2000000000000000000001000000000, 42), (0x100000000000000000000080000, 60), (0x200000000000000000000100000, 61), (0x400000000000000000000200000, 62), (0x2000000000000000000001, 64), (0x4000000000000000000002, 65), (0x8000000000000000000004, 66), (0x10000000000000000000008, 68), (0x20000000000000000000010, 69), (0x40000000000000000000020, 70), (0x80000000000000000000040, 71)], [(0xa220440022044000000005110220011022000, 1), (0x4000000200000000000002000000100, 2), (0x400000000000000000000200, 29), (0x4000000000000000000002000000000000, 30), (0x8000011022000000000004000008811000, 31), (0x10000000000000000000008000000000000, 32), (0x8811100000000000000004408880, 33), (0x80000000000000000000040000000, 34), (0x100000000000000000000080000000, 35), (0x200000000000000000000100000000, 36), (0x400000000000000000000200000000, 38), (0x800000000000000000000400000000, 39), (0x1000000000000000000000800000000, 40), (0x2000000000000000000001000000000, 41), (0x100000000000000000000080000, 61), (0x200000000000000000000100000, 62), (0x400000000000000000000200000, 63), (0x2000000000000000000001, 65), (0x4000000000000000000002, 66), (0x8000000000000000000004, 67), (0x10000000000000000000008, 69), (0x20000000000000000000010, 70), (0x40000000000000000000020, 71), (0x80000000000000000000040, 72)], [(0xa440888011022000000005220444008811000, 1), (0x220440008811100000000110220004408880, 3), (0x400000000000000000000200, 28), (0x4000000000000000000002000000000000, 30), (0x8000000000000000000004000000000000, 31), (0x10000000000200000000008000000000100, 32), (0x80000000000000000000040000000, 34), (0x100000000000000000000080000000, 35), (0x200000000000000000000100000000, 36), (0x400000000000000000000200000000, 38), (0x800000000000000000000400000000, 39), (0x1000000000000000000000800000000, 40), (0x2000000000000000000001000000000, 41), (0x100000000000000000000080000, 61), (0x200000000000000000000100000, 62), (0x400000000000000000000200000, 63), (0x2000000000000000000001, 65), (0x4000000000000000000002, 66), (0x8000000000000000000004, 67), (0x10000000000000000000008, 69), (0x20000000000000000000010, 70), (0x40000000000000000000020, 71), (0x80000000000000000000040, 72), (0x15552a0000000000000000aaa950000000000000000, 1), (0x660cc000000000000000033066000, 28), (0x800000000000000000000400, 29), (0x400000000000000000000200, 31)], [(0xa000000000000200000005000000000000100, 1), (0x4000000000000000000002000000000, 3), (0x800000000000000000000400, 28), (0x550aa00000000000000002a855000, 29), (0x400002a85500000000000200001542a800, 31), (0x8000000000100000000004000000000080, 32), (0x10000000000000000000008000000000000, 33), (0x80000000000000000000040000000, 35), (0x100000000000000000000080000000, 36), (0x200000000000000000000100000000, 37), (0x400000000000000000000200000000, 39), (0x800000000000000000000400000000, 40), (0x1000000000000000000000800000000, 41), (0x2000000000000000000001000000000, 42), (0x100000000000000000000080000, 60), (0x200000000000000000000100000, 61), (0x400000000000000000000200000, 62), (0x2000000000000000000001, 64), (0x4000000000000000000002, 65), (0x8000000000000000000004, 66), (0x10000000000000000000008, 68), (0x20000000000000000000010, 69), (0x40000000000000000000020, 70), (0x80000000000000000000040, 71), (0x15552a0000000000000000aaa950000000000000000, 1), (0x660cc000000000000000033066000, 28), (0x800000000000000000000400, 29), (0x400000000000000000000200, 31)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 85)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 85 true (goal 85) u ys) :
    NatRunT 85 true (goal 85) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 9 0 (NN s)

def poolG : List Nat := [6767497442317458, 3392003199095953, 46174000592802902, 10136408592373909, 6758733530093653, 37199786732046481, 6767529654602898, 6802692489958515, 6769739383789653, 88952699530397841, 3389805243287697]

def Z (s : Nat) := bar 85 true S NN idx ori poolG s

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
private theorem z6_40 : ∀ i, 40 ≤ i → i < 44 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 40 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 44 → Z 6 i = true := (range_split (range_split z6_0 (range_split z6_8 z6_16)) (range_split z6_24 (range_split z6_32 z6_40)))

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
private theorem z7_192 : ∀ i, 192 ≤ i → i < 199 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 192 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 199 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 (range_split z7_8 z7_16)) (range_split z7_24 (range_split z7_32 z7_40))) (range_split (range_split z7_48 (range_split z7_56 z7_64)) (range_split z7_72 (range_split z7_80 z7_88)))) (range_split (range_split (range_split z7_96 (range_split z7_104 z7_112)) (range_split z7_120 (range_split z7_128 z7_136))) (range_split (range_split z7_144 (range_split z7_152 z7_160)) (range_split (range_split z7_168 z7_176) (range_split z7_184 z7_192)))))

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
private theorem z8_184 : ∀ i, 184 ≤ i → i < 185 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 184 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 185 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 (range_split z8_8 z8_16)) (range_split z8_24 (range_split z8_32 z8_40))) (range_split (range_split z8_48 (range_split z8_56 z8_64)) (range_split z8_72 (range_split z8_80 z8_88)))) (range_split (range_split (range_split z8_96 (range_split z8_104 z8_112)) (range_split z8_120 (range_split z8_128 z8_136))) (range_split (range_split z8_144 (range_split z8_152 z8_160)) (range_split z8_168 (range_split z8_176 z8_184)))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_8 : ∀ i, 8 ≤ i → i < 15 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 8 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 15 → Z 9 i = true := (range_split z9_0 z9_8)

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
  scr 85 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRunT 85 true (goal 85) s xsG) : False := by
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

end Sub_1

def taggedFn (a : ℕ) : Bool := (a == 2) || (a == 3) || (a == 4) || (a == 7)

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
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨6, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_3 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_1 (perm_3 i)

theorem hperm_3 : ∀ y : Fin 7 → Bool, fG (substIn cu_3 y) = fG (substIn cSub_1 y) := by decide +kernel

theorem hnc_u_3 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_3 y) ≠ fG (substIn cu_3 y') := by decide +kernel

def perm_4 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨4, by omega⟩
  | ⟨4, _⟩ => ⟨3, by omega⟩
  | ⟨5, _⟩ => ⟨6, by omega⟩
  | ⟨6, _⟩ => ⟨5, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

def cu_4 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_1 (perm_4 i)

theorem hperm_4 : ∀ y : Fin 7 → Bool, fG (substIn cu_4 y) = fG (substIn cSub_1 y) := by decide +kernel

theorem hnc_u_4 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_4 y) ≠ fG (substIn cu_4 y') := by decide +kernel

def perm_7 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨5, by omega⟩
  | ⟨1, _⟩ => ⟨6, by omega⟩
  | ⟨2, _⟩ => ⟨7, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨0, by omega⟩
  | ⟨6, _⟩ => ⟨1, by omega⟩
  | ⟨7, _⟩ => ⟨2, by omega⟩

def cu_7 : Fin 8 → Sum Bool (Fin 7) := fun i => cSub_0 (perm_7 i)

theorem hperm_7 : ∀ y : Fin 7 → Bool, fG (substIn cu_7 y) = fG (substIn cSub_0 y) := by decide +kernel

theorem hnc_u_7 : ∃ y y' : Fin 7 → Bool, fG (substIn cu_7 y) ≠ fG (substIn cu_7 y') := by decide +kernel

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
      apply Sub_1.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_3 ⟨3, by omega⟩ rfl hnc_u_3 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_3 y)⟩
      · exact hop
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hev
      dsimp only at hsz
      apply Sub_1.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_4 ⟨4, by omega⟩ rfl hnc_u_4 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_1.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_4 y)⟩
      · exact hop
  · simp [taggedFn] at hta
  · simp [taggedFn] at hta
  · constructor
    · by_contra! hgt
      obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop fG cu_7 ⟨7, by omega⟩ rfl hnc_u_7 gs o hcl hev
      dsimp only at hsz
      apply Sub_0.noCircuit
      exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_7 y)⟩
    · intro p g hpg hain
      rcases hcl p g hpg with ⟨hop, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_7 ⟨7, by omega⟩ rfl hnc_u_7 gs o hcl hnd hev p g hpg hain (Or.inl hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_7 y)⟩
      · exfalso
        obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop2 fG cu_7 ⟨7, by omega⟩ rfl hnc_u_7 gs o hcl hnd hev p g hpg hain (Or.inr hop)
        apply Sub_0.noCircuit
        exact ⟨C, hfan, by omega, fun y => (hevC y).trans (hperm_7 y)⟩
      · exact hop

def rowsG : List ℕ := [1, 32, 1, 32, 1, 32, 4, 128, 8, 8, 49, 34, 34, 34, 34, 34, 34, 49, 49, 49, 49, 52, 138, 52, 138, 52, 138, 52, 138, 52, 138, 156, 156, 33, 10, 48, 10, 48, 10, 48, 10, 48, 12, 136, 12, 136, 12, 136, 2, 64, 2, 64, 2, 64, 4, 128, 16, 16, 74, 65, 65, 65, 65, 65, 65, 74, 74, 74, 74, 76, 145, 76, 145, 76, 145, 76, 145, 76, 145, 156, 156, 66, 17, 72, 17, 72, 17, 72, 17, 72, 20, 144, 20, 144, 20, 144, 3, 96, 5, 160, 9, 40, 5, 160, 9, 40, 57, 35, 98, 38, 162, 42, 50, 51, 113, 53, 177, 53, 202, 54, 170, 60, 154, 116, 139, 180, 142, 157, 188, 41, 11, 112, 14, 176, 26, 56, 42, 50, 13, 168, 14, 200, 44, 137, 3, 96, 6, 192, 18, 80, 6, 192, 18, 80, 90, 67, 97, 69, 193, 81, 73, 75, 106, 78, 202, 78, 177, 77, 209, 92, 153, 108, 147, 204, 149, 158, 220, 82, 19, 104, 21, 200, 25, 88, 81, 73, 22, 208, 21, 176, 84, 146]

def xsG : List ℕ := [0x135455c3f8018406903e0d5501545541f8000002001e0415, 0x8406903e0d55135455c3f8010002001e041501545541f800, 0x15411eaa820445411eaa820445401aaa000405401aaa00040, 0x102e9aebf0400fdd7d740873002a9aabe0400fd55d5400300, 0x1fdd7d740873002e9aebf0400fd55d540030002a9aabe0400, 0x2008084410024bab2bbffeaa00000000000002aa2abffc2a, 0x4bab2bbffeaa20080844100202aa2abffc2a000000000000, 0x1a821f5504088a821f5504088a801d5400080a801d5400080]

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
  | 6 => 5
  | 7 => 150
  | 8 => 652
  | 9 => 679
  | 10 => 155
  | 11 => 9
  | 12 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0x7aa6bdde52fb98c15008834c35ef489705f59149
  | 7, 0 => 0x2a7765322a374faa29170d0428cb8a422746f0d326f017f224e99f3f24e8ee1424ca4aac24633fa422799d8d21aac973202a7f6a1fd3140f1f5238e41ce1dfc61c6869281ba532da1add020a198b173b193cddb0182eb5b5180f9e8c1746705316b8bf99166af00615db14d4159a060314ee61e914e7e96f149233f31460188a144e228313c205e71391d11513696d3c1317ad181266438f11dfc7ab11d212ef11339b4f11092f59101a14c90dc1ac470d1803e00d1688930cbaa2440c62dc2f0c580f830c0a589e0bdfcb6409c9c25109b49d6509866235095d7614089489800808483c0794c936050fb3420424203303647b1302efecb501f1da6500ac81c5
  | 7, 1 => 0x752b075873a0a824706fe36f6eb66f796eb63d486e56832d6e24318c6a93c2e36a373b3a69c79d746661be556647f5dc65db79866065cd2f5f705bb55e6a43715dd3ba0d5bacc6fd5a0c02b558d9e39b5608cc4b55977c9f5016ab634f0c044c4d51f8dc4d1fb1bd4c6cc9dc4c4a331f4af9e4774a8d1b184a7fc07a4a746f1949fe187f494caef648ea0fe54886a37d4603cc2143e6d83b40ccdec23e0e065a3ce1b5ad3c81c3833bd5cd323a01c35c3860dddf373ae66436e6fb2d36210e3035db8bd335a0659c35337eb534a4bcc733dd3e0733c9d3db33a2cb363344dfb03335b0e62f3748662f353bb72dc463012dadba182d3c475f2d0307062be99e25
  | 7, 2 => 0xf8c6495af445718ce356c86adc3359c0c86b9bcdbc69c4d8b34028e0abfc8d7ca7ab19dfa4493f2b9e700d319c3132dc99b2e8f28afd9fb18a688de886027d2183eff6758261697a8079bab47918b9ec77de81fc765dd44d
  | 8, 0 => 0x73e3c5c072f04b20728d3150724de040720095c071337e107053bcb070506f606ffccf606fbb9c906ec1fd106e1285806db3f6b067de847064f84a1063f89480611d7ba05ffc9a905fc404c05e376be05c37c6d05a729e405a6e20f05a5a1c1059a2d16054f6ea404f26dac04df90f504bb068e04aca51b048aa2170475f1c50452cab40440abc204242033041e5bbc041d98cd040116c403bf390603b1f8cf03832a530325f66602f15cb802efecb502d954be02c62ea3026d77fc025c8452023f136a01dfdcca01d4b83801c56ade01bd6b6f01af2943016d95c30123a0810105a5e800c8a50b00acce25008a6c240079d162003e4f25001f3eb30012e4fe
  | 8, 1 => 0x1047314d1040aa1710379703102fa7520ffded5a0fddf7750fd94a9a0fcf18b80fc6d0020f4356980f1b887f0eed607d0edfd61b0ebf10e80e97de780e7d10df0e729b3a0dd46f750da27db40d5e70780d2ea25b0d2a189b0cde214b0cb47e5e0ca044fd0c9a28b00c8cdad10c51ba2d0c3c9da20c16b4cd0c0a589e0c0314d50bd51c540bab18430b5db7f40b562dbf0b426e150b3f3b810b211a1c0b0b21d70aee76680ada59cc0a8d6a1c0a5eb1830a39aadb0a1b5c4909d1648a09a1e1520986a6dd09735a840953ce2e08fb4cd608f747ad08a7e69e08a64070084e0cc30822f1a308118c4107cf533407b32763076dc7cc076650bb07538a84074c8d34
  | 8, 2 => 0x1b242fb21b0bbddd1aedfd361a8e3bb01a8acf2b1a6c18c31a538e5d1a3bb1201a2f4e611995c6a61980083c197334ae1972c44719311a1018e0206418c82ff018c482c9184eaa9c1848fff0182b8276181c75ab18094fd3176199e5176005d4171537ef170a477516fc0eee16f5b11b162025e4160fce5f1609f75d15afae98159a06031563acac1540c8a6150507d21500d6bc14ee61e914be3f9c14a0e5ca148b9b3e1446fe251391d115137eabcd137173671317ad1812f5e50612da9b7112cd114212ccc23612c7906f12a4dd4a1266438f12469ee112315eff11d66b1711d36f29117bab22112c8ad3112892071123e4d51104a1e610c84fc11074aa59
  | 8, 3 => 0x25003ffc24f5fa1924a51f5e24915bcc2484a4a5243abd41242b924c2414c93b2413150823fff99523e48a2423916d0d2350220e2349a99422c1d8af2272179222685b88225d990d2241b1152222ad7221f65c9221f2e31c21cb2d6121c7a50b21a3c2d5215cb0472102937c20c7019520a174a2205a865e2033d314200fd7cb1fb2f0ce1f1e76d51efbaa5c1ebb610b1e9517441e47f9a21dcbfef11d7516b91d6b1ea41d577a2d1d0153e61cc6903a1c5efa721c525d811c4a5c741c4559e11c3572f61c3161571c23bfdf1c236c6c1bf7a8f71bf067a41bd078be1bc878311bc7113a1bb3cafb1b9eb5a71b7f9b491b723de61b6c93bd1b3204be1b2c5a9c
  | 8, 4 => 0x3425d87533712f66334fbfcc3335638d3305665f32ffe0fa32bae2a432b1e7d23298920932532282322a42e7321e608f31b3c678312797ae3126b39731234f2f310d3c5130c4d8b5301077012ffaa77b2f785d192e5beb822df452162de3ab992d42c2352d2cf9f82d012e102cb7a5a72ca6cdba2be900ba2bdc76172baa11892b8baaaa2b2a209d2acad6682ac43d322a7777752a51ed5d2a24ae7b2a13a2c129d457012954e1f3293313b528dba25428cb8a4228368df327e9304f27ba08ea27a08a8b279e9dd527968d3d2760e99726a82f1426932963268e585c267095c226236707261f15102610951d25fb6c3b25a2af00258c5b0e251303c7250d9d21
  | 8, 5 => 0x3ef831063ec72dbe3eb00c693e5ee4503e22ec193e1570193e09ec203deba7323ddfe6023db0f95b3d9133b03d51e0923cfa99fd3cf6d31f3ce1b5ad3c53f8993c0273063c00c9443be8120a3bd40aff3b9310823b35f8373b27e2753b07d3b83aedd9673abd480d3ab8db5f3a6995ba39bfc02539645fa33953e3633934c2b9390c2fe438aa9d9238780ded3860dddf385a424537f80fa937b103bb3780e95d37753be437603cc93733e5d2372b4be4371a1105370c4ef236f9506536f4bd7436de1b7036d1327836be525c3659ddc3364fd211364f1d7336471865362acd2336188a9135db8bd335ae8bce3522b8ac351a8f3e34e7695634dfa25834845bf4
  | 8, 6 => 0x4e2bc4974d1ef3c74c8504b24c6347494c4b0a714bff54674bb594384b946a7e4b45c1c94adb2f4b4aa7cf224a42aed34a1aa10949dd16d549a79a024941aea54901162c48f5eb8a48ea0fe5487696864863c7e6485fa21348439679480a503c47e04c2b47d690a847cf6dd947c61f4647aebb28478d9d3a47722858476fc28e4754fe0946e458c1460c65ce460a0ca2459ca68945890216457542fd45058a4c44fbe59644eb36ad444777c8442c2b7c44092eab440225c14386b06443553d44433825944330edb142c7b23e422b94004207d9cf42048b5b41cbaab44123ceb540d8e38440bdd57b4087fe9c4064a8fb3fd2cc0d3fc09d813f969a6a3f0ef899
  | 8, 7 => 0x641839b66346cb956249666c6244a46561e3511a619b22a4614968dd61297e8c6105657f60fc7c6160e16562608feacc6065240d603b19ef600412535ea3dd3a5e6b20705dfdc0f15d637f9d5d1a64a85c5024d15c0810a15bb3b9015b2470705aee82745ab435075aabf3445a9f13d75a1267445927803e592683cf58eedb3d58cbeb2a588fe1185869451556e60d6f56da669656a8728256a3c1f956a14cab5623668554910c0a544cb12a540713e053ec998c539a0d9d52baa7a652a1de18529bb10652654969517d2490515994b05152842a51321be750a0a4035082178d4fe8af664fc68bcb4fa67a674f98cee84f69c6e64f59f4354ee8ee2b4ed3b5d2
  | 8, 8 => 0x7fe1a5987fd251607dd2ea627da9096b7d6fdaee7cf115787cb71e5c7ca9b1677c6e123d7c26ffaf7bfaf73c7b27bb457b13e5eb7a9901137a87333c7a20a6457920d1ee78a6f44d7825c019779ec84f776b2c1f765dd44d761a4fa67605156275d512fa75acffaf75ac30087584813075297bda74f570e774eebf9074c37e7a73b013897276563c7275efe8724dcef8724d547c720c43ad71943f1d714fc32670fbf54570144066700cb0a06ff16f3a6fab9bb06ef29c926dff07a46d5ccb966d13f5136cafc3076c7cd49f6c20e01f6b531bcf6a7c5da36941156a6708efd466be60ee665b3ac666098ae96606242c65dde0f7650b698f64f516716465602c
  | 8, 9 => 0xb794635ab60cda04b531c5eab4292487b2b795eab0855a14b018d750ad09e54eacadc14aa9de034aa880cc7fa8230a8aa814a917a77601cfa5ea8ad7a5d356b5a5cc2d59a4887efda4493f2ba3dfc511a39aa8d2a2cc50a99fb096c59dfd92ad9dc83b3c9d73720b9d68574e99baac0099b2e8f298fc5d1198d37c8797c9df36970abff596fc5e8296e36699968a230e950aee9e94bdcc9994229d0d93d2f4f8927b532392603def920adbd7916d5b6290ce11ae8ef7d8778e09600d8d8c9d7f8c860fdf8ac73fcf8aba651d8925ce9688ace76c88aab69887bb1c58879734cd871dafdb85623e30847330a883eff6758233ba2780c88d6c80c3823c80045869
  | 8, 10 => 0xf80ab869ecb8793bdc3359c0ce0f29cdcb19422ac6384414c5f2ce44c4a09c30c0a2a507bf1f731abaf85161b85f8b68
  | 9, 0 => 0x55b6b990557e03e0530dae304f4f1a904ee6c1d04ec2e6e04aca51b049d0014047e893f0473a6dc0448e79d0424b4fb042368f80422672e0407328503b921a003832a5303755e12036cd2bb033fffb403329db80316a26e030c41c102f0579f02d954be02c8392502b6712602a20e3f026d77fc0269d6380262c999024600e3023f136a0235877c02343c9502091fff01e3d6bf01d63bfb01bd6b6f01b225f701a8a567018da3a2018a2152017fe8380176a13b016d95c3016342f40144499c013d8249013256100131881101247dc4010ccdaf00f7926400e4a76400cb40ba00bfb6e10091bbd90079d162004cd00d004adf2e0034a864002e00ce0012e4fe
  | 9, 1 => 0xe76781a0e7600630e4144180e3c19ea0dcb9deb0dc7a74c0db0c9d60d62f6e80d615b390d606e6b0d2ebbd70d2e4e2b0ca044fd0c8cdad10c7d3b280c776cb70c6fadf90c37fa280c2f20060c161c5b0bf814840b9799700b93702e0b8f1bdd0b7972530b64296a0b2586420a6fa2540a45ab1c0a362a3c0a33a63c0a2146250a0ec9c30971bf0509633d770953ce2e0933ecd208de7bb008bc24e008ba074408a7e69e088be3a50884d594084be1ef084417320832354108192d6b07e2a64807d6dfac07c26f3707b32763078305160764d1d907053bcb06f3ca4a067ebdf906581ed306448425063d16430623e54605f5527c05f4d47d05e5165c05bfd077
  | 9, 2 => 0x1626e97a162025e41614e78815e909ef15e3246d15d2443c159ee449159e7f1e157583451574f806156eadf615509c411546f641153318cd14f6720014c32a8314be3f9c148734ee1484f05414682532145a67e8143bb5051417b9731408ea0913ef41d313bd03e813b6a48313a7d3b0136c4f611321a9a212e3420812da9b7112a4dd4a129daf3312918a76127cf1aa11d36f2911c4e44a115aaf801123e4d5110992a11100f23010ff392a10de887710c84fc110c4757e10993c1c1074aa591063fc22104fb69d1035cf25102792ee0ffded5a0ff01a900fd962a20fadb5c50f7be0070f78fd7f0f4202660f2214f60f0a1f5b0f09de660ef5adf60e8c20f4
  | 9, 3 => 0x1cc6903a1c92a9021c3572f61c022f6a1be2805b1bdc9d111bc0309d1bb3cafb1bb1eb871b99c8191b6db88b1b4edd501b0ad7171afe13e81af8cd491aec3d3e1aebe0721abb90051ab514b31aa995f31a9f64c21a703bd11a6c18c319de004519d163c619c4cea619a42e3a1995c6a6198db48b196ce1fc1953f85f19276219190e090618e0206418de9fed18c482c918b32897187d1c6e187b7a4e186315f218583cd2184633f31824ce5f17f3ed0e17ef3c4c17c2a77517b58e53179caee017958b6b177d094b1768d9a31755440d173035f4172062af1707059c16f9f5b816f057c616ef992016e65f6d16c5c9ee16b7b57516a0e929167375cc16301c7d
  | 9, 4 => 0x28c59eaa285b10f127e55aac26ae48eb266dcc432642593325fb6c3b25d9cfb325d0abcd25a02dbe258965a9257e00fe251303c724fe857424ce8b0f24bbce6624b70eaa24915bcc246e2e09246ae5a4243abd412401405423e48a2423ca6018239563d3237128472350220e233b90ca23321b94231a97d222daecd122d93cd022c265e822685b88221379ef21a0b153215341e121356fd42102937c2083caec205a865e204b4143201503b81ffabb4f1ff85e741fd454fd1fcde8971f7e79fa1f357ba61ececf8c1ec9c3e41eae27e41e72a6bd1e3cb5b91e32816d1de3e0641d7d48a41d6b1ea41d488bde1d459cf81d43e1e91d07e2d51d0153e61cc8607d
  | 9, 5 => 0x35ae8bce355d16583550e284353ecc4034dfdd5934acde53347e203a346bb3b53451bfab344a6629340e7a3d340471ad33a0336033956ca133908df533812dbb336b2271335e55a2330f67763305665f32e3c7b932ceeea732bae2a432acd4f33251d347324dba6931785d88316d9f6c3141b23830da5c5430b43360307373703004af172ffc2b3e2fde3aad2fccf7c12fa11af82f93ac662e657cea2e0e18ff2dd5e78d2db4d6912d6d6ae42d4daeac2c24ec472c1127862b7513e42b6c12892b6bc43f2ab0231b2a4e02182a49c5392a0e8dd329f0434a29d457012998ecf6298da97d296a3028295c6d1d295458a629351ff629187482290c6c7828cb8a42
  | 9, 6 => 0x43b2a467439835a24369505943553d444350e9e64346dd0743323b184330edb14307e64942f76e6a42e61c194279b80d4229e8c641b5cdb24157816840f13a114087fe9c4081363b40582a6c3fe3e8b83fb2c4393fa072ab3f8873bc3f2f7b923ec287f63e1e303a3e0b6fe33e09ec203e02cf723dcd441c3cba4e723c6334b63c6242d93c41d7003b99c6cc3a9b56223a91fc493a779bdb3a05eede3a02d40b39ec84a239cc34c339bfc02539908dec398158be3953e36339493500392c6c4a39125b273891ce7a388d10613849ae5b38455d0c38405c3737ddfdcb3794d3da37753be4375d282e371a110536eba9d036de1b7036a77a5e35c1837d35b57e2f
  | 9, 7 => 0x555912245514459d549516b55494fdb854227164540e280953eac23b53d3e7c053ac5e22533089a952f53c9e52d61d11527a0ffc51cd679051a3e1de518f00cc517f533250763692501966ea4f283d924f283b524efadf874e9bf9ba4e810a394de5c1824dac35554d8754904d7da5ae4cf81b664cf696c94c97e81d4c84ea854c55195d4c1e4c8d4c1a0e294c0fcbe94bfe93254ab1538e4a64332b4a5c23934a47cc224a473f7c49dd16d549982ad048e0009b487c7cef48133b30480a503c480905c447effe0847e04c2b47a86c6f476a1d694693a7994646924d461b4bd345a2d9d8458d0c0945890216455ce381450fab4744bb9de84497452c44925c02
  | 9, 8 => 0x6fab9bb06f31211c6edc51736ec3a6596d9917ed6d6f73f56d5ccb966cc5da996c8d4aa56c6e086b6c3c12226b549f926b276cf86af4cd966a434ce769f531c569b9905f6948c57967f8789167aff19667aa47cc678ac0f1665b3ac66622e12366098ae96565e21e654da86a654916d5650b698f64d11692647d20066449349c63a4c6c7635dd880628c0ac661d968ad5e9152795dd4490e5d8a045c5d8875c95c9d60f35c81f4735c7017995c0810a15bba3fec5b2470705afd8d3c5aa7daa55aa5768b5a69f3045a67b55559c3cb1759a4ab445954681a58ca42c1587179e95821589057b2487156a5361b56a14cab56482413563850cd563245ff56236685
  | 9, 9 => 0x992e7113987bfa219834c28c9744ab1096fc5e8295e10538957f7000932e4797927b532390e2622d8dfb998d8b52d59d8b0f8c5d8a97472989897b6a88c69cda88c444dd88ace76c8874d640886b07c68818799d881413d786fd343d86ba1a8385ccec448466d01f8458439c83516e74812daae381274fdf810cdb5280bd2fed807637628046bd7d7fc1bd667e460b487d8c45a07c6e123d7c26ffaf7b27bb457b1590ab7aae365f79aaccc3787130d577abfa48776e8a75776b2c1f775c8bab77069569762a6c4c74ce2b37744873487411ce8872f92a8c72c329af72be3c767275efe872595ce07247244f71bcecce717e2cac714fc3267130d55771294cfe
  | 9, 10 => 0xf701d056ec9611d4e5abf6a0e532d342d7efcfd0ce2dd5e4ccbd87bcc92720a7c6828335c6384414c4b52481c31ca185c0a2a507c0360058bf187490be763442bb6ba573bb536f09b65e014ab575d53bb1fbfc12b1318524af1db5c3abb3303daa535adea85cf5a5a81c6c25a814a917a52672fba498e81aa449797da2e89710a1b06370a12084849f361a109d56e4be9bee5da49bb7319f9b438699
  | 10, 0 => 0x1ec9c3e41e72a6bd1da03c951c1289fb1bb3cafb1aebe0721a9f64c21a3522c619c4cea618b824d6181d3590180f780317b58e53172a723c16f057c616eda3ca16c5c9ee16a0e92915e3876415d8fea015c691fe159e7f1e156eadf615509c4114b1ecd411525f99113b851e1123e4d5110992a110ff392a108d290c10480386103dba6f102792ee0f6de49c0f3b50640f26aaea0f0b7f3c0f0a1f5b0f09de660ebb26a80e3c19ea0e1ecc2b0c8046b60aa052e30a3a6ac00a33a63c0a21462508ba074407982ef706745f3a05f5527c047e893f0473a6dc0448e79d0405572702d954be026d77fc0239ff2e01b225f7014a4d78012ca11b00f79264007b206c
  | 10, 1 => 0x6e36be4b6a434ce7698b208a6829548a67aa47cc670242be6643b4e766098ae9654da86a64258ce26111e9d35edf38895c7017995aa7daa556a14cab560ce8df5486a7fc53eac23b53d3e7c052d61d1151a3e1de4e6aaa344c84ea854c7316ec4ab6787e4a473f7c49982ad0497080624858432747fee48746e113e4461b4bd345b0e3e5458902164350e9e64279b80d412d178d3ee87d3b3e0b6fe33c6334b63a00657c398158be3953e363387d2e0938405c3737753be436a77a5e35b57e2f349a0c3931785d8830cea52c2f972ff92e0e18ff2c1f1caa2bdfc9312a0e8dd3294a527a23321b9422f38a202263622e2102937c203e7da41ff85e741f7139aa
  | 10, 2 => 0xd8381c5ed77a4ee1cb8d7a40c6384414c479e570bc6ad0beb65e014aa5a66b35a52672fba491c60b9f361a108a97472989897b6a860dba6d85ccec4485be4bd084f9154384a9a6a67c26ffaf7b1590ab79f5b684782c3b1a7706956976dfb35172be3c767275efe871bcecce
  | 11, 0 => 0xa52672fb8a97472972be3c766a434ce753eac23b52d61d112102937c159e7f1e026d77fc
  | 12, 0 => 0x2102937c
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x9aa2ae1fc00c203481f06aa80aa2aa0fc000001000f020aa101a40f835544d51570fe00400080078105405515507e003fbafae810e6005d35d7e0801faabaa8006000553557c0801a821f5504088a821f5504088a801d5400080a801d540008025d595dfff551004042208010155155ffe1500000000000005bf7fafcb117f75f5faabdd40aa6aaf81003f55755000c012eadabfffaab2eadabfffaaa02acaabff82a02acaabff82a341cd8ee38475fbffbbffeef00000000000002aa2abffc2a
  | 0, 1 => 0x1dbebeebfc45d617dcbf2eef80aa2aa0fc000001000f020aaa0a7f551422aa0a7f551422aa00755000202a00755000200a82bf554508aa82bf554508aa80355400080a8035540008102e9aebf0400fdd7d740873002a9aabe0400fd55d54003007effffaa6bdd1574d7ffaa457eaaeaa001800154d55f020055047aaa081115047aaa081115006aa8001015006aa800100d75657fffd54d75657fffd540554557ff8540554557ff8542ae9afff548afdffff54d7ba02a9aabe0400fd55d5400300
  | 0, 2 => 0x52074c3d0eabac7fbf3e03558001000f020a81ff3fff021515057eaa8e1155057eab8a1155006aa8001015006aa8001012ebdbbfffaaf2ebdbbfffaae02acaabff82a02acaabff82a2008084410024bab2bbffeaa00000000000002aa2abffc2a7655d51e03ff3dfcb7e0f9557f55d55f03fffffefff0fdf50a0a4a5514228a0a4a5514228000000000000000000000000bf7ff77ffdde6839b1dc708e0554557ff8540000000000007c39ebfc70ce7c39ebfc70ce5401aaa000405401aaa00040
  | 0, 3 => 0x5a2a6a2000aaeffbfbddf7fefeaaeaa001eaffffffffffff80bb6fafc3007f75f5d0a3cc40aa6aaf81003f55755000c01fbbfbe892e6405d35d7e2805faabaa8006000553557c08005419eaac30465419eaac30465401aaa000405401aaa000400174d75f8a017eefefa24b990154d55f02007eaaeaa001802515350000556515350000557f55755000f57f55755000f5568a1888002a9bfe7cf73cff9faabaa8007abfffffffffffefdd7d7428f3102edbebf0c01fd55d540030002a9aabe0400
  | 0, 4 => 0xa0a685514228a0a6855142280000000000000000000000037fdfdeefbff6d15351000557fffffffffffff55755000f55504beaa49113504beaa491135003aa8001015003aa80010057da0aadb77657da0aadb77657fe2abfff7f57fe2abfff7f10060c230c01a5d79ddfff558000000000000155155ffe15251737010455e51737010455ff55755000f57f55755000f54aebbffdff08fa83ff57c7aaeaaabffc3f080a807557c08aa9416d0be3d551754d5eff8450002001e041501545541f800
  | 0, 5 => 0x438348dffeaa89aa2ae3fc008001000ffe0a80aa2aa0fc0015d57ffafe117505feaf8b5555557ff87e101500eaaf81155282da17c5aaa2ea9abd7f08a0004003c082a02a8aa83f000301c58c638034fafbbbffeef00000000000002aa2abffc2a3454950001553454950001557f54d55001f57f54d55001f52afa815575eeaafa815575eeaaff9557ffefeaff9557ffefc26b8bb8ff007081d307c3aae02a8aa83f0000004003c082ad757fffffd55d757fffffd555557fffffc555557fffffc55
  | 0, 6 => 0x9ab2afffe00c203483f0eaa80ab2aaffe000001000f020a9aebceffffaadaebceffffaac0aa8aafff0a80aa8aafff0a8d74647f7dd50d74647f7dd500554557ff8540554557ff854135455c3e8018406903a0d5501545541f8000002001e04157eebeba04b980175d75f86007eaaeaa001800155d55f02002103a60f8755c4d71771fe00c00080078105405515507e001786bebf4d19b786bebf4d19b5003aa8001015003aa8001005bff7ffffeaba40e987e1d5703fe7ffffc2a0002001e0415
  | 0, 7 => 0x3df8b3e0f1547651d11c03fe7ffefff0fdf57f55d55f03ffaa087d5410222a087d5492222a00755000202a0075500020066b8bb8ff0079f5f777ffffe02a8aa83f0000554557ff87e8406907e1d55135655fffc010002001e04150156555ffc005410faa828445410faaa20445400eaa000405400eaa0004025d4b17f7d5525d4b17f7d5500559557ff0540559557ff0554e010307f2a8b7e2cf0bc551f8030003f7abfffbffc3f7d4cfafbbbfffff335c5dc7f80302aa2abffc3f01545541f800
  | 0, 8 => 0x66c7cd9f4fbb89ae2ee3fc018001000f020a80aa2aa0fc000cd71761fa00f3eb6ee07cffc05515507e0000aa0aa87e0fcf7f2df83e555d95754780ffdfffbffc3f7d5fd57557c0ffecca3a27817fc3052447e0c00feabaabe07fffd57d55e07c075f597aaebdd75f597aaebdd7fffffffffffffffffffffffbf75f5daa3dd44bf7fafcb007f55755000c000aa6aaf810019f5b7703e7fe66b8bb0fd00605505543f07e02a8aa83f00057d602abaf7557d602abaf7557fe2abfff7f57fe2abfff7f
  | 0, 9 => 0x2c7fbf3e0355d2074c3d0eab81ff3fff02150001000f020a88020211860092eacaefffaa80000000000000aa8aafff0a9481d30fc3aae36fafbaff1160004003c082a02a8aa83f00028297d54508aa829b954508a00005540000000000000000025d79ddfff5590060c230c018155155ffe150000000000003f4490503cff808a0a2f5c33bf5595507effc0aa8aafff3fcd15a74041556d15a74041557fd53554007d5fd53554007d45411eaaa28445411eaa820445401aaa000405401aaa00040
  | 0, 10 => 0x40000002000955514000000000000000000155000002a087d5492222a087d5410222a00755000202a00755000201fbafae890e6005d35d7e2801faabaa8006000553557c0800438202abae20438202abae2002aa2abffc2a02aa2abffc2a7eebeba147980174d75f82007eaaeaa001800154d55f020000ba6bafc1003f75f5d0a3cc00aa6aaf81003f55755000c01fbafaf855e620ddb7d7e188bfaabaa8006000553557c0800d417faaa2d555655feab28455401aaa000405401aaa00040
  | 0, 11 => 0x70c3f0e0180070c3f0e018001000f02000001000f020033baebafc1ff3f75f5d021cc3faaeaaf81ffff55755000f00f7fefffffd57df5f77fffffe07fcfffff8540554557ff87e030001c3f8000002003e0c0000000001f8000002001e04007655d51e0bff3dfcb7e2f9557f55d55f03fffffefff0fdf500ba6bafc1003f75f5d025cc00aa6aaf81003f55755000c01505bfaacb117505bfaacb1175003aa8001015003aa800100741dfaee38475fbffbbffeef5401aaa0004056abaabffc6a
  | 0, 12 => 0x1260e438400e6c3c981479880000000000000000000000012eacaefffaa88c20271fe0080aa8aafff0a800000007e001481d30fc3aaeb7fefffffd560004003c082a07fcfffff8540002007e1c000002007e1c000002001e04000002001e0400118404e3fc0125d595dfff5500000000fc000155155ffe150802821f870092eacaffffaa80008007810000aa8aafff0a805d35d7e2801fbafae890e600553557c0801faabaa8006004bab2bfffeaa200a087e1c0202aa2abffc2a0002001e0400
  | 0, 13 => 0x9aa2ae3fc00c203481f0eaa80aa2aa0fc000001000f020aa101a40f875544d51571fe00400080078105405515507e000e833d5d8608cb873d778e19ca80355400080a803554000805411eaa820445411eaaa28445401aaa000405401aaa000406ff9f3dcf3fe5a28622000aa7ffffffffffffeaaeaa001eaaf1f7f551477ef1f7f551477ff55755000f57f55755000f540010100820040010100820040000000000000000000000007cbdfaaa2aef7cbdfaaa2aeffea9aaa003eafea9aaa003ea
  | 0, 14 => 0x60c030c0180060c030c0180000000000000000000000000c30661fe00c0c30661fe00c00000007e00000000007e0000450517ae19dfa248281e7fc0554557ff9fffaacaa83f7fe8406903a0d55135455c3e8010002001e041501545541f8002174d75f96007eebefa043980154d55f02007eaaeaa0018021bbefafc3447ff5f5f0e3cc40aa6aaf81003f55755000c00f973d55045dcf973d55045ddfd53554007d5fd53554007d403000187f80003000187f80000000001f80000000001f800
  | 0, 15 => 0x6fffffffffffdbaf6efffeab81ff3ffffe1f80ab2aaffe0a8000800f8300000000100400000080078100000000000000006082307f0020008200c100200000003f00000000000000002e9aebf0c00fdd7d740873002a9aabe0400fd55d54003000174d75f8a017eefefa34f990154d55f02007eaaeaa0018015047aaa081115047aaa081115006aa8001015006aa80010060a488fc1801994744f02ff9faafaabc0f81fd57557c0ffe02ebaebf0c00fdd7d740973002abaabe0400fd55d5400300
  | 1, 0 => 0x2080104008002080104008000000000000000000000000088082fda336d4514503e5540aa8aafff3fff5515507ef5404404176d19bfa2ca281d7fa0554557ff9fffaacaa83f7fe4ba92b81f2aa20080804000202a82aa1f82a0000000000004202480000aa89aa2ac1f40080000000000a80aa2aa0fc0000920321c2003361e4c025cc00000000000000000000000000014107c38040010108820040004003c0800000000000000fff7f7bbeffdfff5f7c1e3fdfffffffffffffffdffe1fbff
  | 1, 1 => 0x7eebeba04b980175d75f82007eaaeaa001800155d55f020012facbefffaaa903a611054480aa8aafff0a800000000000176fbfbaff117585ffafcbbbf52abaa83f1015007aabc092a0000554050008000901400000000554000000000000000000174d75f82007eebeba043980154d55f02007eaaeaa0018000c00060fe00000000010000000000007e0000000000000016ea9ab87f2abbfefef7fdffbfaabaa83f7abfffffffffffe1054544000018406903a0d550154554000000002001e0415
  | 1, 2 => 0x7eefefa24b990175d75f8e017eaaeaa001800155d55f02001d067abb0c1197eefaefffbb95006aa8001015aaeaafff1a8001010082004801255586004000000000000000055400000fd165140ebfd022020bb68cdfd565541fbff02aa2abffcff7ffdf7fefbff7ffdf7fefbff7fffffffffffffffffffffffbf4594503effc08a0a2fde33ff5595507effc0aa8aafff3fdd94744700ff8f7e2cf83c551fd57557c0ffffffbffc3f7d4fcfffe7c07fffffffffbfffffffffffe07ffffffffffffff
  | 1, 3 => 0x4377df5f86aafeebeba043988155d55f020afeaaeaa0018013ebeeefffbbcc0716318e00c0aa8aafff0a8000000000001fbafae810e6005d35d7e0801faabaa8006000553557c0800a821f5504088a821f5504088a801d5400080a801d54000800000002008000001001f06000000000000000001000f020012eacaef7daa88020211040080aa8aafff0a8000000000001fbafae853e6205df7d7e1803faabaa8006000557557c08000004104218010006103e0c010000000000000002001e0400
  | 1, 4 => 0x2575d75f83557eefefa04b990155d55f02157eaaeaa00180122aca8f01aa88020210040080aa8aaf810a8000000000000b873d778e19ce833d5d8608ca80355400080a80355400080a821f5544088a821f5505088a801d5400080a801d54000807ffbfbfdf7fefffbfbfdf7feffffffffffffffffffffffffbb2bee8f83ffdeff5ff0feaaffaaeaaf81ffffff7ff87efa9080500780aa826a08b83e0000004003c082a02a8aa83f00040012aaa280000000800000000002aa00000000000000000
  | 1, 5 => 0x7e8f2ca27dff8114145fbc67feab2aa0fdff8155155ffe7faa097d5496226a097d5592226a00755000202a007550002009756577ffd544010108c30040554557ff854000000000000bc75f55041ddbc75f55041ddfd55d54003d5fd55d54003d50000000000000000000104000000000000000000000000001efe5bf17caabb2aea8f05ffbfff7ff87efabfaaeaaf81ffc05d75d7e3805fbbfbe892e640557557c0801faabaa800600efababbffffe7bf96fc5f2aafeabaabffffffffdffe1fbea
  | 1, 6 => 0x1200241880042034802028800000000000000000000000015047aab081115047aaa0c1115006aa8001015006aa800100a823d5506088a823d5584088a80355400080a80355400080b456d47e0d55dff7f7fbfffdfd57d55e07d5ffffffffffff000000020800018000c3fc0000000000000000000000fc0000ba6ba040003f75f5c021cc00aa6aa800003f55755000c01fbafae810e6005d35d7e1801faabaa8006000553557c0800fdd7d742cf3182edbebf0c01fd55d540030002a9aabe0400
  | 1, 7 => 0x5baf6efffeabefffffffffff80ab2aaffe0a81ff3ffffe1f80000011040000c0806fff0000000000000000008007ff000505252a8a114d75657fffd540000000000000554557ff854ecabaa3807fe7bf96fc1e2aafeabaabe07fffffdffe1fbea2a0cf55610222ec9f5d557322a00d55000202a00d550002004d51571fe0061c1a46fff55405515507e0000008007ff054afbc155f7eeeafbc155b6eeeaffc557ffefeaffc557ffefe13fdfffffc03fddfdf7e9f7703fdfffffc00fd57d55e0715
  | 1, 8 => 0x404020801018404c3fc0100000000000000000000fc002af98554f3ee6af98554f3ee6aff9557ffefeaff9557ffefd57dc3aafbf7757dc3aafbf7757fcaabfff7f57fcaabfff7eabee1557dfbbabee1557dfbbabfe555fffbfabfe555fffbf6651d11c03fe1828222000007f55d55f03fffeaaeaa001e0008a0a3fde33ff45945fbfffc0aa8aafff3fff559557ffffdfa2ca281e7fe0450517ef19ffaacaa83f7fe0554557ff9fe7bfb6ffffeaaecabaa7c17feffffffffffeafeabaabe07ff
  | 1, 9 => 0x2bef0557dfbbabef0557dfbbabff155fffbfabff155fffbf80010401820040010400860040000000000000000000000000000008430000004007c18000000000000000004003c0800698b0b4496224bab2bbffeaa00000000000002aa2abffc2a4377df5f82887febebe1cb980154d55f02007eaaeaa0018029002000005516fc59e078aa3f00600000f57fff7ff87efa9d95754f82ffcf7f6dffffd55fd57557c0fffffffffffffd42008080400024ba92b81f2aa00000000000002a82aa1f82a
  | 1, 10 => 0x6a0bfd5612aa2b28f75598222a00d55000202a00d550002012fbcfefffaae903a6118744c0aa8aafff0a8000000000000505252acb114d75657fffd540000000000000554557ff854135c5dc7f801cd87933e9f7501545541f8000002001e04155412faa82044d412faa92444d400eaa000405400eaa000402101a400834440910520c2004000000000000000000000000b7e2cf03c5514801000002a9fffbffc3f7d5f803000007aa840e983e0d57135c5dc3f8030002001e041501545541f800
  | 1, 11 => 0x4377df5f86aaffebebe1ff988155d55f020afeaaeaa0fd800000a00f8300045515502400000080078100005515500000005df7d7e1803fbafae853e620557557c0801faabaa80060000000004000003000183f80000000000000000000001f8000000000008000000000200000000000000000000000000003aebffffffaaea0b7f559622eaaaffffff2aaa00755000200104242249110400000800000000000000000000000000000a829fd56588aa829fd54508aa801d5400080a801d5400080
  | 1, 12 => 0x7eebeba043988176df5f8600feaaeaa001800154d55f02003f77f7d125cc92baebafc5aabf55755000c000aaeaaf810a820a8a8841003080d20741aaa02a8aa8000000004003c082a4aebaebf0eaafddfdf40973202abaabe042afd55d54003000174d75f8a007eebeba24b980154d55f02007eaaeaa001803fffffeffbffffff7ff07cffffffffffffffffff7ff87effdbfefef77dffb68a9a88412abfffffffffffffaabaa8007aa5411eaac20445411eaaa38445401aaa000405401aaa00040
  | 1, 13 => 0x114145fb467fe8a28a079ff8155155ffe7ffeaa2aa0fdff84d411707c002100a00f0155005515507e00000080078105445d75dfe3805ffffffffff740557557c0801fffffffffe5400080804000049830300962000000000000000000000000077d7ddffffffbdffbfffff558155155ffe1f81ff3ffffe1516efdeefffaac903261b8611c0aa8aafff0a8000000000000f7faff87f557d95f747c1ffffffbffc3f7d5fd57557c0ffeb875f5504089ac25f55041dda955d5400080a801d5400095
  | 1, 14 => 0x19aa2ae1fc00c613d89f26ee80aa2aa0fc000001000f020a88ba6bbfc500bfffffffffee80aa6aaf81003fffffffffca8001010082004931616092c44000000000000000000000000fd145140f3ff022828bf68cffd545541fbff02aa2abffcff7ffeffe0f9ffffffffdff7fffffefff0fdffffffffffffff808a0a2f5833bf4410503cff80aa8aafff3fff5515507effd68a9a88412abbfefef77dffbfaabaa8007abfffffffffffefdd7d740973186efbebf0d55fd55d540030002abaabe0415
  | 1, 15 => 0x2575d75f83547eebeba043980155d55f02157eaaeaa001803aeaffffffaabaeaffffffaaaaaaffffff2aaaaaffffff2a9fbafae810e6015d35f7e9911faabaa8006000553557c0800000410021801000410060801000000000000000000000000000208030400818208c1fc0080000000000000000000fc003f75f5d021cc61bbefafc3557f55755000c000aaeaaf810555053faa0a1155053faa881155003aa8001015003aa80010002ebaebf0400fdd7d740973002abaabe0400fd55d5400300
  | 2, 0 => 0x7eebeba14798c377df5f86aafeaaeaa001800155d55f020a86dd5d74fe226901a41f8355405515507e0000008007810540450517ef19cf2208281e5540554557ff9fffaa8aa83f7d41410c0a820441410c0a820440000000000000000000000007eebeba04b980174d75f82007eaaeaa001800154d55f02002a0a7f551422baeaffffffaaaa00755000202aaaffffff2a80010108820040014107c38040000000000000004003c08004bab2bbffeaa698b0b469e2202aa2abffc2a000000000000
  | 2, 1 => 0x7eebeba043982574d75f83547eaaeaa001e07f54d55f03f50a08485492220a08485492220000000000000000000000001bfffff7fffff68b9b88822affffffffffffffaabaa8007aa4ba323bbeea820000040000002aa2abffc2a0000000000007eebeba243980174d75f8e007eaaeaa001800154d55f02003a68fdd435aa2a0a7f5510222a00755000202a00755000201fff7dff3effdf9f7dcf80ffdfffffffffffffffffffc0ffe5d9bebacb6665419eaac30465401aaa000405401aaa00040
  | 2, 2 => 0x176df5f8200feebeba147988154d55f02007eaaeaa0018015057eaa081155057eaa8a1155006aa8001015006aa800100a823d55c5088a823d5506088a80355400080a8035540008002ebaebf0c00fdd7d7429f3002abaabe0400fd55d54003004202480104aa89aa2ac1f40080000000000a80aa2aa0fc00080306110400d2ebceefffaac0000000000000aa8aafff0a897df7f7ffd57fbbfbe8d3e660557557ff855faabaa80060002a92abf0c0020000040000002a82abe0400000000000000
  | 2, 3 => 0x5410f2a820445410f2a820445400eaa000405400eaa000403f77f7d125cc82ba6befd522bf55755000c000aa6aaf81001fbafae810e619dd75d7e0ff9faabaa800781fd57557c0ffe4bab2bbffeaa698b0b44962202aa2abffc2a0000000000000174d75f82017eefefa04b990154d55f02007eaaeaa0018000bb6fafc3007f75f5d0a7cc40aa6aaf81003f55755000c01d757fffffd555053faa8a1155557fffff9555003aa80010008292914508a200808441002000000000000000000000000
  | 2, 4 => 0x7ffffffdfffffe7fff3e03ffffffffffffffffffffff03ffb7fdfdeffbff6dd53570fe557fffffffffffff5575507ef54f7f2df8be555df57577ffffdfffbffc3f7d5fd57557ffffe02e1a6bb0400fdd7d740873002a9aabe0400fd55d54003001828222000006651d11c03fe7eaaeaa001e07f55d55f03ffae0c7d741c222b087d5f10332a00755000202a0075500020157dc2aabaf7757dc2aafbf7757fcaabfff7f57fcaabfff7e02480c871002cd8f9b049732000000000000000000000000
  | 2, 5 => 0x7efbfba967dc1174d77f82007eaaeaa001800154d55f02003ff5f5f0e3cc21bbefafc1443f55755000c000aa6aaf81001481d30882a2497d65f7ffd540000000000000554557ff854022828bd70cffd165140fbff02aa2abffcfffd565541fbff2a0cf55610232a0cf55418232a00d55000202a00d550002000ba6bafc700bf77f7d125cc80aa6aaf81003f55755000c01fbafae810e630ddb7d7e0aabfaabaa8006000553557c082a31145140f803022828bf78cf01545541f80002aa2abffc3f
  | 2, 6 => 0x7eebeba347980174d75f8a007eaaeaa001800154d55f02003f75f5d0a3cc40bb6fafc1007f55755000c000aa6aaf81000bf7ff77ffddee83bf5dc708ead57557ff8d4a803554000805411eaac30445411eaac30445401aaa000405401aaa000403a08f55410222e58f55411767e00d55001e07f54d55001f50101240a8211440514208a004000000000000000000000000a833d5584088bb27d7516cc8a80355400080a8035540008002480c870000cd8793008730000000000000000000000000
  | 2, 7 => 0x114145fbc67fe8b28a07dff8155155ffe7ffeab2aa0fdff80ba6bafc3003f75f5d025cc00aa6aaf81003f55755000c00a823d5545088a823d5545088a80355400080a8035540008022480cc71002cfafbbbfffba00000000000002aa2abffc2a0002481f060088aa2aa144008000000f020000aa2aa000003f77f7d1a7ccc0bb6fafc700ff55755000c000aa6aaf810004010108820049756577bed540000000000000554557ff8544bebafbf9622fddfdf44973202a9aabe0400fd55d5400300
  | 2, 8 => 0x6ffbfbfdfffeda2b6a3f06aafffffffffffffeabeaaf03ea84d51560fa00610124000055405515507e00000000000005466b09b83e005995754780ffc02a8aa83f0000554557c087e4ba323bbfea820000044000002aa2abffc2a0000000000001004042208010414948a284500000000000000000000000000c0806fff0000000011040000008007ff00000000000000168b9b88822afbfffff7ffffffaabaa8007abfffffffffffe83461557dd1183461557dd110156555ffc150156555ffc15
  | 2, 9 => 0x1004042008012455951f07550000000000000155155f02150001840f830040010410860040008007810000000000000019f4f677fdffa66a8ab87f0020554557ff87e02a8aa83f000fffbefbde7fefff9efc1f3fefffffffffffffffdffe1fbff5202482000aaadfbbbddf75480000000000a81ff3ffffe15332bee8f83ffccd71770fe00c0aa8aaf810fc05515507e000000000041000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 2, 10 => 0x6fffffdfffffdbae6ee3fcabfffffffffffffeaaeaa0fdea8000000100000000000004000000000000000000000000000b7eeeff7fd53480d20fc1aaa07fcfffff8540004003c082a4ba92b85f2aa20080804100202a82aa1f82a0000000000004201401f06aa09a822e0f8000001000f020a80aa2aa0fc002101a40e8355441515100000400080078105405515500000006000307d00000000000000000000003f000000000000000fddfdf7e9f7713fdfffffc03fd57d55e071503fdfffffc00
  | 2, 11 => 0x10000022000025d191ddff540000000000000155155ffe153beaeaffffff9efedbffffaabfaaeaaffffffffffffffffa9ffefefffdffbffefeff7fffbfffffffffffffffffffffffe84049000015510545400000100000000001501545540000067d5d5dfffff182c262208017f55d55ffffffeaaeaa001e008020210040092eacaeffbaa80000000000000aa8aafff0a90809200802aa26a8ab07f00200000000002a02a8aa83f000b454d4401155dff7f7bfeffdfd55d54003d5ffffffffffff
  | 2, 12 => 0x3dfcb7c0f1557654d50001ff7ffefff0fdf57f54d55001ff8000001004000000800f010000000000000000008007810012eadab7fdaab2ea9ab87f2aa02acaabff82a02a8aa83f02a2008084400024bab2bbbfeaa00000000000002aa2abffc2a09a822c0f0004200400000aa00aa2aa0fc0000000000000a840410200c000100200b00110000000000000000000000000975e77fffd56401c30fc38060554557ff8540004003c0800ffffffffffffffffffffffffffffffffffffffffffffffff
  | 2, 13 => 0x2dffbfffff55d3874cfffeab81ff3ffffe150001000ffe0a9effdfffffaafb2bee9f87fffffffffffffabfaaeaaf81ffc401010882004915654782d540000000000000554557c0854cfababbffffe33584dc5f00202aa2abffc3f01545541f80000000003040000000000080000000000000000000000000000c2826fff0080020211040080008007ff00000000000000040000080000097464777dd500000000000000554557ff8542000004010004ba323bfeea800000000000002aa2abffc2a
  | 2, 14 => 0x3dfdb7ffff5577d5d5ffffff7ffffffffff57f55d55fffffa5153510005565d5b56efb5540551550000540559557ff05426acabfff8030e0d23fffaaa02acaabff8000004003ff82aa40e983e0d575bfd7fc3faab0002001e041503fc7fe1f82a2455951f07551004042008010155155f02150000000000003f3dfd9e01ff7ffdfdfefbff7fffffff81ffffffffffffffdfffffffbeffffffffffffffffffffffffffffffffffffffe9456d43e0d559754d5c3f955fd57d55e07d5fd55d541fbd5
  | 2, 15 => 0x3455951e035535d495e0f9550155155f021501541550fc150002020100008002020004008000000000000000000000001080d20080a2004800906200000000000000000000000000000000004000000000002180000000000000000000000000019af2efffe01e7d7ddffffff80ab2aaffe000155155ffe1f84d71771fe00e1c3a66fff55c05515507e0000008007ff055fffbff87f7ffffffff7fdffffffbffc3f7fffffffffffffe0002003e0c00030001c3f8000002001e040000000001f800
  | 3, 0 => 0x6e7bfb1c03feda2a6a2000aaffffffff03fffeaaeaa001ea96fe5bf07caaa902a20f015580ff1ff87e0a8000800781054401010802004915654780d540000000000000554557c0854b454d4440155dff7f7bbfffdfd55d54003d5ffffffffffff6ffbfbddfffeda2a6a2200aafffffffffffffeaaeaa001ea96fd5df0feaa6901a40f83557fff7ff87efabf00e00781f55fffffffffffff9fffcf82ffffffffffffffffffffffc0ffeefafbbbfffff7bfd7fc7faabfeabaabffffffffdffe1fbea
  | 3, 1 => 0x7eefefa34f99a5f7dfdfff55feaaeaa001800155d55ffe151aeacaffffaa9a2aca9f05aa80aa8aafff0a80aa8aaf810a80000008000000004007418000000000000000004003c080003080987f80200080804100200000001f8000000000000004a2b6a3f06aacbab6afdfeaa80ab2aaf020a80ab2aaffe0a97eefaefffbb9d067abb0c1195aaeaafff1a95006aa8001000010100c3004001010082004000000000000000000000000335c5dc3f803ccafba3e0fff01545541f80002aa2abe043f
  | 3, 2 => 0x828222000004201401c02aa00aa2aa000000001000f020a80010400820040010400000040000000000000000000000010801000002a820a088000001f803000007abfaabaa80078020000040100002ab2abf0c0000000000000002aa2abe04004baa6ae1fcaacbab6adff6aa80aa2aa0fc0a80ab2aaffe0a80000000820000000000820000000000000000000000000019f4f6777dffa60a8a88000020554557ff87e02a8aa80000013545583f80184049004015501545541f800000000000015
  | 3, 3 => 0x7fffffffffdd1175d77f8e017fffffffff950155d55f02003f3fff8f01ffffff7ff07cffffffffff81ffffff7ff87effc0004007c18000000008430000004003c0800000000000000fddfdf4497324bebafbffeaafd55d540030002abaabffc2a6a0ffd5f1eababaefff7fc23aa01d55f022aaaaafff0fc203b2aea8f83ff9efe5bf07caabfaaeaaf81ffffff7ff87efa9481510f82aacb7f6dffffd540004003c082a07fcfffff8541154554288010004903e0c010154554000000000001e0400
  | 3, 4 => 0x60403fff800060403fff8000004003ff8000004003ff800ffffffffffffffffffffffff03fe7ffffc3f03fe7ffffc3f
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0xa04088300200602840120c0781980a0e06824180160582812080381980a040180802006
  | 7, 0, 0 => 0x28101a030600458e1302838140906019c560515010060c0a38741c0a0483052067028105003060504ee26028941a0306005c0a240500c180111b8880a040506c0e0670281042030608028e1f028101a1e00851c3a040e02436070338680a0e050300e0670c860080a0600428e0502028060c0385dc0a040b00c18150a384c0a0a048300c127
  | 7, 0, 1 => 0x1f814080a0483052e051f028060c1e8f1c0a250500c180111b814760a0483052067028101403060e828e051c810140c03051c0a04050e0183711b8141c0a04830523270283814360601c0ce05020286a0c1a019c34050207018290338cc1c0a048300e0670281038090d81c64e0518834060c00851c0a04068c0182f0a3814082e018305a147
  | 7, 0, 2 => 0x290014090601c64e490281014030608dc0a04240c0182f0a381414090603c0c1270e81014090601c8ee1f02810140c23019c4c0515010060c00b914880502028060c72181408030600428e4202034060c00851c0a0401808021413b814080a061040e1470e81014090d81c0ce1807028120c03819c0a04050d41829033874800a048300e067
  | 7, 0, 3 => 0x298101430060bc28e050202806521e8f1ca2040680c18010a3814080d01830021470c010a0030600428e490f814080a06051c0a3e0680c18010a38141c0a048301e0670f814080d0600446e4502810144f06051c0a040680c18012738141c0a048300e4d715860080d0183028e0505024180703131c560502028960c11b9280a040680c02147
  | 7, 0, 4 => 0x22014080a018300ce45028103809060a5c885e0281014030338141c0a2e8300c5c72d8141c0a048300ce0507028125a03819c0a59050241807033814085801830025770e81014350601c0ce050200c3c010a09dc0a56050c0182f0a38144a0d01878021472a81014090601c64e0505024a80c03819c0a1c048300e060938141c0a0486c52067
  | 7, 0, 5 => 0x13014080a0183074e26028e4080a06019c30040512c18010a387c0a04050780223702810140300850cee2b0c01014030f051c0a0405198182932b814080a1c0307a64702828120c0381824e0502058060c00851c0a040e0c0180631b874080a1c0300e6270283838090601c0ce0507028126103819c0a040e180183d033814080a1c0307a5f7
  | 7, 0, 6 => 0x25014080a0180446e05021b0060c1e8f1c66040500c18460339ac0a250500c18017350880a0a0601c0ce1a02838140c14819c4c1802028061e00b814080d018307a3c7028101a0906004d2e4902894140306051c0a0401830022313b874080a0483052327028941a030600446e1d07028121b03819c0a040680c183a0a39a00a040183002147
  | 7, 0, 7 => 0x340ac0a040183028e2b0c010144b06051ce24902810060c0a3814080a18030dc6370289414030f00446e0502028600c329c1c32050203418010a3814080d0180802147028101409061bc64e0502028c00c1e9b9c3a040502436290338141c6d048300e067028f814030600446e0508024180703049c3a0405198180732b8141c0d0183002147
  | 7, 0, 8 => 0x281038350601c0ce2202838140c03819c0a040502418013bb814800a048300e06702894144b0600446e0502028600c329d9c0a0e05024182903381454250183002147130ac0a040680c18e04051d4061e00851c0a040680c3c010a38141c0a048300e747028101a033980428e1f0c0101a0c00851c30040500ce4010a38880a04050300e067
  | 7, 0, 9 => 0x3405050300e060938680a0e0e0300e0671307c0a040683002e0502028120c148c9c0a240680c18010a39e40a04051e00e147
  | 8, 0, 0 => 0x28941a030601c0c148028101403038182882809814080a1c03102148229780a040500c0e148130144a0a018300e06840014080a018307a0680d014080a0601c0c6980281014030d8d00c14829810144b0601c0c14802810147f061f8fa1480281090033e01c0c14802810144b3d81c0c148028101403061bc0c1480c01014032901c0c1480281038033081c0c1480f814087a0601c0c148
  | 8, 0, 1 => 0x987c0a040522c0c1480283814090601c0c5c8000680a0e050300e067029001403060a40c1480c01014300601914148028101a03060044614802894144b018300214802810060c038182827844814080a062200c1480281014033e00428878020290c030601c0c14800014080a018300e1770281014380601cfc148020710a030601c0c14822814080a018300e14802810140c4201d06148
  | 8, 0, 2 => 0x22a500a040500c0e14849814080a25830021481311430040500c18078132480a040500c0e06802958144b0601c0c148098141c0a048300e068130141c0a018300e32822814080a258300e23848874080a018300c148481140a04050c0181484781014030601c0c1480f874081c0601c0c14822874080a0186c0e1480281014030d8a40c14802810148e0d81c0c14802a3414030601918148
  | 8, 0, 3 => 0x13014760a018300e0680f814080a4f81c0c148028101a9e0601c0c1480290014090601c0c14809a64080a018300c1480e8101409060a40c69802810144b0f01c0c14809a75380a018300c148028f81403060f40c9b8098144a0a018300c23813014080a4d0300e0684c8101403060f40c9881f8141c0a018300e14822860080d018300e1484b8101403060a40c148028112c030601c0c958
  | 8, 0, 4 => 0x1981014030601cdc1480e81014030601c0c23809814080a048300c698028101a03060040c2382a81014780181c0c14813015380a018300e06802890140306004288785107c0a040503142148130fc0a040500c18078028101a03060054014809814080a01830dc1480281014090d81c0c148028101a9a0601c0c148228144a0a018780e148228141c0a0480c1807822860080a0183002148
  | 8, 0, 5 => 0x1304c0a040e00c1806809814080a3c0e0fc14855014081c018300e14813014080a5480c0e0680283814090601cca0682284c0a04051e00614824814080a018300c1481981014090601c0c69854014080a53a980c148028394a030601c0c148098141c1c018300c14802810144b0601c781482f014080a018f40c9b8028381438048300e06802a9014090601c0c69851814080a0486c0e068
  | 8, 0, 6 => 0x9814080d018314214857814080a0181c0c14848814080a01830641480283814090d81c0c698028941403060040e23802ab814030601c641480281014ad0f01c0c148028101403060e80e1482d814080a018300c14809860080a018780c1480281014032d01c0c1480fab00a0a0601c0c148028101a030600428ab815814080a01830468780004c0a0e0502418067028e4080a0601c0c148
  | 8, 0, 7 => 0x2981014033e01c0c1480281014030601ccab380281014ad0601c781480c8144a0a0601c0c1480281014033081c0c1480289414780181c0c1480c09414030601c0c2380281014035901c0c14822a74080a01a2c0e1485881014030601c0c238028101409060a4646980e81014030601c0c63802894d8030601c0c1485809414030601c0c14822815387a018300e1480281014360601c0c698
  | 8, 0, 8 => 0xc01014030f0040e14802ae414030601c0c1480281014b80181828b78020290a030601c0c148000147204050300c1470987c0a25050300c1480c01014090601c0c69802a9014030601c0c628028116c030601c0c1480281014030601c642381307c0a0e050300e068028101438060dc288780281038030601c0c1482281408b5018300e148028a808030601c0c1485a014080a0601d06148
  | 8, 0, 9 => 0x14080a061040e1472a8101403060a40c1480283814030601c0cbd80295814033e01c0c14822814080a019480e14800074080a0486c0e0670f874080a0601c0c1485e014080a018300c1480281176030f01c0c1481304c0a040529c06068000144a0a0183002237198101403062e80c1480e81038030d81c0c14800014080a01830741471307c0a04068300e0680289414030600428878
  | 8, 0, 10 => 0x61814080a018300c9b802810f4034581c0c1482287c0a040506c0e1480e8381403060a40c1482f30c0a040500c0c9b802810149a06004288781587c0a0405030288780202984030601c0c14822814081c048300e69860814080a0181c0c1486004c0a0405031081480281014030601c646380fa74080a0601c0c148028101403062fd7c878028383809018300e0681307c0a04050300e748
  | 8, 0, 11 => 0xf8604a0a0601c0c1481304cbc05020280606824814080a01830288780fac4080a0601c0c1480282812030601c0c128098141c0a018300c14802b180803060a40c14802b1408030601c0c14813014080d258300e0680281014a70181c0c148098144a0a258300c14813074080a0183052068098158804018300c1480987c0a9c050300c14822814080a1803114148028101a030600446878
  | 8, 0, 12 => 0x9814080d018300c14813015480a018300e068228159e0a018300e1481983814030601c0c1480e810144b0601c0c1480281014030600428ce8028101403060f40ccd80e81014030601c0ccc80289014030f01c0c1481304c0a040500c180680e81014036581c0c148028101a4b060040c148028e59404050300c1486487c0a04050300cc880e83814090601c0c1480f814080a0601ccac78
  | 8, 0, 13 => 0x2894144b060040e1480281014d60f01c0c1480289414030601c0cd5802810147801b500c148028116a033081c0c148098101475018300c1480f815a60a0601c0c148028101403290f40c9b8130cc080a018300e0680c01014030600428d280f814080a0601c0c2380f814080a0601c6414868814080a018300ec7809814080a01831a0148028941403060a40c1480d074080a018300e068
  | 8, 0, 14 => 0x28101a03060040e1480c094144b0601c0c1480281014660601cca6980281014030601c5e4e802b68140c0381828d982287c0a040522c0e148028ec1403060a40c14858810144b0601c0c1482284c0a043d00c181482284c0a040500c3c1480281014030601c0c14802b6014030601c0c23802810144f018300c1482f014080a0181c0c148028381403060a4641480e811ae030601c0c148
  | 8, 0, 15 => 0x28101409061bc0c698498144a0a018300214822a75380a018300e14813060080a018300e0680281014dd018040e14802810144b0601c0c23809874080a0480c180685881014030601ccadc80f814080d060042887802810144b0601c6414848014080a180300c1481307c0a0405030028780e81014030d81c0c1480c03814030601c0c1480e90014030601c0c148028101460060f40cdb8
  | 8, 1, 0 => 0x5881014ad0601c0c1480e81014030601c8e148028103830060191414802810143006018c6db835814080a01830028780c010144b01830021480281014e40181c0c14802810143030819141480281014037181c0c148710cc080a018307a06870814080d018300e0680289414030f01c0c14802811c0030601c0c1480281014df0181dbc1480c0101a030601c0c148131c40a04018300e068
  | 8, 1, 1 => 0x1981014780181c0c14802810149a0f01c0c14813014080a25830028787381014030601c0c14822014080a018307a06802a9014780181c0c14849814080a4d030021480281014ad0601c0c23809814080a3c00c0c1480289414030601c781480281014090d8a40c69822b98080a018300e14800014080d018300214744814080a063940c14851814080a1a8300e06848814080a0186c0c148
  | 8, 1, 2 => 0x281014030d81c0c63822860080a01831dc1480281014ed0181c0cec80281014eb0601d02dc822014080a018300e0684e81014034581c0c1480987c6604050300c148028101403060f4dc9b8028101aea0601c0c14802a70f4030601c0c1481307c0a0405030520680281014030f0040c2380283814660601c0c148028101a030f01c0c23874814080d018300e14802ba014030601c0c148
  | 8, 1, 3 => 0x281038030601cdc14809815e8040500c0c148518680a04050300e0680c01090030601c0c14868814080a018300edc80281014033081cdc14879814080a1c0300e1480c01014780181c0c14802029e4030601c0c1480283814090601c0c12809bc40a04050300c1480fbc0080a0601c0c1480c010d8030601c0c1480981014ef018300c1482d814080a048300c69802810143006019144e8
  | 8, 1, 4 => 0xf814080a0d81c0c1482287c0a9c050300e14802a901403060a40c148028116c090601c0c6980f814800a0601c0c1482284c3a040500c181480d0141c0a048300e0683881408030600428878028381403061bc0c148001100a040500c180670c0101403060042887809814080a7c00c0c1480987c3004050300c148028941403063dc0c1480281014037b01c0cf580281014093081c0c698
  | 8, 1, 5 => 0x2810144b0601ccadc80281014030605428fc80283814380601cfc148000141c1c048300e0672230c0a040500c18068198101403060a40c1482284d3a040500c181480f814080a0601ccafb8028101430060191414813014080a01830de0680f814080d0f01c0c148020290a090601c0c6980fbe8080a0601c0c1480d0141c0a0601c0c6981307c0a043d0300e06822815f20a018300e148
  | 8, 1, 6 => 0x2c081c0a048300e06871014080a018308c068228101475018300e1480f814080a060f40d01813014080a0186c520685184c0a0405024180680281015000f01c0c14878860080a0601c0c1480e89414030601c0c1480281014ff0181c0c14802b3c14030601c0c148132240a04050311006813014080a1c0300e7e802bf81c0a048300e068131140a040500c180787e89414030601c0c148
  | 8, 1, 7 => 0x8381014030601c0c1480f814080a3e01c0c14809814ac0a018300c148028116c030601c0c628028941403064180c1481307c0a040527c0e0680281014380601d0214813014080a258780e0680f81015050601c0c148028381c0a048300e068158144a0a01830288780283814090d81c0c14802810060c03818290488181014030601c0c6380001414090601c0c12709860080a258300c148
  | 8, 1, 8 => 0x1307d5805050300e0680289414030601c0c2380fc0c080a0601c0c1480283814032d01c0c148711140a040500c183d80296414030601c0c14822874080a0480c180780281014030f0047a1480281014600d81c0c1485889414030601c0c1480f814080a4581c0c1480281014030d81ccadc884814080a018300e658028101409060a40cdb80e81210030601c0c148028101409060a464148
  | 8, 1, 9 => 0x9814080a4f80c0c14813014080a019840e068028116a300601914148210101a030601c0c1480283814033081c0c1480281014090601c0c69819c2814030601c0c14809874081c018300c148198101403060f47806802810140306004741480f814480a0601c0c148028101a03062fc02148028101409060a46406822814081c01830521481316c0a040500c180684c81014030601c0c148
  | 8, 1, 10 => 0x2828060c03818290e88684c0a04054301806800060080a25830021478581014030601c0c1480281090380601cfc14802810149a0601c0c238070290a030601c0c14813014081c018300e0680281014781c01cfc1480e81014090d81c0c6980f814080a0f00428878228640a04050300e148130145404018300e0680c15814030601c0c148028396c030601c0c14822860080a018300e238
  | 8, 1, 11 => 0x28ec14030601c0c63815814080d018300e1480f8158c040601c0c1485a014080a0601e261480281014030601c0d128131280a040500c0e06802810060c008504e8782287c6604050300e1480281038030601ce81480281015118801c0c148028101a030601d42148028941a030600428878028f81403062e80c1482284c3e0502028181488781014030601c0c148132a00a040529818068
  | 8, 1, 12 => 0x28116a030601cdc1480f8141c0a0601c6414802bd0080a1c01cfc1488181014030d81c0c1481304c0a0e0500c180680281014038d0a40c14802c64140c03818291880e8103809018300e068028101478018f40c9b8131140a04050c0188a80f814080a8b81c0c14874814080a018780e148028122c030601c0c1480c0101403063b80c148028122a030601c0c1480281015140181c0c148
  | 8, 1, 13 => 0x28a808030600428878028101403038182920802c7c14030601c0c1480c010a0030601c0c148028116c780181c0c1488f03814030601c0c14822c74080a018300e1480283814030601c0c14874814080a01831dc148028101a03060dc0c148028101438060a4fc148130147c0a018300e0680281014788e01c0c14809814080a01c6c0c1482287c3004050300e1484907c0a040501c0c148
  | 8, 1, 14 => 0x281014a6062200c1480281014380f01cfc148028941a030f01c0c14802c8838030601c0c14822814ac0a018300e14802810143006018fa148028101a0306004286980281014030601ce8148028101a09018300214809ac4080a018300c1480e8101403060a464148028101a03060040214802c8408030601c0c14802810380306004288780281014090d8a40c1480e83814030d81c0c148
  | 8, 1, 15 => 0x20290a03060a40c148028116c03060a40c1483587c0a04050300e06893b440a040500c18078934940a040500c180780281014a90181ccadc8602d00a04050300e148028f8d8030601c0c1480987c0a040529c0c1480281014039201c0c148388ac0a040183028878028101403292e80c14815860080a01830288780281090030601c0c4e879c8c0a04050300e1481981014030601c64148
  | 8, 2, 0 => 0x28381430060191414855014080a01830521480f8141c0a0d81c0c148028102c030601c0c14891814080a0601d0214813014080a019480e0689481014030601c0c1481348c0a04050300e7e80281014039401c0c1480c814080a0601c0c1480281014780181c0c1480281014030f0f40c9b874a880a040500c1814802810d8030601c0c14822814080a4f80c0e148110680a04050300e068
  | 8, 2, 1 => 0x1981014030601ccadc802a9014030601ccadc8028101403060a40c148298101403060dc0c1487087c0a04050300e06822814080d01830021480202a58030601c0c1480f860080a0601c0c1480281256030601c0c1480281014039501c0c1482284c0a250500c181482287c0a04050307a9b809814080a258300c148131140a0e0500c180780289414030f0042887802029de030601c0c148
  | 8, 2, 2 => 0x4a014080a0481c0c14809a5c080a018300c1480f814080a0f01c0c23802810d8032901c0c14851814080a048300e068000880a04050300e0674a014080a018a40c14802810143006018e01480281014030f01c0c4e89701014780181c0c1480281014033d81c0c14809814080a568300c14891814080a3c01cfc1481981014030601c0d2d8028101403063b9421480e81014030d8a40c148
  | 8, 2, 3 => 0xc01014030d81c0c1480281014090d81c641489789414030601c0c148130141c1c018300e06802810140c2081c0c148028101a090601c0c6982d874080a018300c1480281014301c0307a65802810f4030601c0c1480281014030f01c0c148028e4080a06019141480283814090601c0c69802810140c2081cfc148028941a030601c0c238028101a0306004289b813275380a018300e068
  | 8, 2, 4 => 0x228141c0a048300e148131140a040500c18298028101403060e828878028101403060f48c0685601414030601c0c14802ccc08030601c0c14809954080a018300c14822014080a018300c9b8028103809060a40c6981307c0a25050300e068028101a03060042932800014080d01878021470281262780181c0c148588101403060f40c9b813114261f02810140c80281014030381829308
  | 8, 2, 5 => 0x22874080a048300e698028101409060a40c698028126a0d0183002148028e4080a180300c14802ab814030601c0c1484a074080a0181c0c14809814760a018300c1481304c0a040500c183284e81014030601c0c148028101a03060051414813014080a018300e74813014080a6e80c0e0680281268030601c0c1480281038030601c0c638028381a030601c0c14802810140906004d2878
  | 8, 2, 6 => 0x2810149a0601c0d39813015380a01a2c0e06800014800a048300e06702810143006018ec1480e81014039c01c0c1480290038030601c0c1480e8116a030601c0c1480281014380601cbe1482281594040503114148130140848018300e0689b81014030601c0c14802838800a048300e068000141c0a048305206748014080a278300c1489b01014030601c0c1480281014030601c2edc8
  | 8, 2, 7 => 0x1304c0a040500d1606802810140306004287780281014039f01c0c148028127a030601c0c1480281014030d81c0d3c80281014df0181e76148028101a033981c0c148518141c0a048300e0680289414380601cfc148028101a03060a40c14811014080a048300e068228741c0a018300e148028381403060a40c1489d01014030601c0c1480281014380601cc814813014080a0183068068
  | 8, 2, 8 => 0x28901a030601c0c148028101438060f4fc9b800014080a048305232702894144b0601c0c2382287c0a04051e00e1482284c0a040500c181480281014030601cca1780281014300619514dc80289014030601c0c14802810060ca001c0c1480289438030601c0c1480202a7e030601c0c148
  | 9, 0, 0 => 0x44814080a1800c18060a4814080a018300e060308e4561f02810140c038182920507028060c03818294390281014380601cca810a4814080a018300e320305244c0502028060c03d080d21f02810145d0601c0c149a0814080a0480c18070348147c0a018300e060a2ae4000502028060c3781829005020286003060f4ca069028101430018780e060a4c344c450281014030601e4260502028060c5f818292000f814087a0601c0c148
  | 9, 0, 1 => 0x144a0d018300e060a4014080a018328a070305244c130f814080a060182920502029be030f01c0c14902810144b018300e0611c84c0a04050e0060c32852400260289414030601c0d00502028060c03818c61490283814030601c641434ca400a04050c0060c0305240a0405024180703170d32e92284c0a040500c1814922814080a018300e1480c8003405020281807031a624c450281014030601c292050202807440601c0c149
  | 9, 0, 2 => 0x2240a040503110060a4014080a568300e060a26e40a040500c18070352c292051d828060c038182869909814080a01d2818060a4814080a01bd836070305243e0502028180703052932260281014030601c6469900014080a1c0300e7e0a40980a040500c18010a21e40a040500c1807192282928902810140c0381914149001140a040500c18070a40980a04051e00607031fa40a9c0500c18070305291347028101403065180c149
  | 9, 0, 3 => 0x281014030601c0d510a4d403a040500c18070305248a0502028060c038529f20502028061b03818289b922814080a258300e1443c915860502028060c038524000502028061b1481829045028101409018300e699028101403060f40e064dc814080a018300e060a2ae40a040500c1807035382923f0281014030601c28699a38983e05020281807034814080aa680c1807030526980502028060c038182921f02810140c1ea200c149
  | 9, 0, 4 => 0x9814081c018300c1434c8980a040500c18010321e4000502028121b038182901f02810140c0381828149028101438048300e0634c8000a040512c3c070305204c0502034060c038190f21302810140306019909b94c81014030601cca060a484c0a250500c18060a21e4b60502028060c03818292450281014034581c0c1490f87c0a04050300e060a4814080a1c00c1807a90525260502028061e038182920502070060c1e81c0c149
  | 9, 0, 5 => 0x51014080a018300c1443ca8c3e05020281807030526ae260281014030601c0d20009814080a048300c698028101403061bc0c14ab4b24261f02810140c0305243a040500c1807030510f21f02810140c03a200c149000980a9c0500c1807034014080a048300e65031a644c050202806a60601c0d226028101555018300e069028101a03060040c1443cc9c0a040500c1807a905248a0502028060caa01c292130281014030601aa6149
  | 9, 0, 6 => 0x49814080a01831dc060a48980a040500c18290305244c1f02810140c0381a9120502028060c039940d52954014080a530300e060a48980a0405198060c0381a40a04050e018073f052ad3580281014030601c0c1492281594040500c18070a484c0a040500c18ba030524260502028060c030517d2050202870030601cc414902810144b0601c0c14a4c9143e0502028600c0385244c0502028060c03d180d21f02810140c03818fc149
  | 9, 0, 7 => 0x2810149f0181c0d520a48983e05020281807031a640aca02028700c038182921f02810140c038191414991814080a018300e7e0a4814080d018300e060a15e44c1f0281014090601c0d34709814080a018300c1491307c0a04050300207034b0c0a040500c183d0326e43e0502028960c038182921f02838140c03818286990016c0a040500c18060a40000a040500cb4070305203e05020281807030182920512828060c0081c28879
  | 9, 0, 8 => 0x79814080a1c00c18070a4898260502028060c1e81a4260502028060c03051313230281014030601c0c14900014080a019840e060a407c0a040518018070305244c0502028060c03d49b92a20f814080a0601c0c1490f814080a018300e656e49148a130281014030605240a040500c180703052b521812828060c03818288790d014080a018300e060a4c948a0502028060c0385243e0502028180703564292b102028060c0381828879
  | 9, 0, 9 => 0x101485018300e060a4495a20502028060c0381a6b60502028060c03818292450281014300601d141490001408b6018300e060a4014080a018306e3d0305240a040512c1807031f8292000281038030601c0c1480281014030601cca146e4814080a018780e060a37240a040500c18070308d0f30302028060c03818289b9000145404018300e060a4014080a018300e320a21e44cc00281014030601c0d2005a014080a0601d06148
  | 9, 0, 10 => 0x7c3a04050300e060a407c0a040500c36070305243e0502028180703052bf20502028964b0601c0c1490281014030601c78146e4d780a040500c18070305248a0512828060c03818292130283814030601c0c1490f814080a0601c5e060a4d740a040500c18070305240a040512c1807030182920502028060c03994fcdc90281014030601c0d5c0a4814080a180300c8a0a36e48b410281014030601c292000289414030600428878
  | 9, 0, 11 => 0x281014090601c0c810a48003e9d0202818070305200a040500c360703050292260281014030f01c0c1490281038030601c0c14b1484c0a040680c18070305240a0405584060c038182920502028060c1e81c0c14902810144b0601c0c8a0a4874080a0183052060a1a64260502028060c030529122609814080a018300e0690281014032d01c0c14ab4d804c1f02810140c0381a4bc0502028063d038182921f7d01014030601c0c149
  | 9, 0, 12 => 0x2810147f0601e84060a4814080a018300e060a59a44c050202870030601cfd20502028060c038c828c7913014080a01832ca070348988a0502028070c0601e40a040500ca40703051572c909814080a018307a06909814080a0480c18060a4814080a018300e060a59244c0502028060c4201c0d20502028060c1b81c0c1490281014030601cca147dc84c0a040500c18010305240a040500c1807b18182922602810f4030601c0c149
  | 9, 0, 13 => 0x987c0a040529818060a48008a0502028600c4505203a0405214060c038182920061814080a018300c9b80281014030d81c0c7e0a48141c0a1c00c18070305243a0405024180703050d320502028060c0381829689198101403060040e060a4814080a018302a070305240a04050c0180631a282924509814080a01830289b90281014030601c0c1459c814080a018300e65453724260502028060c03050d33670281014030601c0c149
  | 9, 0, 14 => 0x13014080a018300e65034814080a180300d4e450526820502028180703052d33261304c0a040500c180690281014030601c0e060a4915500502028060c0385240013028381403060182900502070060c03818295695104c0a040500c18010a48980a04050e0060c0381a40a0e0500c180732818292000281014a70181c0c14864814080a018300c144dc8cc080a018300e060a1a640a0405174060c0381a033410f814080a0601c0d699
  | 9, 0, 15 => 0x7c0a04050300e320a40144a0a018300e060a26e40013028101a03060182912713014080a018300e069b71140a040500c18070a4814080a018300e060a5b640a0e0500c360703050d32001304c0a040500c180680281014030601cca067dc84c0a04055b0060c030525e6450f814080a0601c2920502028060c03818296b9028101403060f40c1480c814080a018300f6a0305240a040500c180719051f92450f814080a0601c28dc9
  | 9, 1, 0 => 0x28101403b98300e060a48980a040500c1807035a661a260281014030601c0d3720281014030601c0c149b004c0a040500c18060a48980a040500c18071e01a44c1361814080a018300d20502028603806018fa149028101403060a4641434c8004c3302028060c0381a2e20502028060c03818292050202860030601c64149b8014080a018300e060a48980a040500c3607031a64001f02810140c03818470050202ade030601c0c149
  | 9, 1, 1 => 0x2284c560502028060c0a48000a040680c18010385200a3b0500c1807030513720502028060c03818be14909814080a01832e8060a4814080a048300e0634b6e4000502028060c038182900502028120c038c828699001780a040500c0e060a4114260502028060c508525d213028101403060182927102810060c0081c0c14993014080a018300e060a48988a1f02810140c038524300405024060c038182921802028060c0081c0c149
  | 9, 1, 2 => 0x281014033e01c0c8a0a48004c1802028060c0381a2ee450281014030601c292260281014034581c0d48900014080a258300e0611c07c0a04050300f760305240090028101430060182901f028101430060f40c149028101403065d40e060a484c0a04051e00607030524001d02028061b038182900502028f0030381828ec9028101409018300e0634ca4c0a040500c18070308e43e05020281807030518f25e61814080a0181c0c149
  | 9, 1, 3 => 0x22814080a018300e145f4814080a01832f4070305240a04051e07003038182920502028060caa01c0c14909814080a01830021443c814080a018317e3d0326e4000512828061e03818290130987c0a04050300c1490281014030601ccadc43cde40a040500c18070305240a04051e07003039f82920502028120c038c80c69900060080d018300e060a4099680502028060c0381a44c450f814080a0601c0d2450281014030601ef0149
  | 9, 1, 4 => 0x28101a0d018300e060a48980a040500c3c070321e4261f02810143806018292051289014030601c0c14902b28080a018300e060a4814080a330300e060a1a640013028101478018182900502028060c03818297c90281014030601c0c640a4954080a018300e063f05240a04052b41807030510f20502028061e8801c0c149028101403065ec0e060a484c30040500c18060a21e40a04051e00607328182920000014080d0183002147
  | 9, 1, 5 => 0x28101430258300e060a4814080a7580c180732b7240a0405198060c039942924509814080a0183114149028101403bf8300e060a487c0a04050300e06a90525261f02810140c038182924509814080a018300c14922814080a018300e144c484c0a040500c18060a5fa43e05020281807728182921d02028060c03818297d90f8144a0a018300e060a4814080a180307a06450524261f02810140c328182920502028060ca3018289b9
  | 9, 1, 6 => 0xc0814080a018300e060a48144a0a2580c18070305243e054e028060c038182920068814080a018300edc813014080a018300e320a487c0a04050300e063e852400f30281014380601c2900512828060c038180c149028101430018300e656e48141c0a018300e060a36e6820502028060c038182920502028060c5d01828ab9132243e05020281807034b000a040500c18840385243e05021e8180703052913800281014030601c0c149
  | 9, 1, 7 => 0x60080a01830021443c6103e05020281807030527060502028060c03818292450281014030601c28c8960014080a018300e650a4814080a1c03002073f05240a2512828060c038182920512828060c03819141490281014380183052060a48141c0a0180c18070305243e0502028180703188292a8028101403060f40c149028101a030601c0c230a48980a040500c18070336e4340502028120c03818d33820281014030601c0c149
  | 9, 1, 8 => 0x1f814080a018300e060a49140a0405618060c0385240a04051e0f0030381829326131140a040500c180790289014030601c0c1443c8cc080a018300e060a26e44c0502028060c038c80d20502028061b148182869900014080a180300c8a0a4014080a1800c3607030524001f7d010140c03818290450c01014030601c0c1490007c0a040506c0e060a4014080a018300e060a61640a04050e018073f050d3226028101403860300e069
  | 9, 1, 9 => 0x281014090601c0c14b4c8980a040500c18070354643e05020281807035a4d320502028121b0381828699c3814080a018300e060a4db80a040500c18070305240a04050e0060c4201c292f30f814080a0601c0c149028ec14030601c0c8a0a4814080a018300e3240852400260281014380601cfd013028101403060f4ca0690f814080a0601c0c146e48004c450281014030601e04c054e028060c0381a9134713014080a018328c069
  | 9, 1, 10 => 0x7c0a040522c0e060a40159404050c0180645052546260f814080a0601c0d20502070060c038182895902813141c018300e060a48983e050202818074401a4b60502028060c03050d321f02810140c0381828fb9601143e050202818070a4814080a018300e060a62640a04050e0060c03994292000281014380601d02148028101438018780e060a4814080a6e80c0e06a705240a040500c1988038182920502028060c5f81c0c149
  | 9, 1, 11 => 0x281014780180c0e060a4814080a048300e06c605244c1f02810140c03819072004c81014030601c0c1480281014030601c0d780a4814081c0480c1807030524260502028060c03052932000289414030601c0c2380281014030601ccadc6e4814081c0183002070305240a040500cc20703050d320512828060c038182887902bd0080a3c00c0e060a4814080a018331607030524262b028101403060182921302810145d018300c149
  | 9, 1, 12 => 0x93014080a018300e06a948980a040500c180732b724000502028f038039f82900502029340c0381828879028101403060f40c144c4814080a568300e060a37248a050202b1c030601c292130f814080a018300c14913014080a258300e060a48101485018300e060a1a64000502028120c03818d302602810149f0181c0d5292287c0a040503108070a481408b6018300e060a1a668e0502028060c1e8182921f02810140c03818298d9
  | 9, 1, 13 => 0x1304c0a040500c1806a44b883e050202818070305248a0502028700c039f82921802028060c03818294991981014030601c0c7e0a49c456050200c18070305240b0207028060c038182924509814080a1800c1814922b440a040500c18070a484c0a040500c18063f052400450987c0a0405030291470281014030601c0c14909814080a0183110060a4814086c018300e060a2ae40a040500c360703051b920013014081c018300e068
  | 9, 1, 14 => 0x13014080ac880c180703486030040500c180703052466040500c1807032282921f02810147803818fc14922814080a018307a144dc8144a0a1800c18070305244c1302810140306018d32130e81014030601c0c1490281014030601f20060a48980a040500c18370381a44c13028101403060040d245028101403060a40e1492287c0a04050300e14b4c860080a018300e060a34a71e1802028060c0381829226028101403060f40e069
  | 9, 1, 15 => 0xb0098260502028060c034a8c0a0405024060c0381a5260512828060c038182920502028700c039f8289b922814080a018307a064dc814080a860300e060a1a640a040500c180703050d320502028060c0381828c890281014030664c0e060a48983e050202818070321e43a04050e0060c038182920502028060c0081c0c149a3b0c0a040500c18060a48cc080a3000c18070305240a040500c1807030529120502028060c0381829929
  | 9, 2, 0 => 0x28101478018f40e060a48980a040512c18070321e44cc30281014030601c0d29302810149a0601c0c1490281014030601c0c149cc8172a040500c1807030524aa040500c180703051b929022814080a018300e14922a240a040500c18070a48cc080a018300e060a65244c0502028068b03818292000283814030601c0c1480281014030601c0c62ab4874080a0186c0e060a1a6430040512c060c038182920074814080a01831dc148
  | 9, 2, 1 => 0xf814080a062100e060a4814080a018300f970305240a040500c1807030532d20502028060c039940c63922814080a2e80c18070a4814080a1800c19460305240a04052981807032282920502028060c03dd00c149028101403060f40c9b4dc814080a330300e063f0524260502028060c030510f20002810143006018fa14802810144b060040c1443c8000a040500c18073a05200a04050e0060c038c8293600281014030601c0c149
  | 9, 2, 2 => 0x281014030605452060a4814080a1803002064505244c0502028600c038191521f02810140c03995061490f814080a0601cca060a4814080a1800c18062e0524001902810140c03818290b444814080a0601c0c14900014080a3c00c0e060a4060080a018300f9803052430040500c1807030510f2450281014030601c2814900014086c018300e060a42243e0502028188803052554450281014030601c2921a02810140c0381828699
  | 9, 2, 3 => 0x4c0a040512c18060a44948a0502028060c0399640a3e0500c1807030513720502028f003038182956902810145d0601c0d8c0a4898260502028060c0326e40004053bc060c038182901d02028060c0381828db90281014030601f32060a4814080a1c0300e7e4505244c450281014030601cd33230281014030601cca149131140a040500c180103c9140a040512c060c0385248a0502028060c038182922622814080a018300f489
  | 9, 2, 4 => 0x48014080a018300e060a4814080a3000c183d0326e40a040500c180719051b739c1981014030601c0c14902813361c018300e060a4d804c450281014030601e43e05020281807036302920502028060c03818289b900014080a0183052060a4668260502028060c0305264e0502028060c03995b92b40f814080a0601c0c1490987c0aca0202818060a48003e180202818070305200a040500c180732995b921f02810148b0381829489
  | 9, 2, 5 => 0x281014030601c0c6234c89866040500c18070305240a040500c180703674292a20281014030601d421490281014030601c0c4e0a48000a043d00c1807030520000502028061e03818290000283814090601c0c6980281014030601c0ca10a49143e0502028183d0385240a0e0e00c180703050d320502028120c03818d2699028101409048300e0634c87c0a04050780e060a21e400a30281014090601c0d00502028120c0081c0c699
  | 9, 2, 6 => 0x28381409018300e060a480158050500c18070305200a0e0500c1801038182920515010060c03818288790f814080a0601c0c1455c91426050202870030605240a04050c0700c039f8292265104c0a040500c1806951814080a018300e060a4814080a018317e010a21e40a04050c0700c1e818292260281014030601c0c9891304c0a040500c18063f4b880a040500c19460305240a04050e018073f0518f2a215814080a018300e149
  | 9, 2, 7 => 0x28116a030601c0c8a0a484c0a0405198060c030525e60502028700c039f82920502028120c038193669900014080a04830520634c3440a040500c18070a37240a040e00c182903050d320502028061b038c80c14900274080a018300e060a4014080a0180c3607030525c43302028060c038182920502034060c0381828699131140a040500c18074dc814080a018300e064505240a0e0500c180703050d320502070060c0381828879
  | 9, 2, 8 => 0x9814080a018300c14b4ca8c0a04050241807031a640a0e0500c180703051372050710014030601c0c149000141c0a0183052060a4014080a1800c18070305240a0405024060c148182920502028060c008a40c149131140a040500c1807454e7c66040500c18070305273c0502028060c038182920502028060c0381828c79028101438018300f780a4814080a01830021434a1e48a1f02810140c038530b2130f814080a0601828c89
  | 9, 2, 9 => 0x281014030601c0c700a481409350680c1807030524004509814080a01830290050202870380601cfc1494e81014030601c0c14a448000a240500c18070305200a0e0500c18070322829204053bc060c03818289b94804c3e050202818060a4a8c0a0e0500c18070305240a0405680060c03818292f30281014030601c0c14913098260502028060c0348980a040500c18070328647e0502028060c038c82920502028120c0381914699
  | 9, 2, 10 => 0x14080a018300e063b0524261f028101430060182920502028060c03818287790281014030601f42060a4814080a0183052063f05244c450281014030601db9205020287003060f40c9b9
  | 10, 0, 0 => 0x7c0a04050300e880305240a040500c18070305136dca0f814080a1800c1807030528001f0f814080a0601c0c14900014080a018307a070326e4000502028060c0381828ab900014080a018300e06a705244c450281014030601c0c14a000000a04050e018073f0520000022814080a018300e1480281014030601c0c8a0a21e8000502028060c03818c614902810145d1800c18070305280a040512c060c038182887a00014080a018300e320305240a040500c1807030182887a
  | 10, 0, 1 => 0x9814080a01830020703052801230281014030601c0c1490281014030601cca060a26280a040500c183d0381c0c14a028101409018300e062e0528260502028060c038182948a000680a040500c1807030524012522814080a018300e149028101430018300e06450528001f02810140c038191414902810147f1c00c18070305284c0502028060c03818289ba028101430018300e063f05280a040500c183d1e81c0c14a000980a040500c1807a301a4001f02810140c03818fc149
  | 10, 0, 2 => 0x14080a018306e070305240013028101403060040c1490281014030601c0c623f05280a040500c1801039940c14a028101438018300e060a1a68000502028060c1e81c0c1490004c0a040500c18060a5224002609814080a018300e069028101438018300207030528260502028060c038182869a09814080a018300e060a322800000281038030601c0c14800014080a018300e650a3724000502028060c038184687909814080a0480c18070305280a040500c1807030510e87a
  | 10, 0, 3 => 0x4344c0502028060c0381a4016009814080a018300c14913014080a018300e060a05284c1f0281014030601c0c14a000004c130281014030601a000260281014030601cca06900014080a018300e07030525c40502028060c03818289ba000980a04050e0060c0381a40a040500c18070305028dca61814080a018307a0703052ac0130281014030601c0c14a0004c0a040500c18060a1a643e0502028060c0381828dca0004c0a0405024060c0305240a040500c1807328182869a
  | 10, 0, 4 => 0x28101438018300e060a26e801410281014030601c0c1490281014090180c18070305280a040500c180703050d2dba00114260502028060c0305248a050202870030601c0c14a68814080a018300e6503052800056501014030601c0c1490281014301800c180703052800050202812030601c0c699601140a040500c1807030529260502028060c038182887a000000a040500c18070305204c0502028060c03818fc14a004980a040500c18070305240a040500c18070322828dca
  | 10, 0, 5 => 0x13014080a018300e06a9052800000281014090601c0c69800014080a018300e06bc0524000512828060c03818288790d014080a0480c18070305284c050202860030601c0c14a00014080a1c00c1807328524000502028060c5f81c0c149028101430018300e060a3728001f02810140c0381828dc9000004c450281014030601e0260502028060c038194214a000cc080a018300e060a26e40000028101430060191414800014080a018300e060a61640026028101403860300e069
  | 10, 0, 6 => 0x130980a040500c1807030528000502028060c038182869900014080a018300e060a3224000502028060c0081c0c14900014080a018300e060a52240a040500c18070305136dba000980a040500c183d0381a40a04050e0060c038191414a0281014030601c0c146e3728001302810140306018fc1490051c0a040500c180703052544130281014030601c0c14a028101438018300e063f0528260502028060c038191414a0281014030601cca060a052800130f814080a018300c149
  | 10, 0, 7 => 0x28101403062fc020703052800450281014030601c0c149028101466018300e060a37280a04050c0060c039940c14a0007c0a04050300e650305240a04050c070030601c0c14a0281014030601c0c8a0a36e800000281014780181c0c14800060080a018300e060a21e40a040500c060c03818fc14a028101438018300e060a31e88a0502028060c1e81c0c14a0004c0a040500c18060a21e401600281014030601c0c149000000a0e0500c1807030520260502028060c038182887a
  | 10, 0, 8 => 0x14080a018300e06450524000507028060c0381828699028101409018300e060a1a6800a30281014030601c0c149028101403060040e060a1a680a0405024060c0081c0c14a02810140306004020703052800000281014030f01c0c14800014080a018300e065085264e0502028060c0381828dca1304c0a040500c180703052800900281014030601c0c149929140a040500c1807030528000502028060c03818289b9000000a040500c182903052000b40f814080a0601c0c149
  | 10, 0, 9 => 0xa040500c1807031f8289ba028101438018307a070305280a040500c180703050d287a000008a130281014030605200a040500c180703051369ba028101403060040e0645052800f30281014030601c0c1490281014030601c0c144d9a6800050202860030601c0c149028101403060040e060a26e8000502028060c0381828c79
  | 11, 0, 0 => 0x50202860030601c0c1490281014030601c0c8a0a4814080a018300e060a26e48a0502028060c038182920502028060c0381828699028101403060040e060a48000a040500c18070305200a040500c183d038182920022814080a018300e148
  | 12, 0, 0 => 0x281014030601c0c148
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 58
  | 7 => 67
  | 8 => 76
  | 9 => 85
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffff000000000000ffffffffffff, 48)], [(0x5400800a01555400800a01555400800a01555400800a0155, 1), (0x2a85541500000000000000002a855415000, 47), (0x1542aa0a80000000000000001542aa0a800, 49)], [(0x1542aa0a80001542aa0a80001542aa0a80001542aa0a800, 1), (0xa801001402aa000000000000a801001402aa, 47), (0x200000400000000000000000200000400, 48), (0x5400800a01550000000000005400800a0155, 49)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 96)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 96 true (goal 96) u ys) :
    NatRunT 96 true (goal 96) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 11 0 (NN s)

def poolG : List Nat := [24780855498085475, 24803893669154962, 78847102114955362, 77710216756563041, 23654905124323426, 24780804994465892, 66439164936162401, 24803893651275922, 66491940419504224, 66440212908182625, 11293107704402018, 11293146329755747, 65313213459303521, 65313253231789157]

def Z (s : Nat) := bar 96 true S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)

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
private theorem z7_144 : ∀ i, 144 ≤ i → i < 150 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 144 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 150 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 z7_24)) (range_split (range_split z7_32 z7_40) (range_split z7_48 (range_split z7_56 z7_64)))) (range_split (range_split (range_split z7_72 z7_80) (range_split z7_88 (range_split z7_96 z7_104))) (range_split (range_split z7_112 z7_120) (range_split z7_128 (range_split z7_136 z7_144)))))

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
private theorem z8_376 : ∀ i, 376 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_384 : ∀ i, 384 ≤ i → i < 392 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_392 : ∀ i, 392 ≤ i → i < 400 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_400 : ∀ i, 400 ≤ i → i < 408 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_408 : ∀ i, 408 ≤ i → i < 416 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_416 : ∀ i, 416 ≤ i → i < 424 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_424 : ∀ i, 424 ≤ i → i < 432 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_432 : ∀ i, 432 ≤ i → i < 440 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_440 : ∀ i, 440 ≤ i → i < 448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_448 : ∀ i, 448 ≤ i → i < 456 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_456 : ∀ i, 456 ≤ i → i < 464 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_464 : ∀ i, 464 ≤ i → i < 472 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_472 : ∀ i, 472 ≤ i → i < 480 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_480 : ∀ i, 480 ≤ i → i < 488 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_488 : ∀ i, 488 ≤ i → i < 496 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_496 : ∀ i, 496 ≤ i → i < 504 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_504 : ∀ i, 504 ≤ i → i < 512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_512 : ∀ i, 512 ≤ i → i < 520 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_520 : ∀ i, 520 ≤ i → i < 528 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_528 : ∀ i, 528 ≤ i → i < 536 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_536 : ∀ i, 536 ≤ i → i < 544 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_544 : ∀ i, 544 ≤ i → i < 552 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_552 : ∀ i, 552 ≤ i → i < 560 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_560 : ∀ i, 560 ≤ i → i < 568 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_568 : ∀ i, 568 ≤ i → i < 576 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_576 : ∀ i, 576 ≤ i → i < 584 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_584 : ∀ i, 584 ≤ i → i < 592 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_592 : ∀ i, 592 ≤ i → i < 600 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_600 : ∀ i, 600 ≤ i → i < 608 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_608 : ∀ i, 608 ≤ i → i < 616 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_616 : ∀ i, 616 ≤ i → i < 624 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_624 : ∀ i, 624 ≤ i → i < 632 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_632 : ∀ i, 632 ≤ i → i < 640 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_640 : ∀ i, 640 ≤ i → i < 648 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_648 : ∀ i, 648 ≤ i → i < 652 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 648 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 652 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 (range_split z8_24 z8_32))) (range_split (range_split z8_40 z8_48) (range_split z8_56 (range_split z8_64 z8_72)))) (range_split (range_split (range_split z8_80 z8_88) (range_split z8_96 (range_split z8_104 z8_112))) (range_split (range_split z8_120 z8_128) (range_split z8_136 (range_split z8_144 z8_152))))) (range_split (range_split (range_split (range_split z8_160 z8_168) (range_split z8_176 (range_split z8_184 z8_192))) (range_split (range_split z8_200 z8_208) (range_split z8_216 (range_split z8_224 z8_232)))) (range_split (range_split (range_split z8_240 z8_248) (range_split z8_256 (range_split z8_264 z8_272))) (range_split (range_split z8_280 (range_split z8_288 z8_296)) (range_split z8_304 (range_split z8_312 z8_320)))))) (range_split (range_split (range_split (range_split (range_split z8_328 z8_336) (range_split z8_344 (range_split z8_352 z8_360))) (range_split (range_split z8_368 z8_376) (range_split z8_384 (range_split z8_392 z8_400)))) (range_split (range_split (range_split z8_408 z8_416) (range_split z8_424 (range_split z8_432 z8_440))) (range_split (range_split z8_448 z8_456) (range_split z8_464 (range_split z8_472 z8_480))))) (range_split (range_split (range_split (range_split z8_488 z8_496) (range_split z8_504 (range_split z8_512 z8_520))) (range_split (range_split z8_528 z8_536) (range_split z8_544 (range_split z8_552 z8_560)))) (range_split (range_split (range_split z8_568 z8_576) (range_split z8_584 (range_split z8_592 z8_600))) (range_split (range_split z8_608 (range_split z8_616 z8_624)) (range_split z8_632 (range_split z8_640 z8_648)))))))

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
private theorem z9_424 : ∀ i, 424 ≤ i → i < 432 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_432 : ∀ i, 432 ≤ i → i < 440 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_440 : ∀ i, 440 ≤ i → i < 448 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_448 : ∀ i, 448 ≤ i → i < 456 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_456 : ∀ i, 456 ≤ i → i < 464 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_464 : ∀ i, 464 ≤ i → i < 472 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_472 : ∀ i, 472 ≤ i → i < 480 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_480 : ∀ i, 480 ≤ i → i < 488 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_488 : ∀ i, 488 ≤ i → i < 496 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_496 : ∀ i, 496 ≤ i → i < 504 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_504 : ∀ i, 504 ≤ i → i < 512 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_512 : ∀ i, 512 ≤ i → i < 520 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_520 : ∀ i, 520 ≤ i → i < 528 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_528 : ∀ i, 528 ≤ i → i < 536 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_536 : ∀ i, 536 ≤ i → i < 544 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_544 : ∀ i, 544 ≤ i → i < 552 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_552 : ∀ i, 552 ≤ i → i < 560 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_560 : ∀ i, 560 ≤ i → i < 568 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_568 : ∀ i, 568 ≤ i → i < 576 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_576 : ∀ i, 576 ≤ i → i < 584 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_584 : ∀ i, 584 ≤ i → i < 592 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_592 : ∀ i, 592 ≤ i → i < 600 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_600 : ∀ i, 600 ≤ i → i < 608 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_608 : ∀ i, 608 ≤ i → i < 616 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_616 : ∀ i, 616 ≤ i → i < 624 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_624 : ∀ i, 624 ≤ i → i < 632 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_632 : ∀ i, 632 ≤ i → i < 640 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_640 : ∀ i, 640 ≤ i → i < 648 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_648 : ∀ i, 648 ≤ i → i < 656 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_656 : ∀ i, 656 ≤ i → i < 664 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_664 : ∀ i, 664 ≤ i → i < 672 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_672 : ∀ i, 672 ≤ i → i < 679 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 672 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 679 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z9_0 z9_8) (range_split z9_16 (range_split z9_24 z9_32))) (range_split (range_split z9_40 z9_48) (range_split z9_56 (range_split z9_64 z9_72)))) (range_split (range_split (range_split z9_80 z9_88) (range_split z9_96 (range_split z9_104 z9_112))) (range_split (range_split z9_120 (range_split z9_128 z9_136)) (range_split z9_144 (range_split z9_152 z9_160))))) (range_split (range_split (range_split (range_split z9_168 z9_176) (range_split z9_184 (range_split z9_192 z9_200))) (range_split (range_split z9_208 z9_216) (range_split z9_224 (range_split z9_232 z9_240)))) (range_split (range_split (range_split z9_248 z9_256) (range_split z9_264 (range_split z9_272 z9_280))) (range_split (range_split z9_288 (range_split z9_296 z9_304)) (range_split z9_312 (range_split z9_320 z9_328)))))) (range_split (range_split (range_split (range_split (range_split z9_336 z9_344) (range_split z9_352 (range_split z9_360 z9_368))) (range_split (range_split z9_376 z9_384) (range_split z9_392 (range_split z9_400 z9_408)))) (range_split (range_split (range_split z9_416 z9_424) (range_split z9_432 (range_split z9_440 z9_448))) (range_split (range_split z9_456 (range_split z9_464 z9_472)) (range_split z9_480 (range_split z9_488 z9_496))))) (range_split (range_split (range_split (range_split z9_504 z9_512) (range_split z9_520 (range_split z9_528 z9_536))) (range_split (range_split z9_544 (range_split z9_552 z9_560)) (range_split z9_568 (range_split z9_576 z9_584)))) (range_split (range_split (range_split z9_592 z9_600) (range_split z9_608 (range_split z9_616 z9_624))) (range_split (range_split z9_632 (range_split z9_640 z9_648)) (range_split z9_656 (range_split z9_664 z9_672)))))))

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
private theorem z10_104 : ∀ i, 104 ≤ i → i < 112 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_112 : ∀ i, 112 ≤ i → i < 120 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_120 : ∀ i, 120 ≤ i → i < 128 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_128 : ∀ i, 128 ≤ i → i < 136 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_136 : ∀ i, 136 ≤ i → i < 144 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_144 : ∀ i, 144 ≤ i → i < 152 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_152 : ∀ i, 152 ≤ i → i < 155 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 152 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 155 → Z 10 i = true := (range_split (range_split (range_split (range_split z10_0 z10_8) (range_split z10_16 (range_split z10_24 z10_32))) (range_split (range_split z10_40 z10_48) (range_split z10_56 (range_split z10_64 z10_72)))) (range_split (range_split (range_split z10_80 z10_88) (range_split z10_96 (range_split z10_104 z10_112))) (range_split (range_split z10_120 z10_128) (range_split z10_136 (range_split z10_144 z10_152)))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_0 : ∀ i, 0 ≤ i → i < 8 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_8 : ∀ i, 8 ≤ i → i < 9 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 8 = true)
private theorem z11 : ∀ i, 0 ≤ i → i < 9 → Z 11 i = true := (range_split z11_0 z11_8)

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

end PEqualNP.Outside.L_meta_8535_aux

theorem PEqualNP.Outside.L_meta_8535 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_8535_aux.Main.noCircuit
  exact ⟨C, hfan, by omega, hev⟩
