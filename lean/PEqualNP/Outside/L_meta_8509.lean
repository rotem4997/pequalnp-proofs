import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8509_aux

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

abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)

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

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK (k : Nat) (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) &&
  (moveBits p.1 p.2 (mask k) == mask k) &&
  (moveBits p.1 p.2 (goal k) == goal k)

theorem applyMoves_run {k s} (ms : List (Nat × Nat)) (hok : ms.all (moveOK k) = true) :
    ∀ ws, NatRun (mask k) (goal k) s ws →
      NatRun (mask k) (goal k) s (ws.map (applyMoves ms)) := by
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
    simp only [moveOK, Bool.and_eq_true, beq_iff_eq] at hp
    have h1 := move_run h p.1 p.2 hp.1.1 hp.1.2 hp.2
    have h2 := ih hok.2 _ h1
    have e : ws.map (applyMoves (p :: ps)) = (ws.map (moveBits p.1 p.2)).map (applyMoves ps) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact h2

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

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil =>
    simp [sumBelow]
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
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f (goal k))

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl]
      by_contra hb
      have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hb)
      exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)) hsum
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

def pickMin (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk img
    if h < bestH then pickMin orig rest img h else pickMin orig rest best bestH

theorem pickMin_run {k u} (orig : List Nat) (h0 : NatRun (mask k) (goal k) u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all (moveOK k)) = true →
      NatRun (mask k) (goal k) u best →
      NatRun (mask k) (goal k) u (pickMin orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    unfold pickMin
    dsimp only
    split
    · exact pickMin_run orig h0 rest _ _ hok.2 (applyMoves_run ms hok.1 orig h0)
    · exact pickMin_run orig h0 rest best bestH hok.2 hb

def rowsG : List ℕ := [1, 1, 1, 4, 8, 8, 32, 74, 74, 74, 74, 74, 138, 138, 138, 138, 138, 161, 161, 161, 161, 161, 164, 164, 92, 156, 10, 10, 10, 10, 12, 12, 12, 24, 33, 33, 33, 33, 33, 36, 36, 65, 65, 65, 65, 65, 2, 2, 2, 4, 16, 16, 32, 81, 81, 81, 81, 81, 145, 145, 145, 145, 145, 162, 162, 162, 162, 162, 164, 164, 92, 156, 17, 17, 17, 17, 20, 20, 20, 24, 34, 34, 34, 34, 34, 36, 36, 66, 66, 66, 66, 66, 32, 64, 64, 128, 164, 92, 92, 156, 156, 24, 36, 68, 68, 132, 160, 28, 88, 88, 152, 152, 3, 5, 9, 5, 9, 40, 40, 75, 78, 90, 106, 202, 139, 142, 154, 170, 202, 163, 165, 169, 177, 225, 165, 172, 93, 157, 11, 14, 26, 42, 13, 14, 44, 25, 35, 37, 41, 49, 97, 37, 44, 67, 69, 73, 97, 193, 3, 6, 18, 6, 18, 48, 48, 83, 85, 89, 113, 209, 147, 149, 153, 177, 209, 163, 166, 178, 170, 226, 166, 180, 94, 158, 19, 21, 25, 49, 22, 21, 52, 26, 35, 38, 50, 42, 98, 38, 52, 67, 70, 82, 98, 194, 96, 96, 192, 192, 228, 124, 220, 188, 220, 56, 100, 100, 196, 196, 224, 60, 120, 216, 184, 216]

def xsG : List ℕ := [0x812f00ffe07efe477e109f000000000f007fe03e7c003e0007, 0xfbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff80, 0xbdf016272f108428589cbc4210a0bdf006070f000020181c3c00008, 0xf83e000884c410800913ff89fff4f83e000080c000000003ff01ffb0, 0xf83e0244ffe27ffd002213104200f83e0000ffc07fec000203000000, 0x5ceb347f483fa11811fd20fe84600441107f003f801001fc00fe0040, 0xb7d7ff90004843e03e4001210f8031866f80004003e03e0001000f80, 0xe71dc80000bffe00200002fff800c619800000bffc00000002fff000]

theorem rowsG_len : rowsG.length = 224 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 112 := by decide +kernel

theorem maskG : mask 112 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 112 zs &&& lo 112) ≠ lo 112 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 112) (goal 112) s xsG) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 112) (goal 112) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 112) (goal 112) s xsG) :
    ¬ HasCircuitSize 8 fG 11 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 11 h
  have hr : NatRun (mask 112) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 6 => 98
  | 7 => 590
  | 8 => 1781
  | 9 => 1125
  | 10 => 51
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0x75860ea6726c6c4d70c027fd6aa8ce9969e3b2df6848be39676fe6dd6555db5c5a1fe7ea58a413345684c02c55bea2e55413f3f951b9d0b54db212d44d29b17a4b130ccd4aa3503b46f7fdb143bbee7f422056bd40f4154c3f41339c3ed0e3aa39f7f61d38c7e72037fd4dde36c09e8f3628e11935bb60d9316cd70e30dcecc92fb849cc2e33c2e42d3aed222d34923d2d2778282c57ca0f280b776527d64a8d26d2c5412649049a25fab4ce245f1d0c2268218420b3c85d1fa601e71d8ad31d1b1c58fe1ad41b49113773950fe739740fd9a3550e5b1de00dd73f550db517eb0d6ef9e70c05aec00bb0e4d00a0cb4f709964f0b07758f850277537e01aad51c
  | 6, 1 => 0xfd747e6ef5e61e39de2794cbdbb71918d95c5055d64b9bbcd329d2c5d3079d6eccaa882dc999d394b2cc5043b004e9a0ae3c3108ab246820a852837ea8119c7d9de42b8e9db7f2779c95f19d9bc8fcc495ffdf01952e46f1951bd0729159dcbf8bc865de8a2d196584d67d5682cdca3d8022f1dd7e07c3137d7b513d7cfb6f2077ccc6d076910ebe
  | 7, 0 => 0x1372a35e136030f81323fa98130c2a2f130bf3a112ff0acf12c2d98312b7f896126993e11232f5c611f8172e117656f910cdc5e010c98b760f34296f0ec5e9ba0ebab4230e9adfb60e4aaf9b0d1df0770d1a749f0c607b630c5c9f060c0bfb5e0c05aec00bf12df60b91bec80b7586b80b41c3b80a5b380d0a5839300a51155508159b3707cc7fcb07bc3206078a1523076d4ea30736fc350704782e06c0db3606a74e3c0640f919063c6f2d0637183d0629624f05b243d9059a51e50536520d04cc8a110468a96d0453c8940413cb2d0379132c02bba52c024e8e950237f57602356d120224ea5801ba6b7501591cd0013798fe011d5576010ad0f2010553e1
  | 7, 1 => 0x2407b67f23f7458223acc85e23a2fbc0239f7ea8234611cb230ffe1022d2f463229d22f1226dd630221bd5fc220d74f821d3d44c2144c3bb210078a120930c1d2081bffc202e07051fee48221fe78a4d1fced0291fa7e5e01f73d5391eaeb83c1e7c7fe61e4ee7801dcff68d1d8f00fe1d79fff81d4425181cf2486e1cdb72311cb4a4801c0d6bf51be1b4da1b38d30d1aed1f501acdee901aa51f111a7ac41d1a73c18019ef3a05196db64a19627e2d1953d6601947d0e21935113c1912aa341867697f17caae9b16ab4780163a7d6a1637ec981614ffd6160fe9da15c6c3c515a6b6111561df8a14e99007143e9119142e18ef13e120c213abe5bb13a62117
  | 7, 2 => 0x37d5fa0e379c60c6375083d23736c8a73719cff33677642f35c5bbde35b9177335aac1a23480fade34252d073418493933ca3b943345617a330f82c232ea5e5f325beed9323921353233755d31cf74c6319d50c931335e3e3126790631181faa3117cdbd3102f232303e54ab2e9f66ee2e81d6202e1910452d7de24c2d7432e72d44f09c2d18451e2cd082f92c9c4d732c8830682bf5de5c2bbb28aa2afc76b02ae58ab82acb1f7629eca70b2983dc2029433d1e291bbb952884955127d0f5b527cb919c27c35c3727a01d4b2790b59c2784746a2751f3d226e76164269e408a25da60b5258b8bd42536ed7e2531efae25272e5d24ac7aff248605232416365e
  | 7, 3 => 0x4a9e45ef4a17027148e67a5a48ddbf9b48b6690147c7133f475c6fda4751910f4730cb95470501a7461c01c44608a26a457a7e1d4575ba7245619b9a454c54eb44e8177744b5034d449f4baa44628a0d4386c66e43681714432112cf43033bf942e1721842d4cb4042b36e91426658b34232e4bd4227e242421b632141a8d4b141a336c4418be2894179868c41766b744165b31441438baa4114198840ebdbc3409b09e740963a6d407e35273f7c5d1a3f6491f53f4569033f3f588f3ee82a7b3ec03c8d3e59a9bd3e53dc513d24c2ca3cf1b75f3c63e9273b72e3663b5111163a3ae0dd3a395fc839ec86b739c98a8239455b0b38af36c7383bf28a38219788
  | 7, 4 => 0x5ece1dfa5e7fde6b5e5b6e425e19954d5ddf7ef45db819325db4f41e5d80e92d5cbc471e5c9cdc965bcf67655b82b2b65b7516f45af5f0125af29c4c5a44084659d7785959b20d1458a41334589eae5e583103bf573f482a5717888456d5925d5657f4b7560ecf7255f0122655c846be555810bf5520640d541b1f0153ed21d75389a1ef53678eb8534ea5d3532a0d7e532940b75318243752df5d8d52cd693752b90ab8525373fa51dd22d651b9d0b551856e6950ea9be8507c596f5056e7144fb504214f04c6644ec34ecc4e90ac394e5ff0d74deb1ba54d27b70a4c5dc8e14c4a33274bd0f8f44bc0ead04b7b5daf4b72a2534b7204b54b5737574afe1ba7
  | 7, 5 => 0x78f2562b78b3d5fd77ca495f776d795c773d908c7715cf9a76ddcb63766d956475ebcc347551be8b749f2694748a93fd737c136f73212dc972cfa75b72c3bec77279e00a70a94af970a7b732709828d9708473817051f2127029fb0f6ff565836fb47e826f77a9a76f75757c6cb3653e6c8c3ce46c6e3f546c39d2846b8bc19d6b71d7fc6b5650f76b4459b66ae556416a552b626a04092969b754d869b184ee682faf0c680a837a66d6995d666bd7dd6667633265c3c4296555db5c652748376465040d6399bd0763830eff635d78b96353de3e62df3e96629131c7620d991b620093a361c236a360f0849060c960e160b89b545f9125b55f7eb34f5f121ee6
  | 7, 6 => 0x949f5e439384b0519341882792b6ef95924a6a8a923a841b91cd00878f9983008f5503de8e1e755a8de9d4af8daa64e08d039a0c8cb65d728c7f0d5d8b6272f68adfe1d48a9d7aec8a5104258a2838df89c6b86e898e561f898d15f0894d16a488a897838850b40a8788139f875eb699870d2f6985b0e11c85a41e538548447485369933851b3e3b84c0d0df8450402584463821842bbc5083a4535a832c74fa832160e782fca0a182f7f46482ef7685825e6287820535f58166bd7c80d71d9a80d339b980b8253980a6a56e808d6ef3801c2c037f4f6b6c7f2ba8327df563bd7dce434c7daf57197c8cf9717c79513f7beec68d7b4e38367a0747c77991156d
  | 7, 7 => 0xb59d5403b42e1d15b3bd5d7eb3718f03b2f5b363b2cc5043b1d50698b18c101aaf93973caf584fe3af403ec2af2da470aeccb513ae9df677ae9aaa67ae8e63b2ad6e3d98ad5cb2b5ad552c3aad44e75dac5f51a8ac0bc40fab5b3a8faa843a20aa814221aa353adda93a9173a927fbc6a8eb8bdba7c2493ea735a090a677e3a6a61df778a5b8ea76a57c28d9a562272ba3af1cfca2a58155a1a2065ba17ecd01a14791ada12e120ea0a6e297a07f68efa02330bf9fd237e29f43dda19e98107c9e9624bf9e2559849e0d312c9d9943df9c4610309c3c9a719bc96c379b35964b9a4858219a24bae1999a4e1298e8799c9868fc6e95c7c9f695b7cad49505f38a
  | 7, 8 => 0xeb5370bfe846b269e6a6ad5ce653c6a8e3b6932ee2336a8ddf7c9b9cdf649656dda83c3cdd582e02dd230931dc18091bdba0103cdb976de9d9332863d872c9b1d7056b00d6a06642d4689318d0f31da1d0b5d5f5d0914873cf512ea2cf2c4cb9ce942d0ace89a0cdcd3b2eaacd017873cb1da7f5cafdde8fcafc89dbcafbef78c9e2d7dfc9b88f1ec80d48e4c7f18434c78101fec72bd723c5d2d8c3c57d08f2c54b3924c4e5a416c4c0c1e4c4391d57c142b988bfb1eeefbf66007dbf56d99dbecdeb7cbd662f7abcb6ab30bc2a8647bbddc423bbadd72dbb3a3f86bacbabe0ba2276bdb9c43e24b864f115b84d7cb9b8484819b7ef3129b711c224b65c3dfc
  | 7, 9 => 0xffb1af48fcc5e023fbb1f641f93d3035f8709a55f6b529f1f6244f51f58cc70df4c86eb0f221d814ef57b866ef381426ee9b6550ed6d9e74
  | 8, 0 => 0x50fc94104d81b6f04d3d56504cf37dd0471082a04322854042aaa3c042928cf041fbc3703ecb1de03e78f9003cadaf4039fd45d039eacdf039572e7038cee8c0370ca3a03640bd303604e71035c4dd80354148e03354ac0031e98f5031c2c7802f3f31b02f395a002ea679402d7a32302d0cdd902b7098d02b2c8e702ab6709028044260275b63802636272025e2fc2023ab06d0233c44f021ffc1a021aaa8502181491020ee0010205dd1d01e9505001dbe7d201dae3f701a48ffe018caeff015d01d1014afa5a013e3130012eef070126b07b01140934010af71100c1486a00ba0fe90078f3170076c93e00599eb900539b890050057a00373c180009aed1
  | 8, 1 => 0xc5c9f060c505eee0c4f70980c3f9a2f0c3e70f20c013d750b9dee570b8220ee0b79e4ed0b531d8b0b03343d0ab72c1f0aa1ed8d0a93dec40a8c18040a5c12560a3319670a2eda0609f7be2909f0580809e1d3d609d8c5c809c3fe1609b2be1e09b100bf099eb8fa095bb0d00908ca640903756e08eb8e3708c62dc208af172d08a8a59308a687170883162708734cf8081824ea080de25307b85b6107af7af407998ac007754ddf0760ed1407350da707338c9206ebaf8e06e9c5b206d7e36f06d6f38306869f750659c57f060fb4d505cc2e4205cbf31b05c9f72c05bf0e4205b23dd7056038cd055b73400551707c054a3ad405429d32052b41f305229ee3
  | 8, 2 => 0x11d53e7d11c9381211c4683d11b2499f11a5e27211694b47115f1ef6115b8510115276d2114e777a1136b0001136a79e11350c01113018c41129a753111b1405110df59710e9930a10d4405410bcdbaf10b76be6105a0a19104bb198102dbbb1101f96f8100e17ae0ff64ac60ff23e8c0fe71cbd0fb619aa0f5d37720f220cc10f1c60ab0f0f20a90ef6d6660eef57430ee3d6880ed46cfa0ebf9a950eafe9370e8df8610e8465e90e71f3110e68e5030e640ef20e524ed10e2ed9ab0e0609f60e0478b30dde3e570dd0a5920dbc46a40db1e4fb0d984ffd0d8da1aa0d77517f0d5f24990d4495570d159afa0d0b4eb10ccde00d0ccc2d190ca844250c8700cd
  | 8, 3 => 0x1805247817f5513217db7b9217d4878a17beff55178bdec9177d04971763ff53175e8638175b45d01708385216d910a81676ed6d166c128f1660e8e3163ef01916101ae115eba44b15d13aea15c2723515bbb03f157f302a156104eb155062b9154a954d1546943e153e89fc153e084e1535818315059d1314ff3f5914f0d8a814ed18a914d7d52614d0cbea14cd4ca114c43e93149eef231482c127143997e714338a18142b45f414109a0c1406063b1402d94d13fcd95313e2d6b513e2a95b13c8ad5a13a953c113a7f01613a54e281392961b13911f051353851b1340e79e13386f6c1311494313039db512ff4a37129af3bf12954e3d126e5d921269f0d4
  | 8, 4 => 0x1e09b2b21dffb62b1ddc9cf51dc25eac1d95083c1d86a5b71d654d611d5fc7501d53fa321d4f33d91d4b2fc31d45c0971d4425181d2ac81c1cf74f401cebb7211cb4a4801c91ce821c7776991c6182821c5ee8f71c540df21c30a5951c1dcbc51c0f248f1c0c8e841beb650b1be493891bd5262d1bb0d92c1b966ee11b7b71891b7415901b297e571b09578b1ade1c951ac3f6751abb063c1aad75f71aa51f111a871edd1a42f4631a3bcab81a38439819fda42419d6b37919ce278919c913c019c1a5a819ba8cfb199ceb13199285bb198d6e251983754719799377194c7dba190e1b8418c9b722188444c61862ca4a185d663318585c8e183a90f118182cac
  | 8, 5 => 0x24650c4224582a86244b40842445dba52437f6852419bbaa2400e6d523bc45f823a2fe152353baf2233640dd231b2ead22e62c2a22c6eaa022b433e322b066a22282ea0d22716fd1225277702246be9b223faa5c2225277721e6ea4b21dff04c21d5dfd221c27ed021b8ce7021add1d82180fef22150439c214ef5b7214b3c652144c3bb21367d702125669a21171a4b208793fb205d54c520594fb620570a3620536dc12037901c20320d09202981192016f8362015ce8520114e591fee1e061fcf33471fa473f81f4da0c41f35793c1f0b316e1f00511d1ef434b01ee6a87e1ed04b6f1ecbe9f31ec0cb571eb524761e6491211e5932fb1e5561101e26f737
  | 8, 6 => 0x29d8d09e29c49bd229b2c31529b07b2029a81b95298d7d5e2977dcb0295033db2948abe1293e35b9292c88402900cd8d28e3970528d4cb0628cad48428c7a42828b46758289144b428808107286916092856e2742853fd0828313962280cfde427c6601827a497ae27a01d4b2786413027764ca327723a702755631a27529804271ded2c2717df4b2701104b26ef529a26e296ab26cbe4b526c2dced267b49612671129b264a573a26343fda2629a5ce26156f3925e5a67025e2351a25df14f225d840db25c188e2258921e22586f127257e19fa25720899256dd49a2566b0bf2557d6232544f2dc25274383250a396f24fd5e23249d98872475d316246b0c6e
  | 8, 7 => 0x2f5e2e3e2f4c48672f33505f2f2f94332f2eb5ff2f13eca42f06e38c2ef1ce622ec796112e806eab2e57fb8a2e4aec922e4260a22e3f157a2e3d4cd92e02d8c02dffe3462dfb1f7a2dfa7a242de44f682ddab6932db373ca2d64ea412d4c7b002d476ad92d40e27e2d3df03b2d20c4232cbf525d2c8bf2632c83ba322c4403ae2c3a6e822c382b1d2c2f49e42c1776e72c0c47c32becc8762bbc3d1f2b7e9dff2b7ae1082b67d8712b4823412b42ea802b41d71a2b2636042b0b689c2b0b53fc2b0131d62acb1f762aabf96e2a96ef9d2a8fa84b2a8080ef2a7f883c2a767f872a5fdd642a585fe22a439db52a42e9ba2a36ab4e2a0805b229f04f7029e9528d
  | 8, 8 => 0x34e7908f34de31ff34dbc83b34d8649334d637f034cd402834cb434f34c0f0b734b3c17934abc9353494ba5134948ba3348b68f1347c1e6b347c1a30347819973427a3b234100514340b0bef33f7d1b533ef5b0633e56e1e33c850c333c043d1337e8a8733719aed3349311a3340230c3338189c330c551532e293fb32d2f1e932cd6c1432b57c60329be1ae3286379f3250d60e323acfed321ef09931dd14293191689931779f623166c22c31372c103116d83830dc5f2f30c00a8430bf691f30bde80a30bb89f430ade608305122f63038905930295c0a302337f5300ea16e300b00432fe8d6ee2fdc0db62fc75eb32fabb1da2f8fac442f857a8c2f81d234
  | 8, 9 => 0x3b27a69b3b198c3a3b1888e23afd917c3ac56ff43ac2e2543a7bfe5a3a71a5b83a41ab2e3a3ae0dd3a35c1fb3a30e8663a2783803a1d31143a0774f139c58bfc39bf59b7394b680a38ea0c2f38e03887388974cc3887f0f03857b1ed3853150b3833e4da382d5cf33827bf063823945b3801ba2837f71d2c37ca3fea37b49b8f3773562a37706405376ccd51375cd3bc3750235f37459b9b37241483371ac2af3702bd6936f7504436deaec336caef2836b0a3f4366659d3364a18eb3643583e362dbf2335e8c49235d24ad535d0ca7f35c8e58135c5822635976445358c23e43569bcdc3558e29f3548df34353efa5a352f3a7c350eabb834f865f734f04003
  | 8, 10 => 0x41fe47bd41f18e5841eb90be41d9235a41d7d5fb41b8405641a6596d418fd9674127af9e40c2a31440ba6ba94082dd10406bb62540647c2040615375404382c64028dd2940211619401ab3473fe86f8a3fe4d97c3f9a6f1d3f7fa1b53f6a100f3f5c56b53f3295d13f22d4ab3f2032873f1d07993f03fa773f01c4f33ef19ea63ee90acf3ee64b4c3ee34a803ee23e853ebccd7d3eadf1823ea565923e98b1603e9080273e6427d63e5d13b83e59a9bd3e44719e3e25997a3df956323dcb51db3da07ba53d87f63e3d57b34a3d56d4543d3b16e93d2648b83ccfee6d3c98f0483c77019f3c631cd23c5e5fbe3c5a5f253c3bb9633bdd423d3b68d1f33b64939e
  | 8, 11 => 0x48b4d4d348a32bb0489a2e724884686f4871d98d483da61648131e8247ff2c3447acc8f8479b0b76476dad43475cc45c47496882473a597a47138b7146fc658046b8c72246b23c4846ad1ddb46ab377e466a1ada4653a9f546514d42461c01c445fb262245f807a045c169854586921b45752a8744fede2f44f49b5b44c01f2c44a5c67a44a46f3d4499778a4494b7c34491288f448f96ae447f395c44528b97440726e943c6b5a543c66c7343c2b50c43b250c24392b809437f5f4c437a0b7b4349a2ca4330710442fcc9b142f5192242e7e36342e2512342e1288342e0f0bb42b9b94e42b5b8b542ad6dd9426890f8425b7116422cc4bb422acb8c420bf24e
  | 8, 12 => 0x4ed3f6ae4e7406214e64bb674e5ff0d74e4120f54e3392d04e02353f4dd71b8d4db49fba4d7dadc44d77c74e4d309eaa4d21ee114cfc2a094cd644a14cbe20404cb7d4f54cb4984b4cb2ec334c9f7e424c9d9e214c8f7afa4c8e6d8d4c5cf1424c5990314c530c924c30f8c54c00252f4bc0ead04bb9d4b44bb688194b9336604b5de9004b505b0a4b2be6734aec8b014adba6eb4adb15f24ac870164ac5d6c74ac492c24abfab684ab652fb4aa96a734a497e6a4a39bb3f4a1e0e9c4a16b1564a0989bc49fe71d949e7b03d49dd6c3749c8f12949c3c6fd49a37395499dc77e496290db4954b8bd494f279249402be24911854c48f0534948d7fc3c48b6caa6
  | 8, 13 => 0x5790fd095747ebd25717888456c56ae056b0cdc8565fc9d7564ebead562b96b055fc49ef55b3e8e1559be8b75596a72855919ed55584c0fb5559e053554f65fc553ce1a0552bb2b85515979c5515888b550991a454d811b754ca089a54c4fc48549e89c4548eec605467a2c3546407365455c7ef5432ebe6543205d254217fdc54183e5c54179a6c54026bac53fe206553f20ca253d4c718538ea47b5375fe0c536dbebe535d43e85357acb453554452531bfc60531b57c45300cd7152af9d7652af4f0a51f2512451a44a025193e5df517f073d5126f71850e9af6c50d298d75080bc2d503658cd4fce432b4f9bdfb44f7194374f588f514f01989e4ef5ec56
  | 8, 14 => 0x5efec1895ef339f85ebf673f5e9697c05e8aea6f5e5b6e425e519e885e037df65dfbb0ce5df70d825ddf31e95da5949d5d6e16f75d6690e85d3dc4885d026a3b5cd8f8315ca17df35c68ecd15c3c0c335c32f01c5c2dbdac5c2d522f5c26deb85bef306f5bcf67655bcd5c565bb789db5b75f72e5b65ae215b2da3005b2975d55b2055d85b0dd99a5b0850925ac5c0d25ab6d3525a9fdafc5a8777735a5b046d5a1f2d5d59f75ff359eed36459d1f227599e6885598ed00c5968d47459551b8359539a6e594f12ae5934607c5919ff935906c15d58f7c1fe58d5ad71588f4cff5887808058520553584af2a8583aeebe58338a8957e8ce7e57cab8bf57a4aa1d
  | 8, 15 => 0x66adc0646678d21e66616ff9663906c4662ca06565b18453659b3031655de885654e9388654787d0652c9ddb6526ceb4652452dd64d66cde64d1c1f16494b8c364941ea363ea6ca563e9a2de63d902fc63d6ce9263cf3df363ccc86a63a67dc4638022636373898b6330590b62f5e28062e7887962d8210e62b124ca629d55ea6287c8ad626fdf0a622eccd6622a45a5621d769f61f6603e61e2e45d616f3706616411fc6137e6c761359dc761319d2e611e3dd460fb6a9b60df6c4360c30f5760bd716a60bbf05560af96ad60a1437e6081d6a0606017e5602ac132600616696004e1285fb4e7145fb075135faef3fe5f986fcd5f7825775f560ffc5f39944b
  | 8, 16 => 0x6fa441d46f9950a16f970ef06f75757c6f46858f6f392b096efa39016eedef5f6ecf3ec76ec611b86eb43f276ea2512e6e7d2a226e7530026e67b3036e629b936dfe72a36ded43666dc9549c6dc7d3876da43cf86d64ead36d10ad026cdd8f656c77d20d6c3c59756bff716c6bb35fb36b646dcd6b44ad3f6b16ff5e6b0c3ecc6adef7916adaf9486ac07df06a755bda6a4fc1ac6a0a44b96a05d7ee69582dc269449dba6939356169387b3068ec1a8f68c1cf9d68b2a9e16899f3156895f8f0688ec548687a8be06849c49c683b1a08682b653e68010d7567a7169a677c7d8f6773c7c56739fb476732af1f6718cafa6715660b6700c5b466b1b8a066ae8726
  | 8, 17 => 0x78d6048778bcb62d787d9e1f78768b36787548b9785ea5be7856ad747845c4b17843770c783027b177bdd5cc778bc81c7786253477737edc77708975775b5b797729b9ad76ddfbec76c5bd7776426fb57640e1ea75fe352175f9460475c1587c75c0ed7575b15cdf75b1384975a9d6e0756f518e754888c2753748707531aa8374c7a87e74c174847480ce59747b1a9c7452cb8e743a9eb3742fcd5a742e7df67424ae2c740ca8e67365088a73409bd97323bef972f305b472f280a77296334272827cd5727d62a17233f190722088de720bb5077200b77171eb2dc771e2501071a3453e716daea07145c5da7129a7ab70cff00a70bf8e8f6fe2e1c76fc46341
  | 8, 18 => 0x8307c14c82b66ff2829e899f825e62878218761181c137b881aaf99f81aa8b7c819d734f817cfe9c816d655b8122032e810e417180a18e76809f41a980648765805ec8d6804f1808804b40b080426ed08040200d802fb1957fa77ff87f67b3717f18bcd77ed251067ec5d0e07e98aa697e023d5a7de858a07de0c9837dcf00077dce434c7da28fb27d9c0c917d355a8f7d0695797cf9b99a7ceec4f97cca77f87cafa3727c72e1d57c6d68917c12ea567c12d0ef7be366247bdd95417bbb21757b51d2b67b4559217ae618687ae419b67ae004ce7ad6eb307a102ab8799c3a51798830157974f37c796cb206795dbb6479542fbd7908f1dc78e2eac978d8bc31
  | 8, 19 => 0x8c8ab3ba8c7e9e338bc764d48bb639b38b6c6ec18b53b54b8b204b5b8afaed1e8aecb44a8acdbbe98ac3e7e98aa35a198aa0600c8a8d45118a8c12a289e58ca489d76f9289c6b86e8970cbfd893b77d788d64cac88c9693b88b0dbaa88a9372f8884b5708863296e88564451884b698d881aaf17880afa6d87b3ceb187a128158788139f87261a788712306c86902c20867a7e0e8649832b862fa0c985fbf36785e1e7b985e0f8f9854844748519a49384f9db2d84e0819884c720588487b31c846fadd68463309184620f8184571ae0842f941a8404439684011c2283f6e8f983f2029483e6e4e183e5658883e55145835fb1348350b93283201ee4831537e8
  | 8, 20 => 0x952cf60294a3eaae946bf9319468be8d94547a6f942a1c1794055284931e8f9a931ae7d793184f3b92e8146c92d1b1d292cba03292c024ea92be2e339288a1429285fb1c927701d49269eaa89267cc1f923b686f923a841b9228e16691f468899185b9e4916df2b3916a7dfc9142fad691417c239103ffa89101679e9101309290c67e2a908e09a290471ed090365dd38fe6f5158fc45b348fc3859f8fc1aa538f9cdbb38f5ddb248f4ef35b8f4586de8eff73128ee76a978ee5ea258eceb9288e8463d18e6619cc8e52cc838e4f51018e4032568e1e755a8de02f168db3e0c98da1ed128d9f85138d82b9b38d58d77b8d51c9e98d3255828ca902cb8c983ccb
  | 8, 21 => 0xa216db47a20fc72fa1f4978ba1d25adfa1d0f7a3a1c60302a1b5297fa1789d2da13ab4e5a0db5e08a0cfb17fa0b2c7279ffb55509fae644c9fad80ba9f762f0b9f4aec4a9f1c95589f07fedf9f004bbb9efed42c9e90ee199e77bafa9e69a6129e67770d9e1417a09e03cfff9de39f219dba28d29db28fcc9d62f31e9ce8c57c9ce87df29c3d72b89c04e2ad9c0128fc9c00b11b9becb9049bbcd0569b9140689b2067b59b1116849afac7de9adf0f1b9a833dbe9964d90a992a09979921826d98bc207897f12ff197c2a2ba976d148d974acd4f9701212d96e390119663d3a096370f0f95fa9d3795d3c20295990a6e958f076295783e47954d96f1954b6ed2
  | 8, 22 => 0xad54201ead501f85ad410b00aceb9031acc5a4caac52e173ac49147eac0c0224abef021cabaf5b47ab01b45baaa44359aa6ed650aa5fe1cfa953b504a93872cea93410c4a92c35cca9197a96a8f77a88a8e0f314a8e0324aa8c0004aa7f2a6c9a7de58c6a7d49e09a73cf4d4a735a090a7081995a6afa188a65ba6e0a6016630a5fda8e6a5fc1014a5d9bdf8a5a9357aa590b7e5a5702e24a548e190a5227eb9a4fb1007a4d219fba48d0b55a4821384a450d3d9a437beb8a3db0b85a3c32c74a35c72d1a34c673ba342f241a33e9c4ea339bb5ca306e67ca2f9964fa2db4096a2d1df22a2bb59f2a2b83625a2996054a2603c3da24cde46a24bc44ba242af07
  | 8, 23 => 0xb7ca6c94b7c7e639b74b1bedb7179fdeb7100735b7032367b6fa297db6e97d9db6a56084b6988731b68b1460b6866823b65b40a1b64aaf5fb6170ad8b5ecd646b5ea5bbbb5ea25afb4f3fce2b4e28076b4bd0a1ab4bbc4abb4b8756cb4b81aebb4b672c4b4afe97cb4a43ceab48d1ddab435192db3a5f731b3513176b34a9089b30a7728b2780918b1e5ab66b1d50698b1d12a3bb1cfa926b1b3ff94b17baf6cb1717185b15cb70bb1503422b148d1a8b0dd6560b0cd663eb08d77bcb0130f22aff78964aff78553afce123cafb614beaf91d396af7cb6e1af05f827ae99f58fae73b96bae6cb851ae46fe54ae37c463ade69a91ada8c724ad6c5631ad6005f4
  | 8, 24 => 0xc3c38e44c377178ec32802e3c1f90b0fc1df6fccc1c85937c1bfbbfbc1a23037c1a031dfc18f3c6fc189a74dc18266d1c10575eac0d0bfaac0b57f3cc0633b35c0064444bf629817bf5ba778bf10b188bf04818ebee74e3ebec4b866bea2273ebe76da6dbe058a40bdcc0501bdaff2d5bd819b74bd5d963abd552c2dbd475c78bd40cae5bce4f62ebcc1f319bca3ed2cbc6e71d3bc6d06e6bc3894ccbbbbf8dfbbaff065bb4e4c1fbb16875ebb0c71b6bb00d928bad1db40ba883644b9adabe6b957d4ffb94d2955b93f1e0fb93ef587b93af4eeb9398022b9345c25b92bb878b8e40553b8c50cf2b873cf54b854d6f3b84f449eb84d7cb9b845bb47b804deab
  | 8, 25 => 0xd1e98ed6d1b98be0d127b79ed1113d69d0ff3ca5d0f74dd5d0a63573d09fa353d09a1902d08e302dd05e0091d03f5c79cf685d1acec40a0ace62dbc2cde6efb9cdd7e84dcd9fd56ecd89f342cd5ff527cceaa202cc3b7b03cc18abf2cbfeb966cba5b38ccba2d449cb696078cacdeaaecabbf568caac6bc4ca78368bca6deb4dc9ed825ec9e9bd58c9cc48adc999b788c970a51ac93f39c3c931c31bc9294ae9c92811e2c8961c5bc85a82c7c805c681c780cd52c72bd723c71a5401c719ed10c715d0b5c6a18150c64fdb36c6456354c6002e8ec5ed2a8fc5d2d8c3c5b70a7ec56582a7c54b884fc4ded507c4dcc937c4d3251cc4a1a3e0c496637fc484c276
  | 8, 26 => 0xe7702f80e71441dee6fb0155e6b43c41e69b3ca4e5dc40a8e5c57291e5b09f08e5488beee4f87349e30206b9e2e43284e2d714dbe2d6fb1ee2bf829ae25b28d2e20b1d69e1f81366e1d2673de0c906fae09fce4ce03ee958dfd65d4edecb3aabde71c1b6de420039dd84e93bdd6924e3dd4133a2dd2b5ca4dc9d5593dc29854ddbbea44bdb92493fda9a837eda547a2cd9ff181bd9e5e686d9d216bad9475e35d90a9c98d8753b4fd7dc92edd76282bfd74021b1d7096bcfd62be1d4d5d2c45ed5c306bdd5b91b46d555c74bd5263a47d4b78ea9d4acf01ad4a920a2d4564e64d452f7e9d40ed2ebd40e24d0d3c7e35cd371ca20d34188ddd2a008c5d214531a
  | 8, 27 => 0xffc47988ff088e72fec49d68feadf12bfe985873fe8c524efcc9e9a3fcc19f91fcabfa13fbc80f07fb81d302fa923706fa4eecdaf9cc2343f98acf1af964b52bf91f2471f908e18df8d53493f7a0388bf698cd5df636378af56ef6b1f558f0f1f4b32271f49294faf4201f88f3101950f2a77b57f29f58b0f247adc1f1ba1f70f18e0997f1410110f10ca002eec8b345ee9b6550ee03928bedef79faedcf19b2eceec69eec08b90bec065316ebd6bbd8ebcb715feb89b164eb7da4e8ea181935e9d8ab29e99ae8fde8c3cd66e846b269e7e77e94
  | 9, 0 => 0x983d279098370c4097f7288097aa7b309642ac8094ebab108d944390883192f087600f7086e585e084150d00827aac6079d46af0760ed14075adaa20739b4b8071deaaf06dc0af606c07cb806a41f3a06906e860682542e067e07b8063b9365062b28bd0628df6c061f3ba505fbdc5f05ec938d05ea83c30578029a05778f07050a221104c28deb04ad33b5042e862e0425dc0b041dfb9504067ecb03e5e1bc03d968d503c9652903b60b59033f393002cabb67028f11370253fddd024e0c98024641680233d50901c02dd1018da899015d01d1015c7452014f5da9013e31300139a2b60138d52c0131f638010af71100fe680900ec089800b7a1a90050057a
  | 9, 1 => 0x1288e3a8126e5d9211b9935b11aef24e117f99c4117be7511151b9ff10b82b1710822c66106e04d7105b93f5104bc7e01011f6670fde56de0fa9a6b70f5ad92c0f572e430f154a6e0ed15a870ecc8a160ec330890e71f3110e68e5030e54e80f0e4387970df12f020de289710dded9ec0dde3e570dbdc1610db634320da70e940d87918c0d82b5930d54e9740d2974200d17db8b0d0ffb2e0cfec0040ce62c330cdc23a30cda73030ca844250c87950f0c47ed1d0c3f9a2f0c0dd9ad0c06ce410bfb3e4b0bed904c0b8221ed0b79e4ed0b5b017d0b4dbfa90b208dc10b00370a0a6bf3b10a5c12560a19bf6a09f09b5209f0580809d0892009b2be1e09929aaa
  | 9, 2 => 0x1de669431ddc9cf51dd54e061d7468b71d70075b1d61be8e1cea3a101ce718811ca837d61ca10fc01c8d3ad91c7f12d21c736bbb1c69d3311c374df91beb650b1bd683231bcf13bb1b504c991af9ef4e1aa5af441a9decc91a6828851a60cca61a53a04219d6b37919ce278919c83c7919c6072619a651be197a39251921e942190282f218e9956d18c9b722187eefd6182aaa221814eceb180c3ee417f67c31178bdec916db927816b71864167e38f3166c42d015eba44b15db078a15c2723515933a70154c02731503b2e6149c9804147263b7145e517014546f38141bd422140b2df913fd695813ead00213ddcdba13c098ec135b337113207dce12c7867c
  | 9, 3 => 0x28a6523428779a6f286be0dd284d375927fc27a427c66018275ee4862711f00626e296ab267a2ee62666f5f62650ab2d262dcc74262733ce25f0c81f25df14f225b1299025a65ffb2570f5972553d60a253ef460250c717224bd34d2248d37cb247ab1982418a70d23d6c75423be40fd2343da9f230c5a64230890262276887e224a278e2231dcb32225277721f1ddc921e835ce21d5dfd221a7f0132152f5e12144c3bb211b77df210b474721038af620d4253320c771fc2043acd9202d7e001f94c6da1f5176be1f3d648a1f2d23bf1f087c121efb7c721ee119461ecbe9f31ec8393f1ec78d991e7ae8c21e7614d71e5932fb1e1de3811e09b2b21deb8023
  | 9, 4 => 0x332d25cd3325a7db32e1da2d32cd6c143295e726328d657732799abd32491ac0321984dd31af88e3314aaff03125b64b30e58c6030bf691f30b5a9f43085f08c300b00432ff7cbca2fa8ad9d2f685beb2f60b5f72f39d19e2ecd29c52e806eab2e7616c52e3158f82e27f6332df3fbbd2da6e5492d98851e2d8965a22d64ea412d4d3f002d4787302d3b2afb2d188e412cf328ef2c76c6b42c3218ab2c2ec15d2b9e285b2b541ae22b4fde852b0ff1332b0b689c2ad8f4462aa9b2632a9716352a80e75a2a79564c2a698b0929f9ba8e29dede65299d0a6b298d7d5e2977ebff295a33b029508bb5294d540d2945ab752927d7da292069f028d1e20e28b607a6
  | 9, 5 => 0x3c5a5f253c25bb1f3c0783ce3bad53243ba3fe1f3b9a12643b207aba3afa1be83aa423293a9974fc3a2783803a213d0139bf59b7399f6068398eb79e398ea70f3981dac4397644223917deca38f5a08b38bbf22938a7a8cb3887f0f03886aeec3810c1223801ba2837ca3fea37631f7d37459b9b36eec23036eac19736d939fb36caef2836c6749636a227853690d164366961be366616e2363ade2e35f2dd4735ec6c0a35e9b90335d991df35b9308535aa69eb3582cc2b3577c40f35742a86356808dc3564fe8034e2584934d6c6e73498695a3487bf8f344fbc293446c864341789903411f73b33c5afd733af99b6336498f1335641b833502c5b334b5aa2
  | 9, 6 => 0x46d7608246c91bd246c09db746943969468dbdf64625ab924623c1fc45dac8ff45c28ec045b8b54c45a008d8459e3461458b828b45210b0844f49b5b44cd0525448997734409364443fb5b4243c2b50c43ae0ab743a676534370d15e43657b2a4348fdc34342f7b34306bf4a4301563d42d6809e42b5b8b54286fbbb4268abbb425b7116424a2b1e4216abb541bc91c44128961140de9a0940c21f1640a184ec408034b14061f4794032383a400ffeb24002e6533ff978383fc8ef493f73385a3f59ad023f13eb573f03025b3f01c4f33effd22c3e6c66c03e418fe23e3013a83e24b27f3dc9cf4d3dc18d263dbe90193d34938b3cb186863ca0e05d3c5e5fbe
  | 9, 7 => 0x5126f7185119802a5115197650e9af6c50e5e9e850d298d750c57a475091da085075666450735ba6504cb7ce504ae8b950176942500ea3e0500c83d34f8e34ff4f6e543e4f588f514f3b6cd54f15845c4eec604f4eab847f4e9c341d4e3392d04e2e707e4e2492164e2072a94df87bb04df870f14d8c17e34d82ead34d5757834d50788f4d25fd194d1be1e44cfda9154cfd64c74cea6a3b4cda6b194c0fd3074c01bacd4bd98d034ba20cc84b4d73144b3ef7744b3bd5ce4acc38964a86bca74a16b15649b12a43496d0acf495d24604951efa1490d70a04908f9bc4862166a4856195947da679f47d316ee477fb3cc474dc68747496dc84740bdd946e28274
  | 9, 8 => 0x5b459d8b5b3b2d295b36b1835b29f8215b0df97e5adbbd705ad1bd415ad00c955a71f21f5a6ef4e75a2e8bcf59e8011d59dc43b8595a0d0859551b8359539a6e5947bcd059479a1e591e723b591a49b25909b0eb58f7c1fe58c9428158a6176658662fad5853dfaa581175e458057d0c57fa2fef57d9b443574d075c574ab9b75741e9df573c2aa856f0c2e655e21d9555d437b055bbd49e55b460b0559f6cbf55374b2f5528a4a454d6f54954c4fc4854aa03f75452c02254212deb54110fa753e57df553b799b753a5a3975394d3c25341e2ea5322aa3952ed90e252d44e3d52c8914152b9aa4852130a0e5209061a51ef128e51daf16451c86eca51b61c54
  | 9, 9 => 0x66676a096632ef8c662a556d65f1ba0a65b91d73655cd2c86506132164eb42056477cea8646787a2645ff82b6437cd7a6427f736638ef5c7637e6b2e63525879630aee5262cc53bc6266dfc86228605961f989e161d3345d618b52ef61781e66615220a561319d2e60f0e12b60c30f5760bd716a60aa0bcf607fd66c607259a7604dc61c600616695fd6e95a5fd5ba965fb075135fa532185fa337135f986fcd5f1168135eff14225e8fc47a5e7ecacc5e68a2455def1cd35debd0055ddf31e95dd15d795da44ff45d7ee6d45d6f841d5d6e16f75d693f1e5d02d2e15d0123eb5ccddbc05c90fa8b5c90f1465c4103945c3d77255bb078045b795b835b6122ac
  | 9, 10 => 0x76403d76761787fd75b57666757a047d756918117545d09a74f90a207478eecf7452cb8e73ef5ce573aab11173a47e9e73734d3b734f003a734925f3734088c77325e870729782477280ed67727d62a172621d837260af6171d2630c71c6693271930c88716daea07164be70713c74b471164a4e70b0cb0c705ffcc47026cb4d701b29ab6fed9d2d6fd8b7ff6fcb6cec6f82f5636ee8fea96eaa3c4b6e3462696e2157f56dc9549c6dae41ef6d329e936cb755d66caa54f76c446f156c3c28b76b4b8c3f6aef49406aeb4dd26ab2e7a06a5b7e5468f7a6dd68981ad0687a8be06839b3d26819dcb067d643dd67ac097c67a71af766b2059d667af02866722299
  | 9, 11 => 0x84a6ffa7844819d983d6522b83d5d82f83d0d4ce83caee5d83c8454b831cc50d82af53bb829218f9825e6287825df5c781c2e21281ad69c1816a5ba58167868b814e9f6280b061d0808cfdc480717564807163f1804b40b07f949f8e7f3911e27eec69fc7ee4452e7eb2e93a7e9f37597e8924f57e7adb727ded044f7dec7f197ddac7297dd1db2d7db3b9167dade4ac7d992d457d6bdff67d25f7407cf9b99a7ceec4f97c9fee767c164e217bf507ad7b6716167ac8fc6f7a76aac87a70a3c87a6dec817a525af17a4f04eb79c8981e79ac553f79090e0a78e2eac978941f3e787ce1a07867cdca78316de177d0bbfb778fc37b774be6c0774359167725ddd5
  | 9, 12 => 0x9778e0649667b0ac9643f4539633da7095fa9d3795adfcef95534ce094c56e199471202b945c2bcd94547a6f943e157493ef12e293de4b2893b1807e9374ee99936c48de93420d8f932031e191f94b5691b3d518917274fe90d18707909f01cf905e242c8ff648338f5ddb248f1a51cd8eceb9288ec125908e9edba88e47ba508dcee4e68d7d47238d546b568c50e1048c36e11f8be58b748bb639b38b53a55d8b49eaa68b204b5b8a9593958a8c12a28a858be28a84b6278a8406d7893fbe3388935c44887f5926885ed8608815bde68806553587c7831887bd7f7987b1a3418794c68686bb9033865a37da85d845aa85cacb0985655d1684eaa20e84c781b7
  | 9, 13 => 0xa4fc45aea48b93a4a450d3d9a3db0b85a3715586a35eaed3a30f453da3011f87a2f1e441a2b20532a2a4ca82a26025cea242af07a2400c2ea1ad6a6ba1789d2da15a2857a133d75ea132b0b7a123b4e2a0f3b534a0dcc325a0c301a9a075a93ca02f91fe9fd6c04a9fcddb7c9fc0bf3f9f8cd5579f6952ae9f27c0179ece8f989ea8dec29ea100479e6041c59de04c139ddcd5599dc9006d9dba28d29dac4a3a9d1effb29ce87df29cd456859c7a8e4e9c5e463a9c2dbdbc9c08ff9f9bb0d09e9b9140689b18e4859af7cfe79aec12eb9a43146d9a2743b99a10e10c99c1d2fc9956676498efc40b98eebc40986e6a639807b06697bf3d279797d8c59789e880
  | 9, 14 => 0xb3cbe4bab3977766b3880eedb37cd05db329fbe7b31acd58b306cb5bb2d83e24b2aa058ab1e396d5b1d12a3bb1c807dab17baf6cb15cb70bb0aa4327b0a4836fb0814096b07d38b8b0680864b05fb316b05d357cb043a593afdb5e6baf91d396af7e59f7af6f1379af6c0900af4dec74ae9d3fa4ae4ef4d6ae247fd2ad96a0bdad805472ad501f85ad403184ace2a37cac9b554eabcd1641abb38b21abb27771aac704baaab82d6caa62649faa322b0caa0d9f2aaa0c1991a9f8ffbaa99d692ba94366e5a8f03537a8e0f314a8e047d2a8c9fe60a842b051a7e04846a7cefa5ba782037ca7530dcfa734e9bda7291526a7225836a6ac39d7a6024fb4a55a0977
  | 9, 15 => 0xc86e1718c835ecdcc7bd4572c723621fc6cba620c69f33a4c64fdb36c638a94dc620307ac4d3251cc4d16e95c4c37020c49b63f7c496637fc42f1600c2ac9a96c2578560c1f48d8bc1ede8bac1ec19c8c1e65edac1bfbbfbc1879a68c0e03da8c0615c3ac054ef8bc0527f48c050d0efc03350e5c026c080c026b08ac0006cbebfc1be68bf4882c1bf1aa49dbeb25628be784b10bdc911debd5bfa8dbd584a71bd552c2dbce4f62ebccf4d63bbe54ce9bbdf3016bbc4d050bba922d6bb42544dbb16875ebac6ad0fba52e4c0b9c4690fb9b88bd0b94d2955b92bdbfab8c8d74eb8c5ff14b8911b52b87d9351b7c58b63b717f74cb5ecd646b4e8aa59b3dd8bc7
  | 9, 16 => 0xe69b3ca4e5786a36e4566418e43ee653e3c9ed05e3a762fde399eaa9e369c932e32037c6e31247b0e28adb58e254fc46e23b84b6e1b253dde11345b5de4cfd21ddcb11f3ddbc61e4dc83267adc61971edb8241e1dad3b46ed9ed673dd9e5e686d93a35d3d86763fbd8332e92d7d177e3d7096bcfd6e4a73ad66052e1d5c306bdd4c928a4d3f9a0bdd3bea3dad3896abed2a1cbf5d25487ffd1c46874d1bafbeed0cce7ead07f7229d0792ae1cff4d482cfe43274cfe10123cf2f65d0cdc5a121cceaa202cce96405ccb7b1b9cc2bc607cbcc1331cab5a9b3ca1b9391ca03d38dc9c4e7d7c9546fafc940605cc93a2b37c931c31bc8f35142c8ab2ab5c898f739
  | 9, 17 => 0xff0faf51fe405bf6fd5abc6cfd2b42aafc24901afac0df01f9e0d615f9891ca4f86dd88df86c1f63f7a0388bf6c08b69f5877ecef4393dcef3290d91f2ae67cbf25bc383f2309afdf103c97cf0d5d037f04ed93aef985b53ef18ace8ec73aa41eb739bfbeb58e053ea181935e9fece6ae9d8ab29e923e0f2e8e68353e87b9b9ce7b05701e75a5a84e7388895e6bb4ef6e6a1aa29
  | 10, 0 => 0xf103c97ce8e68353e7b05701e11345b5dc61971ed6e4a73ac64fdb36c4c37020c1ec19c8c054ef8bb5ecd646b05d357cad805472abb27771a8e0f314a734e9bda1789d2d9ce87df29c08ff9f9af7cfe7986e6a639643f45379090e0a78e2eac96c3c28b768f7a6dd5eff142259551b8353a5a39751b61c545091da084bd98d0349b12a43495d24603ca0e05d3c5a5f253917deca38a7a8cb36d939fb321984dd2f39d19e294d540d2276887e21f1ddc921038af6126e5d9211b9935b0b208dc1087600f7075adaa205ec938d
  | 11, 0 => 0xa1789d2d
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xf83e000884c410800913ff89fff4f83e000080c000000003ff01ffb0fffffc54482a6318306000310c000000000000000000000000000000ffffff9884cc53e03f53ffa9fff4f9be6f8080c003e03e03ff01ffb0f83e0244ffe27ffd002213104200f83e0000ffc07fec0002030000000bdf016272f108428589cbc4210a0bdf006070f000020181c3c00008fffffc7f4c3ff39839ff67ff9cf40441107f003f801001fc00fe004000000fbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff80000000812f00ffe07efe477e109f000000000f007fe03e7c003e0007
  | 0, 1 => 0xffffff7ed0ff001f8101b881ef60fffffffff0ff801fc183ffc1fff8fcff341884cc11801953ffa9fff4f83e000080c000000003ff01ffb0fffffc7f483fe31831fd20ff8c600441107f003f801001fc00fe0040f420fe9d8d0ef7bd7a76343bdef5f420ff9f8f0ffffdfe7e3c3ffff75ceb347f483fa11811fd20fe84600441107f003f801001fc00fe0040b7d7ffbf91dfc727f244bc23ff8100000f9f000f8001c0003c01ff80b7d7fc912f08ffe07efe477f1c9f000000000f007fe03e7c003e0007fffffe7ffffffffd31ff33ffce60fc7f107ffffffffc01fe03fe0040
  | 0, 2 => 0x1a33fd1ffe2fefecf7e319f000000000f007fe03e7c003e0007b7d7fc1000084300304000210c000000000000000000000000000000fbff0366fff37fff85abdbd4630afbff0060fff07fee0183c3c00008f83e0048f6e418c00913ff89fff4f83e0000f0c000000003ff01ffb0b7d7ff90004843e03e4001210f8031866f80004003e03e0001000f80fcff3654ffea7ffd106213304600f83e0000ffc07fec000203000000afdfc96272f94a42a589cbe5290a0bdf006070f000020181c3c00008a715c8812f08ffe07efe477f189f000000000f007fe03e7c003e0007
  | 0, 3 => 0xfcff347f483fa11811fd20ff8c600441107f003f801001fc00fe004014c334912f08ffe07efe477e149f000000000f007fe03e7c003e0007fffffe54ffea7ffd306213314e00f83e0000ffc07fec000203000000a715cfbf91dfc627e204bc23ff8100000f9f000f8001c0003c01ff80ffffffd4ffea7ffd3e6213314f80f9be6f80ffc07fec3e0203000f8000000285bfc2ffe57efe577e529f000000000f007fe03e7c003e0007ff3fca44ffea7ffd202213314a00f83e0000ffc07fec0002030000000bdf0ffff3ff8c67c78dffc7ff8b0bdf0fff70ff8003c181ffc1ff88
  | 0, 4 => 0x14c33fbf91df8527d244bc23ff8100000f9f000f8001c0003c01ff80bfdffd7272f94b42b5c9cbe52d0a0bdf006070f000020181c3c00008000001ab00158002cf9decceb1ff07c1ffff003f8013fffdfcffffff00000380b7c01ce7ce02df00739ffbbeef80ffc07feffe03ff01ffbf482800406e2038d80dbb43dc007efffff060fff07ffe3fffc3fe007fffffffff487fe3f83ffd21ff8fe035c77fff007f83f03ffc01fe0fc0f83e000884c453803953ffa9fff4f83e000080c000000003ff01ffb0fffffc1884cc53803953ffa9fff4f83e000080c000000003ff01ffb0
  | 0, 5 => 0x7c1fdbb001d8002ffddecefbdff07c1ffff003f8013fffdfcffffff00000c912f08ffe07efe477f1c9f000000000f007fe03e7c003e0007fcff36d4ffea7ffd3e6213304680f83e0000ffc07fec3e02030000001fdf357272f9094295c9cbe4250a0bdf006070f000020181c3c00008b0160fbf91dfc727c204bc03ff8100000f9f000f8001c0003c01ff80fbff016af6f518c28d9bffcdfffefbff0060f0f000020183ffc1ffb8f83e0244ffe27ffd0123db906300f83e0000ffc07fec0003c3000000000003e77b33ac7fc6ac0056000b07c1ffff7f3ffffffffc00fe004f
  | 0, 6 => 0xfbff0162f6f118c2858bdbc4630afbff0060f0f000020183c3c00008f83e024cffe67ffd0933ff99fff4f83e0000ffc07fec0003ff01ffb0fffffc5cccee73983973ffb9fff4f83e000080c000000003ff01ffb00bdf01e37ff1ffe2ffffcffe319f0bdf00607ff07fe23ffdc3fe000f00000fbfb3df8c67c68cff47ff8b00000f9f000f8001c0003c01ff80fffffc5c482e6318317120b98c60000000000000000000000000000007c1fff77b3bef7ff6ec0076000b07c1ffff7f3ffffffffc00fe004ffffffd1884cc53c03d53ffa9fff4f9be000080c000000003ff01ffb0
  | 0, 7 => 0xb7d7fc1004085380385247291c940000000000000000000000000000ffffff9884cc53a03b53ffa9fff4f83e0f8080c000000003ff01ffb0ff3fc80884cc52802913ffa9fff4f83e000080c000000003ff01ffb0b7d7fc1022084b4034c843650c0a0000000000000000000000000000fffffc7f483fe39839fd21ff8ce00441107f003f801001fc00fe00400bdf01e373f18c62c78dcfc6318b0bdf006070f000020181c3c0000800000fbfbfdfffe7fefeff7fff9f00000f9f0f0fffe1fe7c3c3fff87fffffc18040c5380395367a99cf40000000000000000000000000000
  | 0, 8 => 0xb7d7fc910108c720724404231c81000000000000000000000000000003d700812f00ffe07efe477e109f000000000f007fe03e7c003e00070bdf016276f118c28d9bcfcc319e0bdf006070f000020181c3c00008a314cb80b7c05ee7ee02df017b9ffbbeef80ffc07feffe03ff01ffbfffff351884cc11c01d53ffa9fff4f9be000080c000000003ff01ffb04020028d8d06b4bd4a36341ad2f5f420ff9f8f0ffffdfe7e3c3ffff7fcff345cccee31981973ffb9fff4f83e000080c000000003ff01ffb0f83e0089afc4ffe07ffffffffffff83e00008fc07fe03e7fff3fffb7
  | 0, 9 => 0x5020369d8d06b5bd5a76341ad6f5f420ff9f8f0ffffdfe7e3c3ffff7fcff365cffee7ffd117333b8c660f83e0000ffc07fec000203000000a715c800000842002000002108000000000000000000000000000000a0140fbf91dfc627c204bc03ff8100000f9f000f8001c0003c01ff80fcff367ffffffffd11ff33fec660fc7f107ffffffffc01fe03fe0040b7d7fd3232d94b42b4c8cb652d0a00000000000000000000000000000300c9ab00158002ef9deccfb9ff07c1ffff003f8013fffdfcffffff0bdf016272f14b42b5c9cbe4210a0bdf006070f000020181c3c00008
  | 0, 10 => 0x3d70fbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff805ceb34ff6f3ffff87fff67fe94ff0441107f0f3ffff03ffc00fe0047a715c8010808e30030fc007f08000000000000000000007c003e000018e237ffff4001ffdffffd0007ff39e67fffff4003fffffffd000ffffcff347fccffb19819fffffffff4fc7f107f80ff801001fffffffff0ffffffdcffee7ffd3f73ffb9fff4f9be6f80ffc07fec3e03ff01ffb0e71dc80000bffe00200002fff800c619800000bffc00000002fff000b016022b0055c3e2c19dedceb27f3647907f007f83f3c1fdfdfff07f
  | 0, 11 => 0xfffff0406e207bd83dfb43fc007efffff060fff07ffe3fffc3fe007fffffff98044c53e03f5367a99ff431866f80004003e03e0001000f80582a0fbf95df94a7cb17ff8bfff500000f9f000f8001c0003c01ff80fbff01667af36b5a85a9cbd4210a0bdf006070f000020181c3c00008fffff0404c207398397300b80074fffff060fff07ffe3fffc3fe007ff83e024cdde635bd0933ff99fff4f83e000080c000000003ff01ffb05ceb367fd9ffa53d11fd30fec6600441107f003f801001fc00fe0040fbff010884c410c00d13ff89fff4f9be000080c000000003ff01ffb0
  | 0, 12 => 0xf83e000084c01080000213004200f83e000080c00000000203000000f83e012a94d510828913ff89fff4f83e000080c000000003ff01ffb014c33410000801001040002004000000000000000000000000000000f83e0244d9e27f3d002012104200c018000000807c000000020000000808016272f108428589cbc4210a0bdf006070f000020181c3c000084828006fffb7bc1fc1bffedef07fce79907fffbffc1fc1fffefff07ff7dfff9000ffffe03e4003ffff80f79fef8000ffffe03e0003ffff8014c33410b7881d07d042de20741fca388000ff807c0fc003fe01f03f
  | 0, 13 => 0x582a00892f04ffe07fff67fe94ff000000000f007fe03e7c003e0007f83e02c5ffe2fffd422617125281f83e0000ffc07fec0002030000004fe9fdd4ffaa3c1d3e6212314d80c9b86f80ff807c0c3e0202000f80f3e1016af63518c28c9a344ddefef3e10060f030000201823cc1ffb8b0160200004043e000000100020030060000004003e0000001000000f83e0244ffe27ffd002213114a00f83e0000ffc07fec000203000000ffffff9084c853e03e4213214f80f9be6f8080c003e03e0203000f80fffffc7f48bfff1831fd22fffc60c659907f00bffc1001fc02fff040
  | 0, 14 => 0x48280fd06e68383803bb42dd0ffece799fe0ffb07c1e01ffc2fe0fffbfdfff9000c843e03f41cba12f80399e6f8000c003e03e01c3000f805bff016a76f518c28d9befccb5fe0bdf006070f000020181c3c00008b7d7ff90b7c85fe7fe42df217f9ffbbeef80ffc07feffe03ff01ffbf482803effff7bcffcfbfffdef3ffffffffffffffffffffffffffffff4828036ed0f7001f8101b880e360fffffffff0ff801fc183ffc1fff807c1f20491c204253dd950ec427e07c1f060003000123ffdc0fe007f582a0fbf91df8427c315bc8bffe100000f9f000f8001c0003c01ff80
  | 0, 15 => 0xc1efcd972ec88407a54272b9cf50c1eff9f70cf8011fe7c3f3ffff7f83e0366fff37fff80229b106300f83e0000ffc07fec000203000000ffffffffd9ffe73ff3fdbcffffe104411fff003f8011c1fc3cffffc000000c3f001f8000000420038c000000001f000f800000000000000058ea377ed0f7001f8101b880e760fffffffff0ff801fc183ffc1fff858ea37fffff7bdffdfffffdef7fffffffffffffffffffffffffffffffffffe7fd9ffe73d31fd30ffce600441107f003f801001fc00fe0040a715ca0491ca4625200010214a000000000000000000000000000000
  | 1, 0 => 0xb7d7ff9022484be03ec843650f8a31866f80004003e03e0001000f8007c1fdbb001d8002fedc246f9cff07c1ffff003f8013fffc3cffffff5ceb347f4c3fb19819ff67fe94f40441107f003f801001fc00fe00400bdf096272f908428589cbc5290a0bdf006070f000020181c3c00008000000677b33ac1fc0ac0056000b0641907f7f3ffc1fc1fc00fe004f00000fbf91dfc727f244bc23ff8100000f9f000f8001c0003c01ff805ceb34ff493fa53853fd24fe94e10441107f003f801001fc00fe0040b7d7ff9000484320324000210f8000000f8000000000000000000f80
  | 1, 1 => 0xf83e0244ffe27ffd05abdbd4630af83e0000ffc07fec0003c3000000fb3f000884c410800913ff89fff4f83e000080c000000003ff01ffb0f83e0fbf95df94a7cb17ff8bfff5f83e0f9f80cf8001c003ff01ffb00000000880c400000000bc01ff80000000000000000000003c01ff805ceb3c7f483fa11811fd20ff8c600441107f003f801001fc00fe0040000008812f08ffe07efe477f189f000000000f007fe03e7c003e0007b7d7ff90044853e03e5247291f9431866f80004003e03e0001000f8014c33490000843e03e400120048000000000000003e03e0000000000
  | 1, 2 => 0x582a0008040410800913678894f40000000000000000000000000000f83e0fffffffffffc226bf13ff81f83e0f9fffcfffedc0023f01ff80e71dca0491fffe25200012fffa00c619800000bffc00000002fff000b7d7ff9491ca47e53e4011214f8031866f80004003e03e0001000f80f83e02c5d0e2801d7edc546e529ff83e0000f0c0000c3e7e033e00075fff347f483fa11811fd20fe84600441107f003f801001fc00fe00400300cbe77b33ee7fe6ac0056000b07c1ffff7f3ffffffffc00fe004f00000000040010800812470810940000000000000000000000000000
  | 1, 3 => 0xbdf0366f3f30c678589dbc4630a0bdf006070f000020181c3c00008f420f1221cd1739ab87288382174f420f0008f007ffc3e7e003e00770400fc99000c80007a54242b9cf50400ff9f000f8011fe7c3c3ffff7b7d7fc14008a4700304000214c000000000000000000000000000000f7dfff9000cc53e03e4003a9ff80f19e6f8000c003e03e000301ff80fffffcff483fe33833fd20ff8ce00441107f003f801001fc00fe0040ff3fca44d9ffff3d202012fffa00c619800000bffc00000002fff000ffffffd4d9ea67fd3e6011314f8031866f80004003e03e0001000f80
  | 1, 4 => 0xc1000080000000000010c0000000000000000000000000000000000020491c204250000100042000000000000000000000000000000a01400812f00ffe07efe477e109f000000000f007fe03e7c003e0007000003af91d78427c204bc02f38100000f9f000f8001c0003c01ff80e71dc7bf91607a27e204befc0781c6198f9f00b07c01c0003efe0f80fffffc7f48bfe71831fd20ffcc600441107f003f801001fc00fe0040fffffc506e287bd83dfb43fd0c7efffff060fff07ffe3fffc3fe007ff83e004ccce631980933ff99fff4f83e000080c000000003ff01ffb0
  | 1, 5 => 0xb7d7ffb210d943e2be4089212f8031866f80004003e03e0001000f805ceb357f58ffa11a91fda8fea5600441107f003f801001fc00fe004000000081010084204204040210810000000000000000000000000000081e004072e00840000003000000081e000070c00000000003000000b7d7fc110008c700304400231c000000000000000000000000000000e71dc800003fe200200000ff880004010000003f8000000000fe0000fffffc7f483feb1831fd22ff8c600441107f003f801001fc00fe0040ffffffd4486a63f83e6001310f8031866f80004003e03e0001000f80
  | 1, 6 => 0xb016000000000000000000010c0000000000000000000000000000000bdf0d7272f908428589cbc52d0a0bdf006070f000020181c3c00008ffffffdc486e63f83f7121b98fe031866f80004003e03e0001000f80ffffff98004c43e03f5121a98fe031866f80004003e03e0001000f80b7d7fd1000484340344001210d0001860000004000000000010000004828006f4837a01801bd20de80600441107f003f801001fc00fe0040f83e0a44ffea7ffd002213114a00f83e0000ffc07fec000203000000f83e0048f6e418c00d9bffcdfffef83e0000f0c000000003ff01ffb0
  | 1, 7 => 0xbdf006240310000018900c400000041006000300000018000c00000fffffc7f483fe35835fd21ff8c600441107f003f801001fc00fe0040b7d7ff910148c7e07e4405231f8131866f80004003e03e0001000f80fffff04040200018010100800060fffff060f0f0001e0183c3c00078ff3fc80884fffe802913fffffff4fe3f800080fffc000003ffffffb00bdf01e377f19ce2cf9fcfce319f0bdf006070f000020181c3c0000817d7351000480140144001200500018600000040000000000100000044090380b77fa0e7ce02ddfe839f3da76f80ff7f83effe03fdfe0fbf
  | 1, 8 => 0xf83e000884c453800913ff89fff4f83e000080c000000003ff01ffb05bff016a72f508428599ebcca56a0bdf006070f000020181c3c00008b7d7fc1000484380384001210f803006000000400000000001000f805b2ac9c44822211aee20cc11399f0380ef8000000003fe01fc01ffbf582a0fffd9ffa53fc224bc13ff8100000f9f000f8001c0003c01ff800400fe9d090ee73d7a74243b9cf50400ff9f0f0ffffdfe7c3c3ffff7f83e024cffe67ffd01333398c660f83e0000ffc07fec000203000000fffffd7f7affeb5ab5fdebffad6a0fdf107f70ff801201fdc3fe0048
  | 1, 9 => 0xf83e02c5ffe2fffd7efe577e529ff83e0000ffc07fec3e7e033e0007000000002f007fe0002203100000000000000f007fe0000000000000e71dc92232fffe42a488cbfff90ac619800000bffc00000002fff000b7d7ffb232d94be2bec8cb652f8a31866f80004003e03e0001000f805bff01667af3295a85a9cbd4210a0bdf006070f000020181c3c00008582a00c56f22fff87efe477e109f000000000f007fe03e7c003e0007f83e012ab6d518c28d9bffcdfffef83e000080c000000003ff01ffb05ceb357f7affa95a95fdebfea56a0441107f003f801001fc00fe0040
  | 1, 10 => 0xb7801c07c002de00701fca388000ff807c0fc003fe01f03f040100812f08ffe07efe477e109f000000000f007fe03e7c003e0007f420f0000c007398387200380074f420f0008f007ffc3e7e003e0077b7d7fc1000084380384001210c800000000000000000000000000000eb3ccbeffff7feffefbfffdffbffffffffffffffffffffffffffffffb7d7fc9000084320324000210c800000000000000000000000000000f83e008985c494a04b17ff8bfff5f83e000080c000000003ff01ffb05734351d3acea95a9474eb3aa56a0f9e101f70cf8012007dc33e0048
  | 1, 11 => 0xfbf95df94a7ca16ff0bff9500000f9f000f8001c0003c01ff80133d369d8db109bd5a7636c426f532397f9f8fb003fdfe7e3ec00ff7ff3fc808040c5280291367a99cf400000000000000000000000000001f23c808847bee802913fd7607f43e278000807ffc000003fdfe0fb0b7d7f02f9197c7c7fc44bd22f0013186601f004f83e1fe003d01f0005ceb347f6a3fa95815fd63fe846a0441107f003f801001fc00fe0040b7d7fc1000084340344001210c00000000000000000000000000000007c1ff900008436036400020000001806f80000003e03e0000000000
  | 1, 12 => 0xbdf0edde32e8c65478d77c7de8b0bdf0fff70ff8003c181ffc1ff88a7d5fc10000843003040002108000000000000000000000000000000ecc2c962724ef642a589c93bd90acdc68060704ffc020181c13ff0085ceb345c482e2118117120b884600000000000000000000000000000b0160fbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff80e71dc92210fffe02a0008afff900c619800000bffc00000002fff000031500812f00ffe07efe477e109f000000000f007fe03e7c003e0007f83e0244ffe27ffd083257185294f83e0000ffc07fec000203000000
  | 1, 13 => 0x3d70000000000000000000000000000000000000000000000000000a715ca0000484220200000210a000000000000000000000000000000f83e024cf7e61ce50913ff89fff4f83e0000f0c000000003ff01ffb0fc3f000884cc10800913ffa9fff4f83e000080c000000003ff01ffb0a314c43f261fdac02c066302841efbbee01fffcfffee3e03c300003ff83e0366fff37fff84aadb54630af83e0000ffc07fec0002030000000000012232d108428488cb44210a0000000000000000000000000000fcff347f483fe31811fd20fe84600441107f003f801001fc00fe0040
  | 1, 14 => 0xfffffc18000c4300315120a98c600000000000000000000000000000fcff367f487fe3f811fd21fe86603447107f007f83f001fc01fe0040b7d7fdbb001dc302ffddecefbdff07c1ffff003f8013fffdfcffffff4828000884c410800913ff88f3f4f83e000080c000000003ff01ffb0fffff0c1412084384305048210e1fffff060f0f0001e0183c3c00078b7d7fe1000484320304000210e000000000000000000000000000000a7d5fdbb001dc202ffddecefbdff07c1ffff003f8013fffdfcffffffe71dc88101bffe20620406fff881c619800000bffc00000002fff000
  | 1, 15 => 0xa715c92210d94202a000882129000000000000000000000000000000b4d73610004843e010400120060030060000004003e0000001000000f83e020c95c614a50913ff89fff4f83e000080c000000003ff01ffb0fffffc7f48bfe31831fd20ffac600441107f003f801001fc00fe0040fbff0244ffe27ffd002213104200f83e0000ffc07fec000203000000fbff0344ffe27ffd0523db906300f9be0000ffc07fec0003c3000000f83e02c4ffe27ffd3e6213304280f83e0000ffc07fec3e020300000050ca379000f7bde01e4003def780f79fef8000ffffe03e0003ffff80
  | 2, 0 => 0x5bff0366fbf32d7f85a9dbd4630a0bdf006070f000020181c3c00008bbdf016272f14b428589cbc4210a0bdf006070f000020181c3c00008fffff8406e287bd83dfb43fd087efffff060fff07ffe3fffc3fe007f5ceb3418000c0100115120a884600000000000000000000000000000b7d7fd1000484300304000210d000000000000000000000000000000000000002200084004884344000a0000000000000000000000000000fffffc7f483fe71831fd20ff9c600441107f003f801001fc00fe0040e0dc35bb00a27e02dfddee1045ffc1d87fff00807c13fffdfe000fff
  | 2, 1 => 0x48280244ffe23cfd002213104200f83e0000ffc07fec000203000000f7dffc1000bfff00304002fffc00c619800000bffc00000002fff000582a0044482221180020001000000000000000000000000000000000a7d5fc1000084200304000210c000000000000000000000000000000582a02c5ffe2fffd7efe577e529f000000000f007fe03e7c003e0007fbff016af6f518c2859bfbcce76afbff0060f0f000020183c3c00008f83e0244ffe27ffd04aa5354420af83e0000ffc07fec000203000000f735fe9d8d0ef7bd7a76343bdef5f420ff9f8f0ffffdfe7e3c3ffff7
  | 2, 2 => 0xfffffc18008c5300315122a9fc60c01800000080000000000201f000bbf6fc7f48805f1831fd22017c60c258907f00807c1001fc0201f040fffffcff493fe73873fd24ff9ce10441107f003f801001fc00fe0040fffffc7f6a3feb5835fd63ff8c6a0441107f003f801001fc00fe0040f83e0fbf91df8427c315bc8bffe100000f9f000f8001c0003c01ff80582a0244ffe23dfd002213104200f83e0000ffc07fec000203000000ff3fc84448bfff18202002fff800c619800000bffc00000002fff000a8cbcae2c53156a56b8b14c55a95f061efe08f307fedff823cc1ffb7
  | 2, 3 => 0x812f00bce04ebe475e109f000000000f007fe03e7c003e000700c037f77b33ad7fd6ec0056000b07c1ffff7f3ffffffffc00fe004ff83e0244ffe27ffd306213304200f83e0000ffc07fec000203000000f83e024cffe67ffd09337798d6f4f83e0000ffc07fec00020300000007c1fd3a2f1d7fe28123ab91ad6007c1ffff0f3ffff3c181fcc1fff8f420fe1c8c0e739d38723039ce74f420ff9f8f0ffffdfe7e3c3ffff7b7d7ffbf91dfc7e7fe44bd23ff8131866f9f004f83e1fe003d01ff8000000f9000480020020000010f8000000f8000000000000000000f80
  | 2, 4 => 0xf83e0008a6c418c00d9bffcdfffef83e000080c000000003ff01ffb0000000010800a10010fc007e00000000000000000000007c003e0000f83e0e54ffea7ffd002213114e00f83e0000ffc07fec000203000000f83e004cfee639d80933ff99fff4f83e0000f0c000000003ff01ffb05ceb3fff487fa13813fd20ff8fe004411fff003f801001fc00fe0fc0fffffc7fccfff39839fffffffff4fc7f107f80ff801001fffffffff043f7010d8d46b45d4436351ad175c5a6901f8f4ffc1dc07e3d3ff077b7d7ff902f487fe03e6203310f8031866f800f407fe03e0001000f80
  | 2, 5 => 0x18e2377ed040fe1fa101ba7e176039e67ffff0407c1fc183fd3e0ff85fff357f487fa15815fd21fe856005c7107f007f801001fc01fe0040f83e0244d9e2673d0020101042000000000000000000000000000000a715c8810108c6206204042318810000000000000000000000000000f83e0089abc4ef6077edb8f7ef6bf83e00008fc07fe03e7fff3fffb7bc08fef272b94ba2bbc9cae52e8a3a596fe070b003e23f81c2c00f88f83e006ffff7bc9fc9bfffdffffffe7f907ffffffc1fc1fffffffffff83e004ccce673980933ff99fff4f83e000080c000000003ff01ffb0
  | 2, 6 => 0xf83e080884cc10800913ff89fff4f83e000080c000000003ff01ffb0fffffc7f483ff31831fd22ff9c600441107f003f801001fc00fe0040f83e0fffd9ffe73fc224bc13ff8100000f9f000f8001c0003c01ff800000024c7b266f7d0931ec99bdf4000000007f007fec0001fc01ffb0abdf016272f14a428589cbc4210a0bdf006070f000020181c3c0000800000fbf91dfc627e204bc23ff8100000f9f000f8001c0003c01ff80a715c92232d94a42a488cb65290a000000000000000000000000000000000f3ebedf7bc7bcfafb7def1e00000f9f0f0fffe1fe7c3c3fff87
  | 2, 7 => 0xb7d7fc1000084b0030c802650c0000000000000000000000000000005ceb3454482a211810600030040000000000000000000000000000005fff357f7affa95a95fdebfea56a0fdf107f70ff801201fdc3fe0048afdfc86240394200218900e508000041006000300000018000c00000f83e0044482263180020001000000000000000000000000000000000a4d53477ccfbb19818eedf777b94fc7f107f80ff801001fffffffff058ea30406e2039d81dfb43dc007efffff060fff07ffe3fffc3fe007f582a004c482621180131209884600000000000000000000000000000
  | 2, 8 => 0x7c1fd90000800003e4000210d8001806f80000000003e0000000f80bfdffff272f94be2bfc9cbe52f8a3bdf6fe070f003e23f81c3c00f8803d70100004000400400010001000186000000400000000001000000000003a7bfd3ffe7fefedf7e739f000000000f007fe03e7c003e00075ceb34fe673f5ef86f03678094ff0441107f0f3ffff03f8000c00047af35c86fff08421fe1bffc21087f0860107fff00001fc1fffc00007feb3ccbef4877e2f82fbd21df8be035c77fff007f83f03ffc01fe0fc0fbff0366f7f31ce7858bdbc4630afbff0060f0f000020183c3c00008
  | 2, 9 => 0xfdf016272f908428589cbe4210a0bdf006070f000020181c3c0000808ca016272f108428589cbc4210a0bdf006070f000020181c3c0000807c1fdb300198002f6cc0066000b07c1ffff003f8013fffc00fe004ff7f7fe9d8d0ef7bd7a76343bdef5f420ff9f8f0ffffdfe7e3c3ffff7fffffdb384d99082f6ce1366420bffffffff80ff8013fffe03fe004f000007bf91d78427c204bc02f78100000f9f000f8001c0003c01ff8008cb006240310000018900c400000041006000300000018000c00000000001a333d18c62c68ccf46318b0000000000000000000000000000
  | 2, 10 => 0x5ceb34d56f2afff87efe477e149f000000000f007fe03e7c003e00075ceb3fffd9ffa53fd3fdbcffffe104411fff003f8011c1fc3cffffc0582a043f001f80000115208a84600000001f000f8000000000000000582a00812f00ffe07efe477e109f000000000f007fe03e7c003e0007e7ddfc7748bfff1830ec02fff800c659907f00bffc1001fc02fff04004010000000800000000002000000000000000000000000000000000583e0244fbe22d7d002013104200081e000070c00000000003000000ff3fc844482a63182020003108000000000000000000000000000000
  | 2, 11 => 0xb7d7ff912348cfe07ecc47671f8b31866f80004003e03e0001000f80f83e0089a7c49ce04f9fffcffffff83e000080c000000003ff01ffb0fbff03c4ffe27ffd3e6213304380f9be0000ffc07fec3e0203000000b3d70300004043e004000100030031860000004003e0000001000000e71dc80108bfff0030fc02fff800c619800000bffc00007c02fff000f82a0244cd2277bd002210104200f02000008f007fec00020000000014c33790004801e01e400120078031866f80004003e03e0001000f80a7d5fff77b3bef7ff6ec0077080b07c1ffff7f3ffffffffc00fe004f
  | 2, 12 => 0xa715c8000008fe002000027f18000000000000007c000000003e0000a314cb81b7c0dee7ee06df037b9ffbbeef80ffc07feffe03ff01ffbfabdfcbe2f7f15ee7ef8bdfc57b9ffbffefe0fff07fefff83ffc1ffbf0314010032c008428400cb00210a0b9e000070c000020001c3000008a7d5fff7fbfbef7ff6ec98776b0bffffffffffffffffffffffffffffb7d7ff9880cc43e03e40bd21ff8031866f80004003e03e003d01ff80f83e016af6f518c28913ff89fff4f83e0000f0c000000003ff01ffb0082003efff4000ffcfbffd0003ff39e67fffff4003fffffffd000fff
  | 2, 13 => 0xf83e0f9884cc10a00b13ff89fff4f83e0f8080c000000003ff01ffb0000000812f91ffe07efe477e309f000000000f007fe03e7c003e00070bdf01e272f108628789cbc4218a0bdf006070f000020181c3c0000800000000260018c00c9a474c109e0000000000000000000000000000e71dc80004bffe80281247fff894c619800000bffc00000002fff0000bdf016272f118428589cbcc310a0bdf006070f000020181c3c00008f83e000884c4108009137788d6f4f83e000080c00000000203000000000000812f00bde05efe475e109f000000000f007fe03e7c003e0007
  | 2, 14 => 0x4bdf016272f328428589cbd4210a0bdf006070f000020181c3c0000800000067ffb3bc1fc0aede56701fce79907fffbffc1fc1fffefff07f07c1ffff7b3fef7ffffdecffbdff07c1ffff7f3ffffffffdfcffffffe71dcfbf91fffe27e204beffff81c6198f9f00bffc01c0003effff8000000a0491df842500001003fa0000000000000f800000000001f000582a0244d9e2253d0020101042000000000000000000000000000000081e016272f108428488cb44210a081e000070c00000000003000000fffff4506e287bd83dfb43fc047efffff060fff07ffe3fffc3fe007f
  | 2, 15 => 0xff3fc80800bffe00211122fffc60c619800000bffc00000002fff000e71dc8812fbfffe07efe47fff89fc61980000fbfffe03e7c02fff007000000000000fe002000027e10000000000000007c000000003e000010020fbf91df8527c204bc03ff8100000f9f000f8001c0003c01ff805ceb377fd9ffa53f91fdb8fee7600441107f003f801001fc00fe0040031d000000b10800000002c420000219000000b00000000002c0000010c23790004001e01e400100078031866f80004003e03e0001000f80f83e0244ffe27ffd012313904200f83e0000ffc07fec000203000000
  | 3, 0 => 0xfffffc7e40bffe18210122fffc60c659907f00bffc10018002fff040081e004072e008400101cb802100081e000070c000000001c3000000fc2afe9d8d0ef7bd7b7734bbdef5f420ff9f8f0ffffdfe7e3c3ffff70000043f001f80000004200284000000001f000f8000000000000000e71dca8591fffe25620416fffa81c619800000bffc00000002fff00003150fbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff80fffffe7ffffffffd31ff33fffe60fe7f907ffffffffc01fe03fff0405ceb347f483fe31831fd20fe84600441107f003f801001fc00fe0040
  | 3, 1 => 0x582a0008000400000111208884600000000000000000000000000000abdf016272f108428589cbc5290a0bdf006070f000020181c3c00008fbff0344ffe27ffd042213104300f9be0000ffc07fec000203000000e01c00000084100000000289f800c01800000080000000000201f00007c1f000000000003dd940ec007e07c1f060003000123ffdc0fe007ffb3ecb88b7c45ee7ef13ff89fffffbbeef80ffc07feffe03ff01ffbfa014000084c010800802df017b94f83e000080c000000003ff01ffb0b7d7ff9000dfc7e03e400123ff8031866f80004f83e03e000101ff80
  | 3, 2 => 0xf83e0244ffe27ffd0cba575c529ef83e0000ffc07fec000203000000a715c800001dc200200000efb80006018000003f8000000000fff000e71dc80000aa7e00200002314800c018000000807c00000002000000a314c98026005ac2ee02cf01399ffbbeef80ffc07feffe03ff01ffbf0bdf014072e00840040003000100099e000070c00000000003000000000000010800ff0030fc027e10000000000000007c00007c003e0000000000812700dee07ede476e109f000000000f007fe03e7c003e0007e71dcc3f00bffe00200422fffc00c619801f00bffc00000002fff000
  | 3, 3 => 0xfdffff77bfbef7ff6ec0376000b0fdfffff7ffffffffffc03fe004fffffff7effff7fff8123bb91ef60ffffffffffffffffc183ffc1fff8f83e0244d0e2001d000010004200f83e0000f0c0000c0002030000005ceb347f48bfa51811fd20fec4600441107f003f801001fc00fe0040a715c80000885e00200002217800c218800000807c0000000201f000a715c8000099420020000021280000000000000000000000000000005febffff7b3fef7ff7fd20fe846b07c1ffff7f3ffffffffc00fe004f04c13477483ba11810ec007600000441107f003f801001fc00fe0040
  | 3, 4 => 0x583e000800c400000111eb88a560081e000000c000000001c3000000fb3e0108b6c418c28d13ff89fffefbbe0000f0c000020003ff01ffb8081e000000c000000101cb802100081e000000c000000001c30000000400fe95090ae73d7264003200010400ff9f0f0ffffdfe7c003e0047a014000884c410800913ff89fff4f83e000080c000000003ff01ffb0b7d7ff912f48ffe07efe477f1f9f31866f800f407fe03e7c013e0f8700000080000043e03e400120008000000000000003e03e00000000005ceb37ffff7fa1ffdffffdfe87ff3de77fffff7f83fffffffdfe0fff
  | 3, 5 => 0xfbb91dd8427c204bc03ff8100000f9f000f8001c0003c01ff80b7d7ff90004843a03a4000210f8031866f80004003e03e0001000f800bdf016272f108428599cbcc210a0bdf006070f000020181c3c0000800000baf91d78427c204bc03fb8100000f9f000f8001c0003c01ff80fbff012a94d510c28d13ff89fff4f9be000080c000000003ff01ffb04fe9ffffffbfff7ff7fffefef07fcff9ffffffbffffffffffefff07f5ceb34992f0cffe07fff67fe94ff000000000f007fe03e7c003e0007a314c80000805e00200002017800c218800000807c0000000201f000
  | 3, 6 => 0x380b74000e7ce02dd00039f39a66f80ff4003effe03fd000fbf44090000003fa000000000fe800004010000003f8000000000fe00000000012210d100028000880021000000000000000000000000000000a715c800000852002000022918000000000000000000000000000000f83e000884c410800913fb89ef74f83e000080c000000003ff01ffb0582a000884c410800913ff88f7f4f83e000080c000000003ff01ffb0e71dc800008c5200200002a9f800c01800000080000000000201f000f420fe9d9dcef7bd7a76343bdef5f420ff9f8f0ffffdfe7e3c3ffff7
  | 3, 7 => 0x1812f40ffe07efe477e119f000000000f007fe03e7c003e000708cb016250f10002818988c421000041006000300000018000c00000f83e0266fff37ffd002213104200f83e0000ffc07fec00020300000007c1fdbb041d9082ffdfefefbdff07c1ffff003f8013fffdfcffffffff3fca44fffffffd202213fffa00fe3f8000ffffffec000203fff000e01c000000a27e00000002104000c018000000807c0000000200000000000800009f840000000003f80000000000000f800000000001f00014c3343f001f81001044202284000000001f000f8000000000000000
  | 3, 8 => 0xa314c800009fde0020000203f800c2188000008ffc0000000201f000e71dc80000bff200200002fff800c419000000bf8000000002fff00007c1ff767a3b6b5fb4e80074000a07c1ffff7f3ffffffffc00fe004fb7d7ffb2005943e03e4001210f8031866f80004003e03e0001000f805ceb37ffffffbdffdffffffef7ffffffffffffffffffffffffffffff18e237ffff5581ffdffffdceb7ff3fe7ffffff7f83fffffffdffffff0400fef77b3bef3ff2ec0076000b0641ffff7f3ffffffffc00fe004fa715c880000843e03e400121088000000000000003e03e0000000000
  | 3, 9 => 0xa400fe958d0af7bd7a6614335a95f420ff9f8f0ffffdfe7e3c3ffff7e7ddfdbb00bffe02ffddeefffdffc7d9ffff00bffc13fffdfeffffff0701c800001d8000200000efb80006018000003f8000000000fff0005ceb347fffbfbd1fd1fffefef47fce79907fffbffc1fc1fffefff07fef3dc86fffbffe1fe1bffefff87fce79907fffbffc1fc1fffefff07fa7d5f00026005ac03ddb43ec007efffff060fff07ffe3fffc3fe007fb7d7ff94004a43e03e4001210f8031866f80004003e03e0001000f80080a00812f00ffe07fff47fe109f000000000f007fe03e7c003e0007
  | 3, 10 => 0xf83e02c4ffe27ffd3eea5374428af83e0000ffc07fec3e0203000000e31cc80000b7fe00200002dff800c619800000bffc00000002fff000f83e000884c410c00913ff89fff4f83e000080c000000003ff01ffb018e23fffffdf85ffdffffd03ffff39e67fffff4f83fffffffd01ffff000007bf91400027c204bc00078100000f9f00000001c0003c000f80fffff8406ebfffd83dfb43fff87efffff060fffffffe3fffc3fff07fe71dc00000207a00200002fc0000c619800000b07c00000002fe00005ceb347b483da11811fd20fe84600441107f003f801001fc00fe0040
  | 3, 11 => 0xbdf0162f2f108428589dbc4630a0bdf006070f000020181c3c00008ef3dc844ffbffe1d202212fff800ce398000ffbffc0c000202fff000e71dc80022bffe40248843fff80ac619800000bffc00000002fff000f83e0040f6e018c0000213004200f83e0000f0c000000002030000000000092210df840280008803f90000000000000f800000000001f000ef1fc84040bffe00200002fff800c619800000bffc00000002fff000fffffff77f3bffffffff43fe007fffffffffffffffffffffc3fe007f4828016ffff7bc1fc1bffedef17fce79907fffbffc1fc1fffefff07f
  | 3, 12 => 0xa31dc80000b15e00200002c57800c219800000b07c00000002c1f000000000892f04ffe07efe677e949f000000000f007fe03e7c003e0007f83e0244d9e267fd00201110420030060000004003e00000010000000bdf03e7f3f38c67c78ddfc6738b0bdf006070f000020181c3c00008081e000022c008400589cbc4210a081e000000c000000001c3000000000004bf011f84204204240294810000001f000f8000000000000000000008000008000000000001080000000000000000000000000000004409043f003fa000000420fe84000401001f003f8000000000fe0000
  | 3, 13 => 0x3c101627231084284880044000a03c1006070300002018000c00008fffffe7fd9ffff3d31fd32fffe60c659907f00bffc1001fc02fff040e71dc82200bffe00200002fff800c619800000bffc00000002fff00008cb016272f108428589cbc4210a0041006000300000018000c00000f83e000884c410c00d13ff89fff4f83e000080c000000003ff01ffb05ceb347fc8ffa11811fd30fec6600441107f003f801001fc00fe0040e715c800000ef6002000003bd800c4008000000ffc000000003ff00018e237ff484001f81ffd210007e031c67fff004003f03ffc01000fc0
  | 3, 14 => 0x18e2377ed040001f8101b800076039e67ffff040001fc183fd000ff8a314cb80b7c05ee7ee12df097b9ffbbeef80ffc07feffe03ff01ffbfa71dc80000bfce00200002e7f8000219000000bf8000000002c1f000fffffbc0ffe07ffffffbdffd7bffffffffe0fff07fffffffffffffffa314cfbfb7dfdee7ee06ff03ff9ffbbeef9fffcfffeffe03ff01ffbf00000b8091c00427c2009c017b8100000f8000000001c0003c01ff8058ea347f4837a11811fd20de84600441107f003f801001fc00fe00400fdffff77bfbef7ff7edcbf6210b0fdfffff7ffffffffffdc3fe004f
  | 3, 15 => 0xb1c016272f108428589cbc4210a0bdf006070f000020181c3c00008f8fe37ffffc411ffdfffff89fffff9fe7fffffc003ffffffff01ffff18220008844000800913fd0007f438260000804000000003fd000fb0e71dc80000bb7e00200002f56800c219000000b07c00000002c00000f7f7ff9d8d4ef7fd7e76353bdff5f5a6ff9f8f4ffffdfe7e3d3ffff7b400fe90000843a03a4000210e8030006f80000003e03e0000000f80e71dccbf01bffe20620426fffc81c619801f00bffc00000002fff000e71dca0000fffe20200002fffa00c619800000bffc00000002fff000
  | 4, 0 => 0xefdfc96272fffe42a589cbfff90acfdf806070fffc020181c3fff008f0200008840410800913fc89fff4f0200000800000000003fc01ffb0e71dc80100bffe00200402fff800c619800000bffc00000002fff00007d7fdbb005d8042ffddedefbdff07c7ffff007f8013fffdfdfffffff83e008884c410a00b13ff89fff4f83e000080c000000003ff01ffb04828006f48b7bc1801bd22def060c659907f00bffc1001fc02fff040b7d7fc110808ff0030fc027f1c000000000000007c00007c003e0000fffffffffbffef7ff7edb8f7ef6bffffffffffffffffffffffffffff
  | 4, 1 => 0x42002000002000000000000000000000000000000000000000810100fe206204067e10810000000000007c000000003e0000fffffc7f483fff1831fd22ff9c600441107f003ffc1001fc00fe0040ffffc90884cc52c02d13ffa9fff4f9be000080c000000003ff01ffb05ceb347f48ffa11811fda8fea5600441107f003f801001fc00fe004000000fbf91df8427c28cbc47ff8100000f9f000f8001c0003c01ff8003d7012232d108428488cb44210a0186000000400000000001000000e71dc80000bffe40240003fff800c619800000bffc00000002fff000
  | 4, 2 => 0xb7d7ff910548d7e07e56472b1f9531866f80004003e03e0001000f80b717c80000484280280001210f803006000000400000000001000f80efdfc86348bfff0031fd02fff800c659806000bffc0001fc02fff000fffff84048bfff1831f902fff860c659906000bffc1001fc02fff040f83e000884c410800913bc89fff4f83e000080c000000003ff01ffb0f71fc80000bfff00200002fff800c619800000bffc00000002fff00058ea37fffff701ffdffffd80e7ffffffffffffff83ffffffffc1fffff83e00088404108009137789def4f83e000080c000000003ff01ffb0
  | 4, 3 => 0xf83e000884d510800913ff89fff4f83e000080c000000003ff01ffb0031d012210f1080280008ac421000219000000b00000000002c00000fb3ecb0894c410878913ff89fff4fbbeef80f0c0000fc003ff01ffb8582a00090804a10011fd20fe84600000000000000000007c003e0000f83e02c5ffe2fffd4a36571a5295f83e0000ffc07fec0002030000004828006fddb7b41fc137bc9af075ce79907fffbffc1fc1fffefff07fbbdf016272f108c28589cbc4230a3bdf006070f000020181c3c0000818e235fb6e0001dadfffed0005ff39e67fffff4003fffffffd000fff
  | 4, 4 => 0xb0160f90004800a00a0001010f8030060f8000400000000001000f800bdf016a72f508428589ebc4a50a0bdf006070f000020181c3c000081bdf016272f109428589cbc4210a0bdf006070f000020181c3c00008b016000000400080080001010f803006000000400000000001000f80f83e0244fff37ffd002213106200f83e0000ffc07fec000203000000e71dc8012fbffe0060be46fff81fc61980000fbffc00007c02fff007f83e004448a27f18002002104000c018000000807c00000002000000a715c8000008e2002000007f080000000000000000000000003e0000
  | 4, 5 => 0xfbf91df8427c214bc0bff8100000f9f000f8001c0003c01ff8010c237bf914001e7de44bd00078131866f9f004003e1fe003d000f805ceb347f483fa11811fd63fe84600441107f003f801001fc00fe0040f83e026ffff7ffffc1bfffdef27ffe7f907fffffffffc1fffffff07f48280044ffa23c1d002212104000c8380000ff807c0c000202000000a71dc80000394200200000e508000001000000300000000000c00000fffffff7fffbfffff6ee1376420bfffffffffffffffffffe03fe004f000002447b226f7d002000100000000000007f007fec000000000000
  | 4, 6 => 0xf83e0244ffe2fffd002213125200f83e0000ffc07fec000203000000a7d5ff900008436036400021080001806f80000003e03e0000000000b7d7ff9000ca47e03e4001214f8031866f80004003e03e0001000f80efdfc86240bffe00218902fff800c659806000bffc00018002fff000a715cc1000084200200000210c000000000000000000000000000000fffff244ffe27ffd3dfb53fc427efffff060fff07ffe3fffc3fe007ff83e00406e207bd8002203100000f83e0000ffc07fec000203000000e71dc80010fffe00200002fff800c619800000bffc00000002fff000
  | 4, 7 => 0xeb3ccb6ed0f7001f8101b881eb60fffffffff0ff801fc183ffc1fff8fffffc7fccffff9839fffffffff4fe7f907f80fffc1001fffffffff0f83e00080084100001112289fc60c01800000080000000000201f000f7dfff90006a63e03e4001310f8031866f80004003e03e0001000f80e71dc800003dfa00200002ffb800c619800000bffc00000002fff000ffffffff48fffff83ffd23ffffe0f7dfffff00fffff03ffc03ffffc0a71dc80000b94a00200002e528000219000000b00000000002c0000000000204bfc27fe5002213104200000000000f007fe0000000000000
  | 4, 8 => 0xa715c800009fc60020000023f80000000000000f800000000001f00018e2347f4800011811fd200004600040107f0000001001fc00000040ef1dc86272bffe02a189cafff80ace59806070bffc020181c2fff008f83e000984c490800917ff8bfff4f83e000080c000000003ff01ffb0bff7ff98844843e03f53fd210ff439a66f80804003e03e03fd000fb000000f9491ca0425020010014f8000000f8000000000000000000f8048280008848410800913ff88f0f4c8380000808000000003fe01f030582a000884c410800913ff89fff4000000000000000000003c01ff80
  | 4, 9 => 0x5bff016272f108428589cbc4210a0bdf006070f000020181c3c00008e71dc80000bf4200200000a1e800c619800000bf8000000002c1f0004828006fffb7bc9fc9bfffdef0ffce79907fffbffc1fc1fffefff07ff420fe1c800e001d00003001ce60f420ff9f800f801dc0023c01fff0a314cb8095c056a7ea029c017b95fbbeef80ffc07feffe03ff01ffbf582a000880c400000111bc89ffe0000000000000000000003c01ff80bfdfffd0406843e03e4001210f8031866f80004003e03e0001000f80fbff0108a6c418c00d9bffcdfffef9be000080c000000003ff01ffb0
  | 4, 10 => 0x1020369d8d0001bd5a76340006f530207f9f8f0003fdfe7e3c000ff7000000802f007fe03e6203300080000000000f007fe03e0000000000f83e000084c01080081257085294f83e000080c00000000203000000a314cb80b7c05ee7ee8adf457b9ffbbeef80ffc07feffe03ff01ffbff7dfff90007fe3e03e4001ff8f8035876f80007f83e03e0001fe0f8040080fbf91ffa427c204bc13ff8100000f9f000f8001c0003c01ff8000000fb210d90022820088012f8000000f8000000000000000000f80e83c000884c410800913ff89fbf4f83e000080c000000003ff01ffb0
  | 4, 11 => 0xffffff1884cc10800913ff89fff4f9be6f8080c000000003ff01ffb05ceb347f483fa19819fd21fe84e00441107f003f801001fc00fe0040f83e000084c010800103db806300f83e000080c000000003c300000000000244fbe26f7d002010104200000000007f007fec00000000000007c1fdbb221d8842ffddefefbdff07c1ffff003f8013fffdfcffffffb7d7fe10004843e0304001210e0030060000004003e00000010000000000008123008c60468c4746108b0000000000000000000000000000ffffff7ed8ff211f8121b891ef60fffffffff0ff801fc183ffc1fff8
  | 4, 12 => 0xfffff0406e207bd83dfb47fc10fefffff060fff07ffe3fffc3fe007fa314c8000080fe002000027f7800c218800000807c000000023ff000e71dc9a311fffe22e2048efff981c619800000bffc00000002fff000e71dc8010cbfff8038fe47fff894c619800000bffc00007c02fff00004c134f76b3bef7876ec0076000b0441107f0f3ffff03ffc00fe0047e71dc80000bffe0020000233f800c0180000008ffc0000000201f000b7d7ff9026485be03eda476d1f9e31866f80004003e03e0001000f80fbff0148f6e418c00d13ff89fff4f9be0000f0c000000003ff01ffb0
  | 4, 13 => 0xc035bb00000002dfddec0005ff01c07fff00000013fffdfc000fffb7dfff9000f94be03e4003e52f80339f6f8000f003e03e0003c00f804bff016ffff7bc5fc5bfffdef17fcfff907ffffffc1fc1fffffff07f0808006272b108028189cac4200a0a59006070b000020181c2c000080820006fff00001fc1bffc00007f0860107fff00001fc1fffc00007fa715c800009ffe002000027ff80000000000000ffc000000003ff000fffff0406a206b5835e900f4006afffff060fff07ffe3fffc3fe007f18e237ffff5f81ffdffffd0287ff39e67fffff4f83fffffffd000fff
  | 4, 14 => 0xfffffffed0ff43ffbf41b9a1efe0fffffffff0ff83ffff83ffc1fff8b7d7ff1000480000000000010f0031866f8000400000000001000f80ffffc86648bfff1821a902fff800c659806000bffc00018002fff0005ceb347f483fa118117520ba84600441107f003f801001fc00fe0040a7d7c800000842002000002108000000000000000000000000000000a715cc3f001fc200200420238c000000001f000f8000000000000000b7d7fff77b7beffffeec01770f8b37c7ffff7f7ffffffffc01fe0fcf4828006b6e35b81ac1bfeedeb07fce79907fffbffc1fc1fffefff07f
  | 4, 15 => 0x4828006efeb7381f81bbfadce07ece79907fffbffc1fc1fffefff07fefdfc86262bffe40258943fff80ac659806000bffc00018002fff0005ceb37ff487fa1f81ffd21fe87e035c77fff007f83f03ffc01fe0fc0b7d7ff98004c43e03e4021218f8031866f80004003e03e0001000f8000000fbf91df8427c204b803ef0100000f9f000f8001c0003c01ff8007c1fdbb001d8002f7cda8e7ad6b07c1ffff003f8013fffdfcffffffe31cc80000a27e00200002117800c218800000807c0000000201f000ffffff7ed0ff001f8111b889ef60fffffffff0ff801fc183ffc1fff8
  | 5, 0 => 0xfffffd7f7affff5ab5fdebfffd6acfdf907f70fffc1201fdc3fff0480bdf006240b10800018902c420000259006000b00000018002c00000a715c8000008c6002000002318000000000000000000000000000000f83e024cffe67ffd00223310c600f83e0000ffc07fec0002030000000000000000004300304000200000000000000000000000000000000058eb006a40350000019920cc84600041006000300000018000c0000007c1ffb33319ce67f6cc0066000b07c1ffff7f3ffffffffc00fe004ffffffc7f6abfff5835fd63fffc6ac659907f00bffc1001fc02fff040
  | 5, 1 => 0x5ceb347f483fa51811fd20fe94600441107f003f801001fc00fe0040f420fc990c0cf3987a76243b9cf5f420ff9f8f0ffffdfe7e3c3ffff7081e000004c010800913cf883194081e000000c000000001c300000003c1016272f1084284888844210a03c1006070300002018000c0000818e237ffff4085ffdffffd0217ff39e67fffff4003fffffffd000fff000000002f007fe004aa4354000a000000000f007fe00000000000000000028591c28425420414025281000000000000000000000000000018eb37ffff7101ffdffffdc407ff39e77fffff7003fffffffdc00fff
  | 5, 2 => 0x400800812f22ffe07efe477e109f000000000f007fe03e7c003e000718e233c0ff4001ffdffbdd0003ff39e67fe0ff4003fffffffd000fff00000008040410800913ef89bdf400000000000000000001fc01ffb007c1fff7593be73ff2640032000107c1ffff7f3ffffffffc00fe004ffffff06fffb7ffdffdfffffef07ffffff07ffffffffffffffffff07ff83e000804041080091363888474f83e000080c000000003c3000030f83e0244ffe27ffd002213185200f83e0000ffc07fec0002030000005ceb35ff59ffa53ad3fdacfeb5e10441107f003f801001fc00fe0040
  | 5, 3 => 0x18e237ffff4011ffdfffff0817ff39e67fffff4003fffffffd000fff07c1fdbb011d8422ffddecefbdff07c1ffff003f8013fffdfcffffff07c1f0406a206b5834e80074000a07c1f0607f307ffe3ffc00fe004fa715c800000842402400012108000000000000000000000000000000f83e0244ffe67ffd00221398c200f83e0000ffc07fec00020300000000000c3f009f840000042003fc000000001f000f800000000001f000e73dc80d8dbffe1d603636fff875c639901f8fbffc1dc07e3efff0770000020c91c604250000bc01ff80000000000000000000003c01ff80
  | 5, 4 => 0xf8ff0244ffe27ffd002213104200f83e0000ffc07fec000203000000a000ca80850056a56a0214015a95f020ef808f007fedfe023c01ffb7ffffff7fd8ffa11f91fdb8ffef60fffffffff0ff801fc1fffffffff85ceb347e403f00180101208084600441107f003f8010018000c00040ff3fcf9884cc52a02b13ffa9fff4f83e0f8080c000000003ff01ffb0a715c80000087e002000023108000000000000007c000000000000001ccb34724039010011c900e404000041006000300000018000c00000fffffc7fffbfff1ff1fffefffc7fce79907fffbffc1fc1fffefff07f
  | 5, 5 => 0x18e236ddef0001fd5fff750006ff39e67fffff4003fffffffd000fff5ceb347e483f211811f920fc84600441107f003f801001fc00fe0040e71dc80000aafe002000027f5800c018000000807c000000023e0000e71dc80000287a00200002fd0800c619800000b07c00000002fe0000f83e0244ffe27ffd082213104280f83e0000ffc07fec00020300000017c3fdbb001d8102ffddecefbdff07c1ffff003f8013fffdfcffffffe71dc80000bff600200000bbf800c619800000bffc00000002fff000f83e02c4ffe27ffd6e225710529ff83e0000ffc07fec3e0203000007
  | 5, 6 => 0xe71dc80000bf5e0020000281f800c619800000bffc00000002c1f000e71dc800002a62002000003108000000000000000000000000000000a7d5fff7fffbfffffeeedf777b9ffffffffffffffffffffffffffffff8280244ffa27fbd002212104200f8380000ff807fec000202000000e71dc80004bffe80200203fff800c619800000bffc00000002fff0000000008981c484204204bc03ff81000000000000000000003c01ff80fffffc1800bfff00315122fffc60c619800000bffc00000002fff000a7d7c900004842402400012109000186000000400000000001000000
  | 5, 7 => 0xff3fc80000bffe00200002fff800c619800000bffc00000002fff00000000f9101488420420404031f8100000f8000000000000000000f80f83e000884c4108001133388c660f83e000080c00000000203000000ff3fcc3f00bffe00211522fffc60c619801f00bffc00000002fff0005febfff77b3bef7ff6ec0076000b07c1ffff7f3ffffffffc00fe004f000000812fc0ffe07efecf7e319f000000000f007fe03e7c003e0007f420fe9daf0efffd7efe777fdefff420ff9f8f0ffffdfe7e3c3ffff7000000810d00f7a07a76043a1095000000000f007fe03e7c003e0007
  | 5, 8 => 0x80a0fbf91df8427c305bc83ff8100000f9f000f8001c0003c01ff80f83e0244ffe27ffd002213104600f83e0000ffc07fec000203000000b7d7ff90b74843e7fe42dd210f9f39a66f80ff4003effe03fd000fbff83e000884c411801953ffa9fff4f83e000080c000000003ff01ffb0e71dcb80b7fffee7ee02dffffb9fffbfef80ffffffeffe03ffffffbff83e02c5ffe2fffd46ae5756528bf83e0000ffc07fec000203000000fffffcff6fbffff87fff67fffcffc659907f0fbffff03ffc02fff047e71dc80000bfff00304002fff800c619800000bffc00000002fff000
  | 5, 9 => 0xf83e0244ffe27ffd00229b106300f83e0000ffc07fec000203000000f83e0244ffe27ffd00aa13544200f83e0000ffc07fec000203000000b7d7ff90004843e03e4043210f8031866f80004003e03e0001000f80e71dc80000bf7a00200002fde800c619800000bffc00000002fff00007c1fd3b001d8002c19deccfbd7f07c1ffff003f8013c1fdfcffffffe71dc80000fffe0020008afff900c619800000bffc00000002fff0000bdf0162623108428589cbc4210a0bdf006070f000020181c3c00008a0140000000042000000000000000000000000000000000000000000
  | 5, 10 => 0xa715c800003bee0020000077080006018000003ffc00000000fe0000582a00cd6f26fff87fff67fe94ff000000000f007fe03e7c003e00071ce337ffff4801ffdffffd2007ff39e67fffff4003fffffffd000ffff83e0244486263f800200110020030060000004003e000000100000018c237f2724001e29fc9c900078a39c66fe0704003e23f81c1000f880bdf036272f108628589cbc4230a0bdf006070f000020181c3c00008b7d7ff9000c843e03e4089212f8031866f80004003e03e0001000f80b7d7fc90000843e03e4001210c8000000000000003e03e0000000000
  | 5, 11 => 0xf73dfe9d8dbfffbd7a7636fffef5f639ff9f8fbffffdfe7e3efffff7e400c800000ef6002000003bd800c4008000000ffc000000003ff000e01c00000484108008124789f894c01800000080000000000201f000e71dc800003ffe00200002ff980004010000003ffc00000000fe0000f83e000885c414a00913ff89fff4f83e000080c000000003ff01ffb0a314c8000000420020000001080000000000000000000000000000005fff35767afb295a95e9cbf4250a0bdf006070f000020181c3c000081fe3ffffff5d81fffffffdefbfff3fe7ffffff7f83fffffffdffffff
  | 5, 12 => 0xffffff7ef2ff085f8589fbc5ef6afffffffff0ff801fc183ffc1fff80bdf016250f100028101888021000bdf006070f000020181c3c00008a715c80000bbfe00200002777800c619800000bffc00000002fff0005ceb36ffd9ffa53d53fd34fed6e10441107f003f801001fc00fe0040e71dc800b7bffe07e002defff81fce398000ffbffc0fc003fefff03f4020000d8d06b41d4036341ad075c420901f8f0ffc1dc07e3c3ff077081e012210d100028101cb802100081e000000c000000001c3000000ffffff90004843e03e4001210f8031866f80004003e03e0001000f80
  | 5, 13 => 0x482800efffb7fffffffffffef0ffce79907fffbffffffffffefff07f000000012f00bc0040be465e101f000000000f007c00007c003e000714c33f9000480120124000210f8000000f8000000000000000000f80f83e0008848410800913ff88f074f83e000080c000000003ff01f030fce2ffffff4ef7fffffffd3bdffffde6ffffff4ffffffffffd3fffff03d5012232d108428589cbc4210a0bdf006070f000020181c3c000085c2b0044483fa118002000fe800004010000003f8000000000fe000018e23798844001e01f53fd0007f439a66f80804003e03e03fd000fb0
  | 5, 14 => 0xe71dcc3f08bfff0030fc22fffc00c619801f00bffc00007c02fff000b7d7ff90004843e03e4005211f8031866f80004003e03e0001000f80fffffd7f58ffff1ab1fdaafffd60c659907f00bffc1001fc02fff0404008000000b7bc00000002def000c619800000bffc00000002fff00000000fbf95df94a7c206bf03ff8100000f9f000f8001c0003c01ff80a314c00026005ac02c024300001efbbee000ffc07fee3e03c300003f4828006ed0b7001f8101b880e060ce79907ff0bf801fc183fec1f078ef3dc8406ebffe1821bb42fff87ece799060ffbffc1e01ffc2fff07f
  | 5, 15 => 0xa715c800040852802812472918940000000000000000000000000000e714c800008efe002000023bf800c6188000008ffc000000023ff00000000fbf91df8427c204ff03ff8100000f9f000f8001c0003c01ff8054cb3410003fa100104000fe840004010000003f8000000000fe0000fbff0366f2f3085f8589dbc4630afbff0060f0f0000e0183c3c000081020379dbf4001ffde76fd0007ff39a67f9fff4003fffe7ffd000fffe71dc80000bfea00200002ffa8000619000000bf8000000002fe0000b7d7ff10004843c03c4001210f0031866f80004003e03e0001000f80
  | 6, 0 => 0xe71dc80000bffe00200006fff880c619800000bffc00000002fff000e71dc80008bfff00202002fff800c619800000bffc00000002fff000f83e0244ffe27ffd093353984274f83e0000ffc07fec0003c3000030fffffc7f48bfeb1831fd22ffac600659107f00bf801001fc02fe004000000e9d8d0ef7a57a76343bde9500000f9f0f0fffe1fe7c3c3fff87ffffffffd9ffff3ff3fdbeffffe1c6599fff00bffc11c1fc3effffc018e237ffffd101ffdffffd0027ff39e67fffff4003fffffffd000ffff4e3fe9d8d0ef7bd7a76343bdef5f420ff9f8f0ffffdfe7e3c3ffff7
  | 6, 1 => 0x7c1fff77b7bef7ff6ec00770f8b07c1ffff7f3ffffffffc00fe0fcf07c1fff77b3bef7ff6ec4376000b07c1ffff7f3ffffffffc00fe004f10020fbf91df8427c204bc03ff8100000f9f000f8001c0003c01ff80b7d7ff9000484be03e4003650f8031866f80004003e03e0001000f80e71dc80400bffe00200002fff800c619800000bffc00000002fff000fffff16272f1085a8589cbc4216afffff060f0f0001e0183c3c00078ffffffffffff01ffdffffd81efffffffffffffff83ffffffffc1fffff83e0f9c95ce14a50b13ff89fff4f83e0f8080c000000003ff01ffb0
  | 6, 2 => 0x5ceb357f487fa11811fd20fe85600441107f003f801001fc00fe0040b7d7ff900048c7e03e4001231f8031866f80004003e03e0001000f80f83e000894c410800913ff89fff4f83e000080c000000003ff01ffb00300c98000000002ee00cc01399f0380ef8000000003fe01fc01ffbffffffc7f48bff31831fd22fffc60c459107f00bf801001fc02fff040f7e1ffbf8d1ff7bffffffcfffffff7e1ffff8f3ffffffffffcffffff58ea37ffff6221ffdffffd1007ff39e67fffff4003fffffffd000fffffffff9884ffffe03f53fffffff4ffbfef8080ffffe03e03ffffffb0
  | 6, 3 => 0x10c00b18018fe477e10940000000000000000007c003e0000f83e067ffffffffd00263312c600f83e001fffcfffec000203000000f7dffc3f00bfff00304422fffc00c619801f00bffc00000002fff000fffffcff49bfff3873fd26fffce1c659907f00bffc1001fc02fff04003150000000000000000000000000000000000000000000000000000000000012a00a94014fc437e000a0000000000000000007c003e0000a7d5ff3a90dd00078101b881ef60fffffffff0ff801fc183ffc1fff800000380004000e00e000100038031866f80004003e03e0001000f80
  | 6, 4 => 0xb717c80000084300200000210800000000000000000000000000000000000089afc4ffe07efeff7fff9f000000000f007fe03e7c3c3fff87e7dfc80000bffe00200002fff800c619800000bffc00000002fff000f83e02c5ffe2fffd7e6617325281f83e0000ffc07fec3e0203000000bff7ffffff4843fffffffd210fff39e67fffff4003fffffffd000fffe71dc80026bffec02c9a47fff89ec619800000bffc00000002fff00000c037bbb74000e7dfdffd0007ff39e67fffff4003fffffffd000fffbbf6ffffffc05fffffffff017ffffbfeffffffc07fffffffff01ffff
  | 6, 5 => 0x4912f08ffe07efe477e149f000000000f007fe03e7c003e0007000000010800e30030fc007e00000000000000000000007c003e000018e2377efe4001df9dfbf900077e39e67fffff4003fffffffd000fff07c1ffbf91df8427ffddfcefffff07c1ffff003f8013fffdfcffffff00000dbb001d8002c204ac03bd8100000f9f000f8001c0003c01ff80f73dfc1d08bfff18307422fffc60c619901f00bffc10007c02fff040ebdf016272f118428589cbc4610acbdf006070f000020181c3c000085ceb347f483fa11811fd24fe94e00441107f003f801001fc00fe0040
  | 6, 6 => 0xe020ca8d8d06f6bd6a36341bdaf5f420ff9f8f0ffffdfe7e3c3ffff70bdf016272f108428589cfc4318a0bdf006070f000020181c3c00008bfdffc7240b94b0031c902e52c000259006000b00000018002c000000bdf016272f1094295c9cbe4210a0bdf006070f000020181c3c00008b7d7ff9080c843e03e4011214f8031866f80004003e03e0001000f80f83e0244ffe27ffd003213184200f83e0000ffc07fec000203000000e71dc80000885200200002214800c018000000800000000002000000f83e0366fff37fff8123db906300f83e0000ffc07fec0003c3000000
  | 6, 7 => 0xbdf016272f18c428589cbc6310a0bdf006070f000020181c3c00008f83e041884cc10800913ff89fff4f83e000080c000000003ff01ffb0a71dc80000884200200002a128000018000000800000000002000000582a047f483fa1180024201284000000001f000f800000000000000000c300812f00ffe07efe477e109f000000000f007fe03e7c003e0007ffdffc7240bfff0031c902fffc00c659806000bffc00018002fff00058e237ffff46b5ffdffffd1ad7fffde6ffffff4ffffffffffd3fffff0bdf016372f18842858dcbc6210a0bdf006070f000020181c3c00008
  | 6, 8 => 0x7c1fffffbffef7ff6ecbc77ff8b07c1ffff7f3ffffffffc3cffffcf00000fb7111b8427c2040002000100000f9f000f8001c00000000000f83e0244ffe27ffd042213104200f83e0000ffc07fec000203000000f734ff9dbfcefffffe76ff3bffffffbeff9fffcffffffe7fff3fffff03d701002240084004884344010a01860000004000000000010000005bff016e7af7295a85b9ebdca56a0bdf006070f000020181c3c00008fffff0c16f20fff87fff47fe10fffffff060fff07ffe3fffc3fe007f000000002e007bc03cfa437c001e000000000f007fe03e7c003e0007
  | 6, 9 => 0x812f82ffe07efe477e509f000000000f007fe03e7c003e0007a7d5ff90004842e03e4001210f8031866f80004003e03e0001000f80e71dc88000bffe20220002fff880c619800000bffc00000002fff000b7d7ff910048c3e03e4401230f8031866f80004003e03e0001000f8003c10162723108428589c8c4210a03c10060703000020181c0c00008e71dc80000ae7e00200002b9f800c018000000807c0000000201f000e71dc8677bbffe1fe0ac02fff80bc659907f7fbffc1fc1fc02fff04ffcff347fccffb19811ff33fec660fc7f107f80ff801001fe03fe0040
  | 6, 10 => 0xef3dc86f48bffe1821bd22fff860c659907f00bffc1001fc02fff0404ccb0062403fa000018900fe800004410060003f8000018000fe0000fffffeddef2efffd7fff77ffdeffffffffffffffffffffffffffffff00000fbf91df84a7ca04bd03ff8100000f9f000f8001c0003c01ff80582a006fffb7bc1fc1bffedef47fce79907fffbffc1fc1fffefff07ffc3efeddffeefffd7a76373bdef5fc3eff9fffcffffdfe7e3f3ffff7f02002048d0277bd002210104200f02000008f007fec000200000000e71dcd3f10fffe02a004aafffd00c619801f00bffc00000002fff000
  | 6, 11 => 0x81e0ffff3ff8c67c204bf03ff81081e0f9f70cf8001c0003f01ff80a715cb80b7c85ee7ee02df217b9ffbbeef80ffc07feffe03ff01ffbf07c1fed56b2aef7d76ec0076000b07c1ffff7f3ffffffffc00fe004ffc28feffffbfffbffbfffefffefffe79ffffffbffffffffffeffffff0000008127009ce04e9e474e109f0000000000000000000000000000fffffeddcd2ef7bd7b7734bbdef5fffffffffffffffffffffffffffff83e0244fbe26f7d002010104200f83e0000ffc07fec000203000000482800efffb7bc3fc3bffedef0ffce79907fffbffc1fc1fffefff07f
  | 6, 12 => 0x5ceb347f48bfa11811fd20fea4600441107f003f801001fc00fe0040fcebfeffcd3ff7bd7bff34ffdef5f461ffff8f3ffffdfffe3cfffff75420341d080ea1181074203a84600400101f000f8010007c003e0040a314cb00b6c05ac7ac02db016b1efbbeef80ffc07feffe03ff01ffbfa314cb80004042e02e0001010b8031866f80004003e03e0001000f805ceb34ff483fa13813fd20fe84e00441107f003f801001fc00fe0040b7d7ff9000484360364000210f0031866f80004003e03e0001000f80ffffff7efeff7bdfbdfbfbfdef7effffffffffffffffffffffffffff
  | 6, 13 => 0x31d012232f108428488cbc4210a0219000000b00000000002c00000f83e0244ffe27ffd002213906200f83e0000ffc07fec000203000000ff3fc80908bfff0031fd22fffc60c619800000bffc00007c02fff000a715c880000842202200002108800000000000000000000000000000fffffe5cc02e001d01013081ce60fffffffff0ff801fc183ffc1fff8b016000004401080081247091f943006000000400000000001000f80ff3fc84c48bfff18213122fffc60c619800000bffc00000002fff00018e237ffffc01dffdfffff0077fffbfeffffffc07fffffffff01ffff
  | 6, 14 => 0x8812f9fffe07efe477ff89f000000000f0fffe03e7c003ff007b7d7ffbf005fc3e03e4421238f8031866f9f004f83e03e0001000f8000000000008204000000000040000000000000000000000000000000f83e000880c400000101b881ef60f83e000080c000000003ff01ffb0f420ffbf9ddff7bffa76bc3bfff5f420ff9f8f0ffffdfe7e3c3ffff71bff37fffff109ffdfffffc427ff3bff7ffffff003ffffffffc00fff08c20162724000428589c900010a09c60060704000020181c1000008fc3efe9d8dcef7bd7a76373bdef5fc3eff9f8fcffffdfe7e3f3ffff7
  | 6, 15 => 0xf912f48ffe07efe477f1f9f00000f800f007fe03e7c003e0f87ffffffffd1ff843fc305bc83ffe1fffffffff0ff801fc183ffc1fff85fff35ff7ffffffaffffeffeb5ff0fdf107f7ffffff23ffdc3fe004fbfdffff2407943e03fc901e50f8031c76fe0007003e03f8001c00f80000000810800e3e03efc017e008000000000000003e03e7c003e000007c1fd3a001d00028101a881ad6007c1ffff003f8013c181fcc1fff80000002b00158002c19decceb07f0641907f003f8013c1fdfcfff07f4409080000bfa400000000fff80004010000003f8000000000fff000
  | 7, 0 => 0x8cb00e36f31ffe07fff47fe109f004100600f307fe03ffc00fe0007031d0fbf91ff8c27c204bec7ff8102190f9f00bf8001c0003ec1ff800bdf016af2f508428589ffc5ff8a0bdf006070f000020181ffc1ff88ffffffff7affebfabffdebffafea3fdf7fff70ff83f23ffdc3fe0fc8b7d7ff900048ffe03e40037f1f8031866f8000407fe03e00013e0f80ebdf016272f518428589cbcdf90acbdf006070f000020181c3c1f008f7dfffbf91ffffe7fe44bfffff81f79fef9f00ffffe1fe003fffff80a7d5ffbbb7dddee7ffdfffefffffffffffffffffffffffffffffffff
  | 7, 1 => 0x4fdf016272ffa8428589cbfea10a0fdf006070ff80020181c3fe0008ffffff7ed0fffe1fa101baffff60fffffffff0fffc1fc183fffffff8a01400000000000000000001080000000000000000000000000000000000000000000000000000000000000000000000000000000000000018220244ff4001fd00221100020038260000ff4003ec000201000000fc3f0244fffffffd002213fec200fc3f0000ffffffec000203fe0000081e00812fc0ffe07fffcffe319f081e00000fc07fe03e7dc33e000700000800009ffe002000027ff80000000000000ffc000000003ff000
  | 7, 2 => 0xe01c000000801000000002004000c0180000008000000000020000005ceb3fffffffffffffffffffffff04411fff0f3ffff1fffc3cffffc700000f90004843e03e4001210f8000000f80000003e03e0000000f80a314cb0090c00007800098016b00fbbeef80f0c0000fc003ff01ffb840080000002220000000001000000000000000000000000000000000fffff048eee47bd83dfbfffdfffefffff060fff07ffe3ffffffffffff83e0fbfbfdfffe7fffffffffffff83e0f9f8fcfffe1fe7fff3fffb7f83e000084c4108000021389fa00f83e000080c0000000020301f000
  | 7, 3 => 0xe7dfc90000fffe40240003fff900c79f800000fffc00000003fff000ff3fcfbf95fffea7eb17fffffff5fe3f8f9f80fffc01c003ffffffb0b3d70100004000c00c0001010f803186000000400000000001000f80fb3f000884f518800913ffcdfff4fa3f000080f000000003ffc1ffb00000008027005ee06e024700109f000000000f007fe03e00000000070000002f91978407c004bc02f0010000001f000f8001c0003c01f000b0160280004043e03e400120028030060000004003e03e0001000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  | 7, 4 => 0x582a00446f227ff8002203100000000000000f007fe0000000000000f71fca0000ffffe0200003fffa00f61f800000ffffe0000003fff000fffffdbb84dd9082ffdfffefffffffffffff80ff8013ffffffffffffefdfcffff3fffe67e78dffffff8bcfdf8fff70fffc03c181ffffff880bdf016240710040058901c4010001c7006000700000018001c00000f83e0244ffe27ffd082213114f80f83e0000ffc07fec000203000f800000000000000080080001000080000000000000000000000000000000000000000000000010000800000000000000000000000000000000
  | 7, 5 => 0xff3fca4cfffffffd2933fffffff4fe3f8000ffffffec0003ffffffb0fffffffef7ff5effef03ff81ffffffffffffffffffffff83ffc1ffff00000000000043e000000100000000000000000003e00000000000000701c800003bee0020000076000006018000003ffc00000000fe0000081e0244f3e20c65000013004200081e000070c0000000000300000010020000000000000000000004000000000000000000000000000000b7d7ffbb005dc3e2ffddedefbfff37c7ffff007f83f3fffdfdffffffe81e000000c410000101cb89f900c81e000000c000000001c301f000
  | 7, 6 => 0x5cff347f48ffa11811fdebfea5600c5f107f00ff801001fdc3fe0040fbff0fffffffffffc7afffd7ff8bfbff0fffffffffefc183ffc1ff88f83e0044cce23198002213104200f83e000080c00000000203000000000000812f0001e05efe4500009f000000000f0003e03e7c00000007fcff3fffddffb5bfdbfffffffff5fc7f1fff80ff8011c1fffffffff00000063f91df842500043002c6000000001f000f800000000000000000000000001f800000000002800000000000000f8000000000000000031d000022b10840048843c4200a0219000000b00000000002c00000
  | 7, 7 => 0x2200110000000000000000000000000000000000000000000003d70fbf91df8467c604bd03ff8101860f9f004f8001c0003d01ff80ff3fc889afffffe07ffffffffffffe3f80008fffffe03e7fffffffb7a0140200b7c05ee5000213004200f83e0000ffc07fec00020300000000000f3e90df00078000b801ef0000000f9f000f8001c0003c01ff8000000fbfbfdfffe7c226bf13ff8100000f9f0f0fffe1c0003c01ff8003df010000f10840040003c42100039f000000f00000000003c00000b0160080004043e03e4001210f8030060000004003e03e0001000f80
  | 7, 8 => 0x84000000000210000000000000000000000000000000000000000400fe802812477e10940000000000007c000000003e0000e71dc80880fffe002000beffff80c619800000bffc0000003effff8000c3000000000000000000000000000000000000000000000000000000000100004000000000000001000000000000000000000000000000b0160000004000800000010002003006000000400000000001000000fcff367ffffffffd19fffffffff4fc7f107ffffffffc01fffffffff0fffffdfb6e3dfbdaffffefffbdffffffffffffffffffffffffffffff
  | 7, 9 => 0xfcff347f48bfff1811fd22fec460c459107f00bffc1001fc02fe0040ffffff7ed4ff109f8913ff89fff4fffffffff0ff801fc183ffc1fff8e71dcf9000fffe20220002ffff80c6198f8000bffc00000002ffff80000000000100042000000000000000000000000000000000000000005fff347f48bfa91811fd22fea4600659107f00bf801001fc02fe0040bfdfffd072e84be03e4003210f80399e6f8070c003e03e0003000f8008df006272f10840018903c40000085f006070f00000018003c00000e31d000000b37e00000002d46000c219000000b07c00000002c00000
  | 7, 10 => 0x812b00ef6076ec0076000b000000000f007fe03e7c003e0007b01602002f407fe0002203100200300600000f407fe0000001000000f83e000004001080091343880074f83e000080c000000003c3000030e41d000000bffe00000002fec000c419000000bffc00000002fe0000a314cb81bfc0ffe7fefedf7f7b9ffbbeef80ffc07feffe7fff3fffbf03c10122001100028589c8c4210a03c10060003000020181c0c000085ceb347f6f3ffff811ff23fe84600441107f0f3ffff001fc00fe0040031d000000b1fe00200002fe30000219000000b07c00000002fe0000
  | 7, 11 => 0xe01c0fbf91df9427c204be8bff81c0180f9f008f8001c0003e01ff8000000008000400000000200084000000000000000000000000000000e01c000000a67e0000000299f800c018000000807c0000000201f000e01c00002fa27fe0002203104000c01800000f807fe0000002000000b0160200004043e0080001010f8030060000004003e0000001000f8000c037f77b00017fd6ec0000000b01c07fff7f0003fffffc0000004ff83e043f84df90800917ff8bfff4f83e001f80cf80000003ff01ffb0e71dcfbfbfffffe7fefeffffff9fc6198f9f0fbfffe1fe7c3effff87
  | 7, 12 => 0xfdffdfb72fd8842ffddefefbdff0fdfffff70ff8013fffdfffffffff01e000000c4108008000389ff80f01e000000c0000000000301ff80b717ca00004843e0200001210a0030060000004003e000000100000058eb00664833211801a900d400000041006000300000018000c0000000000000220008400000030000000000000000000000000000000000081e000000c00000000003000000081e000000c0000000000300000008cb00634831a10011fd00fe0000004100600030000001fc00fe000000000881019f842042040403f88100000000000f800000000001f000
  | 7, 13 => 0xffffffd5ffeafffd7efe577f5f9ff9be6f80ffc07fec3e7e033e0f87ffffff7fffffbc1fc1bffedfff7ffffffffffffffc1fc1fffffffffffffffffffffffffffe66bf33ff81f9be6f9fffcfffedfe023f01ff800000053f10df80028004a802a5000000001f000f8000000000000000f83e0a44fffffffd00221313fa00f83e0000ffcfffec00020301f0000000000010c000000000000000000000000000000000000000000000ff3fc80084fffe80200213fffa00fe3f800080fffc00000203fff000ffdffff272ffffe2bfc9cbffff8affdfefe070ffffe23f81c3ffff88
  | 7, 14 => 0x1c000000a0080000000200000000180000008000000000020000000bdf016272f1fe42a589cbfe310a0bdf006070f07c020181c3fe0008f8ff006ac4f51080099bffcdfff4f87f006080f000000183ffc1ffb0440900812f3fffe07efe47fe909f040100000f3fffe03e7c00fe0007f83e008884c453e03f53ffa9fff4f83e000080c003e03e03ff01ffb003d70f9000480060060001010f8001860f8000400000000001000f800009000000310000000000c400000001000000300000000000c00000000000002200fe402488437e100a0000000000007c000000003e0000
  | 7, 15 => 0xe01c0fbf91fffe27c204be13ff81c0180f9f008ffc01c0003e01ff8000000081000080007edc446e109f00000000000000003e7c003e0007b81e024072e04be0000003000200381e000070c003e000000300000048280008848410000113fe88f074c8380000808000000003fe01f030b0160fbf91dfc7e7c204bd03ff8130060f9f004f83e1c0003d01ff800000000080c00000000010004200000000000000000000000000000007c1ff76503b001f80000000000007c1ffff703f801fc18000c00048ffff377fffffffff95fffbfee76affff107ffffffffe01ffc3fe0048
  | 8, 0 => 0xfb3ecbc4ffe27fffee22df117b9ffbbeef80ffc07feffe03ff01ffbff83e0081afc0ffe07efe577e529ff83e00008fc07fe03e7e033e0007081e000880c400000101ff81ff80081e000000c000000001ff01ff80b7d7f000000043c03c400120000031866000004003e03e000100000000000001000080000004000200000000000000000000000000000000080a0000000000000101008000000000000000000000000000000000fcff34ffeffffff87ffffffffffffc7f107f8ffffff03ffffffffff70000008022004be03ec84364008a00000000000003e03e0000000000
  | 8, 1 => 0xfffff7ffff607bfffffffffc07fffffffffffff07ffffffffffe0fffe71dc80000bf000000000081e800c619800000bf8000000002c1f00000000f9880cc00200200bc01ff8000000f800000000000003c01ff80000000810100c7e07e440522108100000000000003e03e0000000000582a00000000000000000000000000000000000000000000000000005ceb347f483fff1831fd22fe94600441107f003ffc1001fc00fe00400bdf057f72ff8842858debc6a50a0bdf007f70ff80020181c3c000085ceb30404820211811f900fc0060044110600030001001fc00fe0040
  | 8, 2 => 0x81e004072e0084004884344000a081e000070c00000000003000000e01c0800009f94000000028bf800c0180000008f800000000201f00004c1343b001d800011dd20ee84600441107f003f801001fc00fe0040bbdf016272f108c28d89cbc52f8a3bdf006070f000020181c3c00f88fffff1627ef17bdabdfbcbfc217efffff060fff07ffe3fffc3fe007ff83e0000afc07fe0002213104200f83e00008fc07fe0000203000000f83e000084c01080080213014f80f83e000080c00000000203000f80ffffffffd9ffe7fffffdbdffffe135c77fff007f83f1fffc3dffffc0
  | 8, 3 => 0x18e237ffff40ffffffffff7e17ff39e67fffff407ffffffffd3e0fff0000043f80df80000004bc03ff800000001f000f800000003c01ff80e01c00000084fe00200002fff800c018000000807c000000023ff000bfdffffff3ffcfe7ffcdffe7ff8b3bdf6fff70ff83e3ff81ffc1ff8800160000004000400000010000000006000000400000000001000000b01602812f40ffe07efe477e129f300600000f407fe03e7c013e0007f83e0008afc47fe00933ff99fff4f83e00008fc07fe00003ff01ffb0f02000088404108008123409def4f02000008000000000023c01ffb0
  | 8, 4 => 0xb7d7ffbfbfdfffe7fefeff7fff9f31866f9f0f4fffe1fe7c3d3fff870bdf0fffffffffe7ffffffffff9f0bdf0fff7fffffe3fffdffffff8f081e00c17fe0ffe07efe477e109f081e00007fc07fe03e7c033e0007000000000000010010400020000000000000000000000000000000000b1f000000f108000101cbc421000a1f000000f000000001c3c00000f8fe37ffffe27fffdfffff1047fff9fe7fffffc07fffffffff000fff000000002f00ffe02022037e1000000000000f007fe00000003e0000fffffffaf6fd5be2bfdbffedfffefbff6fe0f0f003e23f83ffc1ffb8
  | 8, 5 => 0xbdf01e272f14be2bfc9cbe4218a0bdf006070f003e23f81c3c00008ef1fc84072fffe40200003fff800ce1f800070fffc00000003fff000fbff036efff77fff8dbbffddfffefbff0060fff07fee0183ffc1ffb8f83e02cdffe6fffd7ffffffffffff83e0000ffc07fec3e7fff3fffb7f83e080884df94800913ff8bfff4f83e000080cf80000003ff01ffb00000043f081fa10010fc207e84000000001f000f8000007c003e0000000000800000ffe03e40037e10800000000000007fe03e00003e0000471d000000bfa800000002fea0000619000000bf8000000002fe0000
  | 8, 6 => 0x7c1fff77f3bfffffefe477e109f07c1ffff7f3ffffffffc00fe004f0bdf004062200840058943c4000a0bdf006070f000020181c3c00008fbff0ffff7ff9ce7cf9fffcffffffbff0ffff0ff8003c183ffc1ffb8000004bf2f1fffe07efe677e949f0000001f0f0fffe03e7c003e0007f83e0244ffe67ffd00221399fa00f83e0000ffc07fec00020301f00000000000009100000000000020000000000000000000000000000000ffffc96af6fffec2ad9bfffffffeffff8060f0fffc020183ffffffb8fffffffffffffffd3fff33ffcfe0fdff7ffffffffffc3ffe03fe0fc0
  | 8, 7 => 0x80000000200200000000800000000000000000000000000000000000000084000000000001f800000000000000000000000001f0000000032691d304278000980063000000000000000000000000000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x80380180b03804180e80704400c0500060080840180b00202580202000607c0080060080380180d00207980e80700602c0e000603601c0180d00206980c80e00603400800600801c0c00b02e05980200700602c05009602a0500980d00200180900702202c00810601e0100700301a00580200701802c05009601001c01801000019802804006008008006
  | 6, 0, 1 => 0x801c0180b0140b98168070060340080060080381600d00200180e80700602c1580060080801300b01400180200704c0340080960540a40580100005980200305002c0080960080800180d01400180200e0060341380060080801300b00202580780400e0980580a600e00c1280d00200181201d00e00c0080060080800180d00202581180400e00c058096
  | 6, 0, 2 => 0x80800180d0020418028040060ec00800600801c1d00b07205980e82000602c00809601e0740380301602980200301600400038606e0d80980d00200180c80e00602c0e00060080d40180d00200180900702203400800600801c0983401a0cd80200700600400032602401c0180d00204180e8030620340080060600100180d00200180380305e02c050096
  | 6, 0, 3 => 0x3a01c0180d00204180200708402c0080960081040180d00200180780404000c06801602401c0880b03800180204000602c0083f607c0100180d00200180200704c02c00809603a0f40180d00200180202000602c00809600801c1a00b0020f180781200e00c0680160080800600b00202580200e0060340080060080800880d00200180200e018034008006
  | 6, 0, 4 => 0x801c1100301402581181d00e00c05800602401c0180d03800181200401c00c00800601e0740380301a00580382605e02c05000600801c1600d00207980382605e02c00809600801c0180d04e07980280408a0340080060080801300d00200181180400e09805800604000c1780b00202582200400e00c0500960860100180d00200180700305e034008006
  | 6, 0, 5 => 0x6e0d80580100005982580700600400006600801c1300b01402582200400e09800809600801c058010001298020070060340500960080800180b01402582200404000c0080960080800180d0020018038030920340080060080800600d00200180200709002c00809600801c0180b07211d8020070260e806839603a0800180d00200180200704c02c008466
  | 6, 0, 6 => 0x240380180d002001802007044098008096
  | 7, 0, 0 => 0x801c0985c01a0040038050080f40180d002001c0200700602c0080007ee16c020070a204c1a00b70b4144098030b200400385800804c0180d002001c0200700602c2b80002ce0100381300615800855702a0502a01301600400380400e00c0580a012059c2980500800c06801000e1480200700603400800700e1442800301600400380400e13c0980d002001c2700700602c0080009ae0640381300602c260007
  | 7, 0, 1 => 0x81982881303002c0bb81d00e03005801000059c0c80702600c0581c020e0480380301a00400065700e1900180b0020000b381b0080f40180d002001c020070c602c0080002ce0800182f0160040001670080f43100301a00400384400801c0180a000059c0780400e04c0880b038e0101e86100603400800700801c0980307600400380400e18028803002001c2f80407a04c0180d000e0102885e00602c2e8007
  | 7, 0, 2 => 0xa6010288130061c037b80400e0e805801000059c3700702600c06801000e01c0182f01a00400016700e1b4288030160040038040d81440980b002001c0e80700602c0080002ce010038130060342600070000100380301602804b01b00e1ac0180d002001c3500702600c06801000e1a40200700603400800703a01c3400301602800381900e04c0880b038001c1b06700602c0080002ce01011003062004000167
  | 7, 0, 3 => 0xe0981780b0020000b38070260441780b002041c3d01200e00c05801000e010038130061e400800703601c0180b0020003c380400e1dc28803016001c0200702600c0681c020e17c0e80700602c0001670080380380301a00400380400e1d80180d002001c020510261d4058010dee1d00200700600400016703a01c0180b00200026b87300800c1880b002001c3900400e00c0580102ce01c288130061c4058007
  | 7, 0, 4 => 0xa0100188500200026b81900e00c06801000195c0200702621006801000e0100380310603400800701e0dc1b05102602c00b80400e0300980d002041c0200700602c4100002ce0100380310200400016700801c0180d00220000380400e04c0880d038001c038510261fc05801000e1f80385102602c19800703a01c0180d01600400380400e04c0187d0f8001c0780400e00c068010cae1ec0200702600c0581c7
  | 7, 0, 5 => 0x801c0600b0020000b380411c04c0180d002001c4680400602c0008c02ce0100380311600400016700801c0980301607045380400e2240180d002001c0200702600c06801020e0740381300602c05000700801c0180d00200044380400e00c0680103c195c0200710e00c06801000e010038030160700001670080800380301600404b87400801c0180d002001c1504405214409801000e0a82881310c02c008007
  | 7, 0, 6 => 0x801c0980313400400380401c04405801000135c0389913000c05801000e0100980301a00400097700a0100380301a0040838040a204c1d0310160e5c4b00712a2500180b000e0100382200600404816712601c2881300602c00b82400804c01831002001c020070062480080002ce010070030160040804d700800c4880b00200026b80400e04c0880d002001c0280400603400800120e0a84785102602c008007
  | 7, 0, 7 => 0x801c4a0031440040038a100801c0180b000059c5005102627c05801000e0100389e0a204c0580070be010038130220340038140a204c0589d002001c2f80400e0300580002ce010038030160040009c70360100380301a00408380500801c0880d002001c090070a208801827000e010038620060340081070fc01c0980301a00400380400e00c05801000059c2f80400e04c0180d020e0100389b006034008007
  | 7, 0, 8 => 0x3a01c3402200600400381200e00c058aa002001c2f80400e00c0580002ce01c288a800602c0081a700801c4380315200400380f03201c09803016071c0385115000c2c801000e01003803016028000a7712c01c0980301a00053380400e04c0180d002295c0200700602c5200002ce010038030160700806570e60100380301600404b80400e1880880d002001c0200714604c0180b000e0f40980305e034008007
  | 7, 0, 9 => 0x801c0180b00200003387e00e1440981801605dc3980400e00c59001000e2c40381300603400800702a2c02881301600400380400e1445781815c001c1200400e00c0080002ce010038130060341c8ad700801c4f80b0020000b38150281440980b002001c0900306202c0080009ae054038ac0160040001670e61100200700600400380400e00c058010002adc020070d004c0c00b02ee01003811016070000657
  | 7, 0, 10 => 0x801c5c01300600400380400e13c0980b038001c0a8140c414405801000e0100381300603419800701e010018310160040b380404000c058010002ddc2f8150281440980b000e010038b601600400016700801c288130160cc0bb81201c00c05801000135c0200716800c06801000e0100386816a00c00800700801c2a01306802c19b81200e04c0180d002001c298040d02d001801000e0100380301a2cc008007
  | 7, 0, 11 => 0x80382880301a0040038360a204c058c2002001c02007058034008000cae3042881300621400800700801c098c017e00400381900e04c0180d038001c1b8360a804c05801000e010038130062f800800701e0100380c02603400b80400e1441100304e079c020070a22f41d00b072e2f0020070a204c1d00b70080803400301a0040038bb00a0100180b002041c020070a204c5d00b072e0100380301a2e4008007
  | 7, 0, 12 => 0x80802880301600404b81900e04c0180d002001c0200702611406801000e03c0200e00602c0084d700831c0180b0020000b38070a204c0180b186069c020070a20881600103ce0100385117a00c40839701e0100381300603400b80400e04c6300d002001c0200718a00c06801000e0640380c02603400800700e1440980318800400380400e00c058c3000059c0200700602c1580002ce110020070a204c1d0397
  | 7, 0, 13 => 0x1e0100386200603400b8070180bc05801000059c2200407a04c01801020e0100382600602c00809703601c0180b00206826b81901c00c05801000135c0200719a33005801000e01003813006034008ca709601c2881319600465380f0be01003813006035c0200702600c0680103ce01c0980305e03400810701e0140200700603400b80400e00c42801000059c0a81402602c0080009ae01064851026320008007
  | 7, 0, 14 => 0x1a60100380301a00400385f03201c0980301a001c1b80400e02c0080002ce0a40380301600400016700801c0188100200069380401c00c0580103c135c150290d004c05801000e010100130060340080070083440180b0020000b380400e144098d0002001c1200407a04c01801000e110090070060040004d701e06c0200700603400b8040a204c0180b0ba1bdc038130220bc06801000e33c03813006034008ce7
  | 7, 0, 15 => 0x81445a04501600400380f08801003803002059c0c80700602c0e0000cae1cc0200704400c00800700801c018da0020006cb80400e04c4200b038001c020030620346c001000e0a80280400603400800700801c060130160700838040260441880b002041c0380305e02c0080002ce010038d700600400016700801c0980301a0046b380400e3542881301605dc0200700607c0080002ce01003803016004000d47
  | 7, 1, 0 => 0x801c0982601a00400380400e00c05801000349c0202000602c0080902ce010038e202606005817700801c0981101607000380400e04c0880b002385c0780400e00c0580a02ce010038130060346f80070080380180d00200026b8e00801440980301637dc0200702600c0581c020e010038de02602c00800700804c0180b0020006eb80400e1441300b002025c020dc02600c05801000e010038511b600c058007
  | 7, 1, 1 => 0xa0100381101607000380400e32c05801000059c0200700602c008001cce010038e502602c00800700801c3100301607008386e00e1440983a0160e5c2200404000c0080002ce0100381302224800800700801c3080301607008380400e04c0180d0021bdc020070060040004d1c8e0000200e00603400800600e00c1280b0020000b380500801c0180b038041c0200700602c7180002ce010038030160040003c7
  | 7, 1, 2 => 0x80380180b04e00026b8c100e00c05801000059c0000404000c05801012c3ac020070a204c0180071d401c288130160cc00380400e03006801000195c020070a204c1a00b066e0100380b0020000b0e970360100381101607000381900e04c018e8002001c0202000602c0500002ce0100386202202c0e000700801c3081101607000380400e00c06801012059c020070a204c7380b000e0100380301a070000657
  | 7, 1, 3 => 0xe04c018f101a00400380400e188288340160cdc1b8360a204c05801000e0900200702600c00810700801c0982c01a0040038b100e04c0180b038001c020071e004c1d00b072e01003826016004000ef70e80900200700600400381b00e00c058010003b9c02007006034008000cae0547685102602c00800700801c1300b0020240b38041d804c0180d002001c0200704c02c05001000e1b80385102600c408397
  | 7, 1, 4 => 0x801c7c00301600400380400e00c068010003ddc020071ec00c0080002ce01c018f50160040001670083d00180b0020000b38f300801c2881300602dc298040a22d0018010dee010038680260e80583971760140200301a00400382d00e00c05801000135c02007006164008001e4e0100702c0160040004d70480100381302200400384400801c13001000059c2200400e04c08801020e03c038130060bc068017
  | 7, 1, 5 => 0x6c19c0980301a00400380720004c0180b002001c02007026060058001fee0640380c02602c0e000700801c7f00301a0040038041fa00c05801000059c0900700602c0081009ae03c0200704400c00816700801c098031f800400380400e00c57001000059c7d80700602c0080002ce0a87d05102602c0080071f201c0180b0020000b383706c1882880b002001c0000400e09805801012c0101e80301a004000167
  | 7, 1, 6 => 0x8080110030020000b390500801c0980301a001c4b00702600c058000f0e01c0980305e02c0e01070a60100180100013482380400e00c0580100040dc3980f00801c0180b002e0100380301600400047700801c0983a01a00400380400e0d00580102c409c0c80702600c0581c000e0102881308a02c0086f70a60102881318c00437b84b14014409803002329c0200702600c80801000e0100381306802c1984d7
  | 7, 1, 7 => 0xe60101000301600400381d00e00c0580a002001c850360a204c05801000e06c0c80700602c0e000700801c288cc19000400380511a0100180d002001c0c8070c400c0581c000e0640386100602c0e000721201c0180b0020000b380400e4200980d002001c0281900e00c0581c000e01c2889820e02c0080070080800380301a00400380402600c1880d002041c1b83602602c0080009ae01003906016004000167
  | 7, 1, 8 => 0xe643c0380301600400380401c03005801000135c0380305e034008000cae0100380301a0040801670be010018310160000b387300801c0180d002001c020070440980080002ce0100710e04400c00800700801c0601301a00400380f04801003813006005c258070060040001621ae01c0182f0160040010c700e1440983405e02c19b80400e00c05870000059c0200702600c068011c2e1682881300602c0090b7
  | 7, 1, 9 => 0x801c0606201a00400380400e468288130160e5c0200723200c06918000e0100391704400c00800700801c8b01300600400380400e04c01915002001c0200702600c8a001000e0100381101a00400016700801c0980301a44c00391200e04c0180d002001c0280400e03006801000e2802881300602c0081a700801c0980301a00400384b00e44454003002001c0200722014409801000e01007003016004000167
  | 7, 1, 10 => 0x21201c2881306836800b81500e04c5600d002001c3980400e00c0580123ee010038030160040d016700801c3100301a00400380400e03005801012059c0201300647805801020e03c0900700602c0084d70080380180d01600400391d00e00c05801000059c0280400e00c06801000e1b86885102600c058397238144098750160040038070a204c0191b016005c3980400e09805801000e010070030160040004d7
  | 7, 1, 11 => 0xe1440990701600485b89600e1440989f0b2001c0a9240a204c05801000e03c020130060c406801700801c019230020000b384400801c01801000059c020510bc00c42801000e010038030160280480072440140200301a00400380400e00c05801012059c020070a248405801000e1100200701800400016700801c3400301602804b80400e4800180d002001c0c83d02600c05801020e01020051026114058df7
  | 7, 1, 12 => 0x801c2a01307402c1cb80407a00c05801000059c3980400e18c05801000e0100380301a2c80080070080383402200600400380400e04c0180b014025c020070a24a805801000e4a4020070060340080070084a00980301a00400380407a04c0880d002001c0212700602c0080002ce010100510060340080070f60101e81300602c00b80400e00c59001000059c020070061580092602ce49403803016004000167
  | 7, 1, 13 => 0x801c710af03002c00383700801c0980d002001c1480702600c06801000e0100392f02600c05801700801c0192e0020000b380701804c1780d002001c2c00400602c0080002ce0100385115e06005817700e04c0180d00200096b81b00e1a07b003002001c0200702600c05839258e0109585102600c05801701e0100380301a0040b38e00801440980310a005c1200400e00c008000cae00c1882f016004000167
  | 7, 1, 14 => 0x801c0980311607000380404000c06801000135c0200702600c9b001000e0100380c04400400016700a01c0182f01a00400380400e04c0180d26a001c2180400602c0080009ae0640381302202c0081070a204c0180b0024d000380400e04c9980d002001c0200702600c06932000e010038130160040013170080800180d0020000b380400e144098030164c1c038130060bc06801000e03c0200704c02c008167
  | 7, 1, 15 => 0x801c1300d0020000b380800e04c018010004edc3980400e03005801000e4e80205102600c00800700e00c1780b0020240b38000080800180d00200180200704400c0080002ce4e4020070260440580070081440983406202c19b80400e00c0080002c4e1c0202004c02c0080002ce06c0380305e0340080070084dc0980301a0040038070c400c1780d002001c2f82a0521440980b000e010938510260d06d0017
  | 7, 2, 0 => 0x800c058010000584bb80400e00c068010004f9c2200400e04c0181c020e010038110160040001670081002888900621400b80400e1440983a1020e5c0c83d02600c06801000e3040381300603400800700e00c1780b0140000b380400e04c9e93c002001c0200700602c1381e09ae1cc0200700602c00800700804c0191e01a00400380400e04c068010003a5c220070060bc0080002ce014020450160040004d7
  | 7, 2, 1 => 0x801c0180b07205856b80400e14409803286005c2200400e14409834066e0640980306202c0e00071f201c0980301a00400380400e1440983a0160e5c1200400e04c01801000e0100380328402c0080070962802881300630c00380400e144a0803002001c4b00700602c0001614ce03c0e80700602c0081670480100380c02600400394006c1440980b002001c0200700602c0080027ee0100382c0160040f04d7
  | 7, 2, 2 => 0x21201c0980301a00400381900e04c0180d002041c020070a204c0c0ae02ee0100393d29200400016700801c0180b0660000b380400e04c1a00d002409c1b84406c14409801000e0100385102602c1c948700801c3105107402c1cb80400e00c06947002001c1200400e18801801000e074100030160040001670083f40980301a00400380400e51806945002001c1200500801c01801000e01003851026060059447
  | 7, 2, 3 => 0x1d43242881301600400380400e00c06801000059c020070260440581c020e0100386804c02c00809700801c0600d0020000b38370a204ca680b002001c0785f00801c0180b02ce010038030160040f01672720100381300603400380400e3c05e8030160e5c3f1270a204c05801000e0100394c01600400016700801c0983a0160e426b94b0a204c0180b002001c0200717a00c80801000e01003813006034a50007
  | 7, 2, 4 => 0x98030620bc06801000e0100382c01600400016700801c2100b0020000b383706c1a00980b002001c2580702600c008002a0e0100381101a00400065700801c0994f01a00400380400e04c1300b002025c0200702653806801000e0100385100602c05009700801c5e80301a00400380400e04c0180d002025c0200704c02c0080002ce0102005102600c428df7
  | 8, 0, 0 => 0x81882880306202c00800803601c2895c00602c00800800801cad81300602c00800800e030ad05102602c00800800801c0995900602c00800800804c019580160040004d80080382881300602c00800800801c2881300603400810800801c2881300602c00957800801c28813006558aa800800801c2881300602c00954800801ca981300602c008008088010038030020002686580be010288130060c405800800801c0980301a00400152800e144098032a202c008008
  | 8, 0, 1 => 0x2ca0100385102659000800803601c2a06b00602c0080082c60102881300602c00800800801cb10030160040004d80085842881300602c00800802a144098ac06202c0080080540100385102602c00817800801cb001300602c00800800801c0180b28e0040004d800801c2895f00602c008008008280288a800602c00800800801ca30130060340080080fc01c7101300602c0080080085782881300602c0080080f60100385102600c0580182ba01c2881300602c008008
  | 8, 0, 2 => 0x801c2881306802c0096c80be0100396b02600c05800800801c2881302203400800800801c3401300603400800800801c288132d402c0080080085a42881300602c00800800801c8881319602c0080080be12c0385102600c0010d800801c288bd00620400800800801c2881300602c00968800801c3105100602c3800080540100381300603400800800801c060510160040001680880100381300600400167800801c288130ea02c0080082cc0100385102600c008008
  | 8, 0, 3 => 0x1e0480385102600c05801800801cbb05100602c00800806c144098032ea02c0080080dc01c2a01300602c00800800801c3116b00602c00800800801cba01300602c00173800e1a00980301600400172809601c310510060040010d800801c0983401600426902800801c288132e202c00800800801c2888900602c6f80082e00100385102600c0580082de010098030160040004d800801c2881300602c0096e80081440989f06202c00800800801c288132da02c008008
  | 8, 0, 4 => 0x82803105100602c00800800804c018310160700004d800801c3401300602c6f800800801c2881300602cbe0008088010340130060c400800800801c0605102602c0081a80be0105005102600c05800800e5682881300602c00800800801c288130065ec00800800801c0605112802c00800800801c098110165e800800806c01c2881313e02c008008088010038132f200c0080082f001c2881300602c00800800801c288132ee02c00800800801c06051026164008008
  | 8, 0, 5 => 0x3020100380301600400016800801c3115b00602c00800800801c288130066000080080080383105100602c00800800801c0617f02602c0080080085f80980306202c0097d80be010310510060c405800800801c060130162a80080080be0100395b02600c05800800801c2a01300636800800800801c2880301600400016801e0100385116800c05801800801c288b418c02c00800802a0502881300602c00800800801c0605104400400065800814409803016004378908
  | 8, 0, 6 => 0x801c0993d00603400800803201c098030160040804d800804c0183101600400016800801c2889400602c00800800801c0605117a02c008008008030098310160040004d800801cc285102602c00800800801c2881300616400800800801c3401304c02c00800801e0100385102600cab184800801cc181300602c00800800801c098030166080004d801e010038510264f4a4801800801c2881300602c0088a801e0100385102600c05833801e0100381302202c0084d8
  | 8, 0, 7 => 0x740380301600400016719e01c2881319602c00800800801c3401300602c0086f800801c098030162a80080080080f40180b00200026865800801c098030165280004d800e1440980331602c000a68314010c485102600c00800800801c2882200600400065802401c2881300602c0081e800801cc40030160040004d800801cc381300602c00800802a01c2881330c02c00800821201c098030160040004d80880100385102600c0e000800801c2881300602c0081a8
  | 8, 0, 8 => 0x3280100385102600c0080080880100380c0a204c0080080081445780306202c0080080be0100385100602c00016802a01c2881332602c00800800801cbf01300602c00992800801c2881300602c00991800801c0619002602c0080080a6010340130060040018f800801c2881331c02c00800800e1440980305e2b80080080882340205102600c0008c803201c098110160040004d831a01c3401300602c00800800801cbf81300602c0080081761100218c02600c008008
  | 8, 0, 9 => 0x801c340030160040481681fa1440980305e02c0080080081440980301600437897800e144a302f01651400800800e2640980301600400172800801c098030160040019a80081440980333266000800808801c2a0130060bc00800832e01c2881300602c00800800e04c0182f32c02c00800800801c288bd00602c00800800804c018310160040004d80ce1440980329a02c00800800801c2881300602c0080980880100399502600c00800800801c28813190004000e98
  | 8, 0, 10 => 0x8144d100306202c009a1800801c3401300602c13800801e010039a002600c0580180081440999f00602c0080080be0100385102600c0581a833c6740385102600c0580180be0100385112800c05800802a0100a05102602c00800800801c0980301a0040018f80be0100385102600c2c800800801c098030161c00004d800801c2a08700602c00800800801c288130066700080080281440980305e02c0080080880100399b02600c008008054010288b400602c008008
  | 8, 0, 11 => 0xbe0100385104400c00065800804c0183101a02c00800800801c3105100602c0081a800801c0180b002024000168008144099a501669000800800a010038030162a80080080081440980306202c61800800801c0605102615800926800801c2a08900602c00800800868c2881300602c0080082720100381300602c0004d800801c2881303002c0b800809601c098030020002690d801e0100385102631805801800801c2a01300602c00810800801c31051006164008008
  | 8, 0, 12 => 0x801c2a01302202c00800800a010d505100602c00800800801c310030162a800800800801c2881300602c009a9800a010018310160040004d800801c2889413e02c00800800801c2881313e16400800800801c341a802600c008008088010038680060040001680540102881334e02c0080080be0100397f02600c05800800801c0980334a0340080080be0100381300602c55000800801c098130060340080080880100385102600c00800834c0102881300602c008008
  | 8, 0, 13 => 0x9601c2881300600400138800801c289ae00602c0080080880100385123200c8c00080be0100385117a00c0580080be0100980306202c0004d800801c2881335a02c00800800e1440983405e02c0090280be1100200701814409800800801c2881300602cd6000809601c2881300630c0010d800801c3117f00602c0080083560102881300602c0080082de1440980305e02c00800800801c2881313e02c0081a8008280098030160040004d800801c2881329c02c008008
  | 8, 0, 14 => 0xbe0100380301600400016800801c28813006158009268008188018310160040004d80540102881334a02c00800801e010039b102600c058018008038098030160040004d8008184018310160040004d801e0640385102600c05801801e010038510261140580180880100380c0c414400800800801c2881329e02c00800800849c0605102602c00800800801c0980301a0040804d80880100385115000c00800800801cd805102602c00800800801c2881300602cd78008
  | 8, 0, 15 => 0x801cdb8130066d80080080081440980306221400800800801c3401305802c00800800801c0981101a0040004d800a0100381300603400800800801c2881303002c001b580081002881308a02c00890800801c0180b0020000b016800801c09803016004001b480081980605102602c0080080086cc2881300602c0080080082802881300602c6180080080f42881300602c0e000800815009803016004000978036010018310160040004d80f4010d901300602c008008
  | 8, 1, 0 => 0x801c2881327a6f800800812c01c2881313e02c00800800832428813016004000e9800e144098032ac61000172800801c3081300603400800837a01c2881300602c00800800801c0610e02602c0080081c001c0605102602c00800801e01c340130060bc0580180be110020070a204c01800800e1440980337802c0080080be0100399002600c0580083766e80980306202c0080080fc01c2a01300602c00800800801c0180b002000dc816800801c28813006558dc0008
  | 8, 1, 1 => 0x801ce101300602c00800809601c288130060040013e800801cb58130062140080080081440980338202c00800800801c0180b0020004601680dc01c2881307402c00800802a110038510262b00080080000100381300603400810700801c289a200602c009c0801e010038e202600c0580180181440983105e02c00800800801c2881300602c009bf800801c31013006034008008088010038620a200c00800800849c2881300602c0080080080f40605102602c008008
  | 8, 1, 2 => 0x100380c016004000167088010039c702600c0080080f401c0980305e02c00800800801c288cc00602c00800812c01c2a01300602c000a6800801ce301300602c0080080081440980338a02c0080080be0a8020510266940580080880100385102627c00800800801c289c400602c0080080081982881300602c0080083860100381300602c00800800801c0180b0020000b04d800801c0c0030160040001680083b42881300602c00800802a2802881300602c008008
  | 8, 1, 3 => 0x801c8701300602c00800800e7380980339a02c0080081c001c2881300602c00800800801ce60510062c800800800801c061cb02602c008008176010038130060340080083940100385102600c05800800801c098030160044504d800801c3105100615800926806e0102881306202c00800800801c289c900602c0080080b00100605102602c008008000010038130220340080070540103105134a02c00800800801c098033000040004d800801c2881300602c009c88
  | 8, 1, 4 => 0x801cea01300602ce980083a4010039d102600c05800800801c288b400602c0086f800801c0180d01600400016806e0d80385102602c008008088010038130060700004d800801c3105103002c001b5800801c2881300674000800800801c098030160040d04d80a204c0183105e02c00800800801ce785102602c00800800801c7101300602c00817800801c4a0030160040004d80080f42881300602c00800800801c0980301600404816800801c098030b20040004d8
  | 8, 1, 5 => 0x100380301600400016700849c3105100602c00800801e01c2881300602c00972800801cec05100602c0080080880100397e02600c0097d80a6010288b40060040018f800e1440980305e02c38000801e0100385102600c0680183ae01c2881300602c00800800801c2785102602c0080080be110020070c41440180080be0109385102600c05800800801ceb01300602c0080080087542881300602c0080080081042881300602c00800800801c11003002000268658
  | 8, 1, 6 => 0xe1a03201300602c008008088010038130060040001680880100380c0260040004d80be0103305102600c05800800801cba01300602c001db800801ce581300602c0080080dc01c2881300620400800800e5ac0980305e02c0080080b00102881300602c00800802401c2881300602c13800800801c0998e0160040004d80086a00980306202c00800800801c2a01300602c1c8ad800801ced01300602c00800800801c060680266d80080083b22340205102600c058008
  | 8, 1, 7 => 0xbe0100390e02600c05800800801c28813006558f1000800801c0980301a004001e181401440980305e02c0080080be3800385102600c05800800801c3401300678000800800801c288133be02c0080080320100381300603400800800801cef01300602c0080080081983105100602c00800800801c061dd02602c00800802a7700385102602c00800800801c5e8030160040004d801e1100205102600c18801802a0100380301600400016800801c578030160040019a8
  | 8, 1, 8 => 0x88010039e702600c0080080080f43105100602c00800800801c2881300602c009e680081002881300602c6f890800e144099e500602c00800800801c3110e00602c00800806c19c3401300602c0080080081a0110130060c400800800801c7801307402c0080081c001c3105100602c0080080be144098030620bc05800800801c288133c802c00800800801c061cb0c402c00800802401c2a01300602c00800803201c28813006034008008054010288133c602c008008
  | 8, 1, 9 => 0x860102881300602c00800800801c288130067a800800800801cc600301600400016800e00c1780b28e0040004d8088010038130060040004d803601cca86b00602c00800800801c2a0b400602c00800803601c060510d602c00800800801c061e902602c0080080880100385115e00c0080080c41440183105e02c0080082800100385102602c00800800e56c0980305e02c00800800801cf401300602c00800801c1440980305e02c00800800801c340130066d8008008
  | 8, 1, 10 => 0x2401c2881305802c00800800801c2a01327a5240080080be010039cb02600c058008008144099f00167bc00800800801c0994e0160040004d800801c2a01300602c1980080be1600205102600c05800800801cf701300602c00800800801cee81300602c00800800801c0180b00204026865800017c0200700602c00016700e1444c00301600400172800801cf681300602c00800803a01c3401300602c00800800801c288130167b00080080087ac2881300602c008008
  | 8, 1, 11 => 0x880100385102600c61800801e0640381300602c0084d800801c0994f0160040004d800801c3401307402c00800800801cfb81300602c0097d800801ce586200602c0080080084440980306202c0080083ec0100385102600c00800800801c2881318c02c0086f80b00103105100602c00800800801c2a013006558c2000800801c098030167d40080083e80100385102600cab00080dc01c0605102602c0080083e60100385102600cf900080f4010038130067c4008008
  | 8, 1, 12 => 0x801cf481300602c0080080000540a05102602c0080070d401c2881300602c0080080081000381300603400800800801cfd8513f402c00800800801c0981100602c0e0008008144098450160040018f800801cfc81300602c00800800801c098030ac0049304d80a60102881318c0040018f800801c0880b00200026865808801003813006034008008054010099a50160040004d800801c0980301600408167800801c061b702602c00800800801cfc01300602c008008
  | 8, 1, 13 => 0xbe0100386802600cdb000800e1440182f01600400016801e0100380c0a804c058018008144098cb06202c008008088014020070060040004d84000102005102600c05801800801c288133fe02c00800800801c0182f01600400016800801c0605102636800800800801c288af03002c001b583fc010fe81300602c0080080085d00980306202c001b9800801cfe01300602c00800800801c2881300602c26000803601c2886b00602c00800800801c311de00602c008008
  | 8, 1, 14 => 0x801d0281300602c00800800e1440980340802c00800800880c2881300602c00800801e0100385102600c058278088010038610060040004d800801c3420200602c0080080dc01c2881300602c00800800801cd100301600400016800801c310680066d800800800801c0180b0020002690480be1100200702600c0004d800801c0980301600400201800801c0980301a0e40080080e80100386802600c00800800801c7801300620400800809601c888130060040010d8
  | 8, 1, 15 => 0x801c0980341a02c0080084180102881300602c00800800e1440980305e02c0081a800801c2881300682c00800800801c311dd00602c00800800801c2881300602d05000800801c288130168240080080082808881300602c00800800e1444a00305e02c00800800801cdb81300602c00800800801d0401300602c008008088010038620060040004d800849c098030160040004d800881c098310165e80080080080f4060130160040004d80088182881300602c008008
  | 8, 2, 0 => 0x801c2a01318c02c00800800801d0a81300602c0080080be01003a1402600c05800800e1441100305e00400065800884c2881300602c00800800801cba00301600400016800801d0901300602c008008008344288bd00602c00800800801c288130063680080080be010039cb0c400c0580084220100381300602c008008008198288af00602c0080080088402881300602c00800800801c098030160040820f800814409831016004000e9800801cbf01300602c00a0e8
  | 8, 2, 1 => 0x80f4098030160040004d808801c060510260bc00800811a0100381300603400800800801c28a1700602c0080081c001c098030160040004d800801c0609502602c00800800a0102881308a02c00800800801c2881300602c0e01080082802881319602c00800800801c0980301a5e80080080be06c038510d600c0580080540102881300602c0086f800e04c0182f0162a800800800801c3401300620400800800a01028a1600602c00800801e0100385402600c058018
  | 8, 2, 2 => 0x801c2881300602c1381e800801c340130060040021c80880106885102600c00800800801c0605110e02c00800818201c2881300602c38000843601c2881300602c00800800801d0d05100602c0080080be1b80385102600c05800800801c28a1902602c00800800801c060f002602c00800800e1445e80305e02c00800802600c1882f0160040004d800801c2881306800c05833800801d0c01300602c00800800801c2881300602c2e800800801c34022006004000168
  | 8, 2, 3 => 0xa4010038030160040004d803201c2a01300602c0080080be010039b702600c05800800801c2a01308a02c00800801e010038510260b00580180dc01c3105100602c00800801e010038130060340084d800801c2880301600440000800887c2881300602c00800800801c278130160040004d800801d0381301687800800843a0102881300602c00800800801c098032ac03400800800801c2885e00602c00800800801c2881302202c0e000800801c3401300602c0e0008
  | 8, 2, 4 => 0x80f40980301a02c00800800801c311b700602c00800800801c2881344c02c00800800801c2881344a02c00800806e110020070a204c00800800801c2881310802c0080080880100380c35004c0080080880a40385102600c00800800e1440980310c02c0080080be0140205144800c0580080a6014020030160040004d844601c2881300602c00800800801c0605102602c00810800801d1101300602c00800800801d1080301600400016800801c09803016004002208
  | 8, 2, 5 => 0x801c3105100636800800800801c2a01300602c008ca800801c2881307402c1c8ad800801c288130068b400800845801d1585100602c00800808801c288130060bc00800800801c098030168a800800801e17c020070a804c0180b800801c2a01300602c0081e811a0103401300602c0008c800e6400980305e02c00800800801c4a81300602c008008452144098030160051400080be0100385102600c6d00080b0010098030160040004d800a01028a2700602c008008
  | 8, 2, 6 => 0x801c2881300602c0081080e60100386800602c00800803201c0980301a0040004d80540a42881334a02c0080080081440980301637c0018f800801c2888700602c008008176010d881300602c0080080080382882200602c00800800801c2881300602d17800819e01c2a01300602c008ce801e010038620a800c05801819e2802881300602c00800800801c7801300602c00800800a0101e8030160040004d800801c0606802602c00800800801d1701300602c008008
  | 8, 2, 7 => 0x82382881300602c00800800801c2881305802c0081e802401c0180b00200026865800801c098030160040023380360101e8030160040004d800e1440980305e15800926806e0d82881300602c008008008030288130160040009784648c40385102600c05800800003c0200702600c0680170080f4310030160040004d800801c09803016070008108088010039a802600c00800800801d1801300602c00800800801c09803016004000ee80080f4308030160040004d8
  | 8, 2, 8 => 0x19e01c2881300602c00a38846e01c2881300602c00800800801c288030168d800800814014409803016004000a6803601c288f600602c0080080be0100389502600c05800800801c0981101607000800800801c28a3500602c00800800801c3122200602c00800800e1440981805e02c001b5800801c2881302202c00800800801c3401300602c00800803601c288fe00602c0080081c001c2881300621400800800801c09803016004000ff800801d1a01327a524008008
  | 8, 2, 9 => 0xa0100385100602c00810811a010288b400602c0080080be0100385110e00c05800800801c28a3c00602c00800800801c3411900602c8c000808801c310510060bc00800824e1440980305e02c00800800801c288130062041c8ad800801d1d81300602c00800806c010288130062140080080be010038f002600c0580080000640381300603400800700801d1d0030160040001680be0100380c0d004c0580080080f4c601300602c00800800801c060130168e4008008
  | 8, 2, 10 => 0xa0102881300602c6f800800801c0180b002000d081680be0100385102600c05810847e0100385102600c05801800801c2a01300603400800800801c098030161300004d803601c358030160040004d800801c310f000602c00800819e0100380301600400016800801c060620d002c00800847c0111e81300602c0080080d401c098030160040004d802a0109385102602c0080080d2010038030160040004d80081440980301600400097800801c340a800602c008008
  | 8, 2, 11 => 0x801c2891900602d2100080880100391102600c00800800801c2880301a0040006580dc01c098030160040004d80089042881300602c00800800801c0180b36c004000168008144098030160040024080880100386235000c00800800801c3105100602c0081080cc1440980305e02c008008008144098030622b80080080be1100200735004c01800800801c4a81313e02c00800812c01c0605102602c000a680f40100397900602c0080080be0100385111200c058008
  | 8, 2, 12 => 0x4900102881300602c00800807a1440980305e02c00800801e0100381300602c00a4780a60102881300600400097800801cd001300691800800800801c2a01300602c6f800800801d2281300602c00800800e4380980305e02c0080080be010038510260440580080be0100386802600c0580080089102881300602c00800801e0d83385102600c05801800801c098030168e400800800801cbf01300602c00967800801c2a24300602c00800800801c11013006004000168
  | 8, 2, 13 => 0x801c2881300602c008a5800801c2881349e02c00800802a01c3401315802c00800801e01003a4e02600c0580180880100385102632c00800800801c0180b0020000b0a6800801c098031b40040004d821201c2881306802c00902800801d2685100602c00800800801c3105102202c00800800801d2605102602c00902800801c3106800602c0080084960100385102600c00800801e01003a3402600c05801811a0102881300602c0024a800801c28a4900602c008008
  | 8, 2, 14 => 0x8801003a070265e800800800801c2881300602d2900080b01440980305e02c00800801e010038510260e80580180081882880301600400097800801c2891900602d28800800801c098030160700804d800001c0182f01600400016700801c3401313e02c008008008038038030160040004d800801c3b0030160040004d800801c0605102602c1c8ad80089402881300602c00800800801c098030164f000800812c01c2881300602c000a6800801c0180b002610000168
  | 8, 2, 15 => 0x801c2881306802c00a59802401c0605102602c0080084b00100385102600c0580180e60100381300602c0080080b41440980301600400172800801c09a570165e800800819e01c2881300602c00a56808801003851026004000e9806c9542881300602c00800800e144098030160048597284a80100385102600c00800800801c3425302600c0080080be1f80385102600c05800801e0100380301600426865800801c4c81300602c00800800e72c0980305e02c008008
  | 8, 3, 0 => 0x6c9742881300602c00800800801c098030160040015080a60102a0130060040018f800801c1101300603400800800801c018830160040004d800801c310030168e400800800801c060130160040804d801e0100381300602c0096780a204c018310160052e000831a01c2a01300602c00800800e144098034b602c0080080081892085100602c00800800801c3425a00602c00800800801c098110160700004d800801c2a01300602c0086f80be0100381300602d1c8008
  | 8, 3, 1 => 0x801d3201300602c008008008144098034c602c00800800801d3101300602c00800800801c28a6100602c0080080883040385102600c0080082440100381300603400800800801c0605116802c0080084c00102881300602c00800801e97c0205102600c05801800801c2881307402c1c800800e1a00980305e6d800800800801c2881300697800800800801c3124500602c00800800801c098840160040004d80be010038620d000c05800800801c2881300602c1c8ad8
  | 8, 3, 2 => 0x960100385102600c61800800801c098030160040026a801e010340130060c40580184d20100385102600c05800800e7740980305e02c00800800801d3401300602c00800800801c288030162cc00800812c01c3105100602c000a6800801c0605102602c1980084ce0100385102600c05800801e010038132f200c05801800801d3301300602c0080080000100381300602c0e010708801c0980305e0040004d816201c2881300602c00800800801d3281300602c008008
  | 8, 3, 3 => 0x801d3805100602c00800800e6e8098030169bc00800800e72c3100305e02c0080080000100381302202c0e000700801d370030160040004d800801c098030160040804d800801c0180b0020004404d801e0100385102600c4080180f40100381300602ca5000800801c0180b00207826865800801d368514d802c00800800801c01a6b0160040004d80960100381300603400800800801c438030160040004d80e8010038030160040004d800801c8d05102602c008008
  | 8, 3, 4 => 0x801d3a81300602c00800800801c288cc016004000e9800801c288130069d000800800801c0980301a02c00810800801c3105100602c1c8ad800801c2881327a52400800800801c2881300602c19800800801c098110160040004d800a0100180b00200026890800801c340af00602c00800800801c09803016004002738008238098030160040004d800801c0980301600539000800801c288b400602c0080080dc3442881300602c00800800814538803016360008008
  | 8, 3, 5 => 0xa63042881300602c0080080080f4098030160040800084f00100385102600c0580180081440980306202c38000801e2340205102600c0588c800a1451200305e02c0080080be0480385102600c05800800804c0180b00200026897801e2ec0218c02600c05801800a010038030160040804d800e6dc0980305e02c0080080084902881300602c0080084ee010038514ec00c0580180083f42881300602c0081a80081002881300602c6f80080083f42889400602c008008
  | 8, 3, 6 => 0x96144098030620040010d800801c308030160040804d801e0100399502600c05801800801c28a7c00602c00800800801c2881300602d3d80080320100381300602c0e00080fc01c288af00602c00800801e0100380c0a204c05801800e144098034f402c0080080be0100381300602c0804d800801c061a002602c00800800801c2a01305802c00800800801d3c81300602c00800800801c0981101a02c0080080dc01c2881300602c1c801800801c4d8030160040004d8
  | 8, 3, 7 => 0x883e40385102600c00800800801d3f85100602c008008000010038510260d005833700801d3f01300602c00800800801c0180b28a00400016800801c0180d00200026865800801c340130062a8008008036010038030160040804d800a010038110160040004d80be0100385116800c05800800801c310030160040804d801e01c2a0130060bc05801803201c2881300602c0e00080085ac0980306202c00800802a0100385102636800800800801d3e81300602c008008
  | 8, 3, 8 => 0x801c2881318c02c00800800801c061b102602c00800803201cca81300602c00800800801c098030160045284d800801c288c500602c00800800801cd001300602c00800800854c0980306202c00800800801c3105127a5240080080081440980350202c00800800801c3105100602c19800800801d4001300636800800800801c310110160040004d800801c0180b01600400016800801c2888900621400800800801c308110160040004d807a04c0182f0160040004d8
  | 8, 3, 9 => 0x1e17c020070181440980b80880100385128c51400800800801c0605102602c0081e800801d43813016a18008008096280288130060040010d800801c0180b50c00400016800801c0980301600400285800801c3401300621400800801e0100386800602c00816850801c2881300602c00800800801c0601300603400800800801c0180b0020000b28380083447801300602c00800800801c2881327aa0800800812c01c09803016000268a6801e0100385102600c058018
  | 8, 3, 10 => 0xe3c00980305e02c00800800e0303401305e02c0080080540102881351a02c00800800801c28813016a3000800819e01c0605102602c008ce800801c0180b29200400016801e0100380c0c41440580180a60100380301600400016800801d4581300602c0080080000100380301a00400065719e01c2881300602c00a8a801e0100385123200c05918800801c0605102602c008ca800801c2881300602c1ca8980880107e85102600c00800800801d4401300602c008008
  | 8, 3, 11 => 0x8801cd40130060bc008008008a482881300602c00800800e1444480305e02c00800800e1440980305e02c00810800801c098030160e4268ad80000dc1b05102602c00800700801c288130302b8001b5800801c288130300d005839852201c2881300602c0080080083443401300602c00800800801cd881300602c00800800801c28813006a4000800800801c2881308a02c00800800801c28813006a3c00800800801d4705102602c0080080081440980310a004000978
  | 8, 3, 12 => 0x1e010038620a200c05801800801c3105118c02c0080080081440980352802c008008088010038510260d00090285260100385123200c05800800801c311a000602c00800816201c098030160040004d800801c2881300602c008ca800801d03813016a1800800806e0100386802602c00800801e17c020070a204c0180b80be0100385102631805800800801c2881300602c0081e805201c3401300602c00800800e1440980309202c0080080fc01c2881303002c008008
  | 8, 3, 13 => 0x801cba01300602c00810811a0102881300602c0029880081440980306216400800800801c2881300602c00a9780080802881300602c00800806c19c2a01300602c0080080be0102005102600c05890800801d4b01300602c008008008144098030160040029580081002881300602c0096c800e1440981105e02c00800800e1a00980305e02c00800800801c6b86802600c00800811a0102881300602c0086f806c0100380301600400016819e01c2881300602c008ce8
  | 8, 3, 14 => 0x6c01c2881300602c0081a800801c0605102603400800853601c2881300602c0080080a204c0182f01600400097800801c0180b002a680001680be0640385102600c05800800801c5a0030160040004d80081002881300602c00897800e1440990701600400172800801d4380301600400016800801d4c81300602c00800801e0100385102627c058018008080340030160040001680081440980306202c0081a8008198288130062b800800800801c288a800602c008ca8
  | 8, 3, 15 => 0x801c0180b0020000b0b7800801c0180b1720040004d80be0100385102600c058ca800801c2a01307402c00800800e1440980353c02c0080080081440980353a02c0008c800801c0993d2920040004d800801c098030160cc0004d80be0114905102600c05800800801c311b100602c00800801e110020070d004c01801800801cba01302202c0080080085fc0980306202c00800800801c3105108a02c00800800801c098030160040029c800801c2881300602c008d68
  | 8, 4, 0 => 0x5460102881300602c00800800801c2881300603400800800801c098030160040012c800801c09803016004002a2819e01c3105100602c008ce800849c2881306802c00902800801d298030160040004d800801c0180b0020000b1b5800801c2881327aa8400800800801d5001300602c00800800e04c0182f0168e400800801e17c020070c41440180b80884240385102600c00800800801c3105100602c0081e800801cbf81300602c38000800801d4f81300602c008008
  | 8, 4, 1 => 0x801c1600b00200026865800801d5305102652400800800801c28a4300602c0080080b00102894601651400800800801d120030160040001680f40100381329c02c00800803201c098030160700004d801e0100381300602c00816800801c3400301a00400016801e0100380c02602c0084d854a0100385102600d52001800801c0980301a0700080080be010038e202600c05800800801d0380301600400016800e1883400305e02c0080080f41100200702600c008008
  | 8, 4, 2 => 0x880100396b02600c0080080a6010060510260040018f801e0100381300602c0084d800801c098c60160040004d800a0100385100603400800800801c2a01300620400800800801c288220060040013e800801c0605102602c0086f80880100385102600c3800080080f4bf01300602c00800800801d5481300602c0080080083442881300602c1c8ad8008038288030160040004d8088aa00385102600c00800854e01c2881300602c00800800803828822006004000658
  | 8, 4, 3 => 0xbe01c2881300602c00172800801c3402601600400016800801d5781300602c0080080000640381300602c0e000712c0100385102600c2c800800801c28813006ab800800800801d5681300602c00800800e1440980305e02c1c8ad800801c2881304c02c00800800801d5601300602c00800855601c2881300602c00800800801d5006200602c00800800801c3401319602c00800821249c2881300602c0080080081440980306215800926800e1440980355402c008008
  | 8, 4, 4 => 0x11a0102881300602c002b280a6010288130060040018f80880100395b02600c0080080080800980301600400016800801d5881300602c0080080880100705102600c00800800801c34013016004000e9800801c098450160040004d800801c288af00602c00817800801c2881300602c0086f80be1100205102600c18800801e0100381300603405801800801c3380301600400016801e0100385102600c058c3800801c3105100603400800800801c28946016ac0008008
  | 8, 4, 5 => 0x18201c3401300602c00800801e0100386100602c0084d80f40101e81300602c00800800801d5b81300602c00800800801c0605402602c00800800801c2880301600404816800e1445a00305e02c00800800801c09803016004002b6801e17c0200702600c0584d800801c098030160040f04d856a14c0205102600c0080081760111e81300602c00800800ead02881300602c00800801e0140200700602c0084d800801d5981300602c00800800801c288130061640081a8
  | 8, 4, 6 => 0xbe010038130060340080080081440980357602c00800800801c54003016004002b6800801c710af00602c00800800801c1100315400400065800e1440993d05e52400800800801cee81306802c00902801e06c0200700602c0084d800e1440980305e02c19800800801c2881300602c00aba800801cad81300615800926800e04c0882f0160040004d800801d5c85102602c00ab8812c0100380301600400016819e01c098030160046704d801e0100386200602c0084d8
  | 8, 4, 7 => 0x801c3105100602c0086f858401c2881300602c00800800801c0980301a0040001681a6010038030160040004d800801d6081300602c00992800801c0601301a0040004d8088010038510060040001680be6340385102600c0580080be0640381300602c0004d800801d6001300602c00800801e6ec039ba02600c05801800801d5f81300602c00800800801c2891900602d5f000806caf42881300602c00800800801c2881300602c618ca800801d5e01300602c008008
  | 8, 4, 8 => 0x880100385102600c0081a800801c2a11900602c8c00080880100385112800c00800800801c2881300602c1ca598054014020030160040004d800801d629b700602c0080080083b02881300602c00800801e01c060510260bc05801800810028813006214008908008b102881300602c0080081c001cb581300602c008008586010039a802600c00800800801c0980301a004001b9800801c098030160046b04d800801c2a01300602c0080080be14c0205102600c0018f8
  | 8, 4, 9 => 0x100380c02603400800703201c09803016004002c880080388701300602c008008088010038130062a800800800801c2881300602d63800800801c2881305802c00800800801c0980301a0040004d800801c0981800603400800801e0dc020070a204c05801801e0a40385102600c05801821201cee81300602c00800802a01c2881300602c008ca800801c2881303002c00817858c01c2881300602c00800800801c0980301a0040008c800801c060620a802c008008
  | 8, 4, 10 => 0x801440980305e02c00890800801c0980301a03400800800801c3105400602c0080080087740980306202c00800800801c28acd00602c00800800801c288130063a000800800801c288130160e4748ad80880100385117a00c00800800801d6601300602c00800800801c0982601600400016800e1440980359602c00800800801c340f602600c00800800801d6501300602c00800800e144098031e202c00800800801c2881359202c00800800e6800980305e02c008008
  | 8, 4, 11 => 0x3601c28ad400602c00800800e6c40980305e02c00800800e1440980305e02c0081780000100381300603400800700a0100380301a0040004d800801d6981300602c00800800801c288135a402c00800800801c28ad100602c00800800801c34003016004002d081f201c3401300602c00800859e01c2881300602c00800802a01c2a01315802c00800801e010039a802600c0580180081682881300602c0080083760100381300602c0e000859c01c2881300602c008008
  | 8, 4, 12 => 0xe1440980305e02c0081e800801c09803016004002da800801c3105105802c00800800801c3100301a0040004d800801c288135b202c00800837601d6c01300602c00800800801c098035ae02c00800800801c8b81300602c00800800801c8700301600400016800801c3080301a0040004d800801c2881300602c00ad6800849c28813016004001b580886980205102600c00800800801c2881307420400800800801c340130062b800800800801d6a81300602c008008
  | 8, 4, 13 => 0x140200700603400800700801c0623402602c00800800801c09803016b7000800800801c0601301600400247800801c288130160cc000e9800801c0180b0020000b0ef8008b6c2881300602c00800806c19c0605102602c00800800801c098030160043784d80dc1440980306202c008008000010070030160040004d70083f43401300602c00800800801c341460165140080081d401c2881300602c00800801e0100386804404c01801801e17c0385102600c1780b8
  | 8, 4, 14 => 0x801d7181300602c0080080000100386200603400800709601c288a800602c00800801e0102a0130060c405801800801c28ae2016514008008054010288135c202c00800800801c342c500602c00800800801c0980301a004002c8800801c28ae000602c00800800801c870030160040004d800801d6fade02602c0080081760116e81300602c00800800801cc601300603400800800801c870220060040006580fc01c288130062b800800800e1443201300602c008008
  | 8, 4, 15 => 0x81440980310a0040018f800801ce58030160040004d800801c3400336c00400016800801d1a01300602c00800800801d7401300602c0080085ce01003851026b9805801800801c0980301600400247800801ca300b47251400800800801c0180b0020000b065800801c0600b0020002686580880109385102600c00800801e0100397402600c059b9800801d7281300602c00800800801c3401306802c00902806c19c2881300602c00800800801c28813006b90008008
  | 8, 5, 0 => 0x83b0098030160040004d800801cd101300603400800800801d7801300602c00800800801d7785100602c00aee800801c2891900602d76800800001003803016004048167008bb02881300602c00800812c3f42881300602c000a680540a40205102602c00800801e01003a0702602cbd001800801c8c8030164600024785d601003a0702602c00800800e1440980305e03400800800801c288135d402c00800800801c34013006ba400800800801c0980305e034008008
  | 8, 5, 1 => 0x801c28af600602c00800800801d7a81300602c00800800801cf701300616400800800801ce5af400602c0080080f40100381300602c00810800801c060132f202c00800820a0100385102600c058008088144098030620bc00800800801c2881300602d79800800801c0180b0020002686580880101e85102600c0080085e40100385102600cc200080880100390e02600c00800800801d7885100602c009a1801e0100385102602c008e9800801c2881307402c008008
  | 8, 5, 2 => 0xf40100381302202c00800801ebec020070a204c05801800801d7d01300602c00800800801c098035f202c0080080081440980306202c0081080001100200700600400016700801c2881319602c008ca806c19c3105100602c00800800801c0180b0020000b0ad800801c0982c0160040004d800801c0605102620400800800801cba01300603400800800801c28af800602c0080080081444380306202c00800821201c3401300602c00800800801d7b81300602c008008
  | 8, 5, 3 => 0x801cd01b702600c00800800801c098031d00040004d800801c8405102602c00800800801cdb80301600400016800801c0997900602c00800800a0102881300621400800800801c2881300602d7e800800801c3123400602c008008088010039cb02600c008008036010038030160040024784be0102881300602c00800800801d0105100602c0080080881600205102600c00800800801c34013006bf000800800801c0180d01600400065800801c31003016004002478
  | 8, 5, 4 => 0x88010039dd02600c00800800801c2882200600400016800801d8100301600400016800801c098030160040817d800801d8081300602c0080081760100618c02602c00800800801c2a01300621400800800801c3401300602c38000800801c3105107402c00800800801c28813006204008008008144018310168d800800800801d8005102602c008008176014020030160040004d800801cb588900602c00800800801c09803016004002ff800801d7f01300602c008008
  | 8, 5, 5 => 0x801c0605102602c00800806e0100385402602c00800860a01c2881300602c00800808806c038510d600c00800805201c2a01300602c0080080080383401300602c00800800801c3117900602c008008176010c601300602c00800800801c2881300602c00944800801d0381300602c00810800801c0980360802c00800800e1440980305e02c138008088010039cb0c400c00800800801c28813016c0c00800800e0302a01305e02c00800800801c2881300602c008e18
  | 8, 5, 6 => 0x801c0605123202c8c000800801c2881306802c1990286120100397e02600c05801806c19c098030160040004d86100102881300602c00800800801d8381300602c00800801e3e40385102600c0580180e60100385100602c00800800801ccd81300602c00800800801c2881301630800800800801c2881300624800800800801c7f0030160040004d800e1500980305e02c00800800801c0606801600400016800801c3105100620400800800801d8301300602c008008
  | 8, 5, 7 => 0x22401c2881300602c0080080081440980361c02c00800801e0100385128c02ca2801800801c2881300602d86800800e1440982c05e02c00800800e04c0182f01a0040004d801e110020070a804c01801800801c2881300602c00800800801c0980301a004001a1800801c28b0c00602c00800800801ca300301600400016800801d8581300602c0080086140100385102602c00800800801c4a81300602c0081a800801c6b851006004000658088010039b702600c008008
  | 8, 5, 8 => 0x801d8981300602c00800800801c2881307400c05839800801c0983a0160040004d802a01d8905102602c00800812c01c2881300602c00289800801c341a002600c0080081760103118c00602c00800800801d8881300602c00800800801c0980301a6d800800801e0100a05102600c058018620010038030160040004d8008080038030160040001680bec140385102600c0580080081440980361e02c00800800801c6681300602c00800800801c34003016004000168
  | 8, 5, 9 => 0x801c0980301a0040013b800801c28813006c5c00800800801c0980301a004c2000800801c0980301a004000a6821201c2881300602c19800800801c28b1600602c008008008c542881300602c00800800e1882a00305e02c00800800801c780bd00602c00800800801c3409400602c00800800801c288130062b800817800e144098036280040010d800801c060620a202c00800820a0100381300602c0004d800801c2891900602c8c00080880101e8130060040004d8
  | 8, 5, 10 => 0x801c3401300602c00809800801c710130062b800800800801c9e803016004000168088010038f002600c00800800801c3105100602c00800800801c840130160040004d80880100380c0d004c00800800801c098110160040031b800801c2881300615800b1a80081445a00306202c0080086320100385102600c05801800001c0980305e03400800701e5bc0205102600c05801800804c018310160040804d800801c3402200600400065800801c09b1800602c008008
  | 8, 5, 11 => 0x88010038510260440080080880100386802600c00800801e010060510260c405801800801c060130160040001680240382881300602c00800800801d9081300602c0080086400100386802600c00800800801c2881300615800b1f80480100385102600c00800863c0100385102600cab000800801c0617e02602c0097d800a234020030160040004d800801c098031020040004d800801d8e81300602c00800800801c340bd00602c00800800801d8e013006204008008
  | 8, 5, 12 => 0xe04c0182f0160040024780880102881300600400097800801c44803016004001b4864801c2881300602c00800800801cbf01300602c0097d80f403c0200702600c05801800801c0180b0020000b18f800801c8702202600c00800800801c2a013016004000e980e60100380301600400016800801d9197900602c00800800801d9101300602c00800806e0d83385102602c00800800801d038130168e400800812c01c2889400602c000a6800801c3401300648c008008
  | 8, 5, 13 => 0x801c0180b5f80040004d800801c098031240040004d800801c019a50160040001680000100382200600400016701e010288130060c4058018008144098c606202c00800800801c0980301600400327800801c0980301600400016811a0102881300602d93000800801c060130160040004d818201c2a01300602c00800800801d9281300602c00800800801c340130062c800800800801c3401300615800926800e8d00980305e02c0080080be054038510262b0058008
  | 8, 5, 14 => 0x882580385102600c000a680081440984506202c00800800801d9681300602c00800800801cf381300602c00800800801c0601301a02c00800800e1440980365802d958008088010038620d000c00800800814409831016a3000800800801d8e01300602c00800800849c3401300602c00800800801c0632a02602c00800800801d9485102602c00800800e00c1780b00200026865800e1440983a05e02c008008088010038130068e400800800801c28813006ca0008008
  | 8, 5, 15 => 0x801c0980301a51400800800801d9881300602c00800801e0105005102600c058018008100b581300602c00890800801c288bd00602c1c8ad81780100385102600c058ad800801c3117e00602c0097d866001c2881300602c00800800a0100380301600400016800e04c0182f01600400167822401c098030160040004d800a0100380c0160040004d80086c40980306202c00800800801c2881300602c00b2f800801c0980301a0040032e800801c098030160040004d8
  | 8, 6, 0 => 0x801c2881306802c008e9800801c0980301a02c00800819e1440980306202c008ce80080f42881302202c0080080080f43401300602c00800801e010310510060c405801800801d9501300602c00800800e04cbc80305e02c00800800801c3100301600400016800801c060620160040004d800801c3080301600400016800801c3080c0160040004d800801c8c8030164600004d80001cc0200700602c00800700801c310680062c800800866401c2881300602c008008
  | 8, 6, 1 => 0x801c2881367002c00800800801c308030160040004d800801d9b85102602c00800800801c2881366c02c00800800801c09803016cd40080081760100380301600400016800801c2881366802c00800800801c28b3300602c0080080be0100385115e00c05800809601c288130060046510d800a010038030160040004d80880100385102600c1c8ad800801c288130160cc001b5800e1440980305e20400800800801cbf8b400602c0080080d004c0183105e02c008008
  | 8, 6, 2 => 0x5201c0605102602c00800800801c09803016cf400800800801c288130065599e000800801cdb82202600c00800800801c2881300602c00b3b800801d9d01300602c00800800801c340130064b80080080f40100381300603400800800a0100380301a02c0080081f201c2a01300602c0080080e8110020070060040004d80081451200310602c0080086720100381300602c00800800801c0980301a2fc00800800801c310030160040004d800801c0980301a524008008
  | 8, 6, 3 => 0x480100381300603400800800801c28946016d0c00800800801c2881368402c00800806c010038130060340080080880100385102600c198008088010038130220040004d800e0302881305e02c0080080083f42a01300602c0080086820100385102600c05b40801e0100385102600c2c801800801c2881367e02c00800800801ca3054016514008008008cf82881300602c00800800801c098030fa03400800800801c3100301a02c008008048010038130060040004d8
  | 8, 6, 4 => 0x801c2a01306802c00902800801da501300602c00800800e1440980305e02c00800801e0100980306202c0084d800801da481300602c00800803601c3406b00602c0080080000900200702600c0080076900d82881300602c0080080081440980368e02da3000808801003a7902600c00800868a01c2881300602c008008688010038510264f400800806e0100385102602c00800800801c061a802602c00800805201c2881300602c00800801e0100397f02600c058018
  | 8, 6, 5 => 0x88010039a002600c0080080081440980306202c0086f800801d0381300603400800800801c288220060040f06580be0106885102600c05800800849c2881300602c19800800801cd401300602c0080080880100380301600400016800e0303105105e02c00800800801c0980301a004001b5800801c0606804404c0080080080802880301600400016800801c5e803016004002858000010038510260e805839700801c2888700636800800800e1a00182f016004000168
  | 8, 6, 6 => 0x801da801300602c00800800801c28813006004000e4821201c2a01300602c00800800801c2881300602c00b4f800801c3402202600c00800806e010038620a202c00800800801c28b4e00602c00800805201c3105100602c00800800801c0180b07200400016800801da681300602c00800800801c09a2400603400800800801c28b4c00602c00800800801c1300301600400016800801c288b500602c00800800801c28813016d2c00800800801c34013006004001388
  | 8, 6, 7 => 0x801c3381300603400800800a010b581300602c00800800801c0180b1640040004d80f4010038030160040006586aa0100385102606005800800801c2881300602daa000801e17c2200400e14409803800801da985100602c00800800801c311a800602c0080080880100385102600c0081e800801c0180b2f40040001686a401da885102602c00800801e01003851026060059b58252010038030160040004d800801c2880301a0040001680084dc2881300602c008008
  | 8, 6, 8 => 0x801d038130165e800800801e3800385102600c05801818201c0605102602c0080086b40100385102602c00800800801c288260160040001686b201c2881300602c00800800801dac05100602c00800800801dab81300602c00800800801c3106804400c00800800801c0980301a0040031b800801c34013006d5800800801e0103305102600c05801800801c0195601600400016800801c0980301a2a800800800801c288130067c400800800a0100386804400c008008
  | 8, 6, 9 => 0x801c3135700602c008008008144098036ba02c0080085f60100385102602c0080080320f42881300602c0080086b80100385128c02c00800818201c2881300602c0080081c001c2881308a02c00800806e010038130160040004d805201c098030160040004d800801c2881300632000800800801c66813016004000e980081440980323c02c00800800801c3401302202c00800800801c28813016004000e9800801c098c000603400800800801c2881300602c00b5b8
  | 8, 6, 10 => 0x1f201c0605102602c00800800e14454003016004000a6802a01c288136be02c00800802a0a81b05102602c00800800801c7801300602c1c8ad86bc0100385102600c00800812c01c3401300602c000a6800801c2a00301600400016800801c31051016004000e982140100385102602c00800805a01c2881300602c00800800e144d100305e02c009a1800801c098110168e400800800801d038620165e800800800801cbf81300602c0086f800801c8701300602c0081e8
  | 8, 6, 11 => 0x801c340030162cc00800800801c098033e20040004d800801c288220580040006586c80100385102600c0080081f201c2881300602c00800800801c2a0bd00602c0080080e8010038516c600c00800800801c0180b1540040006580880100380c0a804c00800800801c3401300602c1c8ad800801c28813006d8800800800801c2a02200600400065800801c0180d0020000b04d800801c28b6100602c0080086c00100385102600c0583980084dc098030160040004d8
  | 8, 6, 12 => 0x1f201c3105100602c008008088010038510260b000800800801c28ac500602c0080086d00100381300602c00800800801c3401327a52400800800801c0980301a00400065800804c0191e0160040004d800801c3401300602c19800800801c28813006d9c00800800801c0980b002000268e9800801c289460165140080080880100385402600c00800800801db3051026d9400800800801c110030160040001680000100380301a00400016701e0100385102600c6d0018
  | 8, 6, 13 => 0xa804c0183105e02c00800800801c289460162e400800808801003813006004002da86bc010038130060040004d81a60100385104400c00800800801c098030160040036c80f40100380c02602c0080086d60100385102600c05801800801c0980301a004000ad831a1602881300602c00800800a01028b6a00602c0080082de0102891900602c8c0008088010038620a800c00800800801db481300602c0080080320f4098030160040004d800001003826016004000167
  | 8, 6, 14 => 0x801ca300b28a0040004d80f40140200700602c0080080480100381300602c00800808801003a3402600c00800800801c288bd07402c0080080880d83385102600c00800801e17c020070d004c0180b855001c2881300602c0080086e00100385102602c00800800801c8701305802c00800800801c0981100603400800800801c28813016dbc0080086dc01c2881300602c00800800801c060030160040001680f40100381300602c00800800801db681300602c008008
  | 8, 6, 15 => 0x88010038510260e80080080f40100386200602c00800800801db90136e202c00800800801cbc8030160040004d80f40100386100602c008008
  | 9, 0, 0 => 0x801c2881300602c008006eb26282200400e144098030020024078070a204c0182f01600400480f0081000385102600c058019000010310510060c40580100100100380c0a204c0580100049a4020076e81440980301600400480000801cad81300602c00800801e110020070a204c0180b003201c288130060bc059490020024298070a204c0182f0160040048000080382881300602c00800800801db985102600c0580100125942200400e144098030020024020070a804c9e8030160040048000be010288130060c4058008
  | 9, 0, 1 => 0x801c28813006de80580100120100385102600dbc80b0020024020070d004c018ac0160040048040a204c0183105e02c00800900801c8705102600c058010012010288130060c40580100033a4020070a204c0180b6f000400480400e030288130d602c00800900801c3402202600c0580100120100385102600c058016ee00240780400e144098030160e400c8e000801c2881300602c00800900801c060510260d0058010012010038516ec04c0180b0020024020070a204c0180b0028a00048070a24640980305e02c008009
  | 9, 0, 2 => 0x960100386802600c0580100120100386802600c2b00b0020024020070a204dbe80301600400480400e150098030160040018f900801c0605102602c008000cb2010038516f804c0180b00200246780400e144098030ac02c00c80400e14409803102004000ad901e0100385102600c0580121b20100385102600c05801000dee4020070a204c01a6c01600400480400e14409818016004001b5900801c2881300602c0080024d20d80385102600c1780b0020024020070ce04c0180b00200026c8f900e14409803016004001a19
  | 9, 0, 3 => 0x801c2a013006694058010012010288130061580580100025e4dd80400e1a00980301600400482a0081002881300602c0080090880100385102600c0080037320100380c0a204cfd00b0020024021740a204c01831016004004a3e00801c2881300602c00800900801c288130d600c05801001203c020070a204c0180b2f400640200739614409803016004004aeb00801c2881300602c00800900801c098030160040004d6372000020070a200c0580100005a0020070a204c1a00301600400485f0880100385102600c008009
  | 9, 0, 4 => 0x801c3405102600cdb0010012110020070a204c0180100023240780400e144098032ac02c00c80000801c2882200600400065800e1440980305e02c00918001201003b810a204c0180b0020024020070a204c0180b00200032cb8000801c2881300602c00800900801c2881300602c00b7f0012000020070a204c0180b00206a00385102600c1780b002000bec89600801c098030160040004d90000100385112800c058010010df80780400e1440980301600640000400e144098030b200400400f11a0100385102600c058019
  | 9, 0, 5 => 0x801c310510069b00580100120107e85102600c0580100029a4020070c41440180b00200093480400e03028813016004000ad900801c2881370a00c0580100120100385170804c0180b00200242200400e1440980300200026c80400e145c181300602c00800900801c2881300602c008ca21b2110020070a204c0c00300200240000400e5fc098030160040040070a204c0182f016004001b590be0100385102600c0580024d20000200702600c058aa0020020020077041440980301600400480400e04c0180b002000268909
  | 9, 0, 6 => 0x801c2881300602dc3801001201c28813006cb01780b00200242f80400e1440986b00602c00481500801c2881301600400102900801c3105106800c058010012000020070a22f40180b00200200000402600c1880b00200026c0070a204c0182f01600400102900a0100385402600c0580100120100385102600c05b860020024020073ba1440980301600400480400e144099fa00602c0080090001100200701814409801001001d0385102600c1780b00200242f80400e1440983400602c00488d00801c2881300602c1c8009
  | 9, 0, 7 => 0x801c3105100602c008000cb20002200400e144098030020020020070a204c0180b00200056c80400e81cba01300602c0080090542340205102600c05801001217c020070a204c0180b00019645d8050081440980301600400480400e1440980371202c00800900801c3105402600c05801001206c020070a21ac0180b0020024020070a204c0180b002001c4480400e144ea01300602c00800900801c3085402600c058010012010038620a21ac0180b002002402007396188288030160040048070a204d1200305e02c008009
  | 9, 0, 8 => 0x801c288130062140080012129dc0780400e144098030160064020070a204c0180b002001c6c80400e144db81300602c00800900801c0605102602c0080057120dc020070ce1440980b00200242200400e14409803002001c6480400e151c581300602c0080091760100385402600c0580100120100385102600c05b140020024020070181a0098030160040048150880100385102600c0080097140100385102600c058010012010039890a204c0180b00200240205102600c1883101600400486e00801c2881300602c008009
  | 9, 0, 9 => 0x801c2881300602c0080057120101e85102600c0580100013640005f0880100385102600c00400400e1440981100602c0080090880100385131804c01801001217c020070a204c0180b0002b64678040a204c0183101600400480400ec082881300602c008009000010038510260600580036b003c020070a21500980301600640205137404c0183101600400480400e6802a01300602c00800971c03c020070a204c0180b0032000020070a204c0185600249a0038670a204c0182f0160040048000540102881334a02c008008
  | 9, 0, 10 => 0x7240100385102600c0580100120100381306800c058010001365c880400e14409803016004004b4100801c2881300602c00800900801c288f602600c05801001201003b900a204c0180b00200240205102600c1880b36c00400480400e04c0180b0020009304d912c01c288130060bc0580100120002200400e1882880300200200000424e144098030160040040cf06c01c2881300602c00800900801c3423d02600c058010012010038510263f80180b0020024020070a204dc780301600400480400e18828803016004000ad9
  | 9, 0, 11 => 0x801c060680a204c058010012000700070a204c0180b0020020020070a204c0180b34800400480400e1440980372c02c0080090081440980306202c0098400120a8020070181440980b0020024020070261ac0180b00200026c80400e2542881300602c0080090880100385102600c1780100120100385102600c0580172a0025ca00400e1440980301600400480400e1440980301600400393900801c0605128c04c05801001201c288130060bc0580100024240204000e144098030160044848000081982881300602c008008
  | 9, 0, 12 => 0x801c098030160040004d0cb20100385102600c0580100054a5cc00400e1500980301600400480400e1440980315c02c00800909606c0385102600c0580100120d80385102600c0580100029a58f00400e144098030160040048000a204c0183105e02c00800800801c28b9702600c0580100122340205102600c0580100063e58800400e1440980301600400484400801c289a202600c0080090000101e85102600c058010010010038f00a204c0180b00200240000400e4380980301600400400400ebbc2881300602c008009
  | 9, 0, 13 => 0x801c2881300602c008003812e482f80400e1440980301600240000400e72c0980301600400402a00801c2881300602c00800900801c2881300602c00b9a00120002c0040a204c0180b00200200780400e1440980315802c00c84400801cba05102600c0080090000000200700602c0080002ce010200070a804c0180b0020024020070a204dcc80301600400480400e144a301300602c00800901e0100385104404c0180b0032110020070a804c0180b00200242200400e144d40130060040049d900801c2881300602c008009
  | 9, 0, 14 => 0x801c2881373a00c058010012010038510260601a00b0020024020070a204c01b4701600400480400ebbc3105100602c0080097380100385102600c0580100120100385102600c058010000024020070181440993d01600400484400801c288130060040039b900801ce705102600c05801001203c2580400e1440980301600640780400e144098030ac02c00c98100801c3401300602c00800900801c2a01300602c1c801001201003b230a804c0180b0020024020070a204c0180b00200144c80400e1a02881300602c008009
  | 9, 0, 15 => 0x801dcf85102600c0580100120100385102600c05a390020024020070c4144a300301600400485f0540100385102600c05800900801c2a01300602cbd0010012000020073ba04c0180b00200202f80400e144a301300602c00480400e144098032c802c0080090001100200702600c0080009b003cdd80400e1440980301600640288d0081440980301600400487e00801c2881300602c00800900801c098030160040004d15b2e78020070a204c0180b0020024020073f60302881301600400480000801c340130066d8008008
  | 9, 1, 0 => 0x801cfd85102600c05801001201003ba40a204c0180b0020024020070a204c0180b7460040049f300801c2881300602c00800900801c310680a200c058010012e88020070a204c0180b00200240000400e72c3100301600400400400e04c0180b00200026b8d9054010038620a200c058010012010038620a200c058017340024020070a204c9e80301600400480400e14409803016004003a1900801c2881300602c008007412234020070a804c0180b00200242f80400e1a02881300602c00480400e14409803016ba4008009
  | 9, 1, 1 => 0xe1440986b0060bc058010012010038510264f4019490020024020070a22500180b0020005348040a204cf800306202c00800900801c0981100602c0080009b20100385102600c05801000eaa4038510260d00182f016004004b4800801c2881300602c00800900801c28ba902600c05801001201003ba80a204c0180b0020024020070a204c0180b002001d3c80400e150098032ac02c00800900006c038510d600c05801001001003ba60a204c0180b0020024020070181440980b002000c7cba500801c2881300602c008009
  | 9, 1, 2 => 0x100385102600c6d001001001c288130060bc0580100019642f80400e1440993d00602c00480400e1440980334e02c0080090081440980306202ca280100120100385102600c0580100063e4020070a204c0180b5f800400480000801cdb81300602c00800800801c288130062b80080036b2258678070a204c0180b0020024020070a204c1a0030160e400c8042fc1440980306202c00800900801c2881300602c0081a14d20100385102600dd580b002002402007018144099a50160040048000dc01c2881300602c008008
  | 9, 1, 3 => 0xa60100385102600c0080031f20100397e02600c058010005f642200400e1440980336c0040048000080f4098030160040004d80240100385102600c0580100120100385102600c058016780024020070d004c0180b0020000b480500801c0605102602c00800900801c288130066940580100120100385102604c0180b00200242200400e14409803002000d0c85f00801c3401300602c00800901e0100380c0a204c0180b00320000780400e150098030160060020070c41449e80301600400484419e0100385102600c008009
  | 9, 1, 4 => 0x360100399502600c05801001203c0205102600c1880b0020025d700400e144098030160040048530081440980306202c00800900801c2881300602c0080075b20100380c0c41440980b0020024020070a204c0180b00204026c80400e1445401300602c00800900801c3080c0a204c0580100120100385123204c0180b23000240200702600c05801000134a9484b00e144098030160040010d912c01c2881300602c0080014d20106885102600c058010002b64020070d004c0180b002000dcc80400e1440980375802c008009
  | 9, 1, 5 => 0x100389502600c058010010010038680260600180b0020024020070c41440180b002000c7c8070a204c0182f016004000ad900801c2a05402600c0580100120a80200702600c058010001364020070a204c0180b002001d8c8040a24640980306202c00800900801c2881300602dd80010012110020070a204c018013080024020070d004c0180b00200046484400801c28813006004000a6975e0100385102600c0580100120100399002600c0580130800240200728c04c0180b00200026c80400e144098c600602c008009
  | 9, 1, 6 => 0x801c31051006694058010012010039cc0a204c0180b0020024020070c41440980301600400480400e15009803016004003b497660100385102600c058010012010038610a204c0180b00200240000400e1444380301600400400400e144098030160e4008ad91760100380c0a204c058010012000020071e004c0180b00200200000400e0303401301600400400400e14409803016005d900090001100385102600c17801001001003851026044058010001364020070d004c0180b00200026c80500801c2881300602c008009
  | 9, 1, 7 => 0x100386802600c0580100100100385134400c058010006864020070a24800980301600400480f00801c2881300602c00bbb900801c2881300602ddd00100120100385102600c05bb90020024020070a204ddc00301600400480400e14409bb700602c00800900801c28813006664058010012ed8020070a204c0180b00200240004400801cd401300600400400400eed42881300602c0080090000100385102600c058010210a940780400e1440980301600643a04400801c2881300600400480400e1440984500602c008009
  | 9, 1, 8 => 0x801c2881300602c1980100120100385134004c0180b00200242f80400e1842881300602c004800008144098030160040009780081440980306202c009180012ef4020070a204c0180b00200240280400e18828803016004004844008ef00385102600c00800921201c2881300602c008002052054020070d004c0180b0020024020070264f40180b00200026c8040a204c018310160040017d90be014020070a204c0180b00120100385171604c0180b00200245d80400e1440980301600400480000801c2881302202c008008
  | 9, 1, 9 => 0x100381300602d1c80100100100385102600c05801000efe4020070d06300980301600400480400e14409803016ef80080096a40100380c0a204c058010012010039cc0c41440180b0020024020070a204c019e301600400480400e144098030b202c00800900801c310620a200c0580100120100385404404c0180b0020024020070a204c0195600261000480400e1843105100602c0080090be06c020070a204c0180b001201003adf0181440980b0020024020070a204c0180b002cac00485f00801c3105102600c058009
  | 9, 1, 10 => 0x801d6f85102600c0580100122ec020070c41440180b0020024020070a26c40980301600400480000801c3106800602c00800800801c098030160040004d31f212c020070a804c0180b0020024020070a204c0180b54800400480400e14409803016004001e1900801c2881300602c008003252e60020070181440980b0020025e000400e1440980301600400480400ea982881300602c0080090320100385102600c0580100120002f80400e1a0098030160020020070a204c0180b0020012cc80400e14411003016004000659
  | 9, 1, 11 => 0x801c2881300602c0080078920a80385102600c1780b0020024020070a204c0180b002001e1c80400e1a00980305e02c00800900801c0980334a02c0080009b233c020070a204c0180b00233a40200702604c0180b00200026c8070a25180980305e02c00800900801c2881378400c058010012d48020070a204c0180b0020025e080400e14409803016004004ae700801c2881300602c00800900801c288af02600c058010012010200070181440980b00200240009600e1440980301600053404400801c0605102602c008009
  | 9, 1, 12 => 0x100385102600c0583915b0010200070a204c0180b0020024020070a204c0192301600400484400801c2881300602c00800900e738288130060bc05801001201003bc50a204c0180b00200240205102600c1880b002d1800480400e1a0d101300602c0080096400100385102600c058010012110020070a204c019450020025cc00400e1440980301600400480400ed980605102602c00800900e1a0288130060bc0580100120100380c0a204c0583900200240a82a00801c2881301600400480400e144098035cc02c008009
  | 9, 1, 13 => 0xa6110020070a204c018010012234020070181440980b0020024020070c204c0180b00200026c80400e145e401300602c00800900801c2881300602c0080078f20100385102600c058b20020024020070a204c0185601600493480400ed982881300602c00800900801c0605102602cbd00100120100385102600c058390020024020070a2c8c0980301600400480500801c098030160040004d900801c3417402600c0580100120d8038670a204c0180b0020024020070a204c0180b002001e3492900801c2881300602c008009
  | 9, 1, 14 => 0x74a01c288130060bc058010012000020070a22d00180b0020021cc00400e1882880301600400480400e030288132ac02c00800900801c28bca02600c0580100120100385102600c058010005ca40a80400e1440993d01600400480000801c098030160040804d873017c020070a204c0180b001201c2881327a00c1780b00200240785f00801c2881300602c00c80400e1440980379202c00800912c010288130060c40580100120100386202600c058010001364020070181440980b6ca00400484400801c28813006524008009
  | 9, 1, 15 => 0x10038510264f4a48010010010200070c41440180b00200245d80400e04c0180b00200026c80000801c2881300602c19800800801c288a800602c0080021b2000020070260440580100013602200400e1882880301600400480400e144098030165e800800900e145d48130060bc0580100120100380c0a804c0180b0020024020070a204c01bcb01600400480f00801c2881300602c009b996880100385102600c058010012010288130060c40580100024242f80408001c2881300602c00480400e144fb81300602c008009
  | 9, 2, 0 => 0x1e0100385102600c0580109b2010038d50a204c0180b0020024020070a204c0195601600400480400e1440980b002000da902900801c3105100602c1c80100120100396b02600c058010002424020070a2f3c0980301600400480f00801c2881300602c0088c979c03c020070a204c0180b003201003bcd0a204c0180b0020024020070a204c0180b6ca00400484406c0100385102600c008009252010038620a200c058010012010038540265e40180b0020024020070a204c0180b002001e6488d00801c2881300602c008009
  | 9, 2, 1 => 0xb00102881300602ca2801001201003851026f580180b00200240385102600cd282f01600400480400ef542881300602c00800900801c28bd402600c058010012f4c2200400e1440980300200240a81b00e1440980301600400480400e14409803016f4800800905201c2881300669405801001201003a6d0a204c0180b0020024020070a204c01bd101600400480001e0100380c0a204c0580180be0100385102600c0580021b2010038620a200c058b20020024020070a204c0180b7a00040048070a204c0182f0160040018f9
  | 9, 2, 2 => 0x801c288137b600c058010012010038512326880180b00200244680400e1882880301600400480400e1440982c00602c00800900801d5c80c0a204c0580100120000200734004c0180b0020020020070a204c0180b7b400400484400801c28813006004001b597b20100385102600c05801001201003bd80a204c0180b00200242f88d00801c2881300602c0048040a204c01831016004003d7900801c3105100602cbd00100120100381300602c0080009a7864c680400e1440980301600400481900801c098030160040004d9
  | 9, 2, 3 => 0xa60d80205102600c05801001203c020070a204c0180b002e324020070d004c0180b002000d0c80400e14409803016004003de900801c31051006558058010012010038517ba04c0180b0020024020070a204c0192e0160040048040a204c0183101600514000919e0100386802600c0580100120100380c0a21500980b0020024020070a2f700980301600400480400e1440980301637c00800908801003a070a204c01801001201003a3a0d004c0180b00200240000f00801c2881300602c00c00000801c2881318c02c008008
  | 9, 2, 4 => 0x880100381300602c0080009b20100385102600df100b0020024038610a204c0182f016004004a7700801c2881300602c008009000010038510261140580100100100385102600c05be10020024020070a204c0180b002001f0480400e145ef81300602c00800900801c3401300602cdb001001201003a6d0c41440180b0020024020070a204c0180b5600040048bb00801cc601300602c0080090be01003bd50a204c0180b00120140385102600c1780b00200242200400e14409a2400600400480400e14409a5700602c008009
  | 9, 2, 5 => 0x801c098030160e40080009b2000020070a204c0180b00232a0020510260d00183101600400480400e1a009803016004c2000900003c2f80400e1440980301700100386802600c0580100029a4020070a204c0180b002001f1c80000801c2881300602c0081e801e0100385131804c0180b0032010038510a804c0180b0020025c700400e1440980301600400481b00e1440980305e02c0080090081440980306202c0080024d201c3105102600c1780b0020024020072fc144d101300602c00c80000801cd881300602c008008
  | 9, 2, 6 => 0x801c288130060340080009b203c020070a204d3b0030160064020077cc1440980301600400480400e01c2881300602c008009088010038670a204c0180100120109385102600c0580100040a4020070a204c0180b002001da48bb00e1440980305e02c00800900801c2881300602c0080053120000386802600c1780b0020020020070a204df280301600400480019e01c2881300602c008ce800003c020070c41440180b003001003b720a804c0180b0020024020070a204c0180b7c800400480400e14409ad400602c008009
  | 9, 2, 7 => 0x801c310510a800c058010012fac020070a204c0180b00200244680400e04c0180b00200026c80400e14409803016004003ea900801c2881300602c6180021b203c020070a26880980301600640200702600c0597a00200026c80400e1440980329a02c00800900801c2881300602c1380100120100380c0a20880980b0020025f480400e14409803016004004be800801c2881300602c00800900801c288137ce00c05801001203c020070a204c0182f01600640780400e1440980301600467480400ec482881300602c008009
  | 9, 2, 8 => 0x801c288130065d4058010012010038510260e80180b0020025f780400e1440980301600400480401c1440980301600400065902a01c2881300602c0080021b20100385104404c0180b0020025f700400e1440980301600400480000801c2881300603400800801e010039740a204c0180b003201003813006558058010001365f680400e1440980301600400484b00801c0605102602c00800918201c2881300602c0080031f20100385102600c058017d80024020070a204c0180b0020009c484412c0100385102600c008009
  | 9, 2, 9 => 0x801c2881300602dab001001214c020070a204c018560020024020070a804c0180b002000dcc80400e77409803016004001029008fcc0385102600c0580100120100385102600c05bf20020024020070a204c0180b7e200400484400e1440980305e02c00800900a0100385104400c0580100120000780400e04c0180b00213602f80400e1500980301600400480400e1440980301666000800900801c2881300602c0080027d2e600385102600c1780b0020024020070a204c0180b002001f8484b00801c2881300602c008009
  | 9, 2, 10 => 0xe1440980305e02c0080021b217c2580400e1440980301600240780400e1440980306202c00c8000a6010288130060040018f800801c2a01300602c008001192fd4020070a204c0180b0020024020074681440980301600400480400e1a00980301651400800900801c2881300602dfa0010012000020070a204c0180b0021be0020070a204c0180b00200159480400e14409803016004002479088010039a802600c05801001201c288130060bc058390020024020070c41441100301600400485f00801c288130062b0058009
  | 9, 2, 11 => 0x801c28813006fe405801001203c020070a26e8098030160064020070d004c0180b50c00400480400e1440180b00200026865900e1440980305e02cbd0010012fe0020070a204c0180b00200242f9bb00801c2881300602c00480400e0300605102602c0080090000100380c0a804c0580100100100385102600c05bf70020024020070a204c0180b00255400484b00801c3105100602c00800900801c2a01300602c0080009b2010038540260600180b0020024020070d004c0180b01600400480400e14409bf600602c008009
  | 9, 2, 12 => 0x54010288130060c4058010012054020070a804c0180b0020024020070a25180980b28a00400480f00801c2881300602cdb001900801c28bff02600c0580100120100380c0a204c0180b00200240000400e1500980301600400400400e14409803016004003fe900e1440980305e558058010012010038517fa04c0180b00200240780400e14409803016004d0c80400eff02881300602c00800903601c2881300602c0080014d201003851026fec0180b0020024020070d004c0180b29200400480400e14409803016004003fa9
  | 9, 2, 13 => 0x801c2881300602ca380100120100391102600c058010004364020070a204c0180b00200201c80400e1440980301600400402900801c2881300600c0580100120100382202600c0580100013660080400e1440980301600400480000801c2881305802c008008000010038130060340080009b003c020070a204c0180b00229a42200400e1440980300200032c83600801c3401300602c00800900801c2881300602c0080080120100385402600c05801000e3240385102600c1780b7a400400480400e1440997900602c008009
  | 9, 2, 14 => 0x80e0100385102600c05801001212c0200702600c058010001364020070a221c0180b00200081480400e144098cb0160040010d900801c060620a200c058010012000020070c41500180b00200200240600e1440980301600400480400e189fe05100602c00800900801c3401300602c00a9a00120100385147a04c0180b0020024020070a22f40180b00200056c80400e6302a01300602c00800900801d4386802600c0580100120100385102600e0280b00200240205102600da383101600400480400e14409c0400602c008009
  | 9, 2, 15 => 0x801c2881300602c00a4200120100385102600e0500b0020024038510a804c0182f01600400480400ebc42881300602c00800900801c2881300602c00bbb0012010038510270240180b00200240200740e1a00980301600400480400e1500980305e02c0080090880100385102600c0080015b20100386802600c058010006d640000000801c0980301a00400380400e1456c01300602c00800954a0100385102600c0580100122ec0205131804c0180b0020024020070a204c0583900200074c85f00801c2881300602e040009
  | 9, 3, 0 => 0x5860100385102600c0580100120100385102600c058010008e24020070d01440180b0020000b480400e1440993d01652400800900801c2881300602c0e0010012010039740a804c0180b00200240780400e1460701300602c00c80400e4380980301600400065900801c2885102600c0580100120100385102600c0580181a0024020070a204c0180b00200206481500e1440980315802c00800900801c288136c600c058010012010038680268900180b0020024020070a86880980301600400480400e144098030160040040b9
  | 9, 3, 1 => 0xe144110130060bc0580100120100380c02600c0580100013640780400e5f82881300602c00c80400e81c2894602602c00800900e144098030160040010d14d2010038670d004c0180b00200240000400e8d0098030160040040070a204c0182f39a02c00800900801c2881300602c009b800120000200702600c0580100091e00205102600cd283101600400480006c19c2881300602c00800811a0102881300602c00800119303c020070a204c0180b00200245d80400e5f80980301600400480400e145b901300602c008009
  | 9, 3, 2 => 0x88010038680a204c01801001304c2f80400e1440980301600240205102600ccc83101600400484400801c2894602600c0080090be0100380c0a204c058010012012090070a204c0180b00200240385102600c1785601600400480408001c2881300615805801912c0100386802600c058010012594020070a204c0180b00200240000400e00c0580100013432c01500801c2881315802c008009000010038510260e805801001003c020070a204c0180b28a0064020078221440980301600400480400e1460801300602c008009
  | 9, 3, 3 => 0x801c0605102602c0080009b20100380c0a204c0580100023242f80400e1440980301600400480400e1440980382e02c0080090000100385102600c4080100100100397e0a204c0180b0025f640780400e1448c81300602c00c80f01e0100385102600c05801900801c28c1602600c05801001201c288130060bc05c1500200240000400e04cbc80301600400400f00801c2881300602ca4801900801c28add02600c0580100120100380c0a204c058010006e64020070a3050098030160040049bb00e1440980305e02c008009
  | 9, 3, 4 => 0x2ec0218c02600c0580100100120c8070a204c0180b0020024020070a204c0180b002000464bce00801c2881300602c008009088010038510264f40180100120100385112804c0180b0020024020070190602881301600400480400e1500980301691800800900801c2a01300602cdb001001203c1b00400e144098030160064020070a204c0180b06600081480400e14409803016004001b990880100385102600cb200100120100385402600c058010006864020070a204c0180b0020000b480400e14409803016004f10009
  | 9, 3, 5 => 0x801c288bd02600c05801001201003c180a204c0180b00200240780400e144098030160048c48070181440980305e02c00800900801c2881383400c058010012010039a202600c0580100059e4000070a804c0182f01600400405f00801c3105100602c00800901e0100385102600c058012fb2000020070181440980b0020020020070a2518d100301600400480400e04c0180b0380040004d900801c2a01300602c0098400120100385402600c0580100029a4020070a204c0180b00200026c80400e14411013006004000659
  | 9, 3, 6 => 0x1e0100385102600c0580120520100385123204c0195601600240280400e1440180b00200026cb5500801c2881300602c00800906e0100385102600c0580100120a81b0040a204c0180b00200240780400e81c2881300602c00c80400e1460e81300602c0080090880100385102600c0080031f2010038620a200c058010006e64020070a30700980301600400480400e1457a01300602c00800901e0100385102600c0580136b20100385102600c0680b0020024020070a204c0180b83600400480400e030288130160040038c9
  | 9, 3, 7 => 0x801c2881300602cdf0010012010038510264f40195600200240000400e0303105101600400400000801c2891900602c8c000800801c3105100602c0080009b20100385102600c05801000e3242200400e1440980334a00400480400e184288030160040004d900801c060515bc04c05801001201c288130060bc05947002002402007018144c601301600400480400e188288030160040008c90000100386800602c0080002d017c020070a204c0c0030160024020070a204c0180b00307800480000801c2881300602c008008
  | 9, 3, 8 => 0xbe054020070a204c0180b00120100380c0a26880980b00200240000400e1882880301600400400f00801c3385102600c05801900801c2881300602c008008432010038f002600c058010002b661000400e1440980301600400484400a0100385102600c00800900801c28ade02600c0580100120100385102600c058c30020024020070a26300980301600400480400e18828af400602c00800900801c060510260bc0580100120100385102600c05801000a2a4020070d004c0180b00200032c80400f07c2a01300602c008009
  | 9, 3, 9 => 0x801c289a202600c0580100120002200400e1a0098030020020020070a204db500301600400480400e04c0180b002000dc84d900801c3401300602c0080015b20100380c2e81440980b00200241500400e1440983401600400480400e1440980305e02c00800900801c3105100602c00800719217c0200702600c058010001365b000400e1440980301600400488d0081440980306202c008009088010038620a204c018010013088020070a804c0180b00200241480400e1440980301600400484400801c3085102600c008009
  | 9, 3, 10 => 0x801d2e85102600c0580100120100381300602c0080009a1364020070a204c0180b00200212480400e1440980384602c00800900801cba05102600c0580100120100385102600c05b430020024b780400e1440980301600400480000801cbf01300602c0097d800801c341b702600c05801001203c020070a204c0180b00224240200702600c0580100023026c80400e144d401300602c00800900801c3105131800c0580100120100385402600c059450020024020074aa144098030160040048bb0880100385102600c008009
  | 9, 3, 11 => 0x801c2a01300602ca480100120100385102600c05801000e6e4020070a204c2280b00200048480400e14409c2600602c00800900801c2881300602c008001d32010038620a200c1780b0020024020070d01441101300600400480400ec083401300602c00800900a0100385134400c05801001201003a0702600c0597a00200240000f0081440980306202c00c00400e1440980384a02c0080090000100381300602c0080002d00000200701804c0580100013602900400e1440980301600400480400e150098036e202c008009
  | 9, 3, 12 => 0x140200700602c0080009b01a4020070a204c0180b00200242204400801c2881300600400480400e72c3101300602c00800900801c288130070a00580100120000200702600c0680b00200200780400edd02881300602c00cb980880100385102600c0080091780100385102600c0580100120100385184e04c0180b00200241b00400e1500980301600400480400e188ba05100602c00800900801c8885102600c0580100120000200702600c058010001360020070c4144d100301600400480400e04c0180d0160040004d9
  | 9, 3, 13 => 0x801c28ae202600c058010012304020070a204c0180b0020024020070a804c0180b002000dac80400e1440980301600400429900801d1d05102600c05801001203c020070a204c0180b00249a4020070181440980b36c00400480400e1a03401300602c0080090000100386200602c0080009b0000020070c200c0580100013602200400e1440980307200400480400e1a0a301300602c00800900801d0385102602cbd00100120100380c0a204c0580100068640200731804c0180b00200026c81b00e1440986b00602c008009
  | 9, 3, 14 => 0x801c2881300602d230010012010039a202600c058010001364020070a804d1200301600400480400e144098030166d800800900801ca301300602d1c80100120000380c0a204c1780b00200202200400e144098032f40040048070a204c0182f0160040004d90090ac0385102600c0580100120100385102600c0580100068640780400e1440986b00602c00c80400e81c2a01300602c00800900801c0605102602c0080014d20100385102600c059e000200240200702600c1780b00200026c80400e14409803016006150009
  | 9, 3, 15 => 0x801c3385402600c05801001201c288130060bc05801000e324020070c41440180b002000d0c80400f0b82881300602c0080096b80100385102600c05801001201003a3402600c059490020024000070a204c0182f01600400400400e144a300301651400800985a0100385102600c0580100120001b80400e1440980b0020020020072e804c0180b00200026c80400e14409803016004000a690880100385102600cab0010012000148070a204c0180b0020020020070d004c9e803016004004c2c00801c2881300602c008009
  | 9, 4, 0 => 0x100386804404c0180100100100385102600c4080b0020024020070a25180993d01600400480400e18828803016004000a6900801c2881306800c0580120520100385102600cc300b0020024020070d004c0180b002000c7c80400e1453701300602c00800900801c2881300602c008001112010038620a200c059b60020024020070a204c0180b00207832cc3000801c2881300602c008009000010039a802600c0580100100100385102600d3580b0020024020070a204e1780301600400487400801c2881300602c008009
  | 9, 4, 1 => 0x801c09803016004001a109b2010038620d004c0180b00200240200704404c0180b15400400480400e1843401300602c0080098440100385102600c0580100120100380c0a204c0594500200261980400e1440980301600400480500801c3401300602c00800900801c2881300602c0080086530c4020070a204c0180b00200240385102600c1780b00200067484400801c2885402600c00800900801c4d85102600c0580100120100385181c04c0180b0020024020073541440980301600400480400e1440980332602c008009
  | 9, 4, 2 => 0x86a0100385102600c0580100121e8020070a204c0180b00200241b00400e0302881301600400480400e144098030165240080092120100385102600c0580100120100385102600c05a8600200242200400e1441101300600400480018201c2881300602c00800800801c28813006dc40580100120100385102600c0580b0020024020070a204c0180b0030d000480400e030288130165240080090000100385102602c008001d300100385102600c0594500200240200702600c059b600200026c80000801d038130165e8008008
  | 9, 4, 3 => 0x3e40385102600c0580100100100385102600c058010010e240200701881c2881301600400484400801c3401300602c00800900801c3105100602ca4801001201003a870a204c0180b0020024020070a204c0180b00232800480400e1452981300602c00800900801c0605102602c0080036b201c289ba02600c1780b0020024020070a804c0180b00200032c80400e1440980386e02c00800900801c2881300602c5c801001217c020070a204c01c3601600241b00400e1440980301600400480400e18828803016514008009
  | 9, 4, 4 => 0x801c2881300602c008008732010038620a200c058010006d64020070ce0302881301600400480400e1a0098030165e800800900801c098030165140080009b2000020070a25180594500200202200400e030288130060040048000880100385402600c00800800801c2a01300602c0080015b201003a070a204c0180b00200241b00400e1882880301600400480400e14409803016004001b5900801cad85102600c0580100120100385102600cab0560020024020070d004c0180b07200400480400e1440982c016004000659
  | 9, 4, 5 => 0x801c2881300602c008008752010038680a804c0180b00200256184400801c2881300600400480400e5182a01300602c00800900801c338620a200c0580100120003d00400e04c0180b00200202200400e14409b6300600400483600801c098030160040004d91a60100385102600c0580100120100385102600c05801000c6e4020070a204c0180b54200400480400e144098030162a80080090f40100381300602c0080009b2010038670a204c0180b00200240200702600c0594900200026c80400e81c3105100602c008009
  | 9, 4, 6 => 0x400e1440983a016004000ad900801cba17e02600c05801001201003a0702600c058010001364020071ae1440980301600400480400e04c0180b002000269b59
  | 10, 0, 0 => 0x100386802600c058010010010038620a204c0180b0020024020070c21440980301600400480500801c2881300602c00800900801c288130066940580100120100385102600c0580100063e4020070a204c9e80301600400480400e1a02881300602c0080090540100385102600c0580100120100385128c04c0180b00200240004400801c2881300600400400400e14409803016004000ad900801c2881300602c008000cb2010038510261ac0180b0020024020070a204c1a00301600400480400e14409803016004001269
  | 10, 0, 1 => 0x801c2881300602c0080011920100385102600c058010006e642f80400e1440980301600400480400e0302881300602c0080090000100385402600c05801001012c020070a204c0180b0020024020070a20880980301600400480400e1442a01300602c00800900003c020070a204c0180b00300100385102600cab00b00200244680400e1440980301600400480400e144098030165e800800900801c2881300602c1c8010012010200070a204c0180b00200242200400e144098030160040048bb00801c2881300602c008009
  | 10, 0, 2 => 0x6c0100385102600c0580100120100385102600c059490020024020070a204c0180b28a00400480000e1440980305e02c00800800801c2881300602c0080014d20100385102600c059b60020024020070a204c0180b002000d0c80000801c098030160040004d800801cba05102600c0580100120100385134404c0180b0020024020070a204c0182f01600400480000801c3105100602c00800800801c2898c02600c058010012000020070a204c0180b00200200000400e0302881301600400400400e144098030160040004d9
  | 10, 0, 3 => 0x10038670a204c0180b00200240200740e1440980301600400480400e14409803016004001b59
  | 11, 0, 0 => 0x801c2881300602c008008
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 70
  | 7 => 81
  | 8 => 92
  | 9 => 103
  | 10 => 103
  | 11 => 92
  | _ => 0

def idWidth : Nat := 11

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 224 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3fffffffffff00000000000000003fffffffffff, 46)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)

theorem ori_ok {u ys} (h : NatRun (mask 112) (goal 112) u ys) :
    NatRun (mask 112) (goal 112) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 12 0 (NN s)

def poolG : List Nat := [70950409617917040, 19167848655079541, 59699091024758897, 19166694425657507, 19166713755063500, 59680459425184882, 7907706034866335, 81093406574667888, 7907711420365984, 59680410068697248, 59699107105736818, 46169618683953264, 24788557460783217, 38307042191067253, 24777512904147103, 90130290470684784, 38288408471258224, 19148020913390704, 19148020977353840, 29292204332794992, 19167799259813027]

def Z (s : Nat) := bar 112 S NN idx ori poolG s

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
private theorem z6_96 : ∀ i, 96 ≤ i → i < 98 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 96 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 98 → Z 6 i = true := (range_split (range_split (range_split z6_0 (range_split z6_8 z6_16)) (range_split z6_24 (range_split z6_32 z6_40))) (range_split (range_split z6_48 (range_split z6_56 z6_64)) (range_split (range_split z6_72 z6_80) (range_split z6_88 z6_96))))

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
private theorem z7_584 : ∀ i, 584 ≤ i → i < 590 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 584 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 590 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 z7_24)) (range_split (range_split z7_32 z7_40) (range_split z7_48 (range_split z7_56 z7_64)))) (range_split (range_split (range_split z7_72 z7_80) (range_split z7_88 z7_96)) (range_split (range_split z7_104 z7_112) (range_split z7_120 (range_split z7_128 z7_136))))) (range_split (range_split (range_split (range_split z7_144 z7_152) (range_split z7_160 z7_168)) (range_split (range_split z7_176 z7_184) (range_split z7_192 (range_split z7_200 z7_208)))) (range_split (range_split (range_split z7_216 z7_224) (range_split z7_232 (range_split z7_240 z7_248))) (range_split (range_split z7_256 z7_264) (range_split z7_272 (range_split z7_280 z7_288)))))) (range_split (range_split (range_split (range_split (range_split z7_296 z7_304) (range_split z7_312 z7_320)) (range_split (range_split z7_328 z7_336) (range_split z7_344 (range_split z7_352 z7_360)))) (range_split (range_split (range_split z7_368 z7_376) (range_split z7_384 z7_392)) (range_split (range_split z7_400 z7_408) (range_split z7_416 (range_split z7_424 z7_432))))) (range_split (range_split (range_split (range_split z7_440 z7_448) (range_split z7_456 z7_464)) (range_split (range_split z7_472 z7_480) (range_split z7_488 (range_split z7_496 z7_504)))) (range_split (range_split (range_split z7_512 z7_520) (range_split z7_528 (range_split z7_536 z7_544))) (range_split (range_split z7_552 z7_560) (range_split z7_568 (range_split z7_576 z7_584)))))))

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
private theorem z8_648 : ∀ i, 648 ≤ i → i < 656 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_656 : ∀ i, 656 ≤ i → i < 664 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_664 : ∀ i, 664 ≤ i → i < 672 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_672 : ∀ i, 672 ≤ i → i < 680 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_680 : ∀ i, 680 ≤ i → i < 688 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_688 : ∀ i, 688 ≤ i → i < 696 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_696 : ∀ i, 696 ≤ i → i < 704 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_704 : ∀ i, 704 ≤ i → i < 712 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_712 : ∀ i, 712 ≤ i → i < 720 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_720 : ∀ i, 720 ≤ i → i < 728 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_728 : ∀ i, 728 ≤ i → i < 736 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_736 : ∀ i, 736 ≤ i → i < 744 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_744 : ∀ i, 744 ≤ i → i < 752 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_752 : ∀ i, 752 ≤ i → i < 760 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_760 : ∀ i, 760 ≤ i → i < 768 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_768 : ∀ i, 768 ≤ i → i < 776 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_776 : ∀ i, 776 ≤ i → i < 784 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_784 : ∀ i, 784 ≤ i → i < 792 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_792 : ∀ i, 792 ≤ i → i < 800 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_800 : ∀ i, 800 ≤ i → i < 808 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_808 : ∀ i, 808 ≤ i → i < 816 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_816 : ∀ i, 816 ≤ i → i < 824 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_824 : ∀ i, 824 ≤ i → i < 832 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_832 : ∀ i, 832 ≤ i → i < 840 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_840 : ∀ i, 840 ≤ i → i < 848 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_848 : ∀ i, 848 ≤ i → i < 856 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_856 : ∀ i, 856 ≤ i → i < 864 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_864 : ∀ i, 864 ≤ i → i < 872 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_872 : ∀ i, 872 ≤ i → i < 880 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_880 : ∀ i, 880 ≤ i → i < 888 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_888 : ∀ i, 888 ≤ i → i < 896 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_896 : ∀ i, 896 ≤ i → i < 904 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_904 : ∀ i, 904 ≤ i → i < 912 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_912 : ∀ i, 912 ≤ i → i < 920 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_920 : ∀ i, 920 ≤ i → i < 928 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_928 : ∀ i, 928 ≤ i → i < 936 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_936 : ∀ i, 936 ≤ i → i < 944 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_944 : ∀ i, 944 ≤ i → i < 952 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_952 : ∀ i, 952 ≤ i → i < 960 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_960 : ∀ i, 960 ≤ i → i < 968 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_968 : ∀ i, 968 ≤ i → i < 976 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_976 : ∀ i, 976 ≤ i → i < 984 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_984 : ∀ i, 984 ≤ i → i < 992 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_992 : ∀ i, 992 ≤ i → i < 1000 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1000 : ∀ i, 1000 ≤ i → i < 1008 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1008 : ∀ i, 1008 ≤ i → i < 1016 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1016 : ∀ i, 1016 ≤ i → i < 1024 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1016 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1024 : ∀ i, 1024 ≤ i → i < 1032 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1032 : ∀ i, 1032 ≤ i → i < 1040 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1040 : ∀ i, 1040 ≤ i → i < 1048 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1048 : ∀ i, 1048 ≤ i → i < 1056 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1056 : ∀ i, 1056 ≤ i → i < 1064 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1064 : ∀ i, 1064 ≤ i → i < 1072 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1072 : ∀ i, 1072 ≤ i → i < 1080 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1080 : ∀ i, 1080 ≤ i → i < 1088 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1088 : ∀ i, 1088 ≤ i → i < 1096 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1088 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1096 : ∀ i, 1096 ≤ i → i < 1104 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1096 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1104 : ∀ i, 1104 ≤ i → i < 1112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1112 : ∀ i, 1112 ≤ i → i < 1120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1120 : ∀ i, 1120 ≤ i → i < 1128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1128 : ∀ i, 1128 ≤ i → i < 1136 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1136 : ∀ i, 1136 ≤ i → i < 1144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1144 : ∀ i, 1144 ≤ i → i < 1152 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1152 : ∀ i, 1152 ≤ i → i < 1160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1160 : ∀ i, 1160 ≤ i → i < 1168 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1168 : ∀ i, 1168 ≤ i → i < 1176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1176 : ∀ i, 1176 ≤ i → i < 1184 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1184 : ∀ i, 1184 ≤ i → i < 1192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1192 : ∀ i, 1192 ≤ i → i < 1200 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1200 : ∀ i, 1200 ≤ i → i < 1208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1208 : ∀ i, 1208 ≤ i → i < 1216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1216 : ∀ i, 1216 ≤ i → i < 1224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1224 : ∀ i, 1224 ≤ i → i < 1232 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1232 : ∀ i, 1232 ≤ i → i < 1240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1240 : ∀ i, 1240 ≤ i → i < 1248 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1248 : ∀ i, 1248 ≤ i → i < 1256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1256 : ∀ i, 1256 ≤ i → i < 1264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1264 : ∀ i, 1264 ≤ i → i < 1272 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1272 : ∀ i, 1272 ≤ i → i < 1280 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1280 : ∀ i, 1280 ≤ i → i < 1288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1288 : ∀ i, 1288 ≤ i → i < 1296 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1296 : ∀ i, 1296 ≤ i → i < 1304 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1304 : ∀ i, 1304 ≤ i → i < 1312 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1312 : ∀ i, 1312 ≤ i → i < 1320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1320 : ∀ i, 1320 ≤ i → i < 1328 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1328 : ∀ i, 1328 ≤ i → i < 1336 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1336 : ∀ i, 1336 ≤ i → i < 1344 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1344 : ∀ i, 1344 ≤ i → i < 1352 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1352 : ∀ i, 1352 ≤ i → i < 1360 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1360 : ∀ i, 1360 ≤ i → i < 1368 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1368 : ∀ i, 1368 ≤ i → i < 1376 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1376 : ∀ i, 1376 ≤ i → i < 1384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1384 : ∀ i, 1384 ≤ i → i < 1392 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1392 : ∀ i, 1392 ≤ i → i < 1400 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1400 : ∀ i, 1400 ≤ i → i < 1408 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1408 : ∀ i, 1408 ≤ i → i < 1416 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1416 : ∀ i, 1416 ≤ i → i < 1424 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1424 : ∀ i, 1424 ≤ i → i < 1432 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1432 : ∀ i, 1432 ≤ i → i < 1440 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1440 : ∀ i, 1440 ≤ i → i < 1448 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1448 : ∀ i, 1448 ≤ i → i < 1456 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1456 : ∀ i, 1456 ≤ i → i < 1464 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1464 : ∀ i, 1464 ≤ i → i < 1472 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1472 : ∀ i, 1472 ≤ i → i < 1480 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1480 : ∀ i, 1480 ≤ i → i < 1488 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1488 : ∀ i, 1488 ≤ i → i < 1496 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1496 : ∀ i, 1496 ≤ i → i < 1504 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1504 : ∀ i, 1504 ≤ i → i < 1512 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1512 : ∀ i, 1512 ≤ i → i < 1520 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1520 : ∀ i, 1520 ≤ i → i < 1528 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1528 : ∀ i, 1528 ≤ i → i < 1536 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1536 : ∀ i, 1536 ≤ i → i < 1544 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1544 : ∀ i, 1544 ≤ i → i < 1552 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1552 : ∀ i, 1552 ≤ i → i < 1560 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1560 : ∀ i, 1560 ≤ i → i < 1568 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1568 : ∀ i, 1568 ≤ i → i < 1576 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1576 : ∀ i, 1576 ≤ i → i < 1584 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1584 : ∀ i, 1584 ≤ i → i < 1592 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1592 : ∀ i, 1592 ≤ i → i < 1600 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1600 : ∀ i, 1600 ≤ i → i < 1608 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1608 : ∀ i, 1608 ≤ i → i < 1616 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1616 : ∀ i, 1616 ≤ i → i < 1624 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1624 : ∀ i, 1624 ≤ i → i < 1632 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1632 : ∀ i, 1632 ≤ i → i < 1640 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1640 : ∀ i, 1640 ≤ i → i < 1648 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1648 : ∀ i, 1648 ≤ i → i < 1656 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1656 : ∀ i, 1656 ≤ i → i < 1664 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1664 : ∀ i, 1664 ≤ i → i < 1672 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1672 : ∀ i, 1672 ≤ i → i < 1680 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1680 : ∀ i, 1680 ≤ i → i < 1688 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1688 : ∀ i, 1688 ≤ i → i < 1696 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1696 : ∀ i, 1696 ≤ i → i < 1704 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1704 : ∀ i, 1704 ≤ i → i < 1712 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1712 : ∀ i, 1712 ≤ i → i < 1720 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1720 : ∀ i, 1720 ≤ i → i < 1728 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1728 : ∀ i, 1728 ≤ i → i < 1736 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1736 : ∀ i, 1736 ≤ i → i < 1744 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1744 : ∀ i, 1744 ≤ i → i < 1752 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1752 : ∀ i, 1752 ≤ i → i < 1760 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1760 : ∀ i, 1760 ≤ i → i < 1768 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1768 : ∀ i, 1768 ≤ i → i < 1776 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 1768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_1776 : ∀ i, 1776 ≤ i → i < 1781 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 1776 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 1781 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z8_0 (range_split z8_8 z8_16)) (range_split z8_24 (range_split z8_32 z8_40))) (range_split (range_split z8_48 (range_split z8_56 z8_64)) (range_split (range_split z8_72 z8_80) (range_split z8_88 z8_96)))) (range_split (range_split (range_split z8_104 (range_split z8_112 z8_120)) (range_split (range_split z8_128 z8_136) (range_split z8_144 z8_152))) (range_split (range_split z8_160 (range_split z8_168 z8_176)) (range_split (range_split z8_184 z8_192) (range_split z8_200 z8_208))))) (range_split (range_split (range_split (range_split z8_216 (range_split z8_224 z8_232)) (range_split (range_split z8_240 z8_248) (range_split z8_256 z8_264))) (range_split (range_split z8_272 (range_split z8_280 z8_288)) (range_split (range_split z8_296 z8_304) (range_split z8_312 z8_320)))) (range_split (range_split (range_split z8_328 (range_split z8_336 z8_344)) (range_split (range_split z8_352 z8_360) (range_split z8_368 z8_376))) (range_split (range_split z8_384 (range_split z8_392 z8_400)) (range_split (range_split z8_408 z8_416) (range_split z8_424 z8_432)))))) (range_split (range_split (range_split (range_split (range_split z8_440 (range_split z8_448 z8_456)) (range_split (range_split z8_464 z8_472) (range_split z8_480 z8_488))) (range_split (range_split z8_496 (range_split z8_504 z8_512)) (range_split (range_split z8_520 z8_528) (range_split z8_536 z8_544)))) (range_split (range_split (range_split z8_552 (range_split z8_560 z8_568)) (range_split (range_split z8_576 z8_584) (range_split z8_592 z8_600))) (range_split (range_split z8_608 (range_split z8_616 z8_624)) (range_split (range_split z8_632 z8_640) (range_split z8_648 z8_656))))) (range_split (range_split (range_split (range_split z8_664 (range_split z8_672 z8_680)) (range_split (range_split z8_688 z8_696) (range_split z8_704 z8_712))) (range_split (range_split z8_720 (range_split z8_728 z8_736)) (range_split (range_split z8_744 z8_752) (range_split z8_760 z8_768)))) (range_split (range_split (range_split z8_776 (range_split z8_784 z8_792)) (range_split (range_split z8_800 z8_808) (range_split z8_816 z8_824))) (range_split (range_split z8_832 (range_split z8_840 z8_848)) (range_split (range_split z8_856 z8_864) (range_split z8_872 z8_880))))))) (range_split (range_split (range_split (range_split (range_split (range_split z8_888 (range_split z8_896 z8_904)) (range_split (range_split z8_912 z8_920) (range_split z8_928 z8_936))) (range_split (range_split z8_944 (range_split z8_952 z8_960)) (range_split (range_split z8_968 z8_976) (range_split z8_984 z8_992)))) (range_split (range_split (range_split z8_1000 (range_split z8_1008 z8_1016)) (range_split (range_split z8_1024 z8_1032) (range_split z8_1040 z8_1048))) (range_split (range_split z8_1056 (range_split z8_1064 z8_1072)) (range_split (range_split z8_1080 z8_1088) (range_split z8_1096 z8_1104))))) (range_split (range_split (range_split (range_split z8_1112 (range_split z8_1120 z8_1128)) (range_split (range_split z8_1136 z8_1144) (range_split z8_1152 z8_1160))) (range_split (range_split z8_1168 (range_split z8_1176 z8_1184)) (range_split (range_split z8_1192 z8_1200) (range_split z8_1208 z8_1216)))) (range_split (range_split (range_split z8_1224 (range_split z8_1232 z8_1240)) (range_split (range_split z8_1248 z8_1256) (range_split z8_1264 z8_1272))) (range_split (range_split z8_1280 (range_split z8_1288 z8_1296)) (range_split (range_split z8_1304 z8_1312) (range_split z8_1320 z8_1328)))))) (range_split (range_split (range_split (range_split (range_split z8_1336 (range_split z8_1344 z8_1352)) (range_split (range_split z8_1360 z8_1368) (range_split z8_1376 z8_1384))) (range_split (range_split z8_1392 (range_split z8_1400 z8_1408)) (range_split (range_split z8_1416 z8_1424) (range_split z8_1432 z8_1440)))) (range_split (range_split (range_split z8_1448 (range_split z8_1456 z8_1464)) (range_split (range_split z8_1472 z8_1480) (range_split z8_1488 z8_1496))) (range_split (range_split z8_1504 (range_split z8_1512 z8_1520)) (range_split (range_split z8_1528 z8_1536) (range_split z8_1544 z8_1552))))) (range_split (range_split (range_split (range_split z8_1560 (range_split z8_1568 z8_1576)) (range_split (range_split z8_1584 z8_1592) (range_split z8_1600 z8_1608))) (range_split (range_split z8_1616 (range_split z8_1624 z8_1632)) (range_split (range_split z8_1640 z8_1648) (range_split z8_1656 z8_1664)))) (range_split (range_split (range_split z8_1672 (range_split z8_1680 z8_1688)) (range_split (range_split z8_1696 z8_1704) (range_split z8_1712 z8_1720))) (range_split (range_split z8_1728 (range_split z8_1736 z8_1744)) (range_split (range_split z8_1752 z8_1760) (range_split z8_1768 z8_1776))))))))

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
private theorem z9_672 : ∀ i, 672 ≤ i → i < 680 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_680 : ∀ i, 680 ≤ i → i < 688 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_688 : ∀ i, 688 ≤ i → i < 696 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_696 : ∀ i, 696 ≤ i → i < 704 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_704 : ∀ i, 704 ≤ i → i < 712 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_712 : ∀ i, 712 ≤ i → i < 720 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_720 : ∀ i, 720 ≤ i → i < 728 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_728 : ∀ i, 728 ≤ i → i < 736 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_736 : ∀ i, 736 ≤ i → i < 744 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_744 : ∀ i, 744 ≤ i → i < 752 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_752 : ∀ i, 752 ≤ i → i < 760 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_760 : ∀ i, 760 ≤ i → i < 768 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_768 : ∀ i, 768 ≤ i → i < 776 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_776 : ∀ i, 776 ≤ i → i < 784 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_784 : ∀ i, 784 ≤ i → i < 792 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_792 : ∀ i, 792 ≤ i → i < 800 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_800 : ∀ i, 800 ≤ i → i < 808 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_808 : ∀ i, 808 ≤ i → i < 816 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_816 : ∀ i, 816 ≤ i → i < 824 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_824 : ∀ i, 824 ≤ i → i < 832 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_832 : ∀ i, 832 ≤ i → i < 840 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_840 : ∀ i, 840 ≤ i → i < 848 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_848 : ∀ i, 848 ≤ i → i < 856 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_856 : ∀ i, 856 ≤ i → i < 864 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_864 : ∀ i, 864 ≤ i → i < 872 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_872 : ∀ i, 872 ≤ i → i < 880 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_880 : ∀ i, 880 ≤ i → i < 888 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_888 : ∀ i, 888 ≤ i → i < 896 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_896 : ∀ i, 896 ≤ i → i < 904 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_904 : ∀ i, 904 ≤ i → i < 912 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_912 : ∀ i, 912 ≤ i → i < 920 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_920 : ∀ i, 920 ≤ i → i < 928 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_928 : ∀ i, 928 ≤ i → i < 936 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_936 : ∀ i, 936 ≤ i → i < 944 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_944 : ∀ i, 944 ≤ i → i < 952 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_952 : ∀ i, 952 ≤ i → i < 960 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_960 : ∀ i, 960 ≤ i → i < 968 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_968 : ∀ i, 968 ≤ i → i < 976 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_976 : ∀ i, 976 ≤ i → i < 984 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_984 : ∀ i, 984 ≤ i → i < 992 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 984 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_992 : ∀ i, 992 ≤ i → i < 1000 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 992 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1000 : ∀ i, 1000 ≤ i → i < 1008 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1000 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1008 : ∀ i, 1008 ≤ i → i < 1016 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1008 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1016 : ∀ i, 1016 ≤ i → i < 1024 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1016 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1024 : ∀ i, 1024 ≤ i → i < 1032 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1024 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1032 : ∀ i, 1032 ≤ i → i < 1040 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1032 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1040 : ∀ i, 1040 ≤ i → i < 1048 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1040 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1048 : ∀ i, 1048 ≤ i → i < 1056 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1048 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1056 : ∀ i, 1056 ≤ i → i < 1064 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1056 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1064 : ∀ i, 1064 ≤ i → i < 1072 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1064 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1072 : ∀ i, 1072 ≤ i → i < 1080 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1072 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1080 : ∀ i, 1080 ≤ i → i < 1088 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1080 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1088 : ∀ i, 1088 ≤ i → i < 1096 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1088 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1096 : ∀ i, 1096 ≤ i → i < 1104 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1096 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1104 : ∀ i, 1104 ≤ i → i < 1112 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1112 : ∀ i, 1112 ≤ i → i < 1120 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 1112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_1120 : ∀ i, 1120 ≤ i → i < 1125 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 5 1120 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 1125 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z9_0 z9_8) (range_split z9_16 z9_24)) (range_split (range_split z9_32 z9_40) (range_split z9_48 z9_56))) (range_split (range_split (range_split z9_64 z9_72) (range_split z9_80 z9_88)) (range_split (range_split z9_96 z9_104) (range_split z9_112 (range_split z9_120 z9_128))))) (range_split (range_split (range_split (range_split z9_136 z9_144) (range_split z9_152 z9_160)) (range_split (range_split z9_168 z9_176) (range_split z9_184 (range_split z9_192 z9_200)))) (range_split (range_split (range_split z9_208 z9_216) (range_split z9_224 z9_232)) (range_split (range_split z9_240 z9_248) (range_split z9_256 (range_split z9_264 z9_272)))))) (range_split (range_split (range_split (range_split (range_split z9_280 z9_288) (range_split z9_296 z9_304)) (range_split (range_split z9_312 z9_320) (range_split z9_328 z9_336))) (range_split (range_split (range_split z9_344 z9_352) (range_split z9_360 z9_368)) (range_split (range_split z9_376 z9_384) (range_split z9_392 (range_split z9_400 z9_408))))) (range_split (range_split (range_split (range_split z9_416 z9_424) (range_split z9_432 z9_440)) (range_split (range_split z9_448 z9_456) (range_split z9_464 (range_split z9_472 z9_480)))) (range_split (range_split (range_split z9_488 z9_496) (range_split z9_504 z9_512)) (range_split (range_split z9_520 z9_528) (range_split z9_536 (range_split z9_544 z9_552))))))) (range_split (range_split (range_split (range_split (range_split (range_split z9_560 z9_568) (range_split z9_576 z9_584)) (range_split (range_split z9_592 z9_600) (range_split z9_608 z9_616))) (range_split (range_split (range_split z9_624 z9_632) (range_split z9_640 z9_648)) (range_split (range_split z9_656 z9_664) (range_split z9_672 (range_split z9_680 z9_688))))) (range_split (range_split (range_split (range_split z9_696 z9_704) (range_split z9_712 z9_720)) (range_split (range_split z9_728 z9_736) (range_split z9_744 (range_split z9_752 z9_760)))) (range_split (range_split (range_split z9_768 z9_776) (range_split z9_784 z9_792)) (range_split (range_split z9_800 z9_808) (range_split z9_816 (range_split z9_824 z9_832)))))) (range_split (range_split (range_split (range_split (range_split z9_840 z9_848) (range_split z9_856 z9_864)) (range_split (range_split z9_872 z9_880) (range_split z9_888 (range_split z9_896 z9_904)))) (range_split (range_split (range_split z9_912 z9_920) (range_split z9_928 z9_936)) (range_split (range_split z9_944 z9_952) (range_split z9_960 (range_split z9_968 z9_976))))) (range_split (range_split (range_split (range_split z9_984 z9_992) (range_split z9_1000 z9_1008)) (range_split (range_split z9_1016 z9_1024) (range_split z9_1032 (range_split z9_1040 z9_1048)))) (range_split (range_split (range_split z9_1056 z9_1064) (range_split z9_1072 z9_1080)) (range_split (range_split z9_1088 z9_1096) (range_split z9_1104 (range_split z9_1112 z9_1120))))))))

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
private theorem z10_48 : ∀ i, 48 ≤ i → i < 51 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 48 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 51 → Z 10 i = true := (range_split (range_split z10_0 (range_split z10_8 z10_16)) (range_split (range_split z10_24 z10_32) (range_split z10_40 z10_48)))

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

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 112) (goal 112) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

end PEqualNP.Outside.L_meta_8509_aux

theorem PEqualNP.Outside.L_meta_8509 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_8509_aux.mainG PEqualNP.Outside.L_meta_8509_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩
