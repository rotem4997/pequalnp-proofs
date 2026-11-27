import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8477_aux

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

abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)

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

def rowsG : List ℕ := [1, 2, 2, 2, 32, 60, 60, 60, 60, 120, 180, 180, 180, 180, 225, 240, 10, 10, 10, 10, 18, 18, 18, 33, 33, 33, 33, 36, 36, 36, 40, 40, 40, 48, 48, 96, 129, 130, 130, 130, 130, 160, 160, 26, 1, 4, 4, 4, 64, 90, 90, 90, 90, 120, 210, 210, 210, 210, 225, 240, 12, 12, 12, 12, 20, 20, 20, 65, 65, 65, 65, 66, 66, 66, 72, 72, 72, 80, 80, 96, 129, 132, 132, 132, 132, 192, 192, 28, 1, 1, 8, 8, 16, 128, 120, 120, 225, 225, 240, 240, 24, 24, 129, 129, 144, 144, 97, 97, 104, 104, 112, 224, 3, 3, 6, 34, 34, 61, 62, 124, 188, 122, 181, 182, 188, 244, 227, 242, 11, 14, 42, 138, 19, 22, 50, 35, 37, 41, 49, 37, 38, 100, 41, 42, 168, 49, 50, 98, 131, 131, 134, 138, 162, 162, 168, 27, 5, 5, 6, 68, 68, 91, 94, 122, 218, 124, 211, 214, 218, 242, 229, 244, 13, 14, 76, 140, 21, 22, 84, 69, 67, 73, 81, 67, 70, 98, 73, 76, 200, 81, 84, 100, 133, 133, 134, 140, 196, 196, 200, 29, 9, 17, 9, 136, 17, 136, 121, 248, 233, 241, 241, 248, 25, 152, 137, 145, 145, 152, 105, 113, 105, 232, 113, 232]

def xsG : List ℕ := [0x5dd7578324f9144238324f9144230cc3030100780400101007804001, 0x4039223de4bfc90ffca5f00000000038003de09e0007f000e, 0xbfc90ffca5f04039223de40000009e0007f000e00038003de0, 0xb679edc81c20f13e0c81c20f13e03030cc801c00f03e0801c00f03e0, 0x4bbed28060470bfe08060470bfe0433cd08060070bfe08060070bfe0, 0xfc0fc00082000e28070fffc4fff8fc0fc00080000c20060fff80fff0, 0xfc0fc070fffc4fff80082000e280fc0fc060fff80fff00080000c200, 0xa3efa87f10008fd007f10008fd0083cf207f00000fc007f00000fc00]

theorem rowsG_len : rowsG.length = 224 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 112 := by decide +kernel

theorem maskG : mask 112 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 112 zs &&& lo 112) ≠ lo 112 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 112) (goal 112) s xsG) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 112) (goal 112) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 112) (goal 112) s xsG) :
    ¬ HasCircuitSize 8 fG 10 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 10 h
  have hr : NatRun (mask 112) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 5 => 4
  | 6 => 68
  | 7 => 184
  | 8 => 272
  | 9 => 57
  | 10 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 5, 0 => 0xfa980f5d7d412c221bfd44bb08895e3d
  | 6, 0 => 0xdcd0a354d344f42fca973d96b8813929b44d2105aff03fb8ad85e077aad826879fd5b1139e6a51649d6c8d7b9ba225d797779ba68b938e73832e16f381aa0bb47d55764a7970c40077c097a96f9eaddc68a5ef51681cf7e4653ecb786490b1d96485f4cc5abce9b65a6ed274596e3e20583cd2a5583bbd3b5448d107537ed05b5331db7c522503df513941c44f1c92644d25233b4ce9490a4adee48e49a4e7f249695dde4836dcf944a617744421accb40bd2d1b4069b9203957b45d388d1b9b358c708432aa4a8631ef401731e941d630bcbf3230a0beb22958b759211e2bdb1fbb8dc91965e853121ebfc5101bc4220e999bf80cd74c390970286008ea71b3
  | 6, 1 => 0xf63d77faf2855f9eeb430672e7fb6813
  | 7, 0 => 0x31bcb1a3314628923137db87302bc6992f43381e2f13ac902c65a23b2c5741892b6643fe2aae9c7e2a67c9972a33c319289d1b3527b84aa427b6f37e26081f4023c598e5236aaac922c2795f2298a05a22931800219ead502122ecb221092e30207122161ea2b5411e6e26731aff6a361a24d4d5195ca20a18f253f018b89ee71874868d17d0547e170b7ae415cf6317154ef192150b868814d4ae0c144fdc4611c09ed4116c8f2d10b03b4b106f9dfa105f0d471028c4d30fea938d0e5e1cb10bc97e360ad272d60a07709b084ed2b7079b1c21069e5ab20619059205f87f3f050b83ac05077977048fda50026e5e3f00d7c1f400bc7a78009772de004356b8
  | 7, 1 => 0x753cef1a744c157f737a3ae5709f56bf6f6063ad6e7ef4906e121b566dc36ba76c25d8056bb721fb685420eb6721a006668f34f666532f846521a3a96520ae9f644ca975640cda1262a18c9861d132ac5c735de4593b3c61573cb22c558f50195560c572545ccf3452dd2553512cad4e4ebc1b714e365e564c1fed904a6f758b48dad3ec47aa16ae46df7dec4609f56043e8f96f43ded2d543bc6e50403ba4273ef321033ee32bf23d8e3f9c3cb53d5c3c7120fb3be2801d3b6521403b482cb43b3ea0163a74b3453954bd7f391597ca3905e01238bafff7383d08d738295d76370a87f236b572c635f8059935ba7a3035136daf34fd1cfa3314794c3247d2a2
  | 7, 2 => 0xffe69ec9fa0552f8f740de24ed5e21b6ebed5489e6afc522e1975680e0226ad2da758886d00cc9f5c9aa989ac7844d1cc6d39b7ac651cc37c2f23152c29f8356c03ea6d3bf92e506bf0c25eeb8813929b55bcf77b3404e11ae281364ad2fdf34ac2df76da4edd75ba35056d4a1c6b7809dd87843992e776f982de31b96fb623696d5eddf96b4861e9350e69c931d04439318f76f92914212923265c88fcf28798e120c098ddcd16e8be4c8368540e17482f1f85a7f42d3fb7d2d77be7d08514b7cae6cd87af23bf87aa6bec17904b1a278859c38774cc096770080af76597a3a
  | 8, 0 => 0x23e125d923d95c9d23d2ba142371de78235de8d9233e870222b49cae22a23e9721f603de21c394cd217edd471f7263bf1f70407b1eb16f981e8fdd711e41f49a1dc1ebba1c3e22651bd149201b5393101ac5d5b11ac3c73a199354cc194211c7186a94c41757ed811692333c163faced15a31a6c149598861388373912bf5a3e129d5e55127e46691276de4d120bfe711136d8b110c0c090107e37db0cbd59f70bee87440af70a490ad272d60abf4e450abb2d7f0a3415de094a7bc80857b54e08378d60079614a10785e7280703cb81064ccf680593407a04a8e0fb0495698a03fd1f2e037a20cf030fa05b01a5981c015f285600e73d9000e09fbe00ba1956
  | 8, 1 => 0x52818acc5157c09350fd871d4f999c0f4ee869ce4e07d9994dd903ce4c13c46849be8a6f4992e9e3496b63aa48c7159647749cde466245ac44cefed9440e11cb43c49763436a9a05434f7f4b43008fe542e7aca241d22d863fc0ac3d3f61d6ed3db043c43d1b51d13c7120fb3c21b4e23baae2853b3ea0163b1432fc3a731a8539c5190239af0b3139a4d2d0390bcc36387530ca37a94f7336cfe383369e2d6f34e9aa7b349d3c0832660a5c32308d4b30b5925730633fa82ff10fa12f754f032da7e5ba2da404322d88980c2d2c6a1f2b87a6a52a97572729e260c7280925ec275ec0a8275a6958260a3908256f6a222568e20d255977f125028dfa24e6de83
  | 8, 2 => 0x8ecb2a898cf6de1b8cb8c43d8ab9439b86b11718868a9589859f22e7858854a58506921084c99a5b842c21df835676b382dab303829e77d0825b808481b1c27b81b17a8980db5b1e7fb32a3c7eb0cf727e57baff7ca742fa7ca5b7507ca0aff97b834bd57b28c2137aa2251879c51da077ce6cd976422e1b75da1def74631e997396eeec72e61a4a72a5e94c70cb77776fd07e216dfcadca6c07490e6ac6092c682fd30866a115ee61b93d1b5ecbb9045d6663495d625a3c5bdbf2d35a2fa3ca5969d36057f24331578fc16157342b8856a45afc55f8233155cb1fdf55c560b75560c57255385c7f54d3525354c5d423545c57b153c46f50536c4ac95346832a
  | 8, 3 => 0xdc981d3edbfb3ba1d5e573cfd5b97e45d59592dad329d531d27c462cd27538a3d1856621d14d3f83cf35e5dfcf1c77a4cd17c5fdc9b2a7fdc92e315fc7678154c6d39b7ac57e8fd9c53f27a5c45775f0c441b242c2f4ad73c240c0dbc0fb89a7bfce1735bec0954fbd9ebaedbd0df62fbb824185b8a84e3fb8a0560bb6933e12b1f4e1d1b190da16b17ce170b14a4a3ab1071fe7b01919d1aef59e9eaed11ab2adb510c7acbe5b0eabee7bccab793f7caabd69a7aa49255da9d67e55a98b61eaa810616ea5a26631a47bbf77a3933162a1601c29a07449d79ff25a359d750ef49a6b585899f98a3c98cba158985eb25296498229942a9a2e920f9a42912af63f
  | 8, 4 => 0xfbc0fd4dfb776963f7f1fed0f740de24f595a7edf41b7472f32ba7a9f183353df0983190eed7ad63ee74cd23ebed5489e9ff9d60e2e981a4e2d0d71be24c607d
  | 9, 0 => 0xfb776963e792bd26e17c3782dffa4ccddb9240e8d5b97e45c9b2a7fdc2f4ad73c27266adb2751b61a9d67e55a8075cb3a5a266319ff15cd6985eb252931bfcac912af63f8c4525a38b1f357280db5b1e76b3670866eee36066dec92963423a7c62bb1e726198e57b602fd9d25f300fd4591214ce5892f1f3567b210a44c22c62449a664743b896c3435d0ef33753ed2234e9aa7b34c4060b345c9b5929e260c728d12f6326e1b5b02643214821f603de1ec350901bf758e21a71a44816fb23891578eb2d0d9792be0abb2d7f0934abb009296c0b067b88cf0593407a01e0581e01a5981c
  | 10, 0 => 0xa9d67e55
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xfffffffbfdfdddf7bcb36f9975a30cc3030100780400101007804001000000bfc90ffca5f04039223de40000009e0007f000e00038003de05dd757bfed6ffce7f8427f333de40000009e0007f000e00038003de0fc0fc070fffc4fff80082000e280fc0fc060fff80fff00080000c200fc0fc00082000e28070fffc4fff8fc0fc00080000c20060fff80fff0ffffffcb34f995523cb34f9955230cc3030100780400101007804001fffffffffd6ffdf7fcc37f3b3de40000009e0007f000e00038003de000000004039223de4bfc90ffca5f00000000038003de09e0007f000e
  | 0, 1 => 0xfc0fc0bfcb0ffeadf74fffe6fffcfc0fc09e8007fc20e60fff80fff0a3efa87f10008fd007f10008fd0083cf207f00000fc007f00000fc004bbed2bfe94ffffff8463d72bfe4433cd09e6007fbfee8063870bfe05dd757b3edfd5ce7b8326f9164a30cc30301007804001010078040014bbed28060470bfe08060470bfe0433cd08060070bfe08060070bfe0b679edc81c20f13e0c81c20f13e03030cc801c00f03e0801c00f03e000000034cb9e6fffcbfcb0ffeadf00000000038003de09e0007f000effffffc87c67fbfe0c87c67fbfe0733cdc807c07fbfe0807c07fbfe0
  | 0, 2 => 0xa269a8ffd90ffdb5f4c1392a3de40000009e0007f000e00038003de0a269a84c1392a3de4ffd90ffdb5f00000000038003de09e0007f000efc0fc074fffe6fffcbfcb0ffeadffc0fc060fff80fff09e8007fc20e5dd7578324f9144238324f9144230cc30301007804001010078040015dd757b3effd5eefb83a6f91e6a30cc3030100780400101007804001000000bfcb0ffeadf34cb9e6fffc0000009e0007f000e00038003de04bbed28463d72bfe4bfe94ffffff433cd08063870bfe09e6007fbfee5dd7578727fb36ce7b7edff7ce7f0cc3030100780400101007804001
  | 0, 3 => 0xffffffc83c61f17e0c83c61f17e03030cc801c00f03e0801c00f03e0ffffff4036f0035a0fbfc6ddc21bffffff61fff80fff1fffc7ffc21fffffffc83c61f37e0c87c65f9fe03030cc801c00f03e0801c00f03e05dd7578326f9164a3b3edfd5ce7b0cc30301007804001010078040014996528463d72bfe4bfe94ffeeff00000000038003de09e0007f000e5dd7578727fb37de7bfedfffce7f0cc3030103f807de19f007ff400f000000bfcb9ffeeffb7cb9f7ffff0000009e0007f000e00038003de003f03f8f0003b0007ff7dfff1d7f03f03f9f0007f000fff7ffff3dff
  | 0, 4 => 0xb679edcc17b2b3de4ffdd2ffdb7f00000000038003de09e0007f000e499652bfe94ffce7f8423d323de40000009e0007f000e00038003de0ffffffc8346191520c83461915200000000000000000000000000000fffffffbfffddfffbcbb6f99f7a3fccfc361fff80fff10180780c201a269a848100081100481000811000000000000000000000000000000fddfd7f3fffd5fffb83a6f91e6a3fccfc361fff80fff10180780c2014996528423d323de4bfe94ffce7f00000000038003de09e0007f000efe6fe878fffccfff84892008f380fc0fc060fff80fff00080000c200
  | 0, 5 => 0x499652b4ebdf6fffcbfeb4ffeeff00000000038003de09e0007f000e1451458407b233de4bfcd2ffca7f00000000038003de09e0007f000e5fffd78064671bfe08064671bfe0433cd08060070bfe08060070bfe0b679edc8142091120c81420911200000000000000000000000000000499ed2b3e94d5fffb8022d10a6a0400cc00060000bfe0000000082005dd757bfedfffce7f8727fb37de70cc3039f007ff400f0103f807de1fddfd783a6f91e6a3f3fffd5fffbfccfc30180780c20161fff80fff1ffffffff34f99fd23ff34f99fd238fcf237f00780fc017f00780fc01
  | 0, 6 => 0xb679edf8dd2cddb78c81620931a00000000000000000000000000000480640bfcb0ffeadf34ebde6fffc0000009e0007f000e00038003de05dd757802461104208024611042000000000000000000000000000004bbed28423d323de4bfe94ffdf7f00000000038003de09e0007f000e0000003783980401f3783980401f8cc3237f83f80401f7f83f80401fffffffcf37fbb7de7fffdfffdf7f0cc3030103f807de19f007ff400f000000bfcb9ffffffbfcb9ffffff0000009e0387f3dee9e0387f3dee499652bfe9dffce7f8723db37de70000009e0007f000e00038003de0
  | 0, 7 => 0xb679edffdd2ffdb7fcc17b2b3de40000009e0007f000e00038003de00000000002000208030c90c4ca580000000000000000000000000000ffffffc874679bfe0c874679bfe0433cd08060070bfe08060070bfe0ffffffcb3cf9f57e3cb3cf9f57e33cf3cf811c78f43e1811c78f43e1ffffffc834619bd20c834619bd20030c000000000bc000000000bc00fc0fc034cb0e6eadc34cb0e6eadcfc0fc00080000c2000080000c200fe7fedc896209f3a0f8fffcdfff8fc0fc00080000c20060fff80fff05dd757b3effd5eefbb3effd5eefb0cc3030100780400101007804001
  | 0, 8 => 0x499652832049144238020d1004200000000000000000000000000000000000000290024a0b3c90d5ca5b0000000000000000000000000000499652802041024a080604508e60000000000000000000000000000000000034cb066aadc34cb066aadcf33cfcfeff87fbffefeff87fbffe000000b7cb9f7ffffbfcb9ffeeff00000000038003de09e0007f000ea269a878d90ccdb58481200831800000000000000000000000000000b679edc81420911a0c81c20d13600000000000000000000000000000fffffffffd6ffffffcc7ff7fbfe4733cdc9e7c07fbfee807f87fbfe0
  | 0, 9 => 0xb669ad4016b0031807bdc2cdc21bffffff61fff80fff1fffc7ffc21febfffac870478bfe0c870478bfe0433cd08060070bfe08060070bfe000000030cb0c4ead830cb0c4ead8000000000000000000000000000000000030c90c4ca58000200020800000000000000000000000000000fffffffbfc6ddc21b4036f0035a0fffffffffc7ffc21f61fff80fff1fe6fe84892008f38078fffccfff8fc0fc00080000c20060fff80fff000000034c90e6ca5c040302228c40000000000000000000000000000a228a87cdb06ebbdc7cdb06ebbdcf33cfcfeff87fbffefeff87fbffe
  | 0, 10 => 0xfc0fc070fffc4fff830cb0c4ead8fc0fc060fff80fff00080000c200a3efa87fd90ccff587f12008fd8083cf207f00000fc007f00000fc00b679edf8dd2cfdbf8c81e20f33e03030cc801c00f03e0801c00f03e049861237e3df0ec1f37e3df0ec1fcfcf337fe3ff0fc1f7fe3ff0fc1f5c105780efff702ff80efff702ff7c30df80fffff03ff80fffff03ff1451458004201002080042010020000000000000000000000000000003f03fff7dfff1d7f8f0003b000703f03fff7ffff3dff9f0007f000fa3efa87f12008fd807fd90ccff5883cf207f00000fc007f00000fc00
  | 0, 11 => 0x145145bfcd2ffca7f8407b233de40000009e0007f000e00038003de0ffffffff36f99fda3fffdfddff7b8fcf237f00780fc017f00780fc01a228a87cd906e9b5c4c1202a3184f33cfcfeff87fbffefeff87fbffe000000bfc99ffce7f87039b37de70000009e0007f000e00038003de0ffffffcc7ff7fbfe4fffd6ffffff733cdc807f87fbfe09e7c07fbfee49965280204100420802041004200000000000000000000000000000ebfffaff30418fd20ff30418fd2083cf207f00000fc007f00000fc00fe7fedf8fffcdfff8c896209f3a0fc0fc060fff80fff00080000c200
  | 0, 12 => 0x4bbed2b0e94f4fff88062470bfe0433cd08060070bfe08060070bfe05dd7578725fb34c678725fb34c670cc3030100780400101007804001a3efa848100081500481000815000000000000000000000000000000b4412d7f9fb8f401f7f9fb8f401fbcc32f7f9ff8f401f7f9ff8f401f4bbed2bfeb4ffffffb4ebdf6fffc433cd09e6007fbfee8063870bfe0b679edffdd2ffdbffcc1fb2f3fe43030cc9e1c07f03ee801f80f3fe04bbed280204101520802041015200000000000000000000000000000ffffffcb3461900034034f001520fffffffffc7ffc21f61fff80fff1
  | 0, 13 => 0x499ed28022d10a6a0b3e94d5fffb400cc0000000082000060000bfe0ffffffc83cf1f17e0cb3c69f57e33030cc801c00f03e0801c00f03e0fd9fd2bfeb4ffeefff4ffff6fffcfc0fc09e8007fc20e60fff80fff04bbed28020410bd208020410bd20030c000000000bc000000000bc0049861237ebdf6eedf37ebdf6eedfffffffffffffffffffffffffffff499652802241024a0b0e94d4ce7800000000000000000000000000004bbed28062470bfe0b0e94f4fff8433cd08060070bfe08060070bfe0b679edc81e20f33e0f8dd2cfdbf83030cc801c00f03e0801c00f03e0
  | 0, 14 => 0x4996528723db37de7bfe9dffce7f00000000038003de09e0007f000efd9fd2f0fffd4fff880a2410e6a0fc0fc060fff80fff00080000c200ebfffac8304181520c8304181520000000000000000000000000000000000037c39e0e81f37c39e0e81fcfcf337fe3ff0fc1f7fe3ff0fc1f4806400002000208030e94c4ce78000000000000000000000000000000000004039222ce4b7c90f7ca5f0000000000000000000000000000fddfd7b3effd5eefbf3fffd5fffbfccfc30180780c20161fff80fff10000000082000e28030cb0c4ead80000000000000000000000000000
  | 0, 15 => 0x80000c20000039003de00000000000000000000038003de0fffffffffdfffdf7fcf36f3b35a7fffffffffffffffffffffffffffffc0fc000a6f80e6a070fffc4fff8fc0fc00080780c20060fff80fff0ebefba7ff3df8fd1f7ff3df8fd1fcfcf337fe3ff0fc1f7fe3ff0fc1fffefe87f34f88fd207f10008fd008fcf207f00780fc007f00000fc00a3efa84b1000855004b10008550000c30001000004000010000040005d9657b7efff7eeffb7efff7eefffffffffffffffffffffffffffffffd9fd280a2410e6a0f0fffd4fff8fc0fc00080000c20060fff80fff0
  | 1, 0 => 0xfc0fc0fffffffffff0483922ffe4fc0fc0feffffffffe0083800ffe0a008800082000a28070db044bbd8f00cc00080000820060ff800bff0fc0fc00082900e6a0f3fffd5fffbfc0fc00080000c20060fff80fff00000008f0003b000704019221d640000009e0007f000e00038003de04bbed28461472bfe48461472bfe4433cd08060070bfe08060070bfe04bbed2802041017e0802041017e00030c0800000003e0800000003e0b669ad7fdfbeffbdf7fdfbeffbdfffffffffffffffffffffffffffffa26fa84810008f1007810008fd00800f000000000c0006000000fc00
  | 1, 1 => 0xfc0fc03f82008ea8074fffc4fff8fc0fc01e80000c20060fff80fff0fddfd7f7ffff7ffffbfeffffeefffccfc361fff80fff19f807ffc20f1441050304b8140030304b8140030cc3030100780400101007804001b4412d4016b0000007b9c28d401bbcc32f619ff8040117f9c78f401f0000000082000e28030cb9c4fff80000000000000000000038003de0a3efa8ff10099fd037f10908fd2083cf207f00000fc007f00000fc00ffefe87f92008ff807ffffccfff8ffcfe07f80000fe007ffff80fff0a00f800000000e0007010000fd00800f000000000c0006000000fc00
  | 1, 2 => 0xa0088070db044bbd80082000a280f00cc060ff800bff000800008200141045800c20702e0800c20702e03030cc801c00f03e0801c00f03e0b4412d7f9fbaf7dffffdfbffca5fbcc32f7f9ff8f7dffff9ffff401f49965280604708e6080204303de00000008000070000000000003de04bbed2bfebdffffffbfebdffffff433cd09e6387fbfee9e6387fbfee00000000cb06602dc00cb06602dc7030dc80ff87f03fe80ff87f03fe0238c0800000013e0800000013e00030c0800000003e0800000003e0fc0fc0888a00fe2c070fffc6fff8fc0fc0808000fc20060fff80fff0
  | 1, 3 => 0x3f03f8b0001900034034f00152003f03f9f0007f000f617ff803df15c074030edfc4ce78000200060800c03000000780400000000004000ffffff70fffc4fff8fbfe6dde29bffffff61fff80fff1fffc7ffc21fa00f800002000e08070d90c4ff58800f000000000c0006000000fc00b679edc81cb0f17e0cb1c29f53e33030cc801c00f03e0801c00f03e04bbed2002040035a080604508200433cd00060000bfe080600708200a3efa8ffd90ffff5f7f1392afde483cf20ff0007ffc0e7f03800fde00000003f00008c80004000003d000000001e00000000000000003c00
  | 1, 4 => 0xfe7fedf8fffcffff8c89e20ff3e0fc3fcce0fff8ffff0809c00fc3e0b409c0401c20413e0000000002803000c0001c00003e0000000002004986120060470ac000060470ac00430c100060070bc000060070bc00fc5fc5f0fffc5fff88086201e2a0fc0fc060fff80fff00080000c2005dd75783efff746ff83efff746ff7cf3df81fffff43ff81fffff43ff4bbed283604f1ffe38060d70bfe0433cd08060070bfe08060070bfe0000000040302228c434c90e6ca5c00000000000000000000000000004bbed280604508200002040035a0433cd0806007082000060000bfe0
  | 1, 5 => 0xfc0fc080c2070eac070fffe4fff8fc0fc08080070c20060fff80fff0499ed28060450bfe08020410a6a0400cc00060000bfe00000000820000000000009000420830009140030000000000000000000000000000499ed28020410a6a08060450bfe0400cc0000000082000060000bfe0a269a87f10008d9004c100083d000000001e00000000000000003c00ebfffaff70478ffe0ff70478ffe0c3fff0ff60070ffe0ff60070ffe003ae800000000bd000000000bd00030c000000000bc000000000bc004996528020d100420832049144230000000000000000000000000000
  | 1, 6 => 0xb409c00002000228070dd2c4dbf83000c000000000200001c00003e0b679edcc1d22f1be4cc1d22f1be43030cc801c00f03e0801c00f03e000000087039b37de7bfc99ffce7f00000000038003de09e0007f000effbfd280e2470ffe0f0ffff4fff8ff3fd080e0070ffe0e0ffff0fff0480ec00000000a2800060440bfe0400cc0000000082000060000bfe0fc0fc070fffc4fff88382091e283fc0fc060fff80fff00080000c200fffffffbfe6dde29b70fffc4fff8fffffffffc7ffc21f61fff80fff1480ec030e94c4fff80002000a280400cc00060000bfe000000008200
  | 1, 7 => 0x5fffd78364ff1ffe38364ff1ffe34fffd381607f0ffe181607f0ffe1fc0fc00483022eac474fffe6fffcfc0fc00080000c20060fff80fff0a3efa87f1102afd447f1102afd4483cf207f00000fc007f00000fc005ff77f8f24fbb4427ff7dfff5d7f0ff33f9f007ff400fff7ffff7dfffc0fc00002000208070fc6c4c218fc0fc00080000c20060fc780c2104bbed2bf60478ffe08460470bfe0433cd09e60070bfe08060070bfe0b679edcc1fb2f3fe4ffdd2ffdbff3030cc801f80f3fe09e1c07f03ee000000000000211e0880800f0240000000000000001e0800000f0000
  | 1, 8 => 0x4bbed28063d70bfe080e0470ffe0433cd08063870bfe08060070bfe0ebbefafcfb47ebffcfcfb47ebffcf33cfcfeff87fbffefeff87fbffeb679edff9fb8f53ffff9fb8f53ffbcf3efff9ff8f43ffff9ff8f43fffc0fc030cb0c4ead870fffc4fff8fc0fc00080000c20060fff80fff05c07400024f804420000000040000c03000000780400000000004000a3efa84810008bd004810008bd00030c000000000bc000000000bc00ffbfd28060470bfe0c07c674bfe0733cd08060070bfe0807c070bfe0fc0fc070fc6c4c21800020002080fc0fc060fc780c2100080000c200
  | 1, 9 => 0x401022084404010220844000000000000000000000000000000000000000203de080400708a4000000000000003de080000700000fdcfc073fffc4fff80382000e680fccfc061fff80fff00180000c200fc0fc030cb0c4ead80082000e280fc0fc00080000c2000080000c2004bbed2886847fbfe08060472bfe0433cd0806007fbfe08060070bfe0b7ffedff14209fd20ff14209fd2083cf207f00000fc007f00000fc0003f03f8f0393b3de7fffdfffdf7f03f03f9f0387f3defff7ffff3dffb7ffedff1c20fffe0ff1c20fffe0b3ffecff1c00fffe0ff1c00fffe0
  | 1, 10 => 0x4000003d003f00008c80000000000000003c001e000000000ffbfd2f0ffff4fff880e2470ffe0ff3fd0e0ffff0fff080e0070ffe0fc0fc00082000e28030cb0c4ead8fc0fc00080000c2000080000c2000220280c0002a00047c5906e195c03303c9e0007f000efe7f87f3dfe01c700030000044000300000440000c3000100000400001000004000a228a87c10008b9007c10008b900830c207e00000bc007e00000bc00fc0fc070fffc4fff870fffc4fff8fc0fc060fff80fff060fff80fff0fc0fc00082000e2800082000e280fc0fc00080000c2000080000c200
  | 1, 11 => 0x83000914003000090004200000000000000000000000000000480ec00060440bfe00000000a280400cc00060000bfe000000008200fe7fedc89e20ff3e0f8fffcffff8fc3fcc809c00fc3e0e0fff8ffff05c0740000000040000024f8044200c0300000000040000000780400000000000039003de00080000c20000000000038003de000000000000fc0fc00483922ffe4ffffffffffffc0fc00083800ffe0feffffffffe000000880800f0240000000211e0000000800000f0000000000001e0b409c000000000280401c20413e03000c000000000200001c00003e0
  | 1, 12 => 0xa00f807010000fd000000000e000800f006000000fc000000000c000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x3080206095030807060050403020500504030201005
  | 6, 0, 0 => 0x403081a0206007000e0b0a141209600030e0a0c0621600200308020600600030e1f0c06006001e0403080200600040e1d1c0600600030e0a0c061b600040e0b0a1a196000308021806006000403081417166150308021406007000e0b0a131200600040e110a10066000f0e0d0a0c00600030b0a0206096
  | 6, 0, 1 => 0x40e0b0a103160004030e0a1a30600030e0a14062f60004030b02062e60004032d0206006000e0b0a1c0609600030b0c06002c600030e2b0a2a006002904280a06216002904281f060060004030b020627600030e0a0c26006000403140600256002403080206006000308140609236002203080206006
  | 6, 0, 2 => 0x30e1f1406096000403080206166000e0b0a380600600030b140600376040e110a101406700040e0a14362160f0e0d0a0c140070004030206003560004030a02063460004031405002360004033302060060004030a02062160004081c06002360004031f020600600150e110a14126040308320206007
  | 6, 0, 3 => 0xf0e0b0a1443600030814060042600200308141700600040308020600600150308020600600040b1c06004160004034002060060004030b143f2760004080206003e60004033d02060060004033c3b06006003a0e0b0a1431600030b1406092c600030b0a070600600040e0a14122160004390b1406276
  | 6, 0, 4 => 0x403080231060070004034408060060004030206002560004031406212c6
  | 7, 0, 0 => 0x30e0d0a140609700040e0b0a1c060070004030b0a0217007004b040e0b0a1c06700044a0b0a140616700150e0b0a1c06007000f0e0b0a140609700030e0d0a14004970003480e0b0a060970004030e0a2a0047704030b0a02310600800040328083c06007000403440b0a06007040e0b0a10140600800150e0b0a140646700040e0a1c0600457
  | 7, 0, 1 => 0x403540b02060070003530b0a14060970004030b020600527000e0b0a1451060970f0e0b0a0c1406008000308140600234c70004500b0a141200700040308021406007004f04030e0a14007000f04081406002370029040e110a1a06700040e0d0a1412007000403480806002370004034e0a0206007000e0b0a1406004d7000e0b0a1412004c7
  | 7, 0, 2 => 0x40e0a1406213e70004030e3c06003570058030b1406002c7030e110a0c140600800040e1f1406003e700044a081406002370004081451060023700570e0b0a14120070004030b0a1417167000403080a020600715030b0a021406008030e0d0a0c14060080029040e0a140621704030b2a1406002c80029040e1f14060070003560b551406007
  | 7, 0, 3 => 0xf0e0d0a14004c70004035b1406002370004030b3c06002c7002203280a06005a700030e0b0a0c060970004500b0a1c060070004031406002c5a70029040e0a1426007000403590a140621700040e0d0a1c060070003280b0a0c06007000403591f1406007000e0b0a1c06004c700030b0a0218060070004030a143b0600700040e0b0a1a06467
  | 7, 0, 4 => 0x4030e1f1406007000403081417002370004030b1406272c70060030e0b0a140670004030b145f00237004b04030e1f140670015030e0a140621700045e0b0a1c060070015030e1f14060070004530b0a1c0600700040e0a1426003e700045d0e0b0a060070004030e0b0a1a5c7040308143106002380029040b1406002c700040e110a1c06007
  | 7, 0, 5 => 0x4031f14060065700030b0a1406092370022030b0a02060070004030e080206007000403641406002c704030b0a1a020600800030e080a14060970020030b0a0206007001e04030b0a0200700040e630a14120070003540e0b140609700040b1406002c3e70004030e0a14062170004030b6202060070004030a02060061700570e0b0a1c06007
  | 7, 0, 6 => 0x30e0b0a1431497001e030e0b0a1409700040e080a1c0600704030b0a3202060080004540e0b1c0600700040e0b68141200700030e670a0c06007000403480e0a062170004030b1406002c7000403480e1f06007004b04030b14062c70015030b1406002c70024030b0a02060070004030e0b0a66317004b04030e0a142670015030e0a1426007
  | 7, 0, 7 => 0x4030d1406002c70403081a14060023800040e0b681c0600700220e0b0a1412007001e0403081400237000403480b06002c7000f150e0b0a1431700040e0a1406006a700040e690a1412007000e0b0a1c1806007000403530a1406217000403531f140600700040b0a1c060023700040e0a1451062170004030e0a140500700040e1f145106007
  | 7, 0, 8 => 0x403540e14062170003640e0a0c060070004032d140600237000e0b0a140609707001e040e0b0a1c00700040b145106002c700040e6f0a140600700290e0b0a0c060070004030e6e1406007006d040e0a1426007000403146c06002c7006b04030b140600700040e0a145126007002203081406002370003280b0a140609700030e0a0c06005a7
  | 7, 0, 9 => 0x4030e1f140621700040e0b0a100600700040314060023357000403080206002370004030a0206005a7000403331406002370004030a1406212370004031f140600237000403080b0206007000403740e140600700040e0a14062173704030b143106002c80004033d1406002c700030e0b0a140643700040e0b0a140672700710e0b0a0c06007
  | 7, 0, 10 => 0x3640e0a14060970004780e0a14062170004030e0a1406777000403280a14062170004030b0a0206007000403281f140600700030e0a1406095a70015030b0a02060070076030e0a14062170004030e0a14262170076030e1f140600700000403080206006000403640a02060070004030a14060075700040b0a0206003e7000403081406002c7
  | 7, 0, 11 => 0x4030b0206002c700040308147a0600700040308140600237003a0e0b0a140600700030e0b0a14060970004030d0a020600700030b0a14060042700790403081406007
  | 8, 0, 0 => 0x4b030e0b0a14180680022290e0b0a1406008000403800b0a1406008000f040e0b0a14007f8007e040e0b0a14060080004030b0a1406002380076030e0a1406005a829040e0b0a1a14060090004030e0a1426005a800047d0e0b0a1406008004b04030b0a14062380004030e080a14060080015030b0a1406002380022030e0a1406005a80004037c0b0a14060080004037b0b0a1406008
  | 8, 0, 1 => 0x2904280b0a14060080004030e0b68140600800030e0b0a1406840080004030e830a140600800220e0b0a1406003e8000403280b3c0a06008001e0403640e0a1400800040e690a1406003e8000403280a1406005a800030e0b0a0c06004c80000040e0b0a1c060070004030e0a14820600800030e0b0a141806008008104030e0a1406008001e040e0b0a14003e80004030b0a147a06008
  | 8, 0, 2 => 0x1e15030e0b0a140080004280b0a1406003e8000f040e080a1406008000403540e0d14060080004030e0b0a1406218000403480e080a060080004030e0b1f14060080003540e0b1406004c8002203640e0a14060080004038a0b0a1406008008904880b0a14060080087030e0b0a14004c8000f04540e0b140600800040348540e0b06008000448860e0b0a060080004850e0b0a1406008
  | 8, 0, 3 => 0x48f0e0b0a14060080003480e0b0a18060080015030e0b0a143106800040364280a140600800030b0a140600234c80020030e0b0a1406008008e030e0b0a14060080004030b0a021406008001e04030e0b0a140080004030e0a148d060080004038c0e0a1406008004b1e04030e0b0a14800030e080a1406004c8000403480b0a06002380004030e0a14260600800040e0b0a1406008b8
  | 8, 0, 4 => 0x4030e0a1406940080076030e0b0a140600800040353080a14060080004030e930a140600800040e080a14510600800030e0d0a1418060080022030e0b0a1406008000403920b0a1406008004b22030e0b0a1406800040354530b14060080004030e081491060080004030d0a1406002380004030e690a14060080004540e0b1451060080090040e0b0a1406008000f0e0b0a141806008
  | 8, 0, 5 => 0x4030e0b0a140609800040e9c0b0a14060080004030e0b9b14060080004030e9a0a1406008000403990b0a14980080003970e0b0a14060080004030b0a9614060080003530b0a141806008000403280b0a1406008000e0b0a14511806008004b0403280b0a1406800030e110a141806008001503280b0a1406008000403950e0a140600800044a0b0a14060023800040b0a14510600238
  | 8, 0, 6 => 0x40e0b0a140600a180004030e0b0a145f00804030b0a14310600239002203480e0b0a06008004b04030ea00a14068001e04030e0d0a14008001e030e0b0a14004c804030e080a14310600900030e0b0a149f0600800030e0b0a149e06008000004030e0a1406217001e0f040e0b0a140080004030e5b0a1406008000004030e1f1406007001e0403480e0b0a008009d1e030e0b0a14008
  | 8, 0, 7 => 0x4037c540b14060080022030e110a1406008000403aa0a14a9060080004030e0a140600a880004034e0a14060023800040348280b0a06008001e0403530b0a1400800a7030e0ba614060080022030e0d0a1406008000403540ea51406008001e04030e110a140080004030b0a14170023800a4030e0b0a1406008000403a30b0a14060080004030ea20a140600800220f0e0b0a1406008
  | 8, 0, 8 => 0xb1040e0b0a140600800030e0bb00a140600800030e0b0a1406094c8000403540b14060023800af040e0b0a14060080004030eae0a14060080004030b14060023528002203530b0a1406008000004030b1406002c70004030e0b0a1a06ad80029040eac0a1406008000403280d0a14060080004030e0b0a020600800220e0b0a1451060080004030b0a1406ab008000403540e081406008
  | 8, 0, 9 => 0x1e0403540e0b140080004030e0bb91406b880403280b0a14310600900040e0b0ab71406008000403590a1406005a8000403280b1406002c80004030e0bb614060080004030e0b0a140616800040e0a1406005a3e800040e0b0a1c14060080004030e0b0a1406b580004280b0a14510600800b4040eb30a1406008000403080a14060023800b2030e0b0a1406008000403280a146c06008
  | 8, 0, 10 => 0x22030e080a14060080004030e0a1406005a80004640e0a1406003e804030e080a1a1406009004b04030e0a14065a80015030e0a1406005a80004be0e0b0a1406008000403560b0a1406008002203540e0b1406008000403bd0b0a14060080004030b62140600238001e04030e080a1400800030e0db00a140600800030e0b0abc1406008001e04bb0e0b0a140080004030eba0a1406008
  | 8, 0, 11 => 0x4030e110a1a1406800150e0b0a1406003e800040328080a1406008000403c50e0a14060080004c40e0b0a140600800040354280b14060080022030b0a1406002380022030e0b0ac306008004b29040e0b0a140680004030e081406002380004030b0a14c2060080004030ec10a1406008001e030e0b0a141800804030b0a1a14060023900c0030e0b0a14060080004030ebf0a06005a8
  | 8, 0, 12 => 0x403c80b1406002380015030e0b0a140600800c40e0b0a1406004c8000403330e0a14060080004030e1f0a14060080004030ec70a14060080004030e0b0a6606008000403c60e0a14060080003560b0a1406004c8000403480e0a06005a8000403590b0a1406008000403640e0a14060080004030e2d0a1406008001503640e0a14060080022030e0b0a2a0600800040e0b0a1406003e8
  | 8, 0, 13 => 0x403280b0a1a140600900030e0b551406004c800040348640e0a060080004030ecb0a140600800040e0d0a1406003e80004030b0a020600238000e0b0a1406004c3e8000403ca0b0a14060080004030e0a140600358000403530a1406005a800030e0b0a14c90600800030e0b0a14060900800040e0a145106005a80004480e0b0a06003e80004030e0b0a14060080004030e0b0a1c06008
  | 8, 0, 14 => 0x4030b0a02060070015030e0d0a14060080004030e0b0a1431cf800040e0b0a14060046800040364530a1406008000403480e0b0a060080004640e0a1451060080004030e110a1406ce8000f150e0b0a1406008001503480e0b0a0600800cd030e0b0a14060080004530b0a1406003e80004030b0a1406002c80003cc0e0b0a140600800040e110a1406003e8000403c6480e0a06008
  | 8, 0, 15 => 0x4030a140600235a8000403080a14c2060080004030e0b3c0600528000403530b0a1406008000403080b1406002380004030e083c1406008000403540e1406005a80015d50e0b0a1406008001503530b0a140600800030e0b0a14d406008000403280b0ad3060080004030e0a146c060080015030e110a14060080004030e0d0a1406008000403d20b0a140600800d1d00e0b0a1406008
  | 8, 1, 0 => 0x4030e0b0a661406009000403540e0b14060080004030ea50a14060080000040308140600237000403530d0a1406008000403640a1406002380004030e4e0a1406008000e0b0a145106004c80004030e1f1406005a800040348530b0a06008007904030b0a14060080000030e0b0a140609700040354640e14060080004030e0b1406002c8000403480e0d0a0600800040348d20b0a06008
  | 9, 0, 0 => 0x4030e0b0a1a14060092904030e0b0a1406009001e04030e0b0a140080403480e0b0a140600904030e0b0a1406d90090403d00e0b0a140600904030e0b0a140600cf904030e0b0a1406004c904030e0b0ad8140600900030e0b0a14180600804030e0b0a140600d7904030e0bb90a140600904030ebf0b0a14060090004030b0a140600238d604030e0b0a14060090004030e080a1406008
  | 9, 0, 1 => 0x403540e0b0a140600904030e0b0a14060052904030e0b0a1406005a904030e0b0a140600ce904030e0b0a14180600904030e0bde0a14060090403990e0b0a14060098904030e0b0a1406009dd04030e0b0a1406009d104030e0b0a140600904030e0b0a14dc06009000403280b0a140600804030e0b0a140600db904030e0b0a1491060090022030e0b0a140600804da030e0b0a1406009
  | 9, 0, 2 => 0x403c80e0b0a14060090004030e0b0a140600804030e0d0b0a14060090015030e0b0a140600804030e0b0a14d306009000403640e0a140600804030e0b0a14060023900040e0b0a1406003e804030ee00b0a140600904030e0b0a14a9060090004030e0a1406005a80403640e0b0a140600904030e0b0a140600df94b04030e0b0a140600904030e530b0a14060090f04030e0b0a1406009
  | 9, 0, 3 => 0x403540e0b140600804030e0b0a14310600904030e0b3c0a140600904030e080b0a14060090403aa0e0b0a1406009000403530b0a14060080004030e0d0a1406008000403480e0b0a060080403280e0b0a1406009
  | 10, 0, 0 => 0x4030e0b0a1406008
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 76
  | 9 => 76
  | 10 => 68
  | _ => 0

def idWidth : Nat := 8

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 224 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xfffffffffff00000000000000000fffffffffff, 44)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)

theorem ori_ok {u ys} (h : NatRun (mask 112) (goal 112) u ys) :
    NatRun (mask 112) (goal 112) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 10 0 (NN s)

def poolG : List Nat := [60813999033403504, 48419203370351730, 55184546793111752, 15773610129128604, 55174608189505650, 75489179635666032, 15768107204374728, 15773651913785500, 25913295551800432, 60814004449299568, 15772510619641032, 30414700498068636, 18029907846220912, 98007177776712818, 5635002581765234, 41673700593050736, 25901205269150876, 79954296353006704, 55184546793202888, 22634551873577072, 40579681157762160, 40586366295328880, 5635049872587890, 15768107204420808]

def Z (s : Nat) := bar 112 S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega

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
private theorem z6_64 : ∀ i, 64 ≤ i → i < 68 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 68 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_8) (range_split z6_16 z6_24)) (range_split (range_split z6_32 z6_40) (range_split z6_48 (range_split z6_56 z6_64))))

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
private theorem z7 : ∀ i, 0 ≤ i → i < 184 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 (range_split z7_24 z7_32))) (range_split (range_split z7_40 (range_split z7_48 z7_56)) (range_split z7_64 (range_split z7_72 z7_80)))) (range_split (range_split (range_split z7_88 (range_split z7_96 z7_104)) (range_split z7_112 (range_split z7_120 z7_128))) (range_split (range_split z7_136 (range_split z7_144 z7_152)) (range_split z7_160 (range_split z7_168 z7_176)))))

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
private theorem z8 : ∀ i, 0 ≤ i → i < 272 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 z8_24)) (range_split (range_split z8_32 z8_40) (range_split z8_48 z8_56))) (range_split (range_split (range_split z8_64 z8_72) (range_split z8_80 z8_88)) (range_split (range_split z8_96 z8_104) (range_split z8_112 (range_split z8_120 z8_128))))) (range_split (range_split (range_split (range_split z8_136 z8_144) (range_split z8_152 z8_160)) (range_split (range_split z8_168 z8_176) (range_split z8_184 z8_192))) (range_split (range_split (range_split z8_200 z8_208) (range_split z8_216 z8_224)) (range_split (range_split z8_232 z8_240) (range_split z8_248 (range_split z8_256 z8_264))))))

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
private theorem z9_56 : ∀ i, 56 ≤ i → i < 57 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 56 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 57 → Z 9 i = true := (range_split (range_split (range_split z9_0 z9_8) (range_split z9_16 z9_24)) (range_split (range_split z9_32 z9_40) (range_split z9_48 z9_56)))

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
  scr 112 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 112) (goal 112) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

end PEqualNP.Outside.L_meta_8477_aux

theorem PEqualNP.Outside.L_meta_8477 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) t → 11 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_8477_aux.mainG PEqualNP.Outside.L_meta_8477_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩
