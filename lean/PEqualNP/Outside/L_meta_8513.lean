import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8513_aux

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

abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)

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

def rowsG : List ℕ := [1, 1, 1, 2, 4, 4, 8, 8, 64, 28, 28, 28, 28, 28, 70, 70, 70, 70, 70, 81, 81, 84, 84, 84, 84, 84, 142, 142, 142, 142, 6, 6, 6, 10, 10, 10, 12, 12, 12, 17, 17, 20, 20, 20, 20, 24, 24, 24, 24, 24, 40, 40, 40, 40, 16, 16, 16, 2, 32, 32, 128, 128, 64, 161, 161, 161, 161, 161, 98, 98, 98, 98, 98, 81, 81, 97, 97, 97, 97, 97, 170, 170, 170, 170, 34, 34, 34, 130, 130, 130, 160, 160, 160, 17, 17, 33, 33, 33, 33, 129, 129, 129, 129, 129, 132, 132, 132, 132, 81, 17, 136, 138, 3, 5, 9, 3, 5, 36, 9, 72, 72, 29, 30, 60, 92, 156, 71, 78, 86, 102, 198, 85, 89, 85, 86, 92, 116, 212, 143, 158, 174, 206, 7, 22, 38, 11, 26, 74, 13, 44, 76, 21, 25, 21, 22, 52, 148, 25, 26, 56, 88, 152, 41, 44, 56, 104, 18, 48, 144, 18, 48, 36, 144, 192, 192, 177, 163, 165, 225, 169, 114, 226, 99, 102, 106, 113, 209, 113, 99, 225, 101, 105, 186, 171, 174, 234, 50, 35, 38, 146, 131, 194, 176, 164, 224, 49, 145, 49, 35, 37, 41, 145, 131, 133, 193, 137, 148, 164, 133, 196, 83, 19, 200, 202]

def xsG : List ℕ := [0x34ffe122fe4f800423924438425f30ffe000fe0f8000018000180007, 0xb01103ff11f10240440ffc47c409800003ff01f00200000ffc07c008, 0xf220844408208081ef1ffeffe320f000000000000001e71ffe7fe30, 0xc084000f8108003fe17e3c90bfc4c000000f0000003fe07e3c003ec0, 0x3108e4910e1097d3ff848bf93e0030006000060001c3ff8003f83e00, 0x207bc7ffbff8cbc88211102082000079c7ff9ff8c3c000000000000, 0xd8401208fff46021004823ffd18010000000fff04000000003ffc100, 0xcff85f8f242ff10210003e042000cff81f8f000fb00000003c000000]

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
  | 6 => 1
  | 7 => 142
  | 8 => 1111
  | 9 => 894
  | 10 => 43
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0xb38ef329
  | 7, 0 => 0x44a4b08f4348c1d142df32bf420fbf8c4063ed093ec1725b3e125bfd3cdaf2a338eca98c38d4670b36991541345c20543395aa51306b6fb03037ebfc300abfdc2f06a6912eeb74b12c9b97fb2c8929cb2c5bcabd2bda17332b4dd1972ae4d20628a0899d27f170d625d2d33724190fba23da54cf2261db30224157581ff9edcf1fcce5fb1e857c101d3bebce1c6c27d619781512195aa173189cde69181b875117ec47f5159951dd13e8a96213a5e3f41204a88c11fab2b60fb734580fad98850f06a9400e17a3f10ccfb8950b5f2354097b3d0406c1a02f0662c3ad0629a92505f32e3f05ed775b04a53ef2048566df03a5cbd002836996017d92fd006c048a
  | 7, 1 => 0xc1bc357bc0552f5cbe1eff60b8d50652b6022b97b40c5ddcb21bef78b086a58fabb1c11ca73bab0ca43c62509d02dc7a9ae7c7c99ab7993f98af1b9c8edefed18ed629838e11186585fe43fd84d2a82882cabf13819808577fc1679d7dec527c7d55b0347ad00981796ef4f1795fba06795d99c8794762bc78ec64f475fb6d3275e3498b75b4e69075139b9574d7bdf5748ce4867459161573cd058b73a53e8e6e9c830b6d14198e6b8a941a6af2443269b31927682a800365b6f6c564be79ea618c000b617a6095612695b75e87273c5db08fa05a47868d5920794f563fcafc53472ea44f8df1b54e0067d84dd0ea844897b7c64741a9f9469e3e22468c056f
  | 7, 2 => 0xf3463c50edc59ac0e5282a4de41c6888e3a442f4e245040ddf71bb7add552983dad98afbd1a15041cfc12c29cee0ff0ccba91302c5d59879
  | 8, 0 => 0x85aa15908135e9307f4d92d07ceb4da07cb187f07c8418807b8b3e207b67d2707b3c56a079b1bb90790c6ee076678fd074e2740074993f1072442c506f8dc5206f071fe0660226a063edb6a060fc88605e19ed705ba32b805a98df605a0dccd057222b6051aef0504f0dfb804eddda504b71a5004942d2a045d812d045a7f05041cdfde041cdbc4041a9ec50408e3bc03d482ec03cfbe740379092503363e340332eb5a032f962402efc41402d0fee4029ec05702649f91025b54ca021ded1002110bf4020240d501d5f75501b5379d012022be010954cf00e6ff9c00d73b6300cb5d5e00ca4a1000c692dc00b3b5e90078044600645b780038ec34002c60ae
  | 8, 1 => 0x103b3f5f0fefa35a0fd7423d0fd236950f9a2e500f881a940f2ff7820f2a18d50ea010d60e84ad450e59d4f60e3082c10e2926fa0dea31910d7c89e30d32433e0d2cadc70cd71b7e0ccf70ad0cc0426a0cbbb8a90cbb78a50c89ce460c7e60120c4ddcd90c41669f0c2d6e970bf4494f0bf35d370be8dafb0bdb2a450bc72ac30ba6760b0b9b876f0b98ba490b95e9ce0b9505cd0b87da930b6ebd530b550fa80b422bbd0b36abc20b19edf70ad05fc80abba5a30a7ca8a30a6bdf2e0a3f37fa0a2fa6730a0c13aa0a04989009bb1d2a097ca1ff096d2ea30954ff30092e820409278ecd08ff014108eed4eb08e8973008e3a18b08934ea00873f1ec086f3313
  | 8, 2 => 0x1817324e181188e218054b1d17ff37691784478117753cc3176fb2c0176d490f176d3b401767f474175f7c15175cea7f174ea3b0172ad80316cc61d516c36bce16bfe43116bb649d16b7688916654b4b164a722a1648ff5f1626256116113a4215fc718215f71e03155c4cd9153de3e414e522f9148ece7f14644ff2143305d41420f09a13d3fb3d13bb921f137687d41362105d1361d9401354679113521408132c36941328067d1308901e12f2a02a12dbbd0e12d3e4eb12bb9aa91292c5d81256374d1254314e124c9e8e11d791bb11c9e8ff11c14cf011a6f3f41194ffa91171029f1162758a1160809e1121567710f1795c10cf72f110a0c51d104e3637
  | 8, 3 => 0x2014ec2e200d597f1fd477121fbd0b6e1fba0cbf1fa259be1f99c79e1f7444f21ea5828e1ea487221e7e55a81e03df641dde17f31dd005221db0b26b1d8fa9901d62672f1d5b9deb1d551ab81d3ceadf1d16a0e01d1034471d0b2b271ccb8a001c9b2deb1c6a71701c51a7751c44edf81c1cbcad1c1196cf1bf886181bf6a6f41bbdc19b1ba9b1fa1b74d4531b73e8261b73e6341b4489201b4277461b2f70031b1476451af4cb841ae563961ad9326e1abf81ca1a77934c1a7221f01a4fc8651a3ef6b01a1f6e4419bb0f0f198f99aa195ed78f195c96891927cf5e1904d7cc18ef930a18c20eee18bc2d3718bb3997185fca3a184970bb18216443181d9c57
  | 8, 4 => 0x29f2967129bee18829b14c1729ab872d29726f2e2946603e293a12452931fc3328dcd363288be9cb287f48d0284e999c27d873de27b8327f2754ed09274e0427272f2888271b308026e20b382644a8b726391e302609450725eb25e8259da3b325768d60256175ba251996d924fc678f24db8a9b249a6b882459f34a2432457b24295c462415f87123e724f123dc96d423a439eb238dd38a238a500023775aa8236fb006236bd2b02350e30c234c43902341753f2318505f22f5c34322a8810222a24f20229681572289c5d82288dda221ca802d21b94b7a21a1d400218c7f4e218bde97217c471e20f3cb2b20b2a43f209b503f20907390208490ad2025ba82
  | 8, 5 => 0x33e1bfb533ab98993396dd0833816469337b7be13370fb9133578acd3356889c33504271334d8c2332e5b0ef32a2f5ef328c365d32505da1323c65993221c62e31b8ecaf319768593162334231530d34314885c630f011e030a07920309f29b8309dabc43061bfff304731ae3017a7f92ff1e28c2fb29f102fb1a6792f796dd32f31c89b2f0fd9cb2e7217202e6559912e3f6fe42dfbe1162d9c87cc2d41f3372d3860262d20229e2d0ff4332cbc77b22c5de2d02c56d0562c16d33f2bc2b8322bbd34da2baedadb2b9f1d612b7afeb72b6877542b4c70b62b00f8712afcb2462af1f5cd2add65432ad807c92ac60a442a9d0e3f2a71f79b2a57635d2a2ff65d
  | 8, 6 => 0x3fcee46d3fb6cf5a3f9c17543f82e5e03f573abc3f38989f3ec891953e7febe33e77427d3e6a0fa03e54c40a3e2673733e15a17c3dcb84493d60ec123d3d89073d216bb53d1c39813d0c004d3d089e213cff46603cefdc493cba06543c9e8be33c8ddb8a3c70f53c3bfc52a83bcc12753b8877743b43d65c3ab267583a8789873a8393f53a6abe263a370fea3a17f42539e282e639c57a9739c0c962399ebedf397fb2563977980f394ad96439137e183911543b39090ccf38b2f95d3874aa1837f2cb9837ede14d37bec4b6378687b336f600ac36912401368ba5133688d4983661a81d365b61083595793a3573c3b1354e7ed535362ada3518fe2c3466569a
  | 8, 7 => 0x4798367147844079476748254744923f4736f79e4732b17e47312fca4704952846ff3ef846d9ccd746b57d2b46b2c60646af726a469c9cc4469391374657e0834654700245f67f6345b4b0c145980dc8457dfd734553b89b44ce70f944b764b844b27b4c444417874421f9df44116c6643fb234743c4570b43abd726438567c54371aa68436be7f3436afd0143556b524346556442df32bf42ae337a42a81ed042a26c2a4273d2e8426528c64263d91f4237545841ebc9b541da0cc841c47f9341bba1b8417e13d14173244e416665db412d97aa40b1eb7e40a5c28840a4529940a1fc3b408b22b2407f57e1406851a4404f37a3403e0ec540148b163fe83dfc
  | 8, 8 => 0x4fb6e4084fa1ba5e4f86f7a14f69e29e4f5b82794f5154984f4ae7624ee379a64ecf819e4e9fddea4e7c6b5e4e5ebd7a4e350e084e26f7154e1df5b64e148df34e03aaa74dfe36eb4ddd86c34dd628204db6bbc54da892404d954ec74d7116304d6614f34d5a09cc4d3e3bca4d39a87b4cf95c804cb0543f4c93809d4c804c054c4ef3fd4c4b68474c3bb1f34bf8fe714bc1d57f4ba3e4574ba1786d4b8e3b094b0b038f4acce5434a6e1fc04a672fbc4a4a938f4a3d2ec04a1ccba849d7291549b5dddc49a83624499a98c14982319b4953052648d647ef48b2df6f48970c98487bc2c3486bc0b8482a1fdf4809ab4247e15ef447c918fa47c0a22f4798470e
  | 8, 9 => 0x59db80aa59cc9066596dadcc593986f759075e5258e2ab2158b946325893fdc2582bae71582b4af058278ebb57f2892957de9012579a00f9575d1fdd5732a928570e7bb956ca5b0056a8d261567e1bc05668df8f565acbf35652b562562b53e955d647cf5572c06655494d0755229106551a468154f64455547952005475f5f7546ff3225409af4e53f1c51153e6c01253e1b27853c4af4d53bc32f253b4310d53b1000753821673531a009b52fe1cd952c79d6652b9912e52afef4152abcd3352a6899c529ee6ad5291b6615281efc1522b319551d0062d518cad7850db903750d4864e5071b550506f72e7504cb55e504880ef5032b7544fdf39bc4fd3071a
  | 8, 10 => 0x657978156505c28964ee0041648792196430717963d5ce8b63d2fe106386c39e630410b162f9bc5162ec13a062d9fdbe6298a84d6273090c623bdaa5619bb376618c000b6175601a6164e8dd6157e15e61356fa2612be92d60f87afe6097b59b6096612d60147b6e5ef7eb6a5ef0ccb05ed4401d5eb218f45e6e971b5e432d3b5e3ff6315e3d25b65e179f5b5e00f1c15df458795ded95ac5dd6304e5dc7beb55d95e0b95d696e9a5d4364ab5d3ed15c5cf2c0925cd7e0e75c2f519b5c0708075ba6a14e5b9214825b448b2b5b2df86e5b05dcf95b01dd415ab0eb465aa9e89c5aa491435a8c6b395a85820b5a6b6bfb5a6ab34d5a5a80d65a2e3db059f0b6b7
  | 8, 11 => 0x749287617470522f74622baa7462264f743723d673e040df7351f2c373428c2772f6f0fd72ac3d2b72a6e7f1724217d5722e8f8d721ed8ab721b80da71e891e1716a11be71475acc70a1f9f8708684fd705784746fe4ba4f6fbd6f7c6f7286906efdb5156ed9803e6e9ec1f06e0e44bc6df142ec6da671116d6e30b46d2b1e186cfdd22b6cfadd436ca164346c3fd8076bbeb1276b2d67e86afa40146adfa31b6a07d15069a68855698d25ff69869c996978d0b1696a2d47695b94846956c35b68b264366853d6dc68346187680388c167dda4fe67dcba6167c5fcfd6748e27c66f6098266d8897066307cca66283cfb6609152865efe012659a76326581e636
  | 8, 12 => 0x818f2c778187ddff8121feea811e3eb38107c49280fe795b80f7c97e803ea621800fdcdf7fdf9c0e7fd18f327faccf527f89b76c7f51937f7f3cd6547ec4fa9b7ec080837e7476217e5355fc7de480a07de2e0227d9eb7fd7d6592b57d46716f7d2084707c6ec21e7c1d3aa67c0b24637ba5b2907b858dc47b7fa9fe7b1747b27afb1ed37aa9ced27a8fa8f37a244a327a187c1779e4601179b9b8f5798d66607952bb8d793da0ad79232243790543c478f14efa787c4ae7787afd0a7838227a78312694782c9345771a555377053d7a76946337763620f5762d65dc76130e9875fdee5975e1b08575cc0c02758e694e753d7e59751fc49f75150e61750111cf
  | 8, 13 => 0x92059f7b91b545b691aaf0a591a9bf83911b27c5910a35f990eb4acb900827fa9006dbf48fafe1388f8553f18e72aecb8e4f32d08de809038dcef7698dad58408d195dcb8cff96338cf70e8f8c5a85248c57d3a78c2b476e8c261e608bb98d3f8b45465d8b0ce9748abda9898a375a1989f7f7b889ef06cf897243d888e60e678898335a8844fa8387da5f2987d2c91387d15a2d87b4dcc5878359c48750759a86666a128646b6038620e338861802e785f77e5985c3481785757468854a31d7849071a18467548b844fbfaa844973ee83f8efea83e56cdf83cd332583882b35837f267a835f567d834665a082985c10827ef4a88258e26181e8435581b59850
  | 8, 14 => 0xa33d5481a2af4a73a2a7b072a1e50c77a1e02cd6a1d7064fa1ac0db3a0afdc78a0635a6fa0359f459fe577b29fc42cae9f58261f9f5516749ef442e49e9184449e48b4559df1c5039db3ec739db23f779d727e9f9cf9223d9cbcd3529c4815279c1465449be8eb689bdbc0fd9bd8794c9b4a6f3e9aeacb609aa6890a9a454c8c99eef06b99d1c70299bfd414995f165d9949806098f8d28998c836f49801d71297af7194977720c9972de057966bff5c96697c419663c55e9661c9da9653130e95fc962d95e6b3c99554d459953ba2ec94e1ceed948296379474fe5d946443c7941d9b0793e937ed929b69d39267e4919264f918925262ea923c7ec0921088af
  | 8, 15 => 0xbc6c95b3bc6a3721bc5ef3debc001207bb29c281bb0836e9badc6309bab0cb07ba87ebcab95d207cb94e6171b8cf78e3b8891d97b779dce0b72fe622b6e0435ab6383127b5ff0bdfb5473052b4f63f9bb4192832b40c24c5b3fba2f8b3988df8b38b1e24b36b0cb0b2f9977bb20403c4b1dec306b18ac8b3b1077c1db0a87fc0b06ede16af76b123af17c000ae69166bae4bf9acadeb9d75add53456ac92e6e9ac59c1a1ab69edd4aaf5d713aae8e175aad9d026aa74d25baa4cbeb4a95b87a2a8d5caeca8d28fd1a790c143a781404da6b89e63a6ab16bda687ca25a678788ea66daf8ba66d4b1ea66c2292a61bdbf9a5a02ea8a4342981a42b7e83a36f35b1
  | 8, 16 => 0xe5b27397e593e562e265d062e1e53914e0905ea4dfeab43bdf96c9dedf17386eddec8245dd145a65dcdd93b0dcd9d58ddc5857efdc1ec708dab1fb5bda699bedda02f707d9a26b36d90ba527d8ffb5add8184d40d7b40d3fd752e6f0d7523b83d6e107c2d5703bcad56aa5bcd3cf3686d39d6ccad23d7b7ed23821dad17ab4efd126f20dd0fcfdfed08c1939cf0c29a0cef2ec9dced30458cb324c17cb2386cfca88533bc9fdb7c2c9aaddc6c9a6d7a8c8e96d1dc89498b6c86598adc6cea45fc6bb34edc5bc55f0c4c4b1ccc41426c0c4020d80c34f5487c1df41cec1596640c154b4a4c051b67cc0145ebcbfdb732dbefd3eadbeb4cda0bd26e766bd1aa6aa
  | 8, 17 => 0xfec6d3bffe905794fc2845b1fbef2069fb904dedf84efda3f7177dbef525ba7ef18c9316f0902889edfa4c51ec7902eaeb385a3aeac75f65e8d06ec7e8c3bc48e8b9e73be8b4ddfae8936873e7ace730e69f0e0ee623cd8ae5b91095
  | 9, 0 => 0x9ab872c0994c91609274bc008eccb4d08c241480862a9c6082aa52d0828f3d7080ca2c607f811af07b196a8079fe304078a87a4076f11500763f3f407628365074193e9071b0b3506f6f49d06e20eaf06c2a26e0699c6ff0646d61a060d337805eef56205eb855105cc8f8505c9319505c1a9350532c0e00529848005259dde04c84f4e04979acc047ddb22043f4c8704337d95041749e70408e3bc03cef26f03c0a56c037d091f035636d5033c5760032be508031fdf7302fbab8502f29a3502c2df0e029215b10264dadb02406cd40216709401cae92601b60ffd0196ccb7018502f401415474010c2d4700d6739900d3db79009e97c8009c50300037c004
  | 9, 1 => 0x13ee9bd713cd460413cb8b491369f1121368fe6e133b562b13310de9130d155d128780ef1264fa6412052bec11eb32a711d01207117d5a5211429b8c11407350113a390b11139e591111562810dadc4e10b7fc1e10575ae3104356e6103582bb100991dd0fd7423d0fd236950f870e400f59e5510f02f3a30e65c98d0e3209630e13803d0e117be20df882200de604880dd123290d478ed80d35bb5e0d135ee60d04e9aa0cffb0d70cbb78a50ca4eb630c8962100c6844660c4158be0c37ad620c2d6e970c263a550bee8f940bdcae740bc72ac30b7d0b4c0b446a4e0b43b0410b146b700b0c830e0aecebfa0ab736e00a5e27a809dc90ae09d524e109bf4708
  | 9, 2 => 0x1e0b87ac1dcc49ac1dcb4b321d1efd521d1c11201cf491aa1cd7b92b1cbedc901cbaf9e81c92d66a1c8bbe4b1c8618b81c5e8cbe1c4323781bc38be51bc19d621b826a831b33491b1aedb3631ad82d631abf81ca1a7c7c621a6fca911a6fc1891a3f338d1a04060619d4090b19c5b1da19859ecd196163a31917227f18e55d801880eeb5182e1cb8181cd75317a2a10c17a06511178a499617844781177ab927176d3b40174a536a174938ca172b3879172982cb1720811916ef3c7016d31f0b16d2026f169f17f2169b433816883cfd16674485163b2345161eef9715ed333d154255091537e9c11528a9b51513d28814c2e9d314bf1d87144930aa13f64aa0
  | 9, 3 => 0x2b41183f2add65432acca7872a74d0292a5e2fdb2a37190b2a2915752a13bf302989610529726f2e29538b762940b1df293b079f290f0af12901422628f8ab0428ddba2e2882dc54275867ac2740b96327304f65272f2888271b3080270ca4a826ef6f1d26e20b3826c3a7732692cd9026322c3726194ac125ec25b2250b360c24737470246ca0142464f9b22416b0b523f2d85723dc96d423a429eb23a223ce233f77842329b4b023123e3e22dafbb622dabe1922ad4ac12288dda22254a6782236d74221f252742130d4be20d491e3208633672024a335201cdb6c1ff2b8d21fe1d0711fc3fd311f0562911ea9ae681ea7b16c1ea1c1121e43279e1e3f5312
  | 9, 4 => 0x34a7a3a734918b8c345c4c2833fb7f2733e3f07733e1bfb533c1fee43352688f334d8c23331bdea1330add5a3309708432f6f38432d1966732c1f6bc32ae6da6324e6da7323c659932261801320960f7315a0c6331530d34311ddff2311d189030ff6a8d3062d77a3053795b303c2718303281b23025abaa2ff5b02a2fe876912f36e6aa2f09cb922ecf5c532e7bd22b2e4e181d2e4601e82e1bbc962e1971762e10b08d2e097c462de40bce2de0064a2da18d182d8800e52d85007b2d80e0a32d41f3372d1762ed2cda0ff92cbdd3f02ca863672c97ff4b2c191db72c1322f72c1206042c1159d92bed47bc2be96c982bc936602bbd34da2b85552b2b6c3ad7
  | 9, 5 => 0x41a8cddd415574624110eaba410b6d2c40a64cdb4072f7e0404f37a3402ba5f33ff4fb593fc8e80f3f8fd3f53f573abc3f1f089d3efe5c183e8462833e54c40a3e0ee5723e0673063e0000273de4e85f3dadfd873d4ebab83ccfe9e73c9cfa833b9106b53b6bcaf83b4d684d3b11f6103ad1d7de3ac748323a8aee753a8789873a35a2ff3a28397739c7ed233977980f38f707ed38f4c46e38f220c638ee8a2938e9a5af38d40b5e3811feef380f2dcc37d0707e3764c68e374a062f370c616036f23a0836b098fc36abb142368ba5133688d498367f047b3661a81d364c6e61364122c235e65a8135bfd7a735b49cd23560fc4c353ab80d352c22f834f1c7ef
  | 9, 6 => 0x4fb6bb7a4f4003644ecf819e4ea726294e5ebd7a4dea11404de67d554dc91ac34da5fa704d32a4b64d2f20c04cc704494cb084c34bf006f24bcf92d34bb1bdbf4b8e3b094b8054144b3915ee4b16d10a4ade05ce4ad36c014a8b05384a67f8ec4a672fbc4a55722b4a16d37c49c114f44986123c495a144c4944340749140710490c1b54490bc6da48fe727648e2aebf48c70d98487c6edc4861b5e6482b7a9b47e126bd47b9c6144785c1344775177e4744923f46b676af469c9cc44662201045c5866545a6104645a5d6da4566252d45629212455a0e3f455206b04513e78b44e9124d443d82334375ee8043501e0042ec2d5942ac9b6342934fdb41f39a3f
  | 9, 7 => 0x5cfa14ed5cd01b295c9c259c5c92aae85c55f1d35c2b37cf5c0f04215bc8baa45bb6e6a05ba7dff35b9214825b1c52b05afd6ccf5ae2cb115ad02fbf5acc1ee25abcaa195aa491435a29592759edc00c59a05660596dadcc59494189592eea4b58f8407858e7d7a0586c168e582b4af057d9fcc857cbcab757bef9a1579d201f577a405f575fb78357403da9573d70d256cbb10456a810a8566fb3bf565d61c555ec75a955572f9154d50f9e54750a5e5472250e5412e1d353d515d753d1b59b53925bc552e16dfc529d4ae55234eb5f5229214751bd1682510601c850b59344508635c8506e578f5043eca5502fffe05026320a5017d7294ffe20d64fc82ef3
  | 9, 8 => 0x6c3060b06c142d026ba7fc106b0054ba6aa35ee26a9136446a8935ee6a7a3c16699d9ff9696a2d476946b0ae69435578692c9522692aad1668e3a14468d7d32968b79b7c6853d6dc67fc35bf67abcfca67a544116780e5c06780b24a673b439766e851d966d459d166ad39896687af416653413166455a766612f6fe65f7bcd865b9931c65b864bc65b4514564ee3b84642f679c6414622963ff64d963b95aa563aed11263895e41630c25aa62e4a63462aef11a6257826261e524d26165dcdf611e140b6083b4ae606608196053e716605399fc601bbfdf5ffc1c2e5ed76f095eb218f45ea4f2055e4595d55e432d3b5d95e0b95d88ef545d41b7bb5d00ecdd
  | 9, 9 => 0x7f80f7bf7e4359777defd7a87dce7d6c7dae4a417d9eb7fd7d258cd07d00e4f27cef87257cab04927b343ad27a7915f77a61dd7f7a16030279e815c2793da0ad789be95278312694782c934577dd22c677d9ca3b777c801177181def76a4a889769463377664e95a76572a67761c07d97619aad375fdee59755a0ec1753d7e5974eb70e574cfeaac746bc531746527817434907d742cba6e7429049a7416c4657409698a7400a02773d5998973114e8b72e9cf1572b419fb72a2fe0772680248720208c1719fd5b871475acc71014c7170dbfd0c70b2c3947044f17a6fcb594f6f3a12526e9ec1f06daf85a36d2063ef6cd389fc6c915c236c409ca66c30fed7
  | 9, 10 => 0x960951f49408b3b293e75d6693b99788939a57249266712991d9592091cbafc191c00145913ec973912fb405911b27c590d7c2cd90bafa87908c2447906c8b3a900716fc9006e8068fbdadb18f2252668f041b9a8e88bc758e4f972d8e4f94028dff10748dd790fe8da1dbe48d8d34be8c57d3a78bd7779f8b4a22c98b45465d8a5ffb0e8a51899389bc1cb889af05aa88b3d699880c083588083834878b8821871e22998701eeeb86747a2a8620e338850f1d278409ae7183deca3d83af21f6831ab5e882f584d6824446c882209bb281e8bfbc81c5dda2819afb728190396e81811b3f81370e6f811e3eb380ad1629809c66d4807ca98b7feedd4a7fde4214
  | 9, 11 => 0xa9b91114a94f4c90a92ce220a9147308a8d5caeca80d002da80a34a3a7dfd05da78a2b20a678788ea6105962a5d1712ea4c78393a49194e4a36f35b1a282bf72a2664eb2a2522954a1dc8d1ea1c4d03ea1bf3810a1b8cf2ea1a1503ea18787d1a0cb75e5a0974371a05739b2a04e8e0ca042056ea00ee20a9f5516749f515baa9f09447b9e58f9a79df3ca189deec93a9dcf34129d8f1af29d63f98a9d4f0a0a9d2906139d10b5f49ccfac099ccdd5089c1b639e9be10b8c9bbee1ff9bb42f2c9ba5e24d9b89eaa79b4f4baa9b4a6f3e9b2a50759a1c536699f20a4598fc4da898d6f85998134eb997f9429897ea572f97da297197af84dc96f6165296bfbc22
  | 9, 12 => 0xc154b4a4c1244f5cc0f99c84c0f1180ac03745aabfc79fd7bf42ac51be5d37cebd9c0bdfbd3bd079bc8ee4cfbb3ba724bab27efbb9f70664b9ea09dfb9947716b97d5151b81e42cdb6d6a384b69b2485b64d8c88b63d0d93b6383127b613cb19b5c88714b5b36192b58fb8f0b58be21cb5562d02b54f2cdeb44f8696b4254427b39f9a2db38b1e24b3883de3b33ae8fcb28e36c9b287e853b25d2d70b2211361b198109ab160b80bb13d89e1b0cc34e6b0bb018db0abe763b00207f1aed273b7aebfca37aeb64009aeb21e34ae0a28b9adeb9d75ada6c9a2ad7c17e0ad6d2670ad3e32feaccafdb4acaf6f30ac740609abfddb2aaba000f3ab69edd4ab460208
  | 9, 13 => 0xfe905794fe0e5757fda609c1fc2845b1f529fb5aefc0a743ef0c88baeec60cfeed8e03e6ec173a26eba0f5beeacf79e4eac75f65e9ffbde9e930c2eae843fc48e6474e3ce55dafb4e465a8d5e3d8bd18e3741717e1ab5782df9a1f3adf0423cbde9284f7de1e52d6ddf15eb1ddec8245dd13fe2bdc8afb64dc2d1d9ada699bedd9e5aaa3d31ca336d2508c63d17ab4efd0d7b93ccfc47343ce8e1e0ace2c5cd3cdefc9cbcdb547d7cd76fa4ecd75aa3ccce33d63ccabb9f8cbeb6685c9e13f0ac9b3d1dfc8e5a27dc810c4d7c7ff8cb1c78f42bdc6eb9d13c4fdcff8c4ccfe44c4c4b1ccc43fb3b8c3d32234c31b28c6c29b191cc203a15a
  | 10, 0 => 0xfc2845b1ed8e03e6ec173a26de9284f7dd13fe2bdc8afb64ccabb9f8b9f70664b63d0d93b6383127b00207f1ac74060998134eb98f2252668dff10748dd790fe8da1dbe4871e22998701eeeb819afb7276a4a88973d59989726802487044f17a68d7d3296053e7164ecf819e48fe72764785c13446b676af3e000027331bdea13025abaa2cbdd3f02a74d029271b308026322c371bc19d62113a390b0e3209630c2d6e970699c6ff0408e3bc
  | 11, 0 => 0x271b3080
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xb09503ff91f90244651ffc57c64d800003ff01f00200000ffc07c008d8c4120afffc6025215a27ffd3c410000000fff04000000003ffc100b01103ff11f10240440ffc47c409800003ff01f00200000ffc07c00834ffe122fe4f800423924438425f30ffe000fe0f80000180001800073108e4910e1097d3ff848bf93e0030006000060001c3ff8003f83e000f220844408208081ef1ffeffe320f000000000000001e71ffe7fe300207bc7ffbff8cbc88211102082000079c7ff9ff8c3c000000000000c9cc568ba52cf127315a2e94b3c40000000000000000000000000000
  | 0, 1 => 0xc4a6000fc10a003fe3fe7cb8ffd6c000000f0000003fe07e3c003ec00202ac554a928c988821110208200000000000000000000000000000fff8ff9f2e3ff7d3ff84bffd3e00fff87f8f060fb1c3ff803ff83e00c18c448f8508913ff17e3e90bfc4c000000f0000003fe07e3c003ec035ffe5a3fe4f910633924e38625f30ffe000fe0f8000018000180007d8401208fff46021004823ffd18010000000fff04000000003ffc100f4ffe12fff4f803fe3fe7cb8ffdff0ffe00ffe0f803fe1fe3c183ec7cff85f8f242ff10210003e042000cff81f8f000fb00000003c000000
  | 0, 2 => 0x330aecd54e929fdbffa59bfb3e2030006000060001c3ff8003f83e000f27bc7ffbff8cbc9ef1ffeffe320f079c7ff9ff8c3c1e71ffe7fe30b43303ff51f30240469ffc6fc61b800003ff01f00200000ffc07c008cfa6084ec18a082d3ffbfffffff60f000000000000001e71ffe7fe30c287bc7ffbff8cbda97b35929be400079c7ff9ff8c3c000000000000cff8ff9f2e3ff59298003f042800cff81f8f000fb00000003c000000c084000f8108003fe17e3c90bfc4c000000f0000003fe07e3c003ec036ffe966fecf880c2bb3553a4a7f30ffe000fe0f8000018000180007
  | 0, 3 => 0xda47ae77040bec9d886932fdd9a010079c7f060fcc3c000003ffc100f09103ff11f90242440ffc47e409c00003ff01f00200000ffc07c0083003a0705ad00ec00e81c16b403b3007e070fff04fc01f81c3ffc13ffdfff7abfe6ff10633926e3c625f30ffe000fe0f8000018000180007cf6a5ecd64a6f90a1ef1ffeffe320f000000000000001e71ffe7fe30b6330bff51f30a484ebffd6fce3b800003ff01f00200000ffc07c008372aecd54e929fdbffb5dffb7e3230006000060001c3ff8003f83e00b2130bff51f30a484c2ffd47cc29800003ff01f00200000ffc07c008
  | 0, 4 => 0xc084000a81080025215a249093c40000000000000000000000000000c6a6084fc18a083febff7dbafff6c000000f0000003fe07e3c003ec0dff85f8ffffff12310483ffff180dff81f8ffffff00000003fffc100f85113ff35f56240440ffe47c409800003ff01f00200000ffc07c008f948f6992e34f7d3ff84abfd3e0030006000060001c3ff8003f83e00d8c4120ffffc603fe17e3fffffc4d000000ffff0403fe07e3fffffc0cf22084cc18208291ef9ffffffb20f000000000000001e71ffe7fe30c207bc7ffbff8cbd8869319299a000079c7ff9ff8c3c000000000000
  | 0, 5 => 0xf09503ff91f9027fe57ffcd7ffcdc00003ff01f0023fe07ffc07fec8c8401208a52460210048229491800000000000000000000000000000cffc5f8fa42ff10631123e142244cff81f8f000fb00000003c0000000e731b6170e76813e10548967e3b0fff9ff0f9fffe03e001c007ff3f3fffe966fecf880c3ff3fffffe7f3fffe000fe0f80001ff1fffffe37352ae4914e1297d3ff94cff97e1230006000060001c3ff8003f83e000627bc7ffbff8cbc8ab1552a4a3200079c7ff9ff8c3c000000000000c94856892424f10210002a0420000000000000000000000000000000
  | 0, 6 => 0x27bfedf7000b9fdeffb7dc002e7fefffffff000fbffffffffc003effcffc5f8fa52ff13ff17e3e94bfc4cff81f8f000fb03fe07e3c003ec0f084009f8118027fe57ebcd1bfc4c000000f0000003fe07e3c003ec0b119e7ff1ff197d3ff8ffffffe09b00063ff07f003c3ff8ffffffe08f8401299fff46261444cabffd58010000000fff04000000003ffc100cffa5fcf64aff90a18213f062820cff81f8f000fb00000003c000000da421a4cfff66829086933ffd9a010000000fff04000000003ffc100cffc5f8fa52ff106711e3e14a644cff81f8f000fb000000e3c000000
  | 0, 7 => 0xfcfff32aff6fe02523da66bcd3df30ffe000fe0f8000018000180007f948f699af34f7f3ffccabfdbf8030006000060001c3ff8003f83e00fcfff32afe6fe0042392663c425f30ffe000fe0f8000018000180007cf621a4c64a668081ef1ffeffe320f000000000000001e71ffe7fe30f083a07f5ad80ec20e81fd6b603bf007e07ffff04fc01f81ffffc13ff2da4bc444827b4b692f111209edf0f86380060073c3e18e001801cfcff85f8fa52ff123504e3e94b580cff81f8f000fb000000e3c000000c9485689a524f12310482a94b1800000000000000000000000000000
  | 0, 8 => 0x3119e5b31e5197d3ff86cff97e0930006000060001c3ff8003f83e0034ffe1b3fe5f82446796cc79465f30ffe000fe0f8000018000180007fef0bb1e2a3f66d1ef84b5fd1e00fff87f8f060fb1c3ff803ff83e008f6afc0f6f06fd805a8e3f288432bffffc0ffe0ffdc01f8e3ff801373bdde966becd880c3d63bbd7bc6d3fffe000fe0f80001ff1fffffe37cef71b6ef1ef682c007b7406c1ffcfff9ffff9fffe3c007ffc07c1ffc8c4120fa52c603fe17e3e94bfc4c000000f0000003fe07e3c003ec0f4ffe12aff4f802523da64b8d3df30ffe000fe0f8000018000180007
  | 0, 9 => 0x318ce4938e1897d7ff968ff93e4430006000060001c3ff8003f83e000287bc7ffbff8cbca93315120a6400079c7ff9ff8c3c0000000000000b841ed280b87fc43d13875702640f001ff001f07fc01e01c3e7c138c084a41f8b1884bfe97e3d90bfc4c000000f0000003fe07e3c003ec0330ffcffffff9fffffa59bfb3e203007fc7fffff8dffff8003f83e00d840b619fff4e4b1884823ffd98010000000fff04000000003ffc100fdf843800400734377deeefdf7dffff86380060073c3fffffffffffffff85f9f243ff3425404be452400cff81f8f000fb00000003c000000
  | 0, 10 => 0xcff85f8f252ff102500e3e04a400cff81f8f000fb000000e3c000000cb001edd01b07ffbdc6dbbc7bda0cf001fff01f07ffffe7fffe7fff83217bdfffbff8efccc27dd434c2900079c7ff9ff8c3c000000000000e948f699f1e4f7f2ffcca806ef8020006000f9f041c3ff800007ff00f09503ff91f9027ec42ffc47ec09c00003ff01f0023c000ffc07c008b4ffe3ffffff8244679ffc7fc65fb0ffe3ffffff8200018ffc1fc00f3f33096650c308081ef3ffeffe3b0f000000000000001e71ffe7fe303217bd7ffbff8cbc88235502482900079c7ff9ff8c3c000000000000
  | 0, 11 => 0xfff95faf356ff102500e7e04e409cff81f8f000fb000000e3c000000fff95fff35fff342540ffe47e409cff81fff01ffb200000ffc07c008c094038f8129003fe17e3c94bfc4c000038f0000003fe07e3c003ec0b011a7ff1bf186d0cc0ffd47cc09800003ff01f00200000ffc07c008fff95fbf347ff3425406fe456409cff81f8f000fb00000003c000000f09501bf9159027fe57efcd1ffcdc000000f0000003fe07e3c003ec0c9cc568fa52cf13ff17e3e94bfc4c000000f0000003fe07e3c003ec0cffc5f8fa52ff127315a3e94b3c4cff81f8f000fb00000003c000000
  | 0, 12 => 0xcfa6084bc18a0837ff8fc37f41f6cf00000f0000003ffe0fc3e7c0f00f22ac554a928c989ef1ffeffe320f000000000000001e71ffe7fe30bf330bbb51730a485afe03a83a3b8f0003ff01f002001e7e03e03e38cfb40b8f812b003ff17e3e94bfc4cf00038f0000003fe07e3c003ec00fa60846c08a080c3ff3fffffe760f000000000000001e71ffe7fe3034ffe533fe5f8494ab9245384a5f30ffe000fe0f800001800018000717b84d87dbdb912310481dfbf180dff81f8ffffff00000003fffc100ccf0a7110a10e490885a6504c9dfcff8038000007200007ffc07c1ff
  | 0, 13 => 0x3e2aecd54e929fdbe1757416c0323f006000060001c3e1f1fc1fc0307ee61891e01e6a6c4474884105f64fff9c00f80ffc3c0070000001f7c286ac5fcb9a8cbfe97f3d92bfe4c000000f0000003fe07e3c003ec0da42be5dfff6ecb9886933ffd9a010000000fff04000000003ffc100cb4ffefffffffdbe98213b06282000079c7ff9ff8c3c0000000000003d7c438f8508737c96a0d26d481b3ff8638f060073fc1f81c3ffc13ff09503ff91f90265655ffcd7d7cd800003ff01f00200000ffc07c008f18ce49b8f1897f7ffdeaff9bfc430006000060001c3ff8003f83e00
  | 0, 14 => 0x3059f7b43e75f7c800703c80be0930fffff0ffffffc001f03c183f0ff095012f9149003fe17e7c90ffcdc000000f0000003fe07e3c003ec03207bcfffbff8efccc2599430c2000079c7ff9ff8c3c0000000000003f2208d540920a485ef5ffeffe320f000000000000001e71ffe7fe3013400cd5fe441fdadc2598386c20df001ffffe003ffffe7ffc183ef8cff85f8fa52ff12310483e94b180cff81f8f000fb00000003c000000ca47be7fffffecbd8869339699a000079c7ff9ff8c3c000000000000c907a2a2fa4ff347544caac5b580cf078380f80ff3c3fe7fffe7fff8
  | 0, 15 => 0x36ffed77fedf8c9cabb3553a4a7f30ffe000fe0f8000018000180007bf330bff51f30a485effffeffe3b8f0003ff01f002001e7fffe7fe38b217bffffbff8efccc2ffd47cc2980079ffff9ff8e3c000ffc07c008b213afff5bf38ed8cc2ffd47cc29800003ff01f00200000ffc07c008f85113ffb5f56261444ffed7d589800003ff01f00200000ffc07c008f09503ff91f90246651ffc57e64dc00003ff01f00200000ffc07c008c286084fc18a083fe97f3d92bfe4c000000f0000003fe07e3c003ec097aeee0811fa9d9ebbb82047ea766ffffc0001ffbdfffff00007fef7
  | 1, 0 => 0xe847b27824246edcefb7e2040e7f2007e07000000fffffffc0003eff4de9407f15f1710333d112ba33d67ff8607f07f071c3fff003f83ff7fff85f9f253ff342540ebe45a400cff81f8f000fb000000e3c000000f85113bbfff56261444eefffd58910000000fff04000000003ffc100f0ddf7bbbf7df7f7e10e001001cdf0ffffffffffffffe18e001801cf3f3309f750d30a485ef7ffeffe3b0f000000000000001e71ffe7fe30c283bc707af78c83695f2d92b7e4c0079c70f9ff8c03e07e3c003ec0685111f7ee0562614447dfb81589900003fffe004200000ffff80108
  | 1, 1 => 0xb11947ff15f19342540ffe47e409800003ff01f00200000ffc07c0080f2a4cc54482990a1ef1ffeffe320f000000000000001e71ffe7fe30030ffcffffff9dbe98211b02282000079c7ff9ff8c3c000000000000cf621a4ce5a668291ef9ffffffb20f000000000000001e71ffe7fe30de621a4cfff668290af977ffdbb210000000fff04000000003ffc100fb07beadda60710633927a3c625fff07ff8ffe00300001803c1800070f7c5f80a527f13df17e02949fc40ff81f80000fb03fe07e00003ec00f6efc00ee06fdbdbbf003b81bf63ffffc00fe0ffdfffff003f83ff7
  | 1, 2 => 0xd25b43bbb7d84b496d0eeedf6120f079c7ff9ff8c3c1e71ffe7fe303007a070dad00efdaff1c1fb5bff3007e070fff04ffffff1c3ffffff25b85188fbf413627796cd02265feff86380f9f033c3fffffc003eff84eee2ddefbe8244679db87f8656b0ffe3ffffff8200018ffc1fc00f05f705b3f05f17d7dc16cfc17c5f00ff8000f80f81c3fe0003e03e07709503f090f9027fa571c0d77bcd400003f001f0023fe071c007fec80622ac554a928c988ab1552a4a320000000000000000000000000000fa08fa4c0fa0e82823e9303e83a0ff007fff07f07e3c01fffc1fc1f8
  | 1, 3 => 0xfffd5fafb46ff10631127e14624dcff81f8f000fb00000003c000000cfa6084fc18a083ffffffffffff6cf00000f0000003ffe7fffe7fef00f320946408308081ef1ffeffe320f000000000000001e71ffe7fe303007a070dbd00efdefffc1fbdfff3007e070fff04fffffffc3ffffff00840002800800042112041002440000000000000000000000000000f09503af9169003fe17e7c94ffcdc000038f0000003fe07e3c003ec0f09103ff91f90263444ffcd7f589c00003ff01f00200000ffc07c0080f6afc006e06fd801a80032800323ffffc00fe0ffdc01f8003f80137
  | 1, 4 => 0xfcfff32affffe02523da67ffd3df30ffe000ffffc000018003ffc1073048e000fe44800023800038420030006000fe000000018000180000c8c0120f242c600200003e042000c000000f0000000000003c0000003cffe122fe4f80042392663c425f30ffe000fe0f80000180001800073108e4914e1097d3ff848bf97e0030006000060001c3ff8003f83e003f7bfff07ef7ffc01e81c36f403b3ffffff0ffffffc01f81c3ffc13ff848f208fff4e02123c823ffd38030006000fff04000018003ffc1004feefc00ee0efdbfbbf003b83bf67ffffc00fe0ffdfffff003f83ff7
  | 1, 5 => 0xffffffbbff7ffffffbfe03b83bfffffffffffffffffffffe03f83fffb015a7ff9bf986fccc2ffd47cc09800003ff01f0023c000ffc07c008301101b3105102404406cc41440900000000000000000000000000008000000f01000000400e3c0084008000000f00000000000e3c00000006b70966d1cb082c007b5402c1ffcfff9ffff9fffe3c007ffc07c1ffc084000d8108003fe17c3890bfc4c000000f0000003fe07e3c003ec035ffe5b3fe5f97d7ff96cff97e5f30ffe000fe0f81c3ff8003f83e073008e0000e0080002380003802003000600006000000018000180000
  | 1, 6 => 0xc084004f8188003fe17f3c92bfc4c000000f0000003fe07e3c003ec0cffa5f8f642ff10212907e2c6212cff81f8f000fb00000003c000000b01103fb11f10240440fc043c409800003ff01f00200000fc007c00802020844408208080821110208200000000000000000000000000000ffffffaffe6ff10633927e3c625fffffff8ffe0fb00001803c18000704fa4102640f800002904428421200f80000000f80000000000000003f2aecd54e929fdbfff5fffffe323f006000060001c3fff1fffffe3006220844408208080ab1552a4a320000000000000000000000000000
  | 1, 7 => 0xd8401609fff4e021004823ffd18010000000fff04000000003ffc10010400000fe44000000000038400010000000fe000000000000180000cef71b6ef1ef682c02fb742ec3ffcfff9ffff9fffe3c007ffc07c1ffd8401208fe6460000000223c400010000000fe00000000000018000001000000000000001e808be93e0000000000000000001e0003e03e00d8401208fff4602102c823ffd38010000000fff04000000003ffc100b118e79f0e3197d3ff84bffd3e00b000638f060001c3ff803ff83e00d9485689fff4f12310482bfff18010000000fff04000000003ffc100
  | 1, 8 => 0x1008fbf4002000000102000000000000f9f0000000000000000003000cd500001fdadc2598002c20cf001fff00003ffffe7ffc003ef8d0400008ff440021004820b8d18010000000fe000000000000180000bf310bff11f30240540ffe47e4098f0003ff01f00200000ffc07c008cffffffffffffdbe98213f062820cfff9ffff9ffbc3c00003c00000002041c0fa12f803c80201000080000001c0f000f803c000000000000cef71b6ef1ef682c217b7416c3ffcfff9ffff9fffe3c007ffc07c1fff843b278fff46ee10ec9e3ffd1bb3007e070fff04fc01f81c3ffc13f
  | 1, 9 => 0x3427a070dbd20efdefffc5fbdfff3007e070fff04fffffffc3ffffffcffc5f8fa52ff13e90203e042800cff81f8f000fb03c00003c000000c287bc7ffbff8cbfe97f3d92bfe4c0079c7ff9ff8c3fe07e3c003ec00004000f8108003c8020100008000000000f0000003c0000000000000f220845408208085ef5ffeffe320f000000000000001e71ffe7fe30c840120825b46021004823c791800000000001f04000000003e7c1003df84380040073427796ce6d665ffff86380060073c3ffffffffffffda47be7fffffecbd886933ffd9a010079c7fffffcc3c000003ffc100
  | 1, 10 => 0x34ffe126fe4f800c23f27cb8fe5f30ffe000fe0f800001f03c183e072007a07000000edcefb7c0000e7f2007e07000000fffffffc0003effc8401208242460000000220400000000000000000000000000000000c084000b81080037e15e2c90bfc40000000000000003e00000003e00ccf5132ab16d6024005a6404c1dfcfff9ffff9fffe3c007ffc07c1ff30000091001002404404884104000000000000000000000000000000fdfdf7bbbf7df7f7f7deeefdf7dfffffffffffffffffffffffffffffc0c4000fa50c003fe17e3c90bfc4c000000f0000003fe07e3c003ec0
  | 1, 11 => 0x4feefc0fef0efdbfbbf013b83bf67ffffc0ffe0ffdfffff003f83ff7010844810400910210000a002000000000000000000000000000000027bfedf7400b9fdeffb7dc286e7fefffffff000fbffffffffc003effd9401208fff4602110482bfff18010000000fff04000000003ffc100c958578f2425f10210003e0420008000038f0000000000003c00000000000044008000000401fc47c40000000000000000000001fc07c000cff85f8f242ff10210003e04a400cff81f8f000fb00000003c000000cfeefe4cefaefdbfbbf933bebbf6ffffffffffffffffffffffffffff
  | 1, 12 => 0xfeffffffffffffffe17f7416c1ffffffffffffffffffe1fffc1fc1fff108e4998f1097f3ffccabf9bf8030006000060001c3ff8003f83e00c00000088100002100482090918000000000000000000000000000000f220844c08208081ef1fffffe320f000000000000001e71ffe7fe3036fffd7fffff8cbcabb3553a4a7f30fffc7fffff8c3c0180001800070007a022fa4f800400000000000000078000f80f8000000000000000c080000f01080002400e3c00a400c000000f00000000000e3c000000f01103ff91f10261444ffcd7d589800003ff01f00200000ffc07c008
  | 1, 13 => 0xb01103bf107102404406fc4544098000038f0000000000003c00000004f84102240f800000000400000000f80000000f80000000000000000001007f11f100000001100200000000007f01f00000000000000000f094039f8139027fe57ebcd5bfc4c000038f0000003fe07e3c003ec00207bc7ffbff8cbc88211112082000079c7ff9ff8c3c000000000000cffa5fcf64aff90a1ef1ffeffe32cff81f8f000fb0001e71ffe7fe300f284c850402910210003e0420000f0000000000000000003c000000c9c8568f242cf10210003e042000c000000f0000000000003c000000
  | 1, 14 => 0x4220000400200000290442842120000000000000000000000000000ca47be7fffffecbc88213306082000079c7ff9ff8c3c000000000000f948f699fff4f7f3ffccabffff8030006000fff041c3ff8003ffff00110844810e10910310000bf930001000000006000000000003f800000f220844408208081af113aa3a320f000000000000001e7003e03e30f851132afff56021004a67ffd18910000000fff04000000003ffc100c3840cdf81081ffffd7fbc90bfe4cf001fff00003ffffe7ffc003ef80203087f51f308080821110208200000007f01f00000000000000000
  | 1, 15 => 0xb01103ee11e10240440ffc47c409800003ff01f00200000ffc07c008273bedf500039fdadea5d8002c3befffffff000fbffffffffc003effcfa6080fc10a003ff3fe7ebcffd6cf00000f0000003fe07e3c003ec036fffd7fffff8cbc88235502482900ff9c7ff9ff8c3c000000000000f0ddf7bbbf7df7f7e90e011009cdf0ffffffffffffffe18e001801cfb01103ff11f10240650ffc57c609800003ff01f00200000ffc07c00825b84180000013427796cc00265feff86380000033c3fffffc003effcfe41a0fa52e603ff17e3e94bfc4cf00000f0000003fe07e3c003ec0
  | 2, 0 => 0xcfeefc0fef0efdbffbfe3fb8bff6fffffc0ffe0ffdfffffe3ff83ff7408400008008003fa17000903bc4400000000000003fe07000003ec0c084020f8128003fe17e3c94bfc4c000000f0000003fe07e3c003ec0f18ce49f8f1897fffffebff9bfc4f000600f060001fffffe3ff83ec00f2208454082081bfff5fffffe320f00000000000003fe71ffe7fe300000000100000013e10408903e000000000000000003e00000003e00c084008f8108003fe17e3c90bfc4c000000f0000003fe07e3c003ec0cff85f8f242ff10210403e84b000cff81f8f000fb00000003c000000
  | 2, 1 => 0xdfeefe08fffefdbfbbf823fffbf67ffffc00fffffdfffff003fffff748401000ee046021004003b8118010000000fe004000000003f80100c084000b8108003fe17e00909fc4c000000f0000003fe07e00003ec0b01103ff11f10240440ffc47e409800003ff01f00200000ffc07c008bf7bffff7ff7ffc05e8fff6fc43bbfffffffffffffc01f8fffffc13f301103f010f102400401c0474009000003f001f002000001c007c008c084000f8108003fe3fe3cb8bfc4c000000f0000003fe07e3c003ec034ffe122fe4f80042792cc79465f30ffe000fe0f8000018000180007
  | 2, 2 => 0xf85113fffff56261444fffffd589900003fffff04200000fffffc1089000020811f0000000082047c0000000000001f0000000000007c000fff95faf346ff10210027e046009cff81f8f000fb00000003c0000003f7bfff57ef7ffdadea5db6f6c3bffffffffffffffffffffffffffffcfa4080f810a003ff17e3e94bfc4cf00000f0000003fe07e3c003ec034ffe166fecf80042793fc7fc65f30ffe000fe0f80000181fc1fc007ffff5beef5ef7b6f77fffefff7ffffffffffffffffffffffffffffff0000a4110a1084908800010008000000000000000000000000000000
  | 2, 3 => 0xe2208444082080802f1742ec2320f000000000000000071fc07c030dc621208fff6602102d867ffd39210000000fff04000000003ffc100b019e3ff1ff18240678ffc7fc609b00063ff07f00200018ffc1fc008df621a4cfff668291ef9ffffffb21f000000fff040001e71ffffff30c840120864a46000004023efd0000000000000000000000003e7c000cffaffdf6ebffd9a98213f062820cff81f8f000fb00000003c0000000000005001900ef9cc6d81c39da00000007001f04ffffe7fc3e7fff8b01103bb11f10240440eec47c4090000000001f0000000000007c000
  | 2, 4 => 0x207bc7ffbff8cbc88215502482000079c7ff9ff8c3c000000000000b7bfefff11fb9fdeffbffc47ee7fefffffff01ffbffffffffc07feff201101f7000102404407dc000409800003ff00000200000ffc000008cff85f8f64aff10210003f062000cff81f8f000fb00000003c0000000f2aecd54e929d9a9ef1ffeffe320f000000000000001e71ffe7fe300206ac5fcb9a8cbc8821110208200000000f0000003c0000000000003108e4910e1097d2ff848b692e0030006000060001c3ff8003f83e00cff85f8fa42ff10210003e142000cff81f8f000fb00000003c000000
  | 2, 5 => 0xd948f699fff4f5b398482bfff98010000000fff04000000003ffc100ffffeff7040bffdffffffefdffffffffffff060fffffffffffffffff30110122104100000002440040090000000000000000000000000000f4fff7bbff7ff7f7e39e443843dff0ffffffffffffffe18e001801cf30dde122be4d800421020010004d30ffe000fe0f80000180001800070202bc5f6abf8c9888211102082000001c0f000f80000000000000003d2840800400134377d4eefdf6123f006000060001c3fff1fffffe300f27a866facf880c1ef1ffeffe320f078000f80f80001e71ffe7fe30
  | 2, 6 => 0xcff85f8f242ff10250043e042400cff81f8f000fb00000003c0000003008e4110e108490ab8001380a003000600006000000018000180000f848f619fff4e4b1abc823ffdb8030006000fff04000018003ffc100301101f710d102404407fc47c40900000000000000000001fc07c0004feefc44ee8efdbfbff1fffffff67ffffc00fe0ffdfffff1fffffff70f220800400208081af003a83a320f000000000000001e7003e03e30d8401209fff46031804823ffd98010000000fff04000000003ffc1004ee6b800ea0e6cbdabf001b81bf67ffffc00fe0ffdfffff003f83ff7
  | 2, 7 => 0xc0ddf72abf6df5b7a10a001001cdf0ffffffffffffffe18e001801cf0c2200004082000002d067efd2120000000000000000000003e7c00037ffedf7fe4f9fdeffb7dc386e7ffffffffffe0fbffffffffc183eff24bfe122000b800423924400025f20ffe000000f80000180000000073007a0705ad00edcefb7c16b4e7f3007e070fff04fffffffc3ffffffb2111fff11f10ef8cc2ffd47cc2980001fff01f00e3c000ffc07c0084feefc44ee8efdbfbbf113ba3bf67ffffc00fe0ffdfffff003f83ff73ffffff77effffdeffb7df6f6e7fffffffffffffffffffffffffffff
  | 2, 8 => 0x3108e4950e1097dbffa49bf93e0030006000060001c3ff8003f83e003011017f11f100000003540240090000007f01f00000000000000000c084000e8108003fa17a3490bbc4c000000f0000003fe07e3c003ec0dff85f8f346ff10210003e046000cff81f8f000fb00000003c0000003d79f7b03e75f7c01680c26d401b3ffffff0ffffffc01f81c3ffc13f0207bc7ffbff8cbc8821112a482000079c7ff9ff8c3c0000000000004bccfc00ae0cfdbfb960039039e47ffffc00fe0ffdfffff003f83ff7c8401208f1e4602100482096d18000000000f9f0400000000007c100
  | 2, 9 => 0x3011017211d10240440fc443c4090000007001f00200000fc007c0080f23086650c308081ef1ffeffe320f000000000000001e71ffe7fe30b01503ff91f9027cc42ffc47cc09800003ff01f0023c000ffc07c008cee61a4ce1ae682c0079300681f6cfff9ffff9fffe3c007ffc07c1ff000000040000000800703c80be00000000000000000000703c003e004feefc81ee0efdbfbbf00bb83bf67ffffc00fe0ffdfffff003f83ff7b01103af1061000000027c0440098000038f0000000000003c000000d8401208fff46021214823ffd38010000000fff04000000003ffc100
  | 2, 10 => 0x4ee61800e00e682c0070000001f64fff9c00f80ffc3c0070000001f7cf685e8d2426f10210003e0420000f0000000000000000003c000000c084000f8108003fe57ebcd1bfc4c000000f0000003fe07e3c003ec0effffffff1effffefffffc06efffeffffffff9fffffffffffc07fffff0ddf7bbbf7df7f7e11e041003cdf0ffffffffffffffe18e001801cff8ddf7bbbf7df7f7e10e221401cdf0ffffffffffffffe18e001801cfc7a6084f810a083ffffffc90bff6cf00000f0000003ffe7ffc003ef0c086000fc10a003fe17e3c90bfc4c000000f0000003fe07e3c003ec0
  | 2, 11 => 0x800000040800000004023efd0000000000000000000000003e7c000cf221edd41b27ffbdefdffefffb2cf001fff01f07ffffe7fffe7fff80b000844008008081c61bbc7bc200f000000000000001e71ffe7fe30f948f689fff4f12333c82bfff38030006000fff04000018003ffc100bf394fff15f39342540ffe47e4098f0003ff01f00200000ffc07c0080307bc7ffbff8cbc98211b02282000079c7ff9ff8c3c000000000000cff85f8f242ff10a10203e042800cff81f8f000fb00000003c000000c084000f8108003fe97e3d90bfc4c000000f0000003fe07e3c003ec0
  | 2, 12 => 0xcfffffff242ffd9e98213e042820cfff9fff000fbc3c00003c00000006f7bd7ffbff8cbc88335502487f00ff9c7ff9ff8c3c0000000000070f220cd540921fdbdef5ffeffe320f000000000001c3fe71ffe7fe30100000000e100001000003f910001000000006000000000003f80000b01503ff91f90244440ffc47c409800003ff01f00200000ffc07c008cffc5f8fa52ff13eb1323e142a44cff81f8f000fb03c00003c00000034ff4122f44f000423924438425f30ffe000fe0f8000018000180007cdf853882424710210002e042000cff803800000300000003c000000
  | 2, 13 => 0x37bfedf70e0b9fdeffb7dc382e7fffffffff060fbffffffffc183eff0207bc7ffbff8cbd88211192182000079c7ff9ff8c3c0000000000000207bc7ffbff8cbc88613182982000079c7ff9ff8c3c000000000000cdf8578b242df10210002e042000cff81f8f000fb00000003c00000034ffe123fe4f800463964c38465f30ffe000fe0f8000018000180007f9ddf7bbbf7df7f7f54eaad5b5cdffffffffffffffffffffffffffff310fe4f1dfd09fffffffcbfbffff3007e070fff04fffffffc3ffffff3000a0100a1006d1ef8481f91e0030006000060001c3ff8003f83e00
  | 2, 14 => 0xd8401208b5f46021004822d7d1800000000001f0000000000007c000fef7bb7efbff6efdeffff5ffdfffffffffffffffffffffffffffffff008400068008000c21723c90be44000000000000000000703c003e00f847b278fff46efdefffe3ffdfff3007e070fff04fffffffc3ffffff10000000dbd00021004801fbd18010000000fff04000000003ffc100c084000f8108003fe17e7c90ffc4c000000f0000003fe07e3c003ec0f0dff7fbfffdffffefffc1fbdffff0ffffffffffffffffffc3ffffff3f7ffff0fff7fffdffffc3ffdfff3ffffff0ffffffffffffc3ffffff
  | 2, 15 => 0xfff85f8f242ff10210003e042000cff81f8f000fb00000003c000000b01103ff91f10260440ffc47c409800003ff01f00200000ffc07c008d8401209fff46021404c2bffd58010000000fff04000000003ffc10027bfedf7408b9fdeffb7dd022e7fefffffff000fbffffffffc003effc084000e8108003de17e34909fc4c000000f0000003fe07e3c003ec0c0d5132ab16d6024000a000001cdc0ff9ffff9fffe3c000e000001cfc2dffffffffffdbe882111020820c0ff9ffff9ffbc3c000000000000cad51b6eb1ed682c006b300681edcfff9ffff9fffe3c007ffc07c1ff
  | 3, 0 => 0xc090038f0029000200003c042000c000038f0000000000003c000000d8c0120afffc6021004827ffd18010000000fff04000000003ffc100d8401208ff646021004822bcd18010000000fe000000000000180000b000029911f00240440ca847c4000000000001f0000000000007c000c080000f0008000200003c002000c000000f0000000000003c000000cffc5f8fa42ff10610003e042000cff81f8f000fb00000003c000000d000020891f00021004820d7d1800000000001f0000000000007c0000f2208444082080818213f0628200f0000000000000000003c000000
  | 3, 1 => 0x8010038f0021000000003c0400008000038f0000000000003c00000006fffd7fffff8cbc88211502082000ff9c7ff9ff8c3c000000000000309501229049000421124410424d0000000000000000000000000000b01103a210410240440eec45c4098000038000000200000ffc07c0083017a122fa4f800400024400400900078000f80f8000000000000000bf330bff51f30a485c2fff47ec298f0003ff01f00200000ffc07c008fdf843910410734377deeefdf7dffff86380060073c3ffffffffffff30070060d1c00a6d67ffc0fbd7ff3007e070fff04fffffffc3ffffff
  | 3, 2 => 0xcb841e8f8128713ff17e3e94bfc4cf001f8f0000303fe07e3c003ec0cff85f8f252ff10210003e042000cff81f8f000fb00000003c00000037bfedf7001b9fdeffb7dc412e7fefffffff000fbffffffffc003effcb07befffbffffffdc6dbbc7bda0cf079ffff9fffffffe7fffe7fff802001c5d01b00cb888211102082000001c7f01f00c3c00000000000034ffe122fe4f80042b9245384a5f30ffe000fe0f80000180001800074de840000400710333d002b833d67ff86000060071c3fff003f83ff727bfedf7800b9fdeffb7dc102e7fefffffff000fbffffffffc003eff
  | 3, 3 => 0xfef71b6ef1ef682c007b7406c1ffcfff9ffff9fffe3c007ffc07c1ffc000000f81000021404e3c9095808000000f00000000000e3c00000004fc4102a40f800421120410024400f80000000f8000000000000000301103f710f102404407dc474409800003ff01f00200000ffc07c0084feefc11ee1efdbfbbf003b83bf67ffffc00fe0ffdfffff003f83ff7c08400088108003fa1782090bbc4400000000000003fe07000003ec07feffc70ffdeffffffffc3fbffff7ffffc70ffffffffffffc3ffffff05220000400200001e90cfe97e1200000000000000001e0003e03e00
  | 3, 4 => 0xf220844408208081ee1fbeffc320f000000000000001e71ffe7fe30f0d5b33abb7d66f5e10e001001cdf0ffffffffffffffe18e001801cfcfeefc08ef0efdbfbbf823b8bbf67ffffc00fe0ffdfffff003f83ff7cef71b6ef1ef682c087b7506c9ffcfff9ffff9fffe3c007ffc07c1ff0fa60847c08a081ffff7fffffe760f00000000000003fe71ffe7fe30cff85fdf25bffffbdc6dbfc7bda0cff81fff01fffffffe7fffe7fff8cb001e8d0020710210003a042000cf001f8f0000300000003c00000034ffe123fe4f8014a39244384a5f30ffe000fe0f8000018000180007
  | 3, 5 => 0xf847b228fff4602523da63ffd3df3007e000fff04000018003ffc10707220844408208081ef1ddebfe320f000000000000001e71ffe7fe30cff71ffff1ff7fffdc7fffc7fdffcfff9ffff9fffffffe7fffe7ffffff7bfff87ef7ffc01e81e36f403b3ffffff0ffffffc01f81c3ffc13fb05103ff35f50240440ffc47c409800003ff01f00200000ffc07c0083108e4914e9097d3ff848bfb3e0030006000060001c3ff8003f83e0034ffe172ffdf8efdefffc5fbdfff30ffe070ffffcfffffffc3ffffff3007a020da40000423924038425f3007e000fe000000018000180007
  | 3, 6 => 0xccf8530a242fe00000002604000000f80000000f800000000000000035ffe5b3fe5f9596bb924f386a5f30ffe000fe0f8000018000180007fffdffbfbf7ff7f7f10e3e1421cdffffffffffffffffe18e3c1801cfc0d8578b242df102000000000000c0f81f8f000fb0000000000000000f220844408208091ef1fffffe320f000000000000001e71ffe7fe30cff85f8f242ff10212803e2c2200cff81f8f000fb00000003c000000f1ddf7bbbf7df7f7ff8e8bf93fcdf0ffffffffffffffff8e03f83fcf3008e4910e1097d3e1040010000030006000060001c3e18000180000
  | 3, 7 => 0xb01103bb11710240440eec45c409800003ff01f00200000ffc07c008b4ffe12aff4f8004239a6438c25f30ffe000fe0f80000180001800070f2008040002000010003e0420000f0000000000000000003c000000b01103ff11f10248442ffc47cc09800003ff01f00200000ffc07c00807bc4d87000b911ef1361c002e44cff81f8f000fb03fe07e3c003ec006fffd7fffff8cbca93315120a6400ff9c7ff9ff8c3c0000000000000207bc7ffbff8cbc883115020a2000079c7ff9ff8c3c00000000000034ffe166fecf80042393543a425f30ffe000fe0f8000018000180007
  | 3, 8 => 0xe09501ff8109027fe57ffc90bfcdc00003ff0000023fe07ffc003ec84decf400ae0cf5b7b3d002b833d67ffffc00fe0ffdfffff003f83ff78207bc7ffbff8cbc88293102882000079c7ff9ff8c3c000000000000f19947ff15f99342540ffe47e409c00003ff01f00200000ffc07c0083207a874dbd20efdefffd1fbdfff3007e070fff04fffffffc3ffffff34ffe122fe5f800423924479425f30ffe000fe0f80000180001800073005a0709bd00efded6f81d39ded3007e070fff04fffffffc3ffffff07bfed66000b9d9ebbb354002a7fefffffff000fbffffffffc003eff
  | 3, 9 => 0x3f7bfff17ef7ffc21e81cb6f603b3ffffff0ffffffc01f81c3ffc13fc084000fc108003fe17e3cb8ffc4c000000f0000003fe07e3c003ec035b841800000134377deccf9f7dffff86380060073c3ffffffffffffb010039f003102404404bc4504008000038f0000000000003c000000310ce4938e1897d7ff848bf93e0030006000060001c3ff8003f83e000207bcfffbff8cbc88211902082000079c7ff9ff8c3c000000000000c8000008c1800021004823ffd1800000000000000000000003e7c000f0ddf7babf7df7e4000a000001cdf0fffffffffffffc018e001801cf
  | 3, 10 => 0x7aeec00ca0a9dbfbbf001b83bf67ffffc00fe0ffdfffff003f83ff7c4a4000f810a003fe17e3c90bfc4c000000f0000003fe07e3c003ec0cff85f8f642ff10210003e2c6000cff81f8f000fb00000003c000000c084000e8108002f617e3c90b7c4c000000f0000003fe07e3c003ec0cef71b6ef1ef682d007b7496d1ffcfff9ffff9fffe3c007ffc07c1ffcfeefc0fee0efdbfbbf03fb83bf6fffffc0ffe0ffdfffff03ff83ff70108e4910e1097d3ff848bf93e0030006000060001c3ff8003f83e00fa111bff11f16a68446ffc47c5a9cf001fff01f07e3c007ffc07c1f8
  | 3, 11 => 0xd8401208fff460210448abffd58010000000fff04000000003ffc100b217bffffbff8efcc82f1102082980079ffff9ff8e3c000e000000080f220844408208081ef1bbefbe320f000000000000001e71ffe7fe30d8401208bff46021004823d7918010000000fff04000000003ffc100f9485699fff4f363544cabfff58010000000fff04000000003ffc100008400028108003de17e04909fc4000000000000003fe07e00003ec03207bc7ffbff8cbc88211102082000079c7ff9ff8c3c000000000000fb111fff11f17342540ffe47e409cf001fff01f03200000ffc07c008
  | 3, 12 => 0x287bc7ffbff8cbc88211502082000079c7ff9ff8c3c0000000000003108e4910e1097d3f7848af9360030006000060001c3ff8003f83e00cffa5fcf64aff90a1ab17f2e6a32cff81f8f000fb00000003c0000002fbfedf7408b9fdefff7ffeffe7fefffffff000fbfffffffffe7feff07220844000208081eb1dc002e320f000000000000001e71fc003e300207bc7ffbff8cbc88231502082000079c7ff9ff8c3c00000000000002001c0f202f800000001000000000001c0f000f80000000000000003c7bf3207ef7e0000280436f401b30ffe000ffffc000018003ffc107
  | 3, 13 => 0x4feafc006e06fd833bd003b833f67ffffc00fe0ffdc3fff003f83ff7f9d8438004007343754eaad5b5cdfff86380060073c3ffffffffffff0200bc5d0bb08cb888211102082000001c7f01f00c3c000000000000d840124cfff46021004933ffd18010000000fff04000000003ffc1004ff85f80242ff1021000020420004ff81f80000fb00000000000000034fff12afe6f800423924438425f30ffe000fe0f80000180001800078207be7ffbff8cbc88213106082000079c7ff9ff8c3c000000000000f8401208fff46021004823ffd18010000000fff04000000003ffc100
  | 3, 14 => 0xc8401208f1e4602000482006c18000000000f9f0400000000007c1000200bc1f2a3f849088001100080000001c0f000f8000000000000000cff85f8f242ff10210103e042200cff81f8f000fb00000003c000000f95957ff35f5f342540ffe47e409800003ff01f00200000ffc07c0080100a4110a1084909e808be93e0000000000000000001e0003e03e000f22084cc18208281ef1ffeffe320f000000000000001e71ffe7fe303011016610c100000403fc47c40900000000000000000001fc07c000300000000000024167dec0f9d7df30006000060043c3ffffc3ffffff
  | 3, 15 => 0x8f300b8f0023000010003e0420008f00038f0000000000003c00000035ffe5b3fe5f93467796ce79665f30ffe000fe0f8000018000180007cef71b6ef5ef682c007b7606c1ffcfff9ffff9fffe3c007ffc07c1ffb01103ff11f10242440ffc47e409800003ff01f00200000ffc07c008c8401208e5a46021004823ffd1800000000000000000000003e7c0003108e4810e00910233800a3822003000600006000000018000180000fb07befddbf07ffffffffbffffffff07fffffff07fffffffffffffffdef71b6effff682d007b77ffd1ffdfff9ffffffffe3c007fffffc1ff
  | 4, 0 => 0x7220844408208081eb1dfeb7e3200000000000000001e0003e03e00ce731b6c71e7682800697006c1bbcfff9ffff9fffe3c007ffc07c1ffc884000f8108003fe17e3e94bfc4c000000f0000003fe07e3c003ec00f22a8444a8288081ef1ffeffe320f000000000000001e71ffe7fe3003020844408208081ea19beb3e2000000000000000001e0003e03e00c0ccf699af3cf7f7e10c001001c4f0ffffffffffffffe18e001801cfb01303ff51f30240440ffc47c409800003ff01f00200000ffc07c0080e220844408208080af177efda320000000000000000000003e7c000
  | 4, 1 => 0x3000009100100253e50488d13e000000000000000003e00000003e001f22084450c208081ef1ffeffe320f000000000000001e71ffe7fe30c207bc7ffbff8cbc88213102082000079c7ff9ff8c3c000000000000f108e4990e1097d3ff84abf93e0030006000060001c3ff8003f83e00b01103fd11f10240440df847c409800003ff01f00200000ffc07c0080f220844408208081ef1f76fc0320f000000000000001e71ffe7c03004ffe122fe4f800400000400000000ff8000f80f800000000000000005eee400ee0e9597bb9003b83a5630ffe000fe0f81c3ff8003f83e07
  | 4, 2 => 0xcff85b8e242f710210003e042000cff81f8f000fb00000003c0000000fa20846408a08081ef1ffeffe320f000000000000001e71ffe7fe300001a47f1bf184908801110208000000007f01f0000000000000000004a60002c00a000423924438425600000000000000000000000000000207a874dbd20cbc88211102082000078070f9f00c3c000000000000d0c4000fff4c003fe17e3cb8ffc4d000000ffe00003fe07e3c183ec0d084000f9148003fe17e3c90ffc4c000000f0000003fe07e3c003ec00f200844008200001401fe47e4000f000000000000000001fc07c000
  | 4, 3 => 0xcffe5fcfe5aff93e98213f062820cff81f8f000fb03c00003c0000003007a471dbd08efdefffc1fbdfff3007e070fff04fffffffc3fffffff059f7b93f75f7f3c00c00000189f0ffffffffffffffe18e001801cf3108e4930e1097d3ff868ff93e0030006000060001c3ff8003f83e00fc73132afff7602102da67ffd39b10000000fff04000000003ffc100353be5b35e5397d3ff96cff97e1b30006000060001c3ff8003f83e00f0ddf7bfbf7df7ffe17e3c90bfcdf0ffffffffffffffe1fe3c183fcfc084000b81080037e10e001001c4c000000f0000003fe00e000000c0
  | 4, 4 => 0xb007a07fdbd00efdeffffdfbdfffb007e07ffff04ffffffffffffffffdf943ff15f1734377dffefff7dffff863ff07f073c3ffffffffffffb010038000000240440eec45c4098000038000000200000ffc07c0080004a41f8b1884bc8820110008000000000f0000003c000000000000ccf0030000006000005a6404c1dfcff8038000007200007ffc07c1fffdfc43828408734777deeefdf7dffff86380060073c3ffffffffffff00070060d1c0082c007b4002c1ff00078070f9f04e3c007fc007c1fff4b7012fd14b003fe3fe7cb8ffdfc000000f0000003fe07e3c003ec0
  | 4, 5 => 0x20040408008080ef1c1ebde3200000000000000001e71c3e7fe30b011a3ff1bf18240440ffc47c409800003ff01f00200000ffc07c008b43103ff11f30240440ffc47c409800003ff01f00200000ffc07c00806fffd7fffff8cbc8ab1552a4a3200ff9c7ff9ff8c3c000000000000d8401208fff46021004867ffd18010000000fff04000000003ffc100ca401e0f242fe00000003204000000001c0f000f8000000000000000343301225043000002924428421b00000000000000000000000000003007a07fdbd80efdefffd1fbdfff3007e07ffff04fffffffc3ffffff
  | 4, 6 => 0xf785f812427f10210000a0420000ff81f80000fb000000000000000e7bfedff810b9ffffffffc90bfffefffffff000fbffffffffc003eff008400070008001ee1361c002e44c000000f0000003fe07e3c003ec034ffe123fe4f800623924c38625f30ffe000fe0f8000018000180007f01103ff11f10240440ffc47c409800003ff01f00200000ffc07c008da401a0cfff66021004833ffd18010000000fff04000000003ffc1003003a0705ad00ec16fdfc1fbd7ff3007e070fff04fc3ffffc3ffffff3f27a874dbd20efdffffffffffff3f07e070fff04fffffffffffffff
  | 4, 7 => 0x8010038f01210000400e3c0484008000038f00000000000e3c0000000627bc7ffbff8cbc88211502082000079c7ff9ff8c3c0000000000000006a050cb900efdeffd81fb9ff63007e070fff04fffffffc3ffffff7feefc91ee1efffffff48bf93ff67ffffc00fe0ffdfffff003f83ff70108e4000e009593bb8003b83a0030006000060001c3ff8003f83e00cffc5f8fa52ff12e107a3e04a1c4cff81f8f000fb03c007e3c0000c0300000910e10024144048bf914001000000006000000000003f800000f2208444082080816f1feeff6320f000000000000001e71ffe7fe30
  | 4, 8 => 0x3005a0309b5006f5e10e001001cd3007e070fff04fffe18e001801cffffa4bc444827b4b7ffffffffffffff86380060073c3ffffffffffff0d2000000000000016d0eeedf6120f000000000000001e71ffe7fe30b01103ff91f10240440ffc57c409800003ff01f00200000ffc07c00834ffe122fe4f8005239244b8525f30ffe000fe0f80000180001800073108e4910e1097d3ff84cff97e0030006000060001c3ff8003f83e00fffbffff7effffc21e81ff6f603bffffffffffffffc01f81ffffc13f0f785f802427f1001000020400000ff81f80000fb000000000000000
  | 4, 9 => 0xca001a4c01a068280069300681a0cf001fff01f07e3c007ffc07c1f80f220844408208081eb1df6f6e320f000000000000001e71ffe7fe30000000050000001be1743c90be000000000000000003e0703c003e00cfeefeddefbefffffffdbbffbff6ffffffffffffffffffffffffffff3e73bb707af76ec00e81c16f403b3ffffff0ffffffc01f81c3ffc13fb01107ff11f18240440ffc47c409800003ff01f00200000ffc07c00803000cd501901ffbdc6d99c3bda0cf001fff01f07ffffe7fffe7fff80084000380080017e1160c903e440000000000000003e00000003e00
  | 4, 10 => 0xd8421208fff66021004823ffd18010000000fff04000000003ffc100c08c400f8508803fe17e3c90bfc4c000000f0000003fe07e3c003ec00f220844408208081af177aefa320f000000000000001e71ffe7fe30330ffcffffff9ffedc259b432c2000079c7ff9ff8c3c0000000000000f220844408208083ff1fffffe320f000000000000001e71ffe7fe303108f4992e3497d3ff848bf93e0030006000060001c3ff8003f83e003108e4910a1097d3ff8489f93e0030006000060001c3ff8003f83e00020208444082080808713d82be20000000000000000000703c003e00
  | 4, 11 => 0x3f2a4cd544929b4a5ef5ffeffe320f000000000000001e71ffe7fe30fdf943a21441734377deeefdf7dffff86380060073c3ffffffffffff0206bc44ea8e8cbc88211102082000079c00f80f8c3c0000000000001f220844409208081ef1ffeffe320f000000000000001e71ffe7fe30c085002f9149003fe17e3c90bfc4c000000f0000003fe07e3c003ec0b01113ff31f50240440ffc47c409800003ff01f00200000ffc07c008d840120afff46021004a27ffd18010000000fff04000000003ffc100cf220ac440827b4b5efdffefffb2cf000380000073c3fe7fffe7fff8
  | 4, 12 => 0xd84012087ff46021004823efd18010000000fff04000000003ffc1000007a060dbc00cbdabfb41badbff3007e070fff04fffffffc3ffffffc004000f8108003d8068309099800000000f0000003c00000000000007b70df7000b1fdedc37dc002c7fcfff9fff000fbffffe7ffc003effcfff5feff5eff92e107b7e06e1ffcfff9ffff9fffe3c007ffc07c1ffcef01b0e202f6000000034040000cff81f8f000fb00000003c00000027bf49e6000b1b4e77b7dc00267fefffffff000fbffffffffc003eff0202184cfbf6082808211102082000000000f9f00000000000000000
  | 4, 13 => 0x3008e0910e1082406784887906003000600006000000018000180000f859f32afff5e02123ca67ffd38930006000fff04000018003ffc1000ff85f87242ff10210001e042000cff81f8f000fb00000003c000000c084000f8108003e80203c002800c000000f0000003c00003c0000003908e4910e1097d3ff84abfd3e0030006000060001c3ff8003f83e00c8401208ffe46021004823bed18010000000fff04000000003ffc100f0ddf7bbbf7df7f7e14e209091cdf0ffffffffffffffe18e001801cff0d8438004007343610e001001cdf0f86380060073c3e18e001801cf
  | 4, 14 => 0x3207bc7ffbff8efdefffd1fbdfff3007fc7fffffcfffffffc3ffffff0007a070dbd00cbc88210102082000078070f9f00c3c000000000000cf22084dc182083bfffdffffffb20f00000000000003fe71ffe7fe30301103f011f10240440fc047c409000003f001f00200000fc007c008ff711bff35f76240540ffe47e4098f0003ff01f00200000ffc07c00834ffe122fe4f800423924638425f30ffe000fe0f8000018000180007c8401208f1f46021004823c7d18000000000f9f04000000003e7c10007aeec00000a9d9ebbb000002a766ffffc00000fbdfffff000003ef7
  | 4, 15 => 0x37bfedf75adb9fdeffb7dd6b6e7ffffffffffffffffffffffffffffffffb5faf746ff10212927e2c621bcff81f8f000fb00000003c0000000203ac7f5bf38c988821110208200000007f01f00000000000000000cffe5f8fe42ff10633927e3c6256cff81f8f000fb00000003c000000fdf84382240ff34377deeefdf7dffff86380060ff3c3fffffffffffffb08fedd0fb0fffbffedbbffbfa0ff007fff07f07ffffffffffffff801000491001017d3dc048bc13c0000000000000001c3fe0003e03e003007a0f1dbd00efdefffc9fbdfff3007e070fff04fffffffc3ffffff
  | 5, 0 => 0x3108e4910e1097d2dc048b412c0000000000000000000000000000000203bc7d7bf78cb888211102082000079c7ff9ff8c3c0000000000001000a4110e108491880003f918001000000006000000000003f80000b01103ff1bf10240440ffd47c409800003ff01f00200000ffc07c00825bde5b3000997d6f796cc00265fefffffff000fbffffffffc003eff01084481040091021e808be93e0000000000000000001e0003e03e00f09503ff91f9026c447ffc47c5cdc00003ff01f0023c007ffc07c0c8fffffffbfffffff7ff8fc37f41ffffffffffffffffffff8fc3ffc1ff
  | 5, 1 => 0x34ffe126fe4f800c23b254384a5f30ffe000fe0f8000018000180007bf37bffffbff8efcdeffffeffe3b8f079ffff9ff8e3c1e7fffe7fe38f8ddf7bbfffdf7f7e14e23ffd1cdf0ffffffffffffffe18e03ffc1cfd0401208bf74602100080010018010000000fff04000000000180100c188448f0408910210003e002000c000000f0000000000003c0000000f2a4844448288081ef1ffeffe320f000000000000001e71ffe7fe3034f7a122fa4f000423924438425f30ffe000fe0f8000018000180007c084001f8118003fe17e3c90bfc4c000000f0000003fe07e3c003ec0
  | 5, 2 => 0xfef71bfff1ff6a6c447ffc47c5ffcfff9ffff9fffe3c007ffc07c1ff8011036e11e10000000b7406c009800003ff01f00200000ffc07c0080f220844408208081ea1d36f48320f000000000000001e01c3e7c030b108e4990f1097d3ff8cabf9be0030006000060001c3ff8003f83e00c084000e8108002d217a3c90bfc4000000000000000000703c003e00d8401208bf746021004822fdd18010000000fff04000000003ffc1003108e4910e1097d3ff948ff93e0030006000060001c3ff8003f83e003017a172dbd10efdefffc5fbdfff3007e070fff04fffffffc3ffffff
  | 5, 3 => 0xdb401eddfff47ffbdc6dbbfffda0df001ffffff07ffffe7ffffffff8f5ffe5bfff5f97fffffefff9ffdff0ffe00ffe0f81fffffe3ff83ec76ffffdf7ee0ffffffff7dfb83ffffffffffffe0ffffffffffff83fffb01103ff51f10240440ffd47c409800003ff01f00200000ffc07c0088084000f81080004611e3c1086448000000f00000000000e3c000000d8c0120ffffc602300483ffff180d000000ffff0400000003fffc100b4b703ffd1fb0244679ffc7fc65f800003ff01f00200000ffc07c0083637bd7ffbff8cbc8ab3552a4a3b00079c7ff9ff8c3c000000000000
  | 5, 4 => 0x3108e0000e0080003f808bf93e0030006000060000001f8003f83e00c884000fc188003fe17e3fffffc4c000000f0000003fe07e3fe7fec03108e4950e1097dbfff4bff9be0030006000060001c3fff03ff83e000000000000000000000008803e000000000000000000000000003e000207ac77000b8c9c88211000082000079c7f000f8c3c0000000000003108e4900e1097c01e808369000030006000060001c01f8003f800000207186ef1ef082c00211002002000079c7ff9ff8c3c0000000000003f7ffffffffffffc9ea1d36f483b3ffffffffffffffc1f81c3ffc13f
  | 5, 5 => 0x8000044408000000441ffefd40000000000000000000001ffe7c0008f22084f418208085effffeffe328f00000f000000001e7fffe7fe309001027f11f1000000093047c0000000007f01f0000000000007c00005f84583240f910210000e00200000f80000000f800000000000000000000000000000000000000000000000000000000000000000000000cef7bf7ffbffecbc887b7506c9ffcfff9ffff9fffe3c007ffc07c1ff04eee000ee0e800423900038025630ffe000fe0f800001800018000737bfedf7dbdb9fffffffddfbffffffffffffffffffffffffffffffff
  | 5, 6 => 0x1008202400000000000000000000000000000000000000000000fffbfff07ef7ffc37fdfeffff7fffffffff0ffffffc3ffffffffffff0206084fc18a083c8821110208200000000f0000003c000000000000cfffff6effeffdbfbbfb77befbffffffffffffffffffffffffffffffcf601a0c2426600010003e0420000f0000000000000000003c000000c850138f2425600000003e0400008000038f0000000000003c00000001000044008000001e81ffeffe0000000000000000001e01ffe7fe00010000000000000010000a0020000000000000000000000000000000
  | 5, 7 => 0xf08ce00f8f08803fe3fe3cb8bfc4f000600f0600003fe1fe3c183ec0000004010000800000000000000000000000000000000000000000000f23087f51f308081ef1ffeffe320f00007f01f000001e71ffe7fe30cff71b6ef1ef682c1efbffefffffcfff9ffff9fffe3c1e7fffe7ffffcff85f8f242ff10a10703e84be00cff81f8f000fb00000703c003e007ffffd22fe4ffdbfbbf247b87bff7ffffc00fe0ffdfffff003f83ff70203bc707af78c8008010102002000079c70f9ff8c000000000000000f220840408208001e81c36f40320f000000000000001e01c3e7c030
  | 5, 8 => 0x34f841000400000023924438425f30f86000060000000180001800070000000f002100000000100000000000000f00000000000000000000d8401209fff46033e14c2bffff8010000000fff04003e00003ffff000f2208044002000012907e2c62120f0000000000000000003c000000cef71b6ff1ef683fe17f7c96ffffcfff9ffff9fffe3fe07ffc07ffff0087a022fa4f800421120410024400078000f80f80000000000000009207be7ffbff8cbc88293147c82000079c7ff9ff8c3c00000007c000fff95ffffffff363544ffffff589dff81ffffffff200000fffffc108
  | 5, 9 => 0x9010038f11f1000000083c47c0008000038f01f0000000003c07c000fdfc438f8508737ff7fefefdffdffff8638f060073fffffffffffffffff85f8f242ff34377defefdf7dffff87f8f060ff3c3ffffffffffffdff85f8f2e3ff10310003ffd3000dff81f8f060fb00000003ff80000feffff7fffffecbdabfb77ffdbff30fffc7fffffcc3c018003ffc1070005b43bbb7d84b480000000000000079c7ff9ff8c3c0000000000000000000811f000000000000200000000000001f00000000000000000fffffffffffffffedc2fff47ec29cfff9ffff9ffbe3c000ffc07c008
  | 5, 10 => 0x8810000200000000000000000000000000000000000000000f297bffffbff8effed7ffdd7ffedc0079ffff9ff8e3fe07ffc07fec800000001000000108000000008000000000000000000000000000000ff7bfffd7ff7fffbdeedfbeffdbbfffffffffffffffffffffffffffffb4ffeffffffffffffedbbffffa03007fc7fffffcdffff8003ffff0002020844408208080c21fd47cc2000000000000000000001fc07c000fefffb6effefe82c23fb743ec3fffffffffffffffe3c01fffc1fc1ff0004100ffbfc003c8020110208000000000ff9f0003c000000000000
  | 5, 11 => 0x2108e491000097d2ff8488002e0020006000000001c3ff8000003e00f959f7fffff5f7f3ffcfffffff89b00063fffff043c3ff8fffffff080207bc2ffa6f800400001000000000079c0ff80f80000000000000003108e4d50e9097d3ff85fffffe0030006000060001c3ff81fffffe00180000004e900001004023ffd0001000000006000000000003ffc000fffffffeffffffec1efbf76fc1fffffffffffffffffc1fffffffc1ff07b84d87000b910210001c002000cff81f8f000fb00000003c000000b31fffffffff9fffffaffffffe29b007ffffffff8fffff8ffffffe08
  | 5, 12 => 0xc8401208fff4602000002306000000000000f9f0000000000000000034ffe12fff4f803ca3b254384a5f30ffe00ffe0f803c0180001800070007a02ffb4f803c8020100008000007800ff80f803c0000000000003000a4910a1086d0cc0489410c00000000000000000000000000000000000011001000000000000000000000000000000000000000000000000000040000000000003c002000000000000000000000003c000000b017a3ffdbf10efdeffffdffdfffb007e3fffff04ffffffffffffffff4ffe12ffe4f800623927c38625ff0ffe00ffe0f800001803c180007
  | 5, 13 => 0xf7ffffffbf7fffffffbfdc102ffffffffffffffffffffffffc183fff00000000400000000000002840000000000000000000000000000000fdf8e7910e10f7d3ffdeeffdffdffff86380060073c3ffffffffffff10000000001000000000004100000000000000000000000000000000d9401208fff460211ec8abffff8010000000fff040001e0003ffff00184012007ef460000000036f400010000000fff04000000003ffc100fdf85388fff4736377deeffff7dffff86380fff073c3ffffffffffffc080000f00080013e1043c903e00c000000f00000003e0003c003e00
  | 5, 14 => 0x20000400200000000000000000000000000000000000000000000d00000088f100021004823f991801000000006000000000003f80000d840120835f4600000082247c0000000000001f0000000000007c0008000000f01000013e10e3c90be008000000f00000003e00e3c003e00c080000000000003615e2c90b7c4c000000000000003e07e3c003ec03d784380040073401680c26d401b3ff86380060073c01f81c3ffc13ff087a07fdbd80effeffffdfbfffff007e07ffff04ffffffffffffffffdfff7bbfffff7f7ffdeefffffdf30ffe000ffffc1c3ff8003ffff07
  | 5, 15 => 0xf0ddf7ffbffdf7f7e50ffc57c5cdf0ffffffffffffffe18ffc1fc1cf000400008100003de17e00909fc4000000000000003fe07e00003ec0c084004f8188003fe57ffcd7ffc4c000000f0000003fe07ffc07fec0b6ffffffffff8efcefbffd7fce7fb0ffffffffff8e3c018ffc1fc00f310844910410934254048a412400000000000000000000000000000080000008010000000008200080000000000000000000000000000000310fe4b3fe5f97d7ff848bf93e003007e000fe0f81c3ff8003f83e003f7bfff17ef7ffd3ff85cbff7e3b3ffffff0ffffffc3ff81c3ffff3f
  | 6, 0 => 0x310ce49f8f1897ffffa49bf93e003000600f060001ffff8003f83e000207bc7ffbff8cbc88713d82be2000079c7ff9ff8c3c00703c003e0000000000fa44000000000000000000000000f8000000000000000000da401e0fffffe021004833ffd18010001c0fffffc000000003ffc1003f7bfff47ef7ffc81ef1ffeffe3b3ffffff0ffffffc01ff1ffffff3f0108e4910e10959298000b0028000000000000000000000000000000347be1207e47800002804028401b30ffe000fe0f8000018000180007efffffff242fffdeffb7fe042e7fefffffff000fbffffffffc003eff
  | 6, 1 => 0xfcfff32fffffe03fe3fe7fffffdff0ffe00fffffc03fe1fe3fffffc7b5ffe7ffffff97d7ff9ffffffe5fb0ffe3ffffff83c3ff8ffffffe0f00000002000000000002040000000000000000000000000000000000fffffffffffffdbebbb37f3e6a7fffffffffffffbc3c01803c1800073108f499fff497f3ff848bfb3e0030006000fff001c3ff8003f83e0000000044008000000001100200000000000000000000000000000000c800120801b06021004823c791800000000001f04000000003e7c10000400000240400000000000000000000000000000000000000000000
  | 6, 2 => 0xff7bfff8fff7ffe11ec9e3ffd1bb3ffffff0ffffffc01f81c3ffc13f00000000000000002100001002000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff10001008fff40021000003fb100010000000fff00000000003f80000cfa7bc7ffbff8cbffffffffffff6cf079c7ff9ff8c3ffe7fffe7fef0efbfffff01bbffffffffffc7bfffefffffff01ffffffffffffe7ffff14f84102fe4f800000000438400010f80000fe0f8000000000180000fb111fff11f17ffbdc6fffc7fda9cf001fff01f07ffffe7fffe7fff8
  | 6, 3 => 0x2000804000200000000100000000000000000000000000000000000b017a3fffbff8244440ffc47c409800783fff9ff8200000ffc07c00837fffdffffff9fffffb7dffb7e7f30fffc7fffff8dffff8003f83e07d840124cfff460210449ffffd58010000000fff040000001ffffc100000000004080000000000102000000000000000000000000000000000f27bc7ffbff8cbc98213f0628200f079c7ff9ff8c3c00003c000000801003cf00a100000401fc47c4008000038f000000000001fc07c0009800020851f00000004823efd0000000000001f00000000003e7c000
  | 6, 4 => 0x35f8e5932e1f97d3ff848ff93e0030f86000060f81c3ff8003f83e00ffffffffffffffffffa5bfff3e20ffffffffffffbdffff803ff83e0000000000000000000400884104000000000000000000000000000000110000000e1000011e808bf93e0010000000060000001e0003f83e000080000200080000000004000000000000000000000000000000000034ffe122fe5f8005239247f9525f30ffe000fe0f8000018003f800070000a0000a0080000000000000000000000000000000000000000000f6fffd7fffff8cbfebff7dbafffff0fffc7fffff8c3fe1fe3c183ec7
  | 6, 5 => 0xcb841edf81b87ffffd7fbfd7bfe4cf001fff01f07ffffe7fffe7fff8cff85f8f242ff1021e80bfed3e00cff81f8f000fb0001e003fe03e00c084100ffbfc003fe17e3d92bfc4c000000ff9f0003fe07e3c003ec0080000044080000800703feffe00000000000000000000703fe7fe001f2208444e9208091ef1fffffe321f000000060000001e71fffffe300001007f11f100000401fc47c4000000007f01f000000001fc07c000dff85f8f35fff10210083e47e000cff81f8f01ffb00000003c07c0000006a000ca000cbdabf001b81bf63007e000fe004dfffff003f83ff7
  | 6, 6 => 0x3008e0010e008013e38408b83e003000600006000003e18000183e0004220044408200000691fc6fc61200000000000000000001fc07c000df67be7fffffecbd9ef9ffffffb21f079c7fffffcc3c1e71ffffff3010400000fe540001000003f9500010000000fe000000000003f800000f22184cfbf608281ef1ffeffe320f000000f9f000001e71ffe7fe30d84012082e346001000023fd10001000000006000000000003f8000000000000040000000000020000000000000000000000000000000000ffffffeffeeff90e3ff3fffffe7fffffff8ffe0fb0001ff1fffffe37
  | 6, 7 => 0x4000f8108003fe12418903e000000000f0000003fe00000003e00cfffffaffe6ff10610003e042000cfff9f8ff80fb00000003c00000004f70122f04f000400124400405f00ff8000f80f8000000000000007c080000f0008000a00703c80be00c000000f0000000000703c003e00900002081ff00001000823ffd0001000000007f00000000003ffc000c0000008000000000000200000000000000000000000000000000000cffe5fcfe5aff93ffffffffffff6cff81f8f000fb03ffe7fffe7fef0b4f943ff35ff8240440ffc47c40980f803ff01ff8200000ffc07c008
  | 6, 8 => 0xd844120ffffc603d806833ffd9801000000ffff0403c000003ffc10030000000000000000000000000000000000000000000000000000000dac7be7fffffecbfe97f3fffffe4d0079c7fffffcc3fe07e3fffffc0f4ffe3ffffff827fe7fffcffffdff0ffe3ffffff823fe1fffc1ffecfb4ffe3affe6f800423927c3c425fb0ffe38ffe0f800001803c180007cff85fcf24aff1021401fe47e400cff81f8f000fb0000001fc07c000b01113fffbf50260440ffd47c409800003fff9f00200000ffc07c008b01103ff11f10248447ffcc7fe09800003ff01f00200007ffc07fe08
  | 6, 9 => 0x8000000f01000008407e3c80be008000000f00000000007e3c003e0037bfedf70e1b9fdfffb7dff93e7fffffffff060fbffffffffff83eff8000004f01800000440ffc47c4008000000f00000000000ffc07c000b01103bb11710240400e00000009800003ff01f00200000e00000008b4ffe32affff8004239a647fc25f30ffe000ffff80000180001fc00708001008fbf40020004023efd00000000000f9f00000000003e7c00034fff12affff80242392453a425f30ffe000ffff80000180001800073008e0000e108001238003f912003000600006000000018003f80000
  | 6, 10 => 0xcff85f8f242ff113f1043e943e00cff81f8f000fb003e0003c003e00d084000f8f18003fe17e3ff9bfc4d000000f0600003fe07e3ff83ec0fdffe3a2fe4ff34777deeefdf7dfffffe380fe0ff3c3ffffffffffff0004000f8108003c80703c80be000000000f0000003c00703c003e001f620844fec608081ef1fffffe321f000000fe0000001e71fffffe30b05103fffff50240440ffc7fc409900003fffff00200000ffc1fc0083f2ffcffffff9ffffff5fffffe323f07fc7fffff8dfffff1fffffe30ff731bfffff76a695effffffffbb9f0003fffff042001e7fffffff38
  | 6, 11 => 0xffffffaffffff12733da7ffff3dfffffff8ffffff00001803fffc107fffd5fffb5fff37ff57ffed7ffcdcff81fff01ffb23fe07ffc07fec8cffeff8fee2ffdbfbbf03fbc3bf6ffffff8ffe0ffdfffff03ff83ff7100000000e0000000000003800001000000006000000000000180000cfa2084f408a080a1ef1ffeffe32cf00000f000000001e71ffe7fe303f2ae8444e8288083ff1fffffe323f006000060000001ff1fffffe30d840120ffff46021404e3fffd5809000000ffff04000000e3fffc1000207bc7ffbff8cbfe92519923e2000079c7ff9ff8c3fe00000003e00
  | 6, 12 => 0xffffffafff6ff13ff3fe7ebcffdfffffff8ffe0fb03fe1fe3c183ec700000001000000004004080004000000000000000000000000000000dffc5f8ffffff13ff17e3fffffc4dff81f8ffffff03fe07e3fffffc0dfe61a4ffffe683ffffffffffff6df00000ffff0403ffe7ffffffff014620000fe46000002904438421210000000fe0000000000001800008000000f0000000000003c0000008000000f0000000000003c0000000206bc00ea0e8cbc88200100082000079c00f80f8c3c0000000000000000000f010000000000100000000000000f00000000000000000000
  | 6, 13 => 0xc0001008fbf4002100482192918000000000f9f00000000000000000f19de7ff9ff997ffffffffffffcdf00063ff07f003fffffffffffec809000000408000001ec0abeffe0000000000000000001e0003e7fe008207bc7ffbff8cbcc82f3d028c2080079c7ff9ff8c3c000e3c00000002011c7f31ff800000011002000000001c7f01ff8000000000000000fdffe3f0dfd07fffffffefffffffffffe3f0fff07fffffffffffffff
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x140400c02004006
  | 7, 0, 0 => 0x20110142b0a80a0a5c0501003008010a027702026014040640a005c250442401023008017088080140400c21081c08044050100307c027078040740302802005c110141c00c0a06c01702011068040640a005c080441801017028167020110540400c0a039c080140400c0a050137048110141000c0a009c0803c05010030280e70340c0140b02802005c090200700c06008017
  | 7, 0, 1 => 0x108360780402802005c081040510003008017020110143f0f802005c25044050f4030f00170ec050100302802005c3a020110140400c0a70e42f0100302802005c110140400c020043870dc360780400c02005c080d434010330080170c8110140400c31059c300bc0400c0a0080170200701003008010b9c090b40500c06008017020050100a0b002005c120440501017028027
  | 7, 0, 2 => 0x15c560bc0302802005c12044050104b128027020110104702802155c0804405010540080170d8530100302802005c080445200c0a144507024080144f02802139c08014030284d0080170204c0140412c4a009c490d81e01003028027094410140408c02005c480440411c0a008017020350d04602802005c45044050100a008017020440100302802005c080440510c03028017
  | 7, 0, 3 => 0x20111940400c0a005c5e1900400c0a0080170d81e0100302802005c08104050fc03008017020111700405c0a009c080144000c0a18c0170204c0146212c0a009c61044050100300801702060044050100a009c5f0bc0400c0a0080170dc5e1740400c02005c080445c040030280270240801c4f02802005c5b1680400c0a008017164050700302802005c580140400c06008017
  | 7, 0, 4 => 0x1785d0100302802005c08044051bc04028017020050100318c010b9c080446e0100a0080170206d0140400c6c009c590140400c0a0086b7160690100302802005c080146a010030280271782f01003008010b9c090200500c0618c0170d81e01003008010b9c081a4041a00a008017020670140400c0a005c081684600c0a0080171245e1740400c0a009c080440504003028667
  | 7, 0, 5 => 0x88080144000c21005c080440400c0a144757020111706212c0a009c081a44000c0a008017020111e00400c02005c0801477010030280170207601003028021d5c08044341180a1d00171cc080440500c02005c08044150ac03028297094110903d00c02005c0803c050ac030282971c8070100302802005c08044050401702816702011014040f8021c5c081c01101403028027
  | 7, 0, 6 => 0x20c5e1740400c0a005c08044341180a008757094410143d00c02005c5b0440400c0a208017020810140400c0a009c081b4051fc03028027020112000400c02005c08044051fc03028667020111180302851005c080447e1f41000c0a7020111f00405c0a009c080447b0103e0080170440501023028021adc361e80400c0a00801702005010230080109dc081e40504003028167
  | 7, 0, 7 => 0x448f0102302802005c0d044050100a2388d7120110d0040cc02005c720140400c0a18c017020110140400c8c1c5c08098050100322c017120760100302802005c8a0440500c0a0080170140400c0a22402005c362200400c0a008017020761484702802005c110140400c87008017020112180400c0a009c850bc0400c0a0080170205a0100321002005c4215c2f0100a008017
  | 7, 0, 8 => 0x20110144008c02005c362640400c0a00801715c980100302802005c0804405010030289770bc042580302802005c95020110140400c027020112500302802005c08044050280224c017020110100302882155c082480400c0a008017020260141000c0a005c080440501003028917240080440502802005c720140400c06008017
  | 8, 0, 0 => 0x20aa0140400c0a00801802005288a92a00a00801802011014a7298030080180d8a50140400c0a008018020560440500c0a00850820c57044050100302801802011014a400c0a008018020110140428c0a0080180200528804284030080180dc42020112800400801827c110140400c0a0080180209e0440501017028018020110140400c0a2740180240527003028020049b80209a0140400c0a008018020110542b01003028018
  | 8, 0, 1 => 0x2bc080447e0100302801810808104050100a008018088080140400c0200427810808044050100a008018020112b80400c0a008018108080440402802004ad8020052883d00c0a008018020561740500c0a00801820c08044050104f028018120110140400c0a008758020052880400c0a1d00180200c23c0400c0a0080180bcac0109c00c0a0080182ac08044050100a00801802011014040f80a008018020112801000c0a008018
  | 8, 0, 2 => 0x178112e40400c0a00801820c3710808044050100181c8110140400c0a008208020052880400cb8008018020b70140400c0a0080180209e04405010030280e82d8560440500c0a008018020052880400c0a084018044050109600c0a008018044050109c00c0a008758020112d40400c0a00801802005288040a80a008018020110140400c31058b482cc1101403028022c801802011014b101003028298044050109c00c0a004b08
  | 8, 0, 3 => 0xdc56044052700300801820c08044c40100302801830c110140400c0a008c28048110140412c0302802810808044050104a00801830408044050100a008018020110140430003008018020110140400cbf00801820c080440504003028018124080440529c032f80282f408044050100a00801802011014a700cbc008018044052c4042700a004bb8044180109c00c0a008018020110140400cba0080180b4110140413c0a008018
  | 8, 0, 4 => 0x1080804405010310080180208f2880400c0a00801834c08044050100a008018120110d00402802004d28344080440501003028168020561d80500c0a008018020d00140400c0a00801804405010cf00c0a008018338cd0140400c0a008cc8020110140400c0a32c01812437020112800400c028020110140400c02004ca8324080440501003028028020112800400cc8008c78020c60440500cbe00801802011014a700cc5008018
  | 8, 0, 5 => 0x44340109c02802004d283740804405010030080180dc0804405010030088d80dc080440501003008298020110140400cdc0080180440536c0400c0a0080180dc080447e01003004da8020560440500c0a144018364110140400c0a00801820c112800427003028018360080440400c0a008018120110144600c0a0080180209e014d701003028018044050100335802004d580200c0140400c0a238018020050100302802004d48
  | 8, 0, 6 => 0x88080140439802004e58020110140400c8b004b08020410900400c0a008018020110140400c0a390018044051189c00c0a008018020110900400c0a0080180440538c9c00c0a008e280c8790140400c0a0080180202f3840400c0a008018124081040501003028028124080440501003028028124080440400c0a008ad80dc08044e0010030080180201137c0400c0a008018034112800402802004de8020350140400c0a008018
  | 8, 0, 7 => 0x10856044052700a008018124080440501003128028020110144000c0a0080182cc1101403028023b8018020560447d00c0a008ed8020ec0140400c0a008018020110140400c0a008eb81080804405010020042e83a8110140400c0a3a4018124830dc0804405010038044e80140400c0a00801815811014030280200428820c080440501003320c7839c08044052c40402801802011014040f8020042e8020112200400c0a008018
  | 8, 0, 8 => 0x20560440500c0a008f681240804405010030c402802011014043d4f4008018020112800400c0a3cc018020110147f00c0a008018020110140411cf2008018020052880400c0a238018088082800400c02004e5803483044050100a004de8020110140400c0618c018020f10140400c0a008018020050100301802004278020111f40400c0a008f08124420201128004028028020113bc0400c0a0080180d8110140400c0a0088d8
  | 8, 0, 9 => 0x20fd0140400c0a00801810808044e00100a00801820c08044050101702801810808044050100a0082980240801403028020042780dc0804405010030084e8020110140400c0a008fc83ec080440501003028018020112800400c0a0080e8020113e80400c0a0080183e4080440501003008c78020f80140400c0a008018338052880400c0a008018020560440500c0a18c018020112802b00c0a004f78020560140302802004278
  | 8, 0, 10 => 0x21090140400c0a008018020052880400c33008018020110150800c0a0080181248310808044050100a841c084180400c0a008018021050140400c0a008018410080140402903005028021010140400c0a008018048052880400c0a008018400110140400c0a0080180dc080440518803008018174050109c00c0a008018020113fc0400c0a0080183f80804405010030080180dc320440501003008018020110d00400c0a008758
  | 8, 0, 11 => 0x2011010030280200518820c080451701003005168454052880400c0a008018450080140400c0a008018021130140400c0a0080181080804405010f2008018020111f9120100302801844408044050104b028028020110140412c0a0091080201143c0400d0e0080180210d0140400c0a008018020114300400c0a0080181240804405010030082e820c220200501003004e580c8110140400c0a058b480210b01003028020050a8
  | 8, 0, 12 => 0x20110140400c0a48c018020110140400c0a00922802011014044840a008018094110140400c023d8d5815c2f0140400c0a008018480110140400c0a008018020110140400c0a47c01830c110140408c0a0080182d8110140400d1e00801820c0804405010030280e802011474052a40a008018020110140400d1c0051b8124560440527003028028410370200501002005028468110140400c0a0080e80440500c0a008ee005198
  | 8, 0, 13 => 0x3411014042e002004de80dc0804407010030080181d8050109c00c0a008018020110152901003028028124080447e01003028da8044050100302802234d5810808044050100a0084e8020110140412c4a0091080340804405010b80080182d80f0140400c0a00801802011014e300c0a4a0028020110140400c0a009278020110140b00c0a008018498080452501003008018490110140400c0a008018020110140400c0a0086b8
  | 8, 0, 14 => 0x20110140400d31008018020052880400c0a008758020114c00400c0a00801810808044051880a0080182d8110540400c0a008018020110140400d2f0080184b808044050100332002804405010030281b004288020052880400c0a004b08020560445c00c0a0080180dc080445200c020052d810832044050100a0080184b008044054ac03028018020110140400c0a0092a812408044e001003028028020792800400c0a008018
  | 8, 0, 15 => 0x24080144f028020049b8044050113b00c0a008018020560440500c06008018020560453a00c0a0080180341123c0402802004de8020113804000c0a0080181240804405010033c80280dc0804405010e6008018020114e40400c0a0080184e02202005010030080180201114847028020052d84dc110140400c0a00801802011014a94d80a00801802011014044d403008018020110100302802005348020114cc0400c0a4c8018
  | 8, 1, 0 => 0x510110140400c0a0080180200550c0400c0a008018020110140400c0a00942802011014a700cbe008018020115040400c0a008018020112800400c0a40c0180447d0109c00c0a008ed820c081e40501003028018108080440501002005408020110142b0a80a004f784fc080440501003028018020110140400d1c0053e80dc0815805288030080184f4080440500d3c008018020560440500c0a00820815c2f2b00400c0a008018
  | 8, 1, 1 => 0x20110141000c0a058028020110140400c0a538018020342880402802004d280dc08044a001003008018020112800408c0a008018020560454d00c0a00801810808044070100a00801820c08280a20100302801853008044050100a0080180dc0827805010030054b8020115280400c0a008018178115240400c0a008018020110140400d48008018020110140451c0a008018020111f40400c0a009468021450140400c0a008018
  | 8, 1, 2 => 0x20410140400c0a008018020110140400c0a008018020110100302802004ad8020112800400c0a058b48548080440501003028018020112800411c0a008018020560781100c0a008018021510140400c0a008018021500140400c0a0080181240804405188030280280440427003028020054f8020052884600c0a008018044050109c00c0a18c018014042700302802004278020111f405040030280281080804452028020052d8
  | 8, 1, 3 => 0x21580140400c0a008018020111700400c0a1980180201155c0402802004d2804405010030280255801820c37020110140400c018021550140400c0a00801820c0804405010230280185500804405010f500801854c080440501003028018020110141000c0a004b08094560440500c02004d5812504020050100a009028104050100302802004de815c080bc0400c0a00801803411014040288e004de80240801c0400c0a008018
  | 8, 1, 4 => 0x10808044a00100a00801812408044070100302802820c080440501047028018020110601000c0a008018020052880400c0a00850810808278050100a0054b8020560440500d1c0055f80215e0440500c0a574018020110140457003008018020110140400c4a0080180201156c0400c0a008018020110104702802004d28020110140400c0a0095a802011170e301003028028564110140400c0a008018020110140b00c0a0088d8
  | 8, 1, 5 => 0x5a808044050100302801804405011695a00a0080180445c0109c00c0a0080180dd67044050100300801810808044050100a009668020110140400c0a59401804405010f559002004288020110140400c310080180dc2d04405010030080180201158c0400c0a008018588110140400c0a008018020110156100c0a0080181201101003028020052d8124080445200c0a0092d8125600440501003028028020110140400c0a0f0f68
  | 8, 1, 6 => 0xd8055c00400c0a0080185bc080440501003008018120560440500c0a00801820c4202011014040280181c8052880400c0a008018020110143d08c0a0080181240815805288030280280dc0804405010031d0018020110140400c0a0096e8020111f40501017028028020110140400c0a0096d85b0110140400c0a0080182d8052880400c0a008018020110156b00c0a0080180dc08044052a4a80080181240804405010e6028028
  | 8, 1, 7 => 0x12408044a0010030280285d80d044050100a0080180440501003008010a0e580209e0140400c0a005758020352800400c0a0080181240827805010030294b8044050117400d73008018021720140400c0a0080180dc080440501003084018158110149c00c0a0080180440501003008010b8de80dc052880427003008018044050109c00c0a008208020410140400c020042e8020110140400c020042e85c4ea0440501003028018
  | 8, 1, 8 => 0x78110109c00c0a0080185f00804405010030080180217b0140400c0a0080182cc1128003028023b80180217a044050100a004bb80205603c0500c0a008018020110140400c0a0088d8020110140400c0a008298020111f80400c0a004da81080804405010a10080180454d0109c00c0a0080180c0110140400c0a0080180217904405010030280285e008044050100a0080181082d044050100a008018020110140400c02005778
  | 8, 1, 9 => 0x10805288042700a0080180e4110140400c0a00801802069010030280200427860c050101d00c0a0080180207d2880400c0a008ed8608110140400c0a0080180201145c0400c020058183a8110140400c0a6000185fc110140400c0a00801812483020110140400c0a8020115f80400c0a008018020110140400d7d00801820c080d4050100302801810808044050f40a008018020560441500c0a0080180d8110140400cb8008018
  | 8, 1, 10 => 0x20c080440510003028018020052880400c0a18c01802011014e300c0a0098b8044050109c00d1c0055f8020116280400c0a008018624080440501003028028044050118800c0a008018020052880400c0a008f6802011014b10100a2ec0e80d81123c0400c0a0080180d9870140400c0a008018020110140400d86008018020110140400d850080180201145c0400c02005848020560440500c0a0f0018020110140400cf2008018
  | 8, 1, 11 => 0x20116440400c0a008ed812408044052a4a8028028108080448f0100a0080186400804405010030080180c8110140400c0a008018021132800400c0a008018178110140408c0a0080181240804405010a100c0280dc5e0458f01003008018020560440500c0a0098e8020110140400c0a0084e80240801403028020058d81c811014043d403008018124080458c010030280280dc0813005010030080181242d0440501003028028
  | 8, 1, 12 => 0x20110903d00c0a008018178116640400c0a00801802011014b10100a0059880205665c0500c0a00801812408044050f40302802802056044053d5640080180201114803028020058d8124080440501003028748044050109c00c0a1980180dcce0440501003008018658110140400c0a008018654080440501003008018020110146200c0a008018020350140400c0a1d0018021940440500c0a009938020110159200c0a008018
  | 8, 1, 13 => 0x2011015a000c0a00801867c08044050100a00801804405010032e002004d581240804405010030282180202f6780400c0a008018000360780400c0a0080172cc11014030280267401812405288042700302802812408044050102a028028020112800b00c0a008018020116700400c0a008018094410140400c0a0080180201166c0400c0a008018094110140400c3c004d58020563340500c0a008cc8020056680400c0a008018
  | 8, 1, 14 => 0x24370200500c020049b86980804405010030280180dd150440501003008018020116940400c0a0080180c8110140400c31008018020790600400c0a00801820c0844c050100302801820c08044050104b02910869008044050100a00801830c410140400c0a008018020cd5340400c0a008cc8020110146200c4a008018020110140400c0a68c0181240804405010032e00280dc120440501003008018689a10440500c0a008018
  | 8, 1, 15 => 0x20116ac0400c0a0080180209e04405010030c40180448f0100302802004d580201114803028020052d810808044050100a23801802011014046a80a0080180200f0140400c0a004b48580110140400c0a008018020110144000c0a084018164050100302802004288044056a5a800c0a0080180205c2880400c0a008018020110140400c0a69c0180201101c0400c0a008018044050109c00d1e0080181085e0458f0100a008018
  | 8, 2, 0 => 0x2011015b600c0a00801802005010f500c020042786d5b40440501003028018020110140400c0a6cc018020110540400c0a004b486c8110140400c0a0080186c40804405011b002801802011014046bc03008018020110140400c0a6b8018108ce044050100a0080186b408044052a40a00801820c080440502c03028018454110140411c0a008018020111f80400c0a008758124080448f01003028028020056b00400c0a008018
  | 8, 2, 1 => 0x6ec080440501003008018108080440501033008018020110140400c0a009ba8020110540400d1e008018020110140400c0a009b9802011015b800c0a0080180dc3660c050100300801802056014a200c0a0080180dc080440501003008758020052880400c0a0082082cc1101403028026dc01802011014043980a0080180dc080440501003004b0802011280a700cbe008018020052880400c060080180200f0140400d1e008018
  | 8, 2, 2 => 0x4405011c100c0a0080180200f0540400c0a008018020110140400c0a0081380214d2880400c0a008018700080440501003008018020116fc0400c0a00801810915044050100a008018094110140400c020042e812408130050100302802802011015be00c0a0080180dc08044052c404004bb80dc0804418010030080183a8560440500c0a6f4018088720140400c02004e58020116f00400c0a0080182d8110142b00c0a004f78
  | 8, 2, 3 => 0xdc0871c0501003008018020110600400c0a058b48178080440411c0a008018020111f84600c0a0080181240804405010030288e830c110140400c020042e8020117180400c0a008018020412800400c0a008018020112800400c0a008018020110140400c0a009c581245e0458f010030280280209e0140400c0a0054b80244202005028020049b8021c40440400c0a00801804405011c300c0a00801802011015c200c0a008018
  | 8, 2, 4 => 0x20110140400c0a230018734080440501003028028020112800400c4a008018120110d00400c0a00801810808044050100a004b08178117300400c0a008018020110140413c06008018020110140472c0a00801815c560440500c0a008018044050109c00c0a0098e8108080bcac0100a008018020110140400c0a009ca8020110140400d1c005c98720080440501003028018020110d00402802004ad820c080440529c032f8018
  | 8, 2, 5 => 0x1240804405010030cc028020350140400c3300801802011014047440a008018020110142b00c0a008298334050109c00c0a008cc8468110140400c0a008018020990440400c0a008018021d00440400c0a0080181241204405010030280281083660c050100a0080180200573c0400c0a008018020560440513c0a008018094052880400c02004d58044050109c3d564008018021ce0140400c0a0080180dc080440511803008018
  | 8, 2, 6 => 0x20110140400c0a009d98020567601100c0a0080180201175c0400c0a008018021d60140400c0a0080182d811014b101003028018030050109c00c0a0080180201123c0b00c0a0080180dc420205604405008018754110140400c0a008018021d40140400c0a008018020052880400d1c0055f874c08044050100a00801810808044180100a008018020112800400c3100801820c081040501003028018748080440400c0a008018
  | 8, 2, 7 => 0x20110140400ddc008018034110140400c0a0088d8020110140428403008018020110140400ddb00801820c420201128004028018020052880400c0a198018020116300400c0a008018124080bcac010030280280205a0140400c0a0080180b4110140400c0a00801820c0804405010031280180205a0100302802004ad802056044c400c0a00801802011014043d403008208020050100302802005da8020050106802802004278
  | 8, 2, 8 => 0x1243660c0501003028028020110140400c0a1d0018020110140411c0a0085080dc08174050100300801830c080440501017028028158112809c00c0a00801802011148033c8020052d8020350140400c0a00875802011014a92a00a00801810808044051180a008018020110140400ddf008018020112a4a802802004ad8020117780501003028028108080440538c0a008e28020110140400c0a774018020112800400c020042e8
  | 8, 2, 9 => 0x20112800400c0a0088d8020112800400c0a00829802011014047980a008018794110140400c0a008018020560440500cc8008c78020110140b00c0a2380180201101c0400c0a0084e8020110140400c8c0042e8014a20109c00c0a00801879008044050100378c01812408044052c404028bb8124080441801003028028020110140400c0a009e2830c052880400c0a009e18020410143d00c0a008018020057800400c0a008018
  | 8, 2, 10 => 0x5e1740400c0a008017044057ac0400c0a0080180dc081d8050100300801802011015ea00c0a008018020350d00402802004d2812483020112800400c0a810808044050100a00850820c560440527003028018020110140400c0a009e98020110140400de80080180dc720440501003008018048110140412c0a009108020052880400d1e008018020110140400cb8008018020110140400c0a009e78020110140400c0a084018
  | 8, 2, 11 => 0x20110140411c0a144018044050109c13c0a008018020110140400c0a7c8018020111f80400c0a005f1820c08044e00100302801820c0804405010030288d820c080440501003028298020560440505c0a00801804405011f000c0a009e18020117bc0400c0a0080187b8080440501003028028020560440500c0a009ed820c085e4110140400c0a8020110140400dec008018020112800400cf200801812408044340100a008d28
  | 8, 2, 12 => 0x20052880400c0a0098e80204c0140400c0a0080187d4110140400c0a008018020112806200c0a008018020640140400c0a008018020560451700c02005168020117d00400c0a00801802011014b10100a005f38088081580500c02004e5810872044050100a0080181244202056044050280280dc110140400c02004288020112800400c0a0084e804405010230280200428802011014040640a004b08108b6044050100a008018
  | 8, 2, 13 => 0x2011014040a80a00829802011015fe00c0a00801820c3204405010030280187f408044050100a008018020117f00400c0a00801810808044050100a14401802005288043d564008018020110140400c02005fb8178410140400c0a00801802011014a97e80a0080182cdf90440500c0a008018044050409c00c0a008018020a06680400c0a0080181781163c0400c0a0080187e0080440501002005f7830c110140400c0a009f68
  | 8, 2, 14 => 0x124081d805010030280280240801403028020049b881808044050100a00801820d04020050100a00502812437044050109c00c028022050140400c0a008018020110140400c0a810018108080447d0100a008ed802011014b10100a006038808080440501003028018048110140400c0a008018020113800400c0a084018020118040400c0a008018124b60440501003028028020110140400c0a006008178117fc0400c0a008018
  | 8, 2, 15 => 0x20110140400c0a838018020110140400c0a00a0d80dc080445c0100300801802011014048300a0080180201182c0400c0a008018020110140400c0a82801812408044050100302851802056280a200c0a00801802011014e300c0a00a09810808044050100a18c0181c8110144000c0a008018020118200400c0a00801810808044050100a008f680201123c0400c0a0088d802011280043980a008018020110140400c0a006078
  | 8, 3, 0 => 0x2011014b10100a004bb8020110600400c0a008018020560440500c0a40c018044050109c00c0a00a1380d9830140400c0a008018848080440529c03008018124110140400c0a0082880209e2800400c0a0054b8020110140400c0a008758020110140400c0a1980e8022110140400c0a008018044050109c05c0a008018020110140400c0a004b08020111f80400c0a840018178110140400c020042e84100801404028020060f8
  | 8, 3, 1 => 0x864088600501003028018021c70140400c0a008018124080140400c0a008278044050ac9c00c0a004f7885c110140400c0a008018045170109c00c02005168020110140400c0a2388d80206d0140400c0a0080e8020110140400c0a8580180dc081581101403008018020111f40400c0a00a158020560440508c0a008018020110144000c02004d580dc08044050100300820802408014030280200614812442044050109c028028
  | 8, 3, 2 => 0x44050100a00801884de8088080440510003008018020110600400c31008018022200140400c0a0080180dc080781101003008018020110144600c0a008018020111180302802004ad8020052880413c0a00801887c110140400c0a008018044050121e00c0a00801887408044050100302801802011014048700a008018020560440500c0a058b480dc080454d01003008018020110140400e1b00801802011014048680a008018
  | 8, 3, 3 => 0x2011014043980a0840180204c0146200c0a00801802011280042840300801810808158110140a008018020111480302802006298044050122800c0a008018020110141000c0a004f78094110140408c02004d58046270140400c0a0080180b4112800400c0a008018898080462501003028028108080440501006008018020110542b00c0a004f78020cd0140400c0a00a24802223044050100a009108888080440501003028028
  | 8, 3, 4 => 0x20110140400e32008018124080445c010030280280440501003028021ac2880340c0140402802004de8044050123100c0a008018044058c00400c0a0062f8020118b80400c0a008018020118b40400c0a008018020110140400c0a00a2c81e4050109c00c0a008018020112800400c0a1d00180d81e0440400c0a008018020110140400e2b00801802011280a92a00a00801830c110140400c0a00a2a80d9830140400c020042e8
  | 8, 3, 5 => 0x12437020052880400c028020110140400c0a8e0018014a20100302a37008018048110146200c0a00801812408044050100301802820c08045de0140400c0a88d8088d405010030080180200f014b101003028018020112800400cb8008018020110163400c0a0080180205d0140400c0a008018120111f80400c0a008018020112800400c0a084018020118cc0400c0a00801820c2d0440501003028018280a20109c00c0a008018
  | 8, 3, 6 => 0x2011014049080a008018020110140405c0a004f7802011014a9284a8008018904050100302a40008018020760140400c0a008018020110144000c0a008208178118fc0400c0a008018178080440400cf20080180dc110140427003008018044050109c08c0a008018020110140400c0a2c1108020110140400c0a00a3e8044050123d00c0a008018020118f0048ec0a0080188e8110140400c0a00801802011014043d639008018
  | 8, 3, 7 => 0x20119280400c0a008018022490440500c0a008018410080140402802006488044050124700c0a6f4018044050100302802004288094110900400c02004d58020110680400c0a0080180204c2800400c0a0080180202f014043980a00801891808044050100302a458020111ec0400c0a00801810808044050100a198018020119100400c0a008018124080781101003028028020110164300c0a008018044050109c00c0a058b48
  | 8, 3, 8 => 0x201101003028020054f802011014049440a008018020410140400c0a008f680209e0140400c0a0065080224f044052a00a008018020560440512c0a009108020110140400c0a93801810808044050111e0080180209e0140400c0a0064d80202f0440400c0a008758020110142b00c0a004b08108c3044050100a009e18020052882b00c0a004f78020530440400c0a008018930080445200c0a0080180200592c0400c0a008018
  | 8, 3, 9 => 0x22560140400c0a0080180dc083340501003008cc8020110141005c0a008018124480440501003028028020110140400c0a954018120350140400c0a00801820cce04405010030280182d8110140400c0a008298178360bc0400c0a008018020110140400cf2008508020110140400c0a00a548020110140400c0a94c0181080803c050100a00801802011014049480a0080180dc0804405010030098e8048112800400c0a008018
  | 8, 3, 10 => 0xd9832800400c0a00801820d150440501003028018020110140400c0a970018020112800400c0a0087580225b0140400c0a008018020119680400c0a008018020111f00400c0a0080e8020110140400c0a198b48020110140400e5900801820c120440501003028018022580440501003028018044240109c00c0a008018124110140427003028028020110140400e57008018020111ec0400c020042e80201123c0400cb8008018
  | 8, 3, 11 => 0x20110900400c0a0f00181240804405010030283c8020114e80400c0a008018020110140400cc800a608020110140400cb8238018020110140412c0a199108020110140400cf2144018124080441501003028028020110140400c0a97c01897808044050100302802802011280b10100a004bb8020760140400cf2008018020110140400c0a00a5d8020111700400c0a008018044051009c00c0a00801820c090200500c0a0049b8
  | 8, 3, 12 => 0x201e0440400c0a00801810808158112800a008018020790141000c0a008018020110140400e67008018020ac2600400c0a008018044050126600c0a00801820c37020560440500c018020115340400c0a008018020cd0140400c0a00a658020111480511c0a00801899008044050100300801898e62044050100a0080189840804405010030080180201114803028021412d810808030050100a008018020110140400c0a008208
  | 8, 3, 13 => 0x2011014049ac0a0080180dc080440504003008018020110140400e6a0080180201114803028510052d89a4080440501003028018020110140400d1c0055f80205d2800400c0a008018020110140400c0a208018020110100302882004ad8094110140400c02004d580dc08044050104f00801820c0804405118030280189a0080440501003028b48020110140400c0a1d07580d81e0140400c0a008018020111f805010030280e8
  | 8, 3, 14 => 0x44050109c00c0a008018044042700302802004ad8020110140400c4a198018124ea0440501003029bd8020242880400c0a008018020762800400c0a00801802056044e000c0a008018020790140405c0a00801812408014a20100302802820c0817405010030280180dc11280042700300801802011014a99bc0a008018020110141000c0a058b4802011014049b8030080189b4110140400c0a0080180da6c0140400c0a008018
  | 8, 3, 15 => 0xc8560440500c0a0080189ec080440501003028028044050109c00c310080189e8080440502802006798044050127800c0a008018044050127700c0a00a768020110140400c0a9d4018020110100302851004d28020110100302802006748020119cc0400c0a008018020110167200c0a008018044a00100302802004288020111706200c0a008018020110140400c020067182cc0528803028023b8018020119c00400c02005168
  | 8, 4, 0 => 0x2011014043980a008208022810440400c0a008018020cd0140400c0a008cc8a0008278050100302801802011014403d4030080189fc0804405010030080189f8110140400c0a008018044050109c00c020042e8020110140400c0a0098e84100815805028020050280dc08044050ac03004f7812408044c401003028028020110140400c0a058b08020110140400c8b008018020110140400c0a00a7d89f0110140400c0a008018
  | 8, 4, 1 => 0x2011014043d6850080180dc080440501023008018020111f87d01003028b48020110140400c84008018124220200501003008e58020110100321002004ad8021133100400c0a008018020112800400c0a00820802011a100400c0a008018a0c080440501003008018020410140400c02004e5802011014b10100a0068280200f0140400c0a00829812483044050109c00c0a810808044050100a0080e80b4110140400c0a18c018
  | 8, 4, 2 => 0x44050129000c0a008018020110168f00c0a00801802011a380501003028b48a34080440501003a300180da8b0140400c0a008018044050109c6bc03008018178081740400c0a008018020110140400c0aa28018020110168900c0a008018022880140400c0a0080180201101404028020068780b4110140400c060080180dc080440501003058b48020110140400c0a00a8681202f0440400c0a00801820c081581101403028018
  | 8, 4, 3 => 0x20052880400c0a0084e8020050100302802006938020110142b00c0a006298020052880400cf2008018020110141000c310080180240801403028630049b8020110140400e92008018124080440501003029038044a00109c00c0a0080180201101404a440a00801802011090a701003008018020590140400c0a008018020110142b00c0a0061480200510003028020049b830c110140400c0a0f0018020110141000c0a008018
  | 8, 4, 4 => 0xa68360140400c0a00801802011a640400c0a008018020110140400c0a00a988020072880400c0a008018020cd2800400c0a008cc8044050f49c00c0a0080180201145c0400c0200516802011014041a00a008018120110140400c0a1d0018a5c08046960100a008018108080d4050100a008018338560440500c0a008018020052886200c0a008018020110140400c0aa540180201101404a500a0080180d8080140413c0a008018
  | 8, 4, 5 => 0xa74080451701003008018020110140400c0a058b480dc0804405010030080180dc080440400c02004ad802011a700400c0a0080180d81e60c0400c0a0080180202fa6c0400c0a008018
  | 9, 0, 0 => 0x20110140400c0a00801a92437020110140400c02006a39020110140400ea202802006408014a20100302802005109020110140400c0a00801a86437020110d0050100300801902011016a0010030280200669f020560440500c0a008019044050109c00cc802802006408278110142b010030280190dc08044050109c00c02006411148050109c00c0a00801912408334110140400c0a00a4080440501003028020053e90202f0140400c0a0080139669e020110140400c0a008019
  | 9, 0, 1 => 0x201145ca00100302802006408044052c4a90100a008019020cd044050100302802332408045832800400c0a00801908808158110140302802006408158110140302802004bb9000420201101404028020060080440501003a9c0a008019020110140400c0302802006408a98110140400c0a0080190201101404a94030280200640804405010030cc02004d290dc080440501003008013324420201101404028026f40190345e0440501003028020064110140427003028020054b9
  | 9, 0, 2 => 0x20110140400c0a00801ab6408044054180400c0a0080190200c044050100302802006408044050100302802004289020111700501003028020064080440501003028020052d9020112800412c0302802006408044050100302802ab001910808044050100a00801aae6aa020110140400c0a0080190201101404aa403028020064081581101403028020059390d811014042700302802006437020110140400c02004b49aa008044050100302802006507020112800400c0a008019
  | 9, 0, 3 => 0x10808044340140402802006408044050100302851008019020110140400c0a0080130a44202011014042700a008019020110140400c0a00801ac6442020112800400c0a008019020110140400c0a00801ac2437020110140400c020049b9020110140400c0a00801abe697020110140400c0a0080190207e014a20100302802006408044a00100302802004da902011ab805010030280200645e020112800400c0a008019020111f40400c0a008014b644910808044050100a008019
  | 9, 0, 4 => 0x49020110140400c0a00a049020110140400c0a00a459ad008044050100302802006483020110140412c03028019000080d4050100302802006008044050100302802acc019124080440501003028026f640804405ac80400c0a008019020560440563c0302802006442020110140402802004cc9020560440500c0a0080157e40815811014030280200516920c08045170140400c0a0064080440501003028021d4d2920c08045830140400c0a0064080440501003028020040e9
  | 9, 0, 5 => 0x12408044050100302802aae408044050100302802005f1920c42020110140400c0a0064080454d0140400c0a008019020110140400d1c32002006408044050100302802006b7920c0804405010030280136a442020110140402802004b4920c5e020110140400c0a0064086d0110140400c0a008019000080442401003028020062b6020110140400c0a008019020110140400c0a00801ad6408158111f40500c0a0080199e808158110140302802006408158110140302816008019
  | 9, 0, 6 => 0x2cc0804405010030280200640804405010030286300801912408044050109c00c0a00a408278050100302802004e59044050109c00c0a00801356408044a029c0400c0a0080190201e044050100302802006408014a2010032a00a00801910808044050100a0080126e400020110144000c0a008018000b30440500c0a008ee006049124080440501003028029020052880400c0a00801ae6408014a20100302802ae001991849020110140400c0a00a408044052880400c0a008019
  | 9, 0, 7 => 0x2011014a700c0a2f8020064090200501003028020049b9020112800400c0a590020066c0020110140400c0a008019afc08044050100302802006408044050100302802006be912408044050100302802332437020110140400c023b8019020110140400c0aaf40200640815811014ac00c0a008019af008044050100302802006408158110140302802004e2912408044340140400c0a00a408044051180302802004d29aec0804405010030280200640804405ae80400c0a008019
  | 9, 0, 8 => 0x21a10440501003028020064080466c0140400c0a008019021130140400c0a009bd006408044050100302802006c69020110140400ec502802006422044050109c00c0a008019044050109c00c0a008012ee48302011014a7010030280190dc08044a00100302802006449020110140400c0a008b4902056044052a40302802006408044050100302802b10019b0c08044050100302802006408044050100302802006c2920c08044050ac0400c0a006408044050100302802b04019
  | 9, 0, 9 => 0x20110140400c0a02802006449020110140400c0a0089b9020110140400c0a0f001356408014a22c40400c0a00801979037020110140400c020066cc020110140400c0a0080190000844c05010030280200600804405b2c0400c0a00801900008044050104b02802442008044050100302802006ca9020110140400c0a00801b266c8020110140400c0a008019020110140400cd602802006408014a201003028020050290201101404b1c0302802006408044052c40400c0a004f79
  | 9, 0, 10 => 0xb4408044050100302802006408014a201003028020054b910808044050100a008ee0064830dc080440501003028019000080440502c0302802006008044050100302802006d09020111f40538c0400c0a00a40804405b3c0400c0a00801902011014e3010030281600a6ce124080440501003028029b3408044050100302802006408014a2010033200a008019020110140400c0a00801466483020110140400c0a59001902052014a2010030280200640804405a6c0400c0a008019
  | 9, 0, 11 => 0xdc080440501003008013de472044050100302802004e59b500804405010030280200668d020110140400c0a0080190440563c0427003028020064110140427003028020055f9020110140400c0a058012d241101404270030280200516939c080440501003028020064090dc0804405010030080190201101404b4c0302802006408044050100302802006d290219415811014030280200640804405010031280a0080190dc08158110140400c02006408334110140400c0a008019
  | 9, 0, 12 => 0x20c080440501003028be0066da020110140400c0a00801909408044050100300801356408b64110140400c0a00801902011b60050100302802006408044051180400c0a008019020110140400c0a00801b5e4080440538c0400c0a008e29410080140400c0a0080140a408b58110140400c0a008019020110140400c0a00801b56408044050100302802840019020110140400c31028020064080440538c0400c0a004b0910808988110140402802006411014042700302816008019
  | 9, 0, 13 => 0x2442020110140402802006411014ac0109c00c0a00801920c0804405010036c00a006408044050100300801354e59044050109c00c0a0080138a4000dc08044a001003008018108081581101404028020064080440501003028020042e902011b780501003028020064080440543c0400c0a008019124080440501003028023ba408044050100302802006dd90201101404b700302802006408044050100302adb008019000080440529c032f802006008158110140302802004c79
  | 9, 0, 14 => 0x1080804405a5804028020064080447d0140412c030280294f4080440501003028020066e0020110140400c0a008019044052a4042700302802006400020410140400c0a0080180000804405010030280200600804405010e600c0a00801902011474050100302802006400020110100302802004ad84103602005010030280200640804405010f500cc8008019020110140400c0a009bd0064080440501003028020050a910808044050100a008013de437020110140400edf008019
  | 9, 0, 15 => 0x30c08044050100302802786400020110140400c4a00801802011016e60100302802006449020110140400c0a008019020110140400c0a00801b96408044050100302802006e49020110140400c0a00801b8e448020110140400c0a008019020560bc11014030280200640020c37020110140400c018918080440501003028020064080440501003470020055f9020110140400c0a00801b8a411b84050109c00c0a008019020110140400c0a00801aae408014a20100302802004d59
  | 9, 1, 0 => 0x804405010030c402006008158110140302802004ed9020110140400c0a19802006408044340140400c0a008019044050109c00c0a0080137a449024080440501003028029020110140400c0a00801bb24080440501003bac0a008019020110140400c0aba80200640804405010034d80a008019020110140400cf2028020066e912408044050100302802902011ba005010030280200640010808044a00100a008018020112e4050100302802006408044050100302802006e79
  | 9, 1, 1 => 0x89849020110140400c0a00a4085e8110140400c0a00801902011281060100302802006422020052880400c0a008019020112800400c0a008014b645e0201145c0400c0a0080190201138405010030280200640804405bc00400c0a008019124080440501003028023de52c020110140400c0a008019bbc08044050100302802006408044050100302802006ee9bb449020110140400c0a00a408044341f40400c0a008019020110140400c0a00801a8e408044a0012a900c0a008019
  | 9, 1, 2 => 0x20110140400c0a4a002006400020110140400c020042e80201101404be4030280200640804405be00400c0a008019020110140400c0a00801bde40020c420201101404028018020110140400c0abd802006408044050100302802006f59020560440500d1c0280200640804405bd00400c0a00801912408046f30140400c0a00a4b302011014a700c0a00801902011014d70100302802006408044050100302802004b4902011016f201003028020066f1044050109c00c0a008019
  | 9, 1, 3 => 0x22fd044050100302802006408046fc0140400c0a008019044050109c00c0a0080131e4081e4110140400c0a00801920c080440501003028014b640012408044a001003028028020560440500c0a0080178640815811014a000c0a008019000560440527003028020060080440501003028020049b90201101003028020052d34a408044050112b00c0a008019020110140400c0a00801bee408046180140400c0a008019020110140400c0a008b2006408044050100302802006fa9
  | 9, 1, 4 => 0xc0037020110140400c020064081f4052880400c0a00801904405010f500c0a008010a2400020110140400c0a0088d8000080440501003028020a62ff020110140400c0a008019000080447e010030280136a00804405010030c402004b492ccea044050100302802006408044a02880400c0a008019020110140400c0a00801bfa408044050104b028020051090dc080447e0140400c02006411014049dc9c00c0a008019094081581101403028020066ce020110140400c0a008019
  | 9, 1, 5 => 0x2011014040a80302802006408044050101d00c0a0080190205627811014030280200640012483020110140400c0a802011017030100302802006408046ba2800400c0a008019020110140400c0a0f0020064b3020112800400c0a008019020110140400c0a00801c0a437020118d40501003008019020560440500c0a00801396408158110140302802004d2910808044050100a00801442408014a20130100c0a00801902011014a900ca8028020064c3020560440500c0a008019
  | 9, 1, 6 => 0x2011a2c050100302802006408158110140302802007099020110140400c0a008ee006437020110140400ca80080190200c0140400c0a0080137a4080440501003028020070890201101404c1c0302802006408044056440400c0a0080190bc11014042700302802006668020110140400c0a008019020110140400c0a00b060064d1020110140400c0a008019020110140400c0a00801c164080440501003028f4008019020110140400f0402802006400020110140400cf2008018
  | 9, 1, 7 => 0x2011c38050100302802006408988110140400c0a008019020110140400c0a00801c3670c020110140400c0a0080190201101404c2c03028020064080440501003028020054690000804405188030280200600804452014a900c0a00801912408044050100302802442411014045a49c00c0a008019020110140400c0a00801c2a4000c8110140400c0a008018044050109c00c0a008013b64ea020560440500c0a0080192cc83020110140400c0a006400020110140400c0a0084e8
  | 9, 1, 8 => 0x1080804405010a802802006408c40560440500c0a008019020110140400c0a008b4442449020111f80501003028029020110140400c0a00801006411014a00109c00c0a0080190dc08044052c40400c020064c302011014e301003028029020052880400c0a0080137a483410080440501003028019020cd044a0010030280200670f020110140400c0a0080190d8080140400c0a0080126e40804405010030290300502979008044050100302802006457044052b00400c0a008019
  | 9, 1, 9 => 0x2313044050100302802006483020cd0440501003028019020110140400c0a008013de437020110140400c020054b9020cd04405010033200a00a712020110140400c0a0080190c8110140400c0a008012d2448044050100302802004d29020110154901003028020064080440501003c440a00801902408044050100302802006437020110140400cc8008019000080445200c0a008014b6008158110140400c0a0080190000804407010030280200600888c110140400c0a008019
  | 9, 1, 10 => 0x81580528803028020060080d4110140400c0a0080193a8110140400c0a009bd006408044052c40412c0a0080190201143ca0010030280200640804405010a100c0a008019c5408158110140302802006408278110140400c0a004b490000804405010e6028020060080440501003028021389b9044050109c00c0a0080134a40815811014f500c0a00801915c0804405010030280200641101404271a800c0a008019020110140400c0ac50020064c3044050109c00c0a008019
  | 9, 1, 11 => 0x20110140400c0aa300200640d044050109c00c0a00801900008044a0010030280200604202011148050100a0080190000827805010030280152e049020110140400ca8028029020112800400c0a009bd00640804405c640400c0a008019020110140400c0a00801c6244202011014b10100a00801902005c5ca2010030280200640804405010030280200716910808044050100a0080140a40804405a580400c0a008019278110140427003028020064370d8080440501003008019
  | 9, 1, 12 => 0x108360201101404028020064080440501003c700a0080190201101c0400c0a0080126e408045170140400c0200516912408044a001003028020064080440529c0400c02004d593a811014042700302802006408044a00100302802006ab9020110140400c0a00801c6e408044050100302b1a008019020110140400c0a00801662408158110140302802006799454110140400c0a008014b640804405010032e00a008019020110140400edf02802006408044054cc0400c0a008019
  | 9, 1, 13 => 0x1240804405010033200a00a408014a20100302802004ed9088080440529c0400c0200640844c110140400c0a00801912408044520140400c0a00a437020110140400c02004d59020110140408c0a008013565ad020110140400c0a00801902011c7805010030280200644902011014b1010030280291240804405010030280240a4080440501003028020058b9020110d0a001003028020064b3178110140400c0a008019020110171d01003028020064080bc052880400c0a008019
  | 9, 1, 14 => 0x20110140400c0a0080188640002011014a92a00a0080180205604517014030280200640d020110140402802004de90205604583014030280200640002011014042840300801820c08044050109c00c0a006408044340100302802004d29020110140400c0a008015d6449020110140400c0a0094b9020110140400c0a008293de4000b4110140400c0a008018020112800400c0a008012d245e0201101003028020052d912483020110140400c0a00661920c080440501003028019
  | 9, 1, 15 => 0x20110140400c0a00801c8645e020560440500c0a008019020110140400c0a0084e006715044050109c00c0a008019c80080440501003028020064370880804405010030080190dc080440501003008012ee41101404270f500c0a00801912436020110140400c0a00a408158110144b00c0a0080190000804405010030287400629a020110140400c0a008019044056a4042700302802006511020110140400c0a008019020112800400c0a0080126e4080440501003028020071f9
  | 9, 2, 0 => 0x20111f87d010030280200640804405010030280200725920c0804405010030280126e4080447e0140400c0a00801920c08044050112b00c0a006483020118600501003028019020110140400c0ac9002006483044050109c00c0a0080190000804405010032e0020060080440501003128020051090201e045830100302802006400020110140400c0a0840180000528804270030280200600804405010030280200723902011017220100302802006408158110140302802004da9
  | 9, 2, 1 => 0x44058c004270030280200640815811014a700c0a008019020112800400c0a008ee0064080440501003028023a40190dc08044050100305802006408158110142b00c0a008019ca408044050100302802006408044050132800c0a0080190201101404c9c03028020064080440501003028021412d90dc080440563c0400c02006437020110140400c020055f90dc0804405010030080145a408014a20100302802004d29c0008044050100302802006726020110140400c0a008019
  | 9, 2, 2 => 0x20110140400c0a00801cb24000204c0140400c0a008018020110140400c0a00801ae6408044a50140400c0a008019020110140400c0a00ab800640804405011f000c0a00801903408014a20100302802006408044240100302802004d5902041044050100302802006408044110140400c0a0080191240804405010030280235640902011014a700c0a008019020110140400f2b02802006408044050100302802006609020110159901003028020064080440501003028020072a9
  | 9, 2, 3 => 0x12422020110140400c0a00a449020110140400c0a008bb904583014042700302802006730020110140400c0a0080190dc08158110140302802006408cbc110140400c0a008019020110140400c0a008017da408014a20100302a4000801902011a380501003028020064001781163c0400c0a0080183a808014a2010030280200672e020110140400c0a008019020560440500c0a590020065f8020110140400c0a0080190232d04405010030280200640804405010032a00a008019
  | 9, 2, 4 => 0x20560440500c0a2f802006408278cd0140400c0a008019000090200500c0a0080126e008044050100302b32008019020110140400c0a0099d006408044a00100302802004f7902011014b10100302802006442044050109c00c0a00801902408044a00100302802006400048110140400c0a008018044050104b270030280200643702011014a9010030080190215e158110140302802006408044050100302802007319108080447d014040280200641145c050109c00c0a008019
  | 9, 2, 5 => 0x20110140400f3502802006483024080440501003028019020110140400c0acd002006449020111f405010030280291240804405010030281600a40804405010030290e0080190201109005010030280200640804405188030280200510902005288043d40302802006483020560440501003028019020110140400c0a0080152e449020110158f010030280291240804405010030280257e449020110140400c0a009169020110140400c0accc0200640804405010033200a008019
  | 9, 2, 6 => 0x20110140400c0a009b700640002011014b10100a004bb800008044180100302802006008014a238c0400c0a008019020110140400dfa02802006408045332800400c0a00801920c08014a20100302802006436020110140400c0a0080190003660c050100302802006008044057300400c0a008019020110140400c0a00801cda4110142b0109c00c0a008019020110140400c0a008017ce400020110140400c0a008758020110140400c0a40c02006400020110140400c0a004b08
  | 9, 2, 7 => 0xce408044050100302802006408047380140400c0a00801917808044340100302802006408044050100302802006039020110140400f3702802006400020110144600c0a00801812408044052a40400c0a00a483020110140400c0aa3001902011014100100302802006437044050109c00c0a008019044050109c00c0a59002006442020110140402802004de912408044052b00400c0a00a4080447d0140400c0a008b491240804405010030280238a4000dc081581101403008018
  | 9, 2, 8 => 0x20110140400c0a008018aa504020110140402802005029044050100302802004d537a4080440501003028020073f9cf808044050100302802006436020110140400c020042e9020110140400c0a00801356408044050100302802cf40190dc080bc110140400c02006408044180100302802004b490004202056044050280200603702011015250100300801902011cf0050100302802006408044050100302b3b008019020110140400c0a00801cea411014042700302973008019
  | 9, 2, 9 => 0x20110140400c0a00a09006449020110140400c0a008c79d1008044050100302802006408047430140400c0a008019020110140400c0a0080164e442020052880400c0a008019020111f8a00100302802006742020110140400c0a00801908808044050100302802006408044050100302802004bb902011d040501003028020064000205d0140400c0a0080180dc080440501003008013b64110140427003028be00801902011d000501003028020064081581101403028020052d9
  | 9, 2, 10 => 0x201101404c040302802006437020110140400c02004d293a808044052c40400c0a0064080440501003028160080190dcc3020110140400c02006408044050140400c0a008019020110140400c0a008012b64b3020560440500c0a008019020110158f01003028020064080440501003028020055f9020110140400c0a0080145a408044050ac0400c0a004f79000081d8050100302802006345020110140400c0a0080190dc08044052800400c020064000dc110140427003008018
  | 9, 2, 11 => 0x20110140400c0a00801d2a504020560440500c0a008019020566841101403028020064c30d8110140400c0a00801910808044050100a0080178640804405d240400c0a008019094360440501003028020064080440501003d200a008019020117fc05010030280200640804517014043d403008019020110140b00c0a0080137a40004405010030280200428810808044050111c028020064080440501003d1c0a008019020112800400ca802802006408044050100302802007469
  | 9, 2, 12 => 0x20110174c0100302802006408044a001003028020054b912408044052800400c0a00a4001241101404270030280280201101404284032a002006408044a0010033200a00801902011b84050100302802006449020110140400d1c02802902056334110140302802006408044052a40400c0a00801902011280b10100302802006442020110140402802004e59020112a40400c0a008012b6408044055c00400c0a0080190dcea020110140400c0200640804405d2c0400c0a008019
  | 9, 2, 13 => 0x124c3020110140400c0a00a436020112800400c0a008019d3837020110140400c0200640804405d340400c0a008019020111f805010030280136a48302011014b10100302801902408278050100302802006411014a20109c00c0a00801912425020110140400c0a00a40d10808044050100a008019094110140400c0a008013564080440529c043d4030080190204c0140400c0a00801442408044a0010030290e008019124080440501003028027864080440538c0302802004e29
  | 9, 2, 14 => 0x48110140400c0a00801442408044050100302802140019020110175101003028020064490209e0440501003028029020110140400c0a18c0126e43702011014043d403008019a74080440501003028020064080440501003028020060f9bc408044050100302802006408047500140400c0a0080192cc1101404270030280200640804405d3c0400c0a00801902011014043d40359002006449020110140400c0a008e59000080445c010030280200600804405010034700a0055f9
  | 9, 2, 15 => 0x20110140400c0a00801d52408044a00100302802004d5902011016700100302802006408158110149c00c0a00801900008078110100302802006008130110140400c0a008019020110140400f5302802006408047520140400c0a00801912408158110140302802006400020115340400c0a0080184101101404270030280200640804405c5c0400c0a00801920c37020110140400c020064f9020110140400c0a008019000080440501003028020823150dc080440501003008019
  | 9, 3, 0 => 0x20110140400c060080126e408044a00100302802004bb9020111480500c0a008014b6408044070140400c0a0080190000804405010034700157e0af020110140400c0a008019020115340400c0a0080133244202011014e30100a0080190202f0447d0100302802006757020110140400c0a008019d58080440501003028020064080bc110140400c0a008019d5449020110140400c0a00a408044054940400c0a0080190002504405010030080135610402011014a90100a008019
  | 9, 3, 1 => 0xdc08044050104b00c0200640012408014a201003028028020110140400c0a008f60064080bc112b00400c0a008019020110140413c0302802006715124080440501003028029020110144001003028020064370201145c05010030080190dc08045830140400c02006408044050100302a39008019020110140400c0a00b580064080447d0100302802004ed9020110163f0100302802006408044050116900c0a008019020110140400c0a008013b6422020112800400c0a008019
  | 9, 3, 2 => 0x17836044050100302802006411014042700302802006ab9020112800400c0a05802006408044050f40302802004d590d81160c050100302802006408044052800400c0a00801900011014042700302802006008044050100302b5c0080190235b0440501003028020064080458f2800400c0a00801902005288a20100302802006408044a001003028020055f9020112800400c0a0080145a4110140427003028026f4019020110175a0100302802006408047590140400c0a008019
  | 9, 3, 3 => 0x804405010030280263a037020110140400d6400801902011015120100302802006408044050100302802007099020110140400e6f02802006408044a02a40400c0a008019044050109c00c0a008012d275f020110140400c0a00801910842020110140402802006411014042700302802004cc9d780804405010030280200666310808044050100a008019020110140400c0a008019424c3020110140400c0a008019d74080440501003028020064080440501003028020064d9
  | 9, 3, 4 => 0xd9c080440501003028020064080440501003028020076690209e0140400c0a0080152e765020110140400c0a008019d9008044050100302802006408044050100302b6300801912408044058940400c0a00a755020110140400c0a0080191240804405010030280236a4491780804405010030280290000833405010030280233200804405d880400c0a00801949837020110140400c020064080440501003028020076190dc37020110140400c02006408044050100302802007609
  | 9, 3, 5 => 0x201145c0400c0a0080145a400020110141000c0a008018020110155701003028020064080445c01003028020051090224f04405010030280200640020c081581101403028018178110158f01003028020064080476a0140400c0a008019020c6044050100302802006408278110140400d1c028019020110140400c0a00801da644902011014a701003028029020052880400c0a0080142a715020110140400c0a008019da00804405010030280200640804405010f500c0a008019
  | 9, 3, 6 => 0x68808158110140302802006483020110140400c0a004d292cc37020110140400c02006408014a201003028023b8019048080440501003028020064080440501003028020076b9020110141000c0a008012d24c3020112800400c0a00801902011060050100302802006442020110140402802006a19020110140412c030280200640804405010030280200584902011280a00100302802006400044a00109c00c0a0080180201145c050100302802006408045830140400c0a008019
  | 9, 3, 7 => 0x80440501003028162d2037020110140400c02006ab9178080bc1101003028020064000dc080440501003008018c5408044a001003028020064080440501003028023d8d59020110140400c0a00801db6526020110140400c0a0080190dc08044050100302802006408044050100302964008019db008044050100302802006408044a001003028020076190000804517010030080145a011014042700302802005109
  | 10, 0, 0 => 0x20110140400c0a008013de409020110140400c0a008019020560440501003028020064080440501003028023b8019020110140400c0a0080126e408044050100302802004b49020110d0050100302802006449020110140400c0a008019000080440501003028020060080440501003028026f4019020cd0440501003028020064b3020110140400c0a00801902011014a20100302802006400124080440501003028028020110140400c0a008014b640010808044050100a008018
  | 10, 0, 1 => 0x202f044050100302802006408044052a40400c0a008019020110140400c0a058020064080440563c0400c0a008019020110140400c0a0080157e40804405010030280200516908808044050100302802006408044050100302802004bb9020110140400c0a00801356436020110140400c0a008019020110140400c0a0080152e40804405010033200a00801902011014b1010030280200640804405010032a00a008019020111f8050100302802006400020112800400c0a008018
  | 10, 0, 2 => 0xdc0804405010030080180dc08044050100302802006408044050100302964008019020110140412c0302802006408045170140400c0a0080190201160c05010030280200640804405010f500c0a00801930c08044050100302802006408044052800400c0a00801900011014042700302802006008044050100302802004ed9
  | 11, 0, 0 => 0x20110140400c0a008018
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 64
  | 7 => 74
  | 8 => 84
  | 9 => 94
  | 10 => 94
  | 11 => 84
  | _ => 0

def idWidth : Nat := 10

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 224 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0x3fffffffffffff000000000000003fffffffffffff, 54)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)

theorem ori_ok {u ys} (h : NatRun (mask 112) (goal 112) u ys) :
    NatRun (mask 112) (goal 112) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 12 0 (NN s)

def poolG : List Nat := [70960367455551601, 10161701677865128, 21402016508134514, 10161754284867750, 70947107870196853, 76589848794876023, 21407501209684080, 10221088183276711, 21480132299571314, 70941670447946920, 43943091553551472, 124995790194197616, 90100600426054773, 21420708218443888, 117114567083016305, 76571109846271093, 21420771644653681, 21420695349216368, 111492687901923440, 33846276254713968, 50686401715486834, 71019664899163248]

def Z (s : Nat) := bar 112 S NN idx ori poolG s

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
private theorem z7_136 : ∀ i, 136 ≤ i → i < 142 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 136 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 142 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 z7_24)) (range_split (range_split z7_32 z7_40) (range_split z7_48 (range_split z7_56 z7_64)))) (range_split (range_split (range_split z7_72 z7_80) (range_split z7_88 z7_96)) (range_split (range_split z7_104 z7_112) (range_split z7_120 (range_split z7_128 z7_136)))))

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
private theorem z8_1104 : ∀ i, 1104 ≤ i → i < 1111 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 1104 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 1111 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 z8_24)) (range_split (range_split z8_32 z8_40) (range_split z8_48 z8_56))) (range_split (range_split (range_split z8_64 z8_72) (range_split z8_80 z8_88)) (range_split (range_split z8_96 z8_104) (range_split z8_112 (range_split z8_120 z8_128))))) (range_split (range_split (range_split (range_split z8_136 z8_144) (range_split z8_152 z8_160)) (range_split (range_split z8_168 z8_176) (range_split z8_184 z8_192))) (range_split (range_split (range_split z8_200 z8_208) (range_split z8_216 z8_224)) (range_split (range_split z8_232 z8_240) (range_split z8_248 (range_split z8_256 z8_264)))))) (range_split (range_split (range_split (range_split (range_split z8_272 z8_280) (range_split z8_288 z8_296)) (range_split (range_split z8_304 z8_312) (range_split z8_320 z8_328))) (range_split (range_split (range_split z8_336 z8_344) (range_split z8_352 z8_360)) (range_split (range_split z8_368 z8_376) (range_split z8_384 (range_split z8_392 z8_400))))) (range_split (range_split (range_split (range_split z8_408 z8_416) (range_split z8_424 z8_432)) (range_split (range_split z8_440 z8_448) (range_split z8_456 (range_split z8_464 z8_472)))) (range_split (range_split (range_split z8_480 z8_488) (range_split z8_496 z8_504)) (range_split (range_split z8_512 z8_520) (range_split z8_528 (range_split z8_536 z8_544))))))) (range_split (range_split (range_split (range_split (range_split (range_split z8_552 z8_560) (range_split z8_568 z8_576)) (range_split (range_split z8_584 z8_592) (range_split z8_600 z8_608))) (range_split (range_split (range_split z8_616 z8_624) (range_split z8_632 z8_640)) (range_split (range_split z8_648 z8_656) (range_split z8_664 (range_split z8_672 z8_680))))) (range_split (range_split (range_split (range_split z8_688 z8_696) (range_split z8_704 z8_712)) (range_split (range_split z8_720 z8_728) (range_split z8_736 (range_split z8_744 z8_752)))) (range_split (range_split (range_split z8_760 z8_768) (range_split z8_776 z8_784)) (range_split (range_split z8_792 z8_800) (range_split z8_808 (range_split z8_816 z8_824)))))) (range_split (range_split (range_split (range_split (range_split z8_832 z8_840) (range_split z8_848 z8_856)) (range_split (range_split z8_864 z8_872) (range_split z8_880 z8_888))) (range_split (range_split (range_split z8_896 z8_904) (range_split z8_912 z8_920)) (range_split (range_split z8_928 z8_936) (range_split z8_944 (range_split z8_952 z8_960))))) (range_split (range_split (range_split (range_split z8_968 z8_976) (range_split z8_984 z8_992)) (range_split (range_split z8_1000 z8_1008) (range_split z8_1016 (range_split z8_1024 z8_1032)))) (range_split (range_split (range_split z8_1040 z8_1048) (range_split z8_1056 z8_1064)) (range_split (range_split z8_1072 z8_1080) (range_split z8_1088 (range_split z8_1096 z8_1104))))))))

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
private theorem z9_888 : ∀ i, 888 ≤ i → i < 894 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 888 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 894 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z9_0 (range_split z9_8 z9_16)) (range_split (range_split z9_24 z9_32) (range_split z9_40 z9_48))) (range_split (range_split z9_56 (range_split z9_64 z9_72)) (range_split (range_split z9_80 z9_88) (range_split z9_96 z9_104)))) (range_split (range_split (range_split z9_112 (range_split z9_120 z9_128)) (range_split (range_split z9_136 z9_144) (range_split z9_152 z9_160))) (range_split (range_split z9_168 (range_split z9_176 z9_184)) (range_split (range_split z9_192 z9_200) (range_split z9_208 z9_216))))) (range_split (range_split (range_split (range_split z9_224 (range_split z9_232 z9_240)) (range_split (range_split z9_248 z9_256) (range_split z9_264 z9_272))) (range_split (range_split z9_280 (range_split z9_288 z9_296)) (range_split (range_split z9_304 z9_312) (range_split z9_320 z9_328)))) (range_split (range_split (range_split z9_336 (range_split z9_344 z9_352)) (range_split (range_split z9_360 z9_368) (range_split z9_376 z9_384))) (range_split (range_split z9_392 (range_split z9_400 z9_408)) (range_split (range_split z9_416 z9_424) (range_split z9_432 z9_440)))))) (range_split (range_split (range_split (range_split (range_split z9_448 (range_split z9_456 z9_464)) (range_split (range_split z9_472 z9_480) (range_split z9_488 z9_496))) (range_split (range_split z9_504 (range_split z9_512 z9_520)) (range_split (range_split z9_528 z9_536) (range_split z9_544 z9_552)))) (range_split (range_split (range_split z9_560 (range_split z9_568 z9_576)) (range_split (range_split z9_584 z9_592) (range_split z9_600 z9_608))) (range_split (range_split z9_616 (range_split z9_624 z9_632)) (range_split (range_split z9_640 z9_648) (range_split z9_656 z9_664))))) (range_split (range_split (range_split (range_split z9_672 (range_split z9_680 z9_688)) (range_split (range_split z9_696 z9_704) (range_split z9_712 z9_720))) (range_split (range_split z9_728 (range_split z9_736 z9_744)) (range_split (range_split z9_752 z9_760) (range_split z9_768 z9_776)))) (range_split (range_split (range_split z9_784 (range_split z9_792 z9_800)) (range_split (range_split z9_808 z9_816) (range_split z9_824 z9_832))) (range_split (range_split z9_840 (range_split z9_848 z9_856)) (range_split (range_split z9_864 z9_872) (range_split z9_880 z9_888)))))))

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
private theorem z10_40 : ∀ i, 40 ≤ i → i < 43 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 40 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 43 → Z 10 i = true := (range_split (range_split z10_0 (range_split z10_8 z10_16)) (range_split z10_24 (range_split z10_32 z10_40)))

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

end PEqualNP.Outside.L_meta_8513_aux

theorem PEqualNP.Outside.L_meta_8513 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_8513_aux.mainG PEqualNP.Outside.L_meta_8513_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩
