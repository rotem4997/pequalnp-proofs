import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7404_aux

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

abbrev fG : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)

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

def rowsG : List ℕ := [1, 2, 4, 16, 4, 16, 64, 64, 104, 60, 14, 49, 14, 49, 74, 97, 74, 97, 74, 97, 74, 97, 74, 97, 104, 104, 104, 104, 193, 194, 193, 194, 20, 6, 17, 6, 17, 6, 17, 6, 17, 12, 48, 20, 20, 24, 24, 24, 24, 65, 66, 1, 2, 8, 32, 8, 32, 128, 128, 148, 60, 14, 49, 14, 49, 134, 145, 134, 145, 134, 145, 134, 145, 134, 145, 148, 148, 148, 148, 193, 194, 193, 194, 40, 10, 33, 10, 33, 10, 33, 10, 33, 12, 48, 40, 40, 36, 36, 36, 36, 129, 130, 1, 2, 14, 49, 193, 194, 60, 60, 12, 48, 5, 18, 5, 18, 68, 80, 68, 80, 232, 124, 30, 53, 78, 113, 75, 99, 78, 113, 90, 101, 106, 105, 202, 225, 105, 106, 108, 120, 197, 210, 209, 198, 84, 7, 19, 22, 21, 38, 25, 70, 81, 76, 112, 21, 22, 25, 26, 88, 152, 67, 67, 9, 34, 9, 34, 136, 160, 136, 160, 212, 188, 46, 57, 142, 177, 135, 147, 142, 177, 166, 153, 150, 149, 198, 209, 149, 150, 156, 180, 201, 226, 225, 202, 168, 11, 35, 42, 41, 26, 37, 138, 161, 140, 176, 41, 42, 37, 38, 164, 100, 131, 131, 3, 3, 15, 51, 195, 195, 61, 62, 13, 50]

def xsG : List ℕ := [0x5ff14ab28d57402e295651aae80506500aa28555400a015450aaa801, 0xaff2857512aea05650aea255d40a09a0055502aaa01400aaa0555402, 0x710f12007baab8001abb94091e55710f10007aaab8001aab00001614, 0x7100d5dca048f2a9e2400f7557007100d5580000b0a1e2000f555700, 0xb20021007dd55801fd5d68062eaab20020007d555801fd5500002a28, 0xb20feaeb4031755004200fbaab00b20feaa80001514004000faaab00, 0xc080007860008068781fffff3f00c000007800000060000ffffc1c0, 0xc343c0fffff9f810000f0c001000c300007fffe0e000000f0000000]

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
  | 7 => 65
  | 8 => 532
  | 9 => 470
  | 10 => 27
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0xe594771c
  | 7, 0 => 0xe4fdea67cceb7942c496cdd8b91fe6469ef6af4a8ebd2f19894112fc8248e93681911a2c8176ef897d39721173df480671bbfeb67079f9b96db956fb6da279286c4318dc6a46a0a2648e191a5c6b0e0159c89c50584075d8575cb0e853bb6376521efc7d4fda309c481e62e64807747c459859b944a765a44161557840e437293c025762383eb99836ce9e50344797ac2cc80d6f2c3bca5827584c5d238e7ce023390b5b23362bf023247fb621d709221cf556e01c4072471a3b66c51743cdaa173ac0b11704dee6134f801111b319181113dcd20fdc24d90de1a4ea0c7b0f8b09809e00089f506207c542f30764c38804a97b8903dc67fe03b591aa02259b3c
  | 7, 1 => 0xe5be9398
  | 8, 0 => 0x78cfdb507765ee40758ab260756b8a40715b108071305c106ddf64906aeca5a06ab449a067a0d110676dcd706649405064674ff06380917062135c405d683ca05ca463f05acd754057a4359054922ea053c992d0520630504f2461d04db3d98049b37fe0491a86e0470395e04494ab4042826aa0423124503cb094b03b5c82f03aaa8f8039539030319f381031876870305142802fe883102eb0e3602956a420273524201effa8501ec209701e98fe101d5181201b79ae801ac37600193fd4f017d8c8801660cd5014ceaf70124d43d010be97700e5efdd00d7f0f600cee758007854c400642ea80057fbee004ec8df0036adda00214a1e001c7cd700057452
  | 8, 1 => 0x128b29bf1259c8fa123d2631123c567411ebc53911cf899111a3d3a2119a77491197470f11266d421100127c10f4292e10e909f710e426c810c53f4e10b1734110aeeed210a5b33210627afb100d1f8b0ffe10500f8c6bd30f4890e20f41f3990f3da1c10f286a190ea2547b0e2d5a7a0e1651f50e11c77a0e0c896d0dffb7a10dc283760d722dad0d20803f0d0cfc9a0ca262300c8b856b0c7d4e380c77c35f0c72c5270c5fb5bd0c367a970c1f72120bb647220bafca3f0b528d630b4a2d280b07436e0abeb4560abe56f60a387981099e3abe0936826108e92b6a08b53763089f13750888efe50847204908412c5b07eaf56007e31af407cd6ca407a09b46
  | 8, 2 => 0x1ccc493b1cb4e3b91c888ce51c86f1e11c4aac3f1c08c3431c05e8061bb4727f1baef6891b7dad0f1b5650ad1b1a0f171b09bd9d1ac10c6f1a3ec63e1a3215f01a27f09d19cb980319a2e539197969601977bd09196630fd1964e7c1192fdf35192be5361923f8af191fdc1f18627230183b92851813118c17f8c956174215d9171d33d216f3a44216dc9bbd169dfedd1699d2a11623f17b161ff74a160ce8f615fb5f9e15de596915c750e415bc7c4d1576b67c1547f60a152d7828152ca01d1501595a14f11bd014802e3814700dbf146aaadd145d922514572d5b143abcb8139bde83138f4a7a1388d7351384a0be13842b4312e6cb8f12e0afab12b1b9fc
  | 8, 3 => 0x296667982951270c2934841c292b56a129277190291d79cb290e47b028fef84028a1944027dba0a127d5e3bd27d3154e2708fc4526f6b61d26ed4f7226c36e62264cda0f25cb42c6257039392536fdf8251de6b024a905fb247c6ff024729d5624604398243ccf53242bb4b924155cd6240805b323debcf52396de802323f08e2314267f23032771227066722244e5332241dec7223fba59223de44221bf1dca21a7d533217af9252170c95a21073914210333ee205178fe1fe992251f76512c1f550b341f28696b1eecb0931ed5a80e1e4dfc121e1d8fd31da87a0b1d5379d41d3c714f1d383b761d236e161d1c6eb41d13bdfc1d12c4ee1cf2f7371ce70372
  | 8, 4 => 0x3c542bc43c396aac3c160c4e3be57e263bcdf04f3ba9202f3b4932ec3b23e7af3a37f75639ba5bd93975ca453951c02e3950fc18394184243920523137f8165b379c2b27374c926e3732a5ec371e2ef636af4e2f36a1268935f769ef35def84b34f601843499795e345525d8341cfffd33e0bdbb3358a1b0335795fb33255fb432e25c1b32dca9bc3218e9ba309c3ebb30870ce1305890f530418870303f32fe301c89c8301065f62fc56d372fc22e2b2f7711b12f642b512f40f4442f1d50ae2e1072bc2dd86a932dbd77632d8ff5942d251f772c60a12a2c25eda22c13f1d82bc176e72b9521182b8ac35c2b56b6352b2b4de42a68b0ce2a2c876f2a250130
  | 8, 5 => 0x51b3911950c25bd24ffe0c344f7f690a4ef1bd344ef0a19b4da04e334d36201e4d2b54324cd36fa34cae9c174c5cb1b74c0c48584bebd5834be242124b9fac264b9db1ba4b633b054b4b97114b34744f4ac111554a90d9d44a20252a4a0916f249bb86a049ac4a654934709148e3a667489e864e48088f8b47f45a6247cadd24473f26134733b13146ee88d346d9fa7b46277040460ed7ac4598a85545021ffb44f0e2f0448890b143df396a43c9bdd042f0a2ee4281216f417472d44112b6044111c34340f97c1f40d2b41a3ff3d06d3fe3e9953fa5a0713fa21e503eef4d103e868ac33e50b04a3dc87f6d3d229d113cb892af3c965dc83c7f55433c6b3449
  | 8, 6 => 0x74b31afc72bc17a970e3da1770dc54cc70d696d67043327f6f84d3bb6c9adf906bbd93366a0cfaf967d177dc67089cf066877659663ced226566ae2564dd5e6664b399c66449fe2963b749ec636c548462a9a8b56288c24361aaf478619264bf61657b99616018b7614e7314610fb7a4609626685f9f9c5c5ec4f76b5df4f4e85d844fd05ce222be5cca18835cb2c9445cb190af5c78d4295c51738c5bfeeb5a5b0c2db95a9ab1ec5a5b32d759ddbcbe59bfb983595d2c9b5925fd535882ada6583f53125633a92655f19dfa558177665564887d5535003e5532e6f25521eb3354cdc60e54b129a25420947e52edf87d529faeb95299d83b527fac8a51f69b6d
  | 8, 7 => 0xade5c7fbadb37bf3a8f7372fa853357ea78aec12a77ff0a2a0aaee8ea0a751669ef1364f9e8250db9dff87509cae2ca999e57afd968d5764960cf66f94410eb994093e9d92a286eb925df64e91bcf5f29129ac6690ddea978f26a7808dafc8868c8ed1f98bc30faf8b14493f8b01d5d989d47adc89ac7c378917bae587d2e7e186e46f0f86158d4185bbd52c84c6a30684605648835a445c834e8c0280d62b957fe42ad67f36aab67ddfc3cf7da60ac47d9cb2b57d6728117d297fa17d18f11c7b9457807b692e017a7605fc7a509537783502b877e6d30d779ed705773c7d937721f549770aecc476f1cebf75bd8dba759c3f8e754030707503be3c74ba05f6
  | 8, 8 => 0xf89e316aefa0efe9eee952d7ed222699ec617d68ea2d5ce4de685ea1d6f9da02d3073855cfdbe44fc8a9adf3c69e9591c41a7ccac138b41dc020ccccbff3679fb7cd75f5b756b609b292f091b0a2f631
  | 9, 0 => 0x77e1a8807752900076b367b0756b8a40751cf830718c13b06b3d41c06ad1c72069d118f068cd316066bda77066494050658ad20062008e5061eb23d061b4b8505ffc5e105b80731059c1034052853a505206305051244cd050833e604bd4b7c04b2a30c0491a86e0478050f045963e8044aa1a80445240c03f1e95d03b9b709039e5f7d039a07fb0382c83a037bad1a0366e09a0364a4950318768703052f5602e86e1002d76d3f02bbc79502a70f2a028ff9a9027fd9d302735242023932b502234ade02222a300213ba0d01effa8501dd4a960153e0ab011f39100108e3e200d6b89700cda1a300c846a80059e13c003fe16b0036adda002f0c64001a0b0f
  | 9, 1 => 0x12f218e812cb257012aa09b4126288b311e9570f1197470f1196c446114e4400113d1d58111ff71510ceb22210afbb2910aab1c01025d962100fb53a0ff38d5a0f67efd50f41f3990f407fe50f3026020ec31e8a0e7f93570e56f7cb0dbd9bad0da31d5a0d6f74930d67ca1c0d5f6a6e0d4bddf80cfacb990ca300430c5f7a850c2dbaee0c1ef63b0b56c1c50b1f04930b1765130b07fc0e0adb332f0a9faa220a7532930a746d9b0a36e93f0a23e3450a1ee77c09ad2fa909ac2d7309754c4d095f93c809268b800922fe77090d858708f667db08dc97a108c8575608798608086881460864c55e08571a68084011e3083c39b0080ca8a407b3466507b25be0
  | 9, 2 => 0x232eda62232c778522f7783522c9e1e62271635a2268386c2264dcd5225a534021eed14121a7e50a217e074d2170c95a215a17b42103b1e420d4c15920cd2ef32054450d20208ef42009866f1fd8aa181f0e8ccd1eecb0931ed5a80e1ec45fcf1e7b2d521e6a9ff51e4ff7ba1dd055691cfda6aa1cc7cc511c800b121b913f761b71212d1b1a0f171b13d0401ae33f761a7f280e1a7687ac1a27f09d19e3b30d19ba27411985049f193caf381939da561915c0e718b8a382183e47a917edd01217d920da17acabd11759e01b167b6a9d15f479c815bf222b15ba2ee215a3265d14ff9319146c50c2146b4b401416022413e8483513b9a47b13addfde133fb757
  | 9, 3 => 0x32c9e0a232412bac31ea2ff5319469e6318c0ebe30f85c0230cfda2a30a1ca253081e1093053b6e9301726412fea2b542fdc95f52fc6ccde2fae6c3a2f40f4442ef43e0f2eaf174e2e6b4ac42e545ef52e00243b2d60c04b2d3788d52d20b59a2cc416352cc0c6a32c8179b12c65e38f2c0855be2bd841472b6e6e3d2b1168472b07b9e62acceb462aa0db292a74433829d7682329cad1b329c862d629c332b02993a98c29605762292b56a1291be0ff290691e428b7509728a19440286d7d4e283c59e227639df7270f90c5264cda0f258f07a2252ac4fa24fe827824d1c88f24ced8ce24a88bd02456a0de23b4e2a12389e317236c56442364f9ec235658c7
  | 9, 4 => 0x49f33742493b697d493afa2d48d9b158480753a447b16c92469dc4364659ed4f458e05cc44d0dbbe449a09ec43ac8bf543a48732436b87234365967c434e8df742f8f552427b75c44279a6d2425c2db4417d14b641277dec406da5f93fe3e9953fb618403f5987783f55861e3f4efbce3e236cae3d9c65273d31ff793d1af6f43d07f8173cced2263c965dc83c7f55433c461eb73bfad7fa3ba9202f3b95a4a33ab629cf398e915e38fd77a538ca99a7382634443806485f379c2b27379811523749b4bd3732a5ec3718ba0f366e2af6364a3d4436102cf8359b57ff355dc4f3355d3c05355ab5d23529ad5e34b14222348871b93343f2b4331cc8c53305f9d0
  | 9, 5 => 0x6b064f7668f5f7c068d56b2e68bba0fd68b360f76738adcb66d64b0266456887662f4830661c270a65fe280a64e9d46e6453efaa6357d3d96188a9fb61186eea5f1e88ac5edec4e95ec7bc645da604995c9be6bb5c51738c5908491a58d9deac587e86fc57b280a85798b10f5607605c55f19dfa55a6bcab553eb3c35521eb3354b8289a545c7fdd53bd963f53995ac35329f39f52fc1f2852e042565299d83b51fb91cd5146e3ec50786d50502dc9074ffe0c344ff7f67f4fdeedd44fa1990f4e7f24be4e4c1a644dd514914dc30f7d4da04e334d2b54324d07ce724c6d6e4b4c17440f4b78d6324b34744f4a8739364a654a514a225c3e4a1cfe4b4a0a9a62
  | 9, 6 => 0xaea11ddeade5c7fbadb37bf3ac62d757aa960b6aa7212979a300d6789f4a97ae9eecbc4d9d3d58849cd3748598ee5c5b98168efa97f8000c91f65fd09087d6a58fca80328f7023c08f367ae28f02680b8e341c828db7e0af895b5b5388e89bfc86feb1518640215982f3776382c826928237cbd18101965680d44ba3806c12ee7ddc34de7d7a69267c34833e7c1467ca7bcfef767b9457807b8183fd7b692e0179d12f8179b4238779b06a7778aec8aa77aaf7e676f7bb7676859997764b614474589aa473d772f8738f9564712b231370647c656fd5dd8a6f7fdac16f2f99466ec4c6966deb095a6d3211766cc59c096ca6cb256c7de28b6b8541886b3fb9c4
  | 9, 7 => 0xf01274e0efa0efe9ec136e8aea2d5ce4ddeab605d863ea62d3073855cfdbe44fcf85d05dcf2d90b7c8c4c103c7a5f32cc12dc775bc36fde6b9cca5a4b8f9f4d5b5495afcb3a6f195b27d929eb187898bb1147b28b01ea124
  | 10, 0 => 0xf01274e0ea2d5ce4ddeab605b5495afc7b94578079b423876f7fdac16ec4c6965f1e88ac54b8289a4c6d6e4b4a1cfe4b4279a6d23806485f318c0ebe2fae6c3a2ef43e0f2e6b4ac4292b56a11e6a9ff512f218e810ceb2220c5f7a8509754c4d039e5f7d02735242002f0c64
  | 11, 0 => 0x292b56a1
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0xf306fdffe079f7f9e2600ff5d7007100d5580000b0a1e2000f5557000c080007860008068781fffff3f00c000007800000060000ffffc1c0b20feaeb4031755004200fbaab00b20feaa80001514004000faaab007100d5dca048f2a9e2400f7557007100d5580000b0a1e2000f5557000c343c0fffff9f810000f0c001000c300007fffe0e000000f0000000aff2857512aea05650aea255d40a09a0055502aaa01400aaa05554025ff14ab28d57402e295651aae80506500aa28555400a015450aaa801f30903001f860800df9ffc0f3eff0000000000000000000000000000
  | 0, 1 => 0x7ff1dffead5ff2afeb565fffff057750dffa8555f0abe3545fffff01710f5290fbeaf8283afb95295e55710f10007aaab8001aab00001614f30ffeffe079f7f924600ffaeb00b20feaa80001514004000faaab00b20021007dd55801fd5d68062eaab20020007d555801fd5500002a285d347c9fffffdfa92040f1e041000c300007fffe0e000000f0000000120e944d0f7de7d02bf4c65339504bafd55d07ffe7f403feaf557dd6b206a96b7df57d51fd7d6a96afaab20020007d555801fd5500002a28710f12007baab8001abb94091e55710f10007aaab8001aab00001614
  | 0, 2 => 0xf30fba6b7bbbbd501abb96999f55710f10007aaab8001aab00001614fff7eafbcd77757e297653bae90506500aa28555400a015450aaa801b20feaeb42317d5006a19fbbbb50b20feaa80001514004000faaab00ffff97757baeb8565abfb65dde5f79af15557aaab8141aaba0555616affa857796aea856d7affffff7fa0da0055782aaa01600aaffffd5c27fff5ab2fffff82e3bffd5abfe55775f1aa2fffff80a1bff50aabe157101d7dca94af2a9ea521f7d5f057100d5580000b0a1e2000f5557005d353e0fffff9f810812f0c809050c300007fffe0e000000f0000000
  | 0, 3 => 0x7d34fddfffffffa9e240fff557007d30d55ffffebea1e200ff555700aff2957db2eeb2d750aea255d50a09a0055502aaa01400aaa0555402fff2c5f592eee07e70eea375d40a09a0055502aaa01400aaa05554025ff15ebead5fd2af295651eae90506500aa28555400a015450aaa8017d0f1207ffaab8069fbbfffffff57d0f1007faaab8061aabffffd7d47108d5dca248faa9e2c19f7d57507100d5580000b0a1e2000f5557000c3c3c0fffff9f810281f4c913500c300007fffe0e000000f0000000f30feaeb493375500c321fbaab05b20feaa80001514004000faaab00
  | 0, 4 => 0xaff2857516aea856d5afea57f6aa09a0055502aaa01400aaa0555402b2043d0ffdfddf81fd5d68c62faab20020007d555801fd5500002a280c0c3c0fe6799f878781fffff3f00c000007800000060000ffffc1c0ac3a89428d572050d6a95e9516faf59ff55a8554b1f5feab5f5557feb20ffeefe079f7d104200ffaab00b20feaa80001514004000faaab0000043c0fe0799781000000c001000000000000000000000000000000aff6ad7f52bfb55650aea2d5d50a09a0055502aaa01400aaa0555402b200350cfdddda81fd5d68462faab20020007d555801fd5500002a28
  | 0, 5 => 0xbe082107ffd55807ffddfffffffabe002007fd555807fd55ffffebe8710f12007faab8009fbbfc0f3ef5710f10007aaab8001aab000016145ff14ab28d57482ead5779aeeaa506500aa28555400a015450aaa801f30f13007faeb800dfbffc0f3eff710f10007aaab8001aab00001614fff14bb29dd7482efd5f79aeeeaf06500aa28555400a015450aaa801510902000f0208008f93fc0f3af5000000000000000000000000000041f8151339ce82a97c5e0fbaa70f41f015507ffeaeb9fbff0faa953fb20febeb54b57d50d52d6fbeafaab20feaa80001514004000faaab00
  | 0, 6 => 0xb20f23007df57801fd7d6c0e2eaab20f20007d555801fd5500002a28710fd7dce068f2a9e2600f7d5f00710fd5580000b0a1e2000f55570082cb162ca04892d71dbf004aa9ff82cf2aa00001415e1dff00aaa8ffbff2a5757ffff857fdffea57feaabba025557ffff815fdffa0557e2af300d5dcb0ccf2a9f24c2f75570a7100d5580000b0a1e2000f555700fff14bb29dd7402e795e71aeec0f06500aa28555400a015450aaa801b20821007fd55801ffddfc0f3efab20020007d555801fd5500002a28fff03823241db55607046483b6aafff03aa78555f75e0754f0aabeeb
  | 0, 7 => 0x5ff56abbcd77552e295651aae90506500aa28555400a015450aaa801ae08010796840806d78dfffff7fa0c000007800000060000ffffc1c05ff94ab28f57482e2bd7d5abfa5506500aa28555400a015450aaa801def250a9b2e652ffb2eead20830a78a0d00d02aa10b5e2aaaf000302710f3e0ffbfbbf811abb94c91f55710f10007aaab8001aab000016145ff57ebfed7fd7af295651eae90506500aa28555400a015450aaa801d101a74d090207d1cc123a5c09af88a0e55d000007f5e400af5541eaf30ffaeb7bbbfd501ebb9fbbbf55f30ffaa87aabf9401eab0faabf14
  | 0, 8 => 0xae343d0fffff9f81d50df8c627aa0c300007fffe0e000000f0000000f30f13007baeb8005abfb40d1e5f710f10007aaab8001aab000016147d071207fdaab0069d3a6bf6eda57d0f1007faaab8061aabffffd7d4b204290b7df55d01fd5d68862faab20020007d555801fd5500002a28a3c6b97aed513fd750ae5295d50a05900552fd54ae1400aa50555402affa857516aea856d7affe5ff6fa09a0055502aaa01400aaa05554025ff94ab28f57482eafd7fdaffaf506500aa28555400a015450aaa801be3ffeefffffffd10420fffaab00be3feaafffff5f400400ffaaab00
  | 0, 9 => 0xc343c0fffff9f818501f8c623a00c300007fffe0e000000f0000000a206a86b4031355000200290810000000000000000000000000000003cf0c0c81f867806199fff3003ff3cf0c00ffffe1e1e19ffff0003ffc30f3f37e07987f9e66000cffc00c30f3ff00001e1e1e60000fffc007d3b2e0f845527811abb64c91f557d3f10078554b6001aabf0001614c300f4dcdd9daaa81f1d677379aac300f5587d55e8a01f550f557d28003c3c0879ff978787810f3ff2f0003000007ffe0e0600000fffc1c0f300d5dcb4ccfaa9f74d6f7777aa7100d5580000b0a1e2000f555700
  | 0, 10 => 0xfff3cff79fffe07e79fef3fffc0f0ff00ff787ffe01e01fef0fffc030ff80037860608068787fffff3f00c000007800000060000ffffc1c0fffb87751baea8565abfb65dde5f09a0055502aaa01400aaa0555402000fcbeb3de42d51f97d67bc85aa000fcaa87d540941f9550faa8128bfffefff52bff55654aeafffff0abbafeffd02abf15404aaafffff02f302d5fda068f2f9e2600f75d7007100d5580000b0a1e2000f555700fff3caf38d77607e297653bae80506500aa28555400a015450aaa8017100d5dca448faa9e7416f7777a07100d5580000b0a1e2000f555700
  | 0, 11 => 0x3cff0b2322625557e0e2988c86553cff0aa782aa175fe0aaf0aa82d70ffc303860061f8786070c00c3f0f00ff00878001fe1fe010f0003fcf003cfc79ff9e07879f8f3ff3c0f0ff00ff787ffe01e01fef0fffc03a200010014840800d50d680626aa0000000000000000000000000000510902000b0208000a9394091a550000000000000000000000000000ffc3c3f786006878787ef0c00d0fffcfffff8001f1f9fffff0003e3f2ef19f6e2d1fb287cb165edfbf057750dffa8555f0abe3545fffff01bff021307dd75807fd5f6806eeaab20020007d555801fd5500002a28
  | 0, 12 => 0xa200010010840000500c2004040a000000000000000000000000000000080000060008008781fc0f32f00000000000000000000000000000a00eb54d72a8bfd1d6a9ae5517faf9aff55d7aaabff5feabaf5557fe500d7a8aed515fa9af515daa2bf5f65ffaaafd555febff555faaabfdf3f7fff879fff7f9787e00000c0ff3fffff87ffffff9ffff00003e3f4df01514bfce8aaffbdff04554ff4df01557fffeaebffbfff05554ffbfffeafb4037755604260fbaeb00b20feaa80001514004000faaab007ff0d5fca04ef2afe2460f75d7007100d5580000b0a1e2000f555700
  | 0, 13 => 0xc0c280fc6311d068781fffff3f00c000007800000060000ffffc1c02102000012aaa00010aa800114000100000002aaa00000aa00001400b20421007df55801fd5d68062eaab20020007d555801fd5500002a28fff6fdfffffffffff2eefff5d70a7db0d55ffffebeb5e2aaff5557020000140ca048928100000040010000000000000000000000000000000cfedcff8228a7fe02a087f1d1504dffdfff82aaa7fe02aaffffd5d70ff000300006000600060000c0000000000000000000000000000000300f020040203000002004080a00300f000000001000000000000200
  | 0, 14 => 0x40008008501680622a00000000000000000000000000000aff2957532aeb05650aea255d40a09a0055502aaa01400aaa0555402fff2d5fdb2eef2fff2eeaf75d70a79a0d55d02aab0b5e2aaaf55570251004090804040282040012040000000000000000000000000000000b20febeb60717551e4600fbeaf00b20feaa800015141e4000faaab00b20febeb7df57d51fd7d6fbeafaab20feaa87d555941fd550faaab280c080005060008068781fe5ff2f008000005000000040000a05540008ef0edff845547ffe5446bf6e1aa8ef0efff855547ffe554ffffe9eb
  | 0, 15 => 0xac0eb54ff6a8bfd7d7a9fffff7fafdaff55ffaaabff7feabffffd7fe00080005020008008681ae5513f008000005000000040000af5541c04df7deff802aa7fe002203f0c1054dffdfff82aaa7fe02aaffffd5d7f30f92617baab8501abb96199e55710f10007aaab8001aab000016144dffdeff822aa7fe02a297f9d1554dffdfff82aaa7fe02aaffffd5d7f10ef5ddf2e8fff9f6e9af7557faf9aff55d7aaabff5feabaf5557fe2000954c2008b281c2000e5517007100d5580000b0a1e2000f5557008eff2a235fb70d561dbff08aa8ff8eff2aa7ffff4f5e1dfff0aaa8ff
  | 1, 0 => 0x710f160cfbeaba811abb94491f55710f10007aaab8001aab000016140c08140fa6489a878781fffff3f00c000007800000060000ffffc1c0b200200040115000040008022a00b200200000015000040000002a007ff14bb28d57402e695651aeec0506500aa28555400a015450aaa801f30fffffe079f7f9e6600fffff00f30ffff80001f1e1e6000fffff003000c1c820407001e0400f3407003000c00800001001e0000f0003000c080007864008068781fffff3f00c000007800000060000ffffc1c0710bd7dca048f2a9fafb0f7d5f55710fd5580000b0a1faab0f555714
  | 1, 1 => 0x5ff57ebfffffdfaf2956f1eae9050e700aa7ffff4e0a0154f0aaa8010c3008028d57000000005080000004100002855400000000500000000ff00035020600060086a255d00008000005000000040000a0554000ae343d0fffff9f81500cf0c4050a0c300007fffe0e000000f0000000aff6bd7fffffbfd750aef2d5d50a0db00557fffeae1400aaf05554020c30040512ae80000000a04000000820000502aa00000000a0000000b20feaeb44317d5085216fbeaba0b20feaa80001514004000faaab00fffbd7f4bfceeaffffffff7ffeffffffffffffffffffffffffffffff
  | 1, 2 => 0x710f92407baab8001abb96191e55710f10007aaab8001aab00001614aff28574128ea05650aea255d40a09a0055502aaa01400aaa05554020ff43c3fffff9f870006f0c0c1000c300007fffe0e000000f0000000b20febeb50b57550542c2fbeaf0ab20feaa80001514004000faaab00710b02001baaa8001abb94091e550100000002aaa00000aa00001400be343d0fffffdf81fd5df8c62faabe302007ffff5e01fd55f0002a28000020007dd51801000060000000000000007d540800000000000000f30feafbc071757824600fbaeb00b20feaa80001514004000faaab00
  | 1, 3 => 0xc000005020000060080a255d00008000005000000040000a0554000fff16bb2fdd7582ffd5f79aeeeafb6502aa2fd55580bfd5550aaaa295ff94ab78f57482eafd7fffffbf50e500aa78555400e0154ffffe9c1710f16047baab8001abb94491e55710f10007aaab8001aab00001614710fd7dcfbeafaa9fafb9f7d5f55710fd5587aaab8a1faab0f555714710f12006028b000022004091e00710f10000000b0000200000016007100c0d88040702820400f3043003000c0080000100000000f0003000c080007860008068781dffbf3f00c000007800000060000ffffc1c0
  | 1, 4 => 0xb20021017df55801fd5d68062eaab20020007d555801fd5500002a28710f3a0b7bbbbd001abb94891f55710f10007aaab8001aab000016147104fddfe079f7a9e2400ff557007100d5580000b0a1e2000f5557000c043c0fe6799f810000f0c001000c000007800000000000f00000000c30140db2ee92810000a04001000820000502aa00000000a0000000710fd7dce268faa9e2e19f7d5f50710fd5580000b0a1e2000f55570000043c0f72b99f810000a0c00100082000057aaa0e000000a000000050057a88695157a9285000000805f25ffaa87d555fe9ff5500002a3d
  | 1, 5 => 0xb200200044115800850168062aa0b200200000015000040000002a00710fffdfe079f7a9e2600ffd5f00710fd5580000b0a1e2000f555700f3cbc3f10020607effff0f3ffefff3cffff80001f1ffffff0fffffffaffa857512aea85652afb65dd65a09a0055502aaa01400aaa05554025d0840978640482ea7c1fffff3f00c000007800000060000ffffc1c0400fdecf8228a7f802a097f911554dffdfff82aaa7fe02aaffffd5d7f3cff7fd72a8ffffffffaf7ffffffbeffffd7aabffffffffafffffff500d7a8bed715fa9af515daa2bf5f65ffaaafd555febff555faaabfd
  | 1, 6 => 0x7101d7dca048f2a9e2400f7d5f007100d5580000b0a1e2000f555700f30feafbc97375782c721fbaeb05b20feaa80001514004000faaab007d08d5dfa648faafe7c1fffff7f07d00d55f8000b0a7e200ffffd7c05100409480404028a2400f755300000000000000000000000f554100fff7fff879fff7ff787e0000cc0ff3fffff87ffffff9ffff00003e3f510d12007b8a98001a9b94091e55710f10007aaab8001aab00001614f3cfd3f07baaf87effff9f3ffefff3cffff87aabf9ffffff0fffffff710b0200000020001abb04091e55710f10000000b0001aab00001614
  | 1, 7 => 0x5ff14ab28f57402e29d6d1abf80506500aa28555400a015450aaa801f3cfebfb4031757effff0fbffffff3cffff80001f1ffffff0fffffffb20bc2e00000605004200f3aaa00b20feaa80001514004000faaab00ffffeafbcd77757e2d765fbaeb05b65feaaa8555514a05545faaab0112056aab40315500000001aaa90002000aa000014000000000aaa800f10f33007baab801debbbc0d1efff10f30007aaab801feab0000163cb20021007fd55801fd5df8062eaab20020007d555801fd5500002a28b200210054955800d50d68062eaab200200000015000040000002a00
  | 1, 8 => 0xb202a1617df57851fd7d6a16aeaab20020007d555801fd5500002a28dff1efff8d5747ffed567bfee9af8ef0efff855547ffe554ffffe9eb0ef048b28455402e214441a2e00006500aa28555400a015450aaa8010c342c0f52bf95000000a0c001000820000502aa00000000a0000000f3cbc3f00000607effff0f3ffefff3cffff80001f1ffffff0fffffff0c3c3c0fffff9f878781fffff3f00c300007fffe0e060000ffffc1c00c000007860008000000f0c001000c000007800000000000f00000000c3c3c0fffff9f818781fccf33f00c300007fffe0e000000f0000000
  | 1, 9 => 0xc04280fc6311d000000f0c001000c000007800000000000f00000005d0902078f0208068f93fffffbf50c000007800000060000ffffc1c0a2028061002020500020021080000000000000000000000000000000ae36bc6fffffbfd10020f2d081000c300007fffe0e000000f0000000b20feeef4039f55004200ffaab00b20feaa80001514004000faaab00f20ffaebe07177f9a6600fbaab00f20ffaa8000151e1e6000faaab00be3feeef52bff5500420affaab00ba2feaad02ab51400400afaaab007d30d5dca04ef2a9e2400f7557007100d5580000b0a1e2000f555700
  | 1, 10 => 0xb200210050955000540c28062e0ab200200000015000040000002a007100d5dcb0ccf2a9e2402f7557007100d5580000b0a1e2000f555700f30123007dd75801fd5f780e2eafb20020007d555801fd5500002a28f307330079fff001787e00000c0ff30f30007ffff801ffff00003e3c510f12000b2aa0000ab294091855410f100002aaa00002aa00001414f30f33007ffff801fffffc0f3efff30f30007ffff801ffff00003e3c3000000079801800181900000e0030000000780018001801000002004df94ab78602082e8783fffff3f50c500aa78000000e0000ffffc1c1
  | 1, 11 => 0xa302010012aea00050aea005140a0100000002aaa00000aa000014000000140ca048928182000f755300000000000000000000000f5541000cf01514b6cc8aaff3cde04554fa4df01557fffeaebffbfff05554ffb20021007dd55001fd5c68062caab20020007d555801fd5500002a28710010002008b000020004011600710010000000b0000200000016007fff52b0fbeef82e3aff9529de55710f10007aaab8001aab00001614aff2857712aea05650aea2d5d50a09a0055502aaa01400aaa0555402aef0edff94d547fff54c6bf6e5aa8ef0efff855547ffe554ffffe9eb
  | 1, 12 => 0xb20eb54d7ffdffd1fffdee573ffafbaff55d7ffffff5ffffaf557ffea000210070801801d409280406aab000200078001801fc0100000228400d5a8a800007a8020015a80155445fdaaa800007ea02005faa81d5710f12037baab8001abb94891f55710f10007aaab8001aab00001614aff280710026205600260210c0000000000000000000000000000000000d2a024d110d000d11508a28f5865f2aa2fd554f4a1d5550aaa8fd210085540008a000400002555400010005500000a000000000555400710f1200fbaab8001abb95295e55710f10007aaab8001aab00001614
  | 1, 13 => 0x5d3d3e0fffff9f810a93f4c91b550c300007fffe0e000000f0000000000001003dc40801fd5d680626aa000000007d540801f95500000028710f52807baaf8001abb95291e55710f10007aaab8001aab00001614ae00010512840006508ca255d40a08000005000000040000a0554000710f569cfbeafaa93afb95695f55710f10007aaab8001aab000016145100549ca048d2a92040016041000000000000000000000000000000affa857512aea05650aea65dd60a09a0055502aaa01400aaa0555402fff7fffff9fff7ff787e03f0cd0fffffffffffffffffffffffffffff
  | 1, 14 => 0x7100f5dce059f2a9e2400f7557007100d5580000b0a1e2000f5557007100c5d48048e028604003755400010005500000a0000000005554002000d5dca048f2a9e2400f7557007100d5580000b0a1e2000f555700b20821007dd55801fd5d6c0e2eaab20020007d555801fd5500002a28ae0a80678620285687a1fffff3f00c000007800000060000ffffc1c000080000020008000281940912500000000000000000000000000000f3c2d5fca048f2fff2ee0f75d70a7180d5580000b0b5e2aa0f5557020e343c0fffff9f810004f0c001000c300007fffe0e000000f0000000
  | 1, 15 => 0x5ff14ab38d57402e295651aae90506500aa28555400a015450aaa8010c080407860888068781fffff3f00c000007800000060000ffffc1c0000feaeb40313550002007b88100000fcaa80000014000000faa81005d080007860008068781fffff3f00c000007800000060000ffffc1c0b20feaeb4035755004240fbaab00b20feaa80001514004000faaab007100d5dca048faa9e2410f7557007100d5580000b0a1e2000f5557007dffdfffa26af7ffe2e29ffdd7557dffdfff82aab7ffe2aaffffd7d74100d4dc8008a2a80200077151004100d5580000a0a002000f555500
  | 2, 0 => 0xcfffffff867fe7ffe7e6fffff1ffcfffffff87ffe7ffe7fefffffdfff3f7fff8f9fff7f9787e01204c0ff3fffff87ffffff9ffff00003e3f710f1a027bbbb8001abb94891e55710f10007aaab8001aab00001614b20001003dc44801fd5d68062eaab20020007d555801fd5500002a28fff03514ffdfdaafffdff8477efffff03557fffffebffffff0557eff000001003dc40801f95d600404aa000000007d540801f95500000028aff2a57552bfb05650aea255d40a09a0055502aaa01400aaa0555402b30021007dd75801fd5f68062eaab20020007d555801fd5500002a28
  | 2, 1 => 0x8ef028230415055605046082a0aa8ef02aa78555475e0554f0aaa8eb710f13007beaf801fafb9c0d1e55710f10007aaab801faab00001614710f32007bbbb8001abb94091e55710f10007aaab8001aab00001614affeb57d72aebfd7d6afae55d7faf9aff55d7aaabff5feabaf5557fea002854512a8a05050a8a255140a09a0055502aaa01400aaa0555402aff2857510aea056502e2254c40a09a0055502aaa01400aaa055540251005594a048c2a9e24001655400410015500000a0a1e20000555400ffff13307baeb8065abfb40dde5f710f10007aaab8001aab00001614
  | 2, 2 => 0xc3428035fb70d000000f08000000c300007fffe0e000000f0000000b20001007d841800dd1d68062eaa30000000780018001801000002000c00000284000006010051aae0000400000280000002000050aa8000be0feaefc6317d5687a1fffffbf0be0feaaf800151460400ffffebc0000800030200080006819fbbb350000000000000000000000faa8100f30f23007df77801fd7f7c0e2eafb20f20007d555801fd5500002a280e343c2fffff9f810000f0c081000c300007fffe0e000000f0000000510d12007baa98000a9394091a55000000007aaa0800000000000000
  | 2, 3 => 0x7d3f12007baeb8001abb94091e55710f10007aaab8001aab00001614b20021005d954800fd5d68062eaab20020007d555801fd5500002a28bff285751fffe05679fee257fc0a0ba0055507ffe01401fea0557c027100d5dda068f2a9e2400f7557007100d5580000b0a1e2000f555700b30feaeb4033755004220fbaab00b20feaa80001514004000faaab007df0d5dcbfcefaaffbdfff7557ff7df0d55ffffebebffbffff5557ff41001514a04882a9e24000455400410015500000a0a1e200005554008eff3e2fffff9fd71dbff0caa9ff8eff2aa7ffff4f5e1dfff0aaa8ff
  | 2, 4 => 0x4280b4031150000000080010000000000000000000000000000000c0800078f0208068781fffff3f00c000007800000060000ffffc1c0b20feaeb46317d5087a1ffbfbbf0b20feaa80001514004000faaab00a00ea14152a02d50d6a9ae1516faf9aff55d7aaabff5feabaf5557fe5ff53e3fffff9f870816f0c8c9050c300007fffe0e000000f00000005000548ca048d2a9a2400d6003007000d008000010a1e2000f000300deff7aabfff75fffbffffdaaabfffefffaafffff5fffffffffaaabffdff0edff845547ffe5446bf6e1aa8ef0efff855547ffe554ffffe9eb
  | 2, 5 => 0x410007baa9800000090000000000000007aaa0800000000000000f3ff97707baeb8505abf94091e5f71af15507aaab8101aab000016161c343c0fffff9f810810f0c009000c300007fffe0e000000f00000000c3c3c0fffff9f810000f4c803000c300007fffe0e000000f00000004df01514bbce82af7ade9041545f4df01557fffeaebffbfff05554ff0cf0ccff800007fe000003f0c1000cf0cfff800007fe0000ffffc1c312014aa200114000000001aaa80002000aa000014000000000aaa800500d12006b0018000a9194091a55700f1000780018001a0100000214
  | 2, 6 => 0xaff2857d12aeb05650aea255d50a09a0055502aaa01400aaa055540251014290894240282852112848050000000000000000000000000000aff0013010860006500e2004c40a000000000000000000000000000051010200090200000812100808050000000000000000000000000000aef6fdfff4fdf7fff56c6bf6e5aafffffffffffffffffffffffffffff3006190fdd55829fd5d69266eaab20020007d555801fd5500002a28b20123007dd55801fd5d680e2eaab20020007d555801fd5500002a287d3f3e0fffffbf811abbf4c91f557d3f1007fffebe001aabf0001614
  | 2, 7 => 0x8ef085750004005640042254c00a08a00555000000140000a0554002fff3cbf39df7607e797e73beec0f06500aa28555400a015450aaa8015ff14ab38d77402e295651aae80506500aa28555400a015450aaa80151f57f9879dfd7a9785e00000c0ff3fffff87ffffff9ffff00003e3faeffbf6f7fbfbfd7dfbffedfbfffffffffffffffffffffffffffffff7000d5cca048f2a9e2400f7517007100d5580000b0a1e2000f555700fff7fffcfffffffffbfff0455cfffffffffffffffffffffff0557efffff387751baea05658beb25ddc0f09a0055502aaa01400aaa0555402
  | 2, 8 => 0xc080006860008068781fdef73f00c000007800000060000ffffc1c051c943900000402effdf0d2f7efff3cffff80001f1ffffff0fffffff0ef048b78455402ea5446bf6e1a00e500aa78555400e0154ffffe9c17fff12307baeb8061abf9409de55710f10007aaab8001aab000016140c343c0fffff9f810200f4c113000c300007fffe0e000000f00000003c080007ff8018069f99fffffff03c000007f80018061801ffffc3c000043c0ffbfb9f81000090c00100000000007aaa0800000000000000aff2edff96ffe7fff5eeebf7f5aa8ff0efff87ffe7ffe5fefffffdeb
  | 2, 9 => 0x1c090207860008068781fffffbf00c000007800000060000ffffc1c04dfd5e9e820a87ae028295e951554dffdfff82aaa7fe02aaffffd5d74df81514bfce8aaffbdff44d56ff4df01557fffeaebffbfff05554ffbff285751baea05658bea255dc0a09a0055502aaa01400aaa05554027100d5dca048f2a9e2402f7557007100d5580000b0a1e2000f555700710f5390fbeaf829fafb9d2d5e55710f10007aaab801faab00001614000eb44d6228bfd186a18e5113f0f9aff55d7aaabff5feabaf5557fe8eff2a2b5fb71d561dbff08aa9ff8eff2aa7ffff4f5e1dfff0aaa8ff
  | 2, 10 => 0x4df0dcff820a87fe028293f1d1554df0dfff82aaa7fe02aaffffd5d7500d7a8aef515fa9afd1ddab3bf5f65ffaaafd555febff555faaabfd510f12006b2ab8000ab394091a55710f10007aaab8001aab0000161453014aa209134000081211aaa80502000aa000014000000000aaa800fff7fffd7bfff7ff78fea255dc0ffbfffffd7ffffffdffffa0557e3fa3f2857010aea050502e0000040a01a0055002aaa01000aa00001402000c300860001f8186010c0003f0f00ff00878001fe1fe010f0003fcfff2857512aea05650aea255d40a09a0055502aaa01400aaa0555402
  | 2, 11 => 0x41c001100000002efbdf000554ff41c015500000a0bffbff005554ff0c343c0ffdff9781000060c001000c300007fffe0e000000f0000000aff2857592aea05650aea375d40a09a0055502aaa01400aaa0555402b207ebe87df57d51fd7d68062eaab20feaa87d555941fd5500002a28a20eb54d72acbfd1d6adae5517faf9aff55d7aaabff5feabaf5557fe00043c0ffff99f810000f0c001000c300007fffe0e000000f0000000710f12007baeb8001abbb4091e55710f10007aaab8001aab000016145d357e9fffffdfa92852f1e849050c300007fffe0e000000f0000000
  | 2, 12 => 0xf00fffcffff9fff9fff9ffff3fffffffffffffffffffffffffffffff5ff142b08946402e28561128c80500000000000000000000000000007100559ca048d2a9e040096447003000000000001001e000000002004ff01534bfce8aaffbdff045d4ff4df01557fffeaebffbfff05554ffffcbc3f78600687effffffffffffffcfffff8001f1ffffffffffffff000800000000000687810f3ff2f0000000000000000600000fffc1c07dffdeffc22ab7fe02a297f9db557dffdfff82aab7fe02aaffffd7d7b20021037dd55801fd5d68862faab20020007d555801fd5500002a28
  | 2, 13 => 0x820021003dd54801fd5d680624aa820020007d554801fd550000282882f72a2059b70550183e0000080f82ff2aa07fff4f581dff0000283f0c343c0fffff9f810001f0c003000c300007fffe0e000000f00000003004e8cb4031750000000fb003003000c0080000100000000f000300000000048000000082000f755300000000000000000000000f5541001c08000786404806a7c1fffff3f00c000007800000060000ffffc1c0b20f826140203050002006188a00300f0000000010000000000002000cf8ccff86000ffe8781fffff3f00cf0cfff800007fe0000ffffc1c3
  | 2, 14 => 0x3000010020405001e040080406003000000000001001e000000002000cff0a230222055600a2908880550cff0aa782aa075e00aaf0aa80d7f300f5dcfdddfaa9ff5d6f777faaf300f5587d55f8a1ff550f557f28cffffeffdfbfaffe1fbff7fbf9ffcfffffffffffeffe1ffffffffdfff3cbc3f00400687effff6f3ffefff3cffff80001f1ffffff0ffffffff30feaeb4031755004200fbaab00b20feaa80001514004000faaab00f3c3c3f00000607efd7e0b36ecaff3cffff80001f1ffffff0fffffff8eff2a235bb7055618be9088885f8eff2aa7ffff4f5e1dfff0aaa8ff
  | 2, 15 => 0xa00a95443288aad1d6a9ae5516faf9aff55d7aaabff5feabaf5557fef00bc3c000006078fff90f3f3efff3cffff80001f1ffffff0fffffffbff2a57552bff05654aeaa57fe0abba0255502abf01404aaa0557e02aff8013796860806d78ffffff7fa0c000007800000060000ffffc1c0b20021007dd57801fd5d6c062eaab20020007d555801fd5500002a28300f2a0b40313500002004880b00300f000000001000000000000200f20feaeb40317578af710fbaabf5f24ffaa8000151ebff550faaabfd2ff08574000ea00640060255d400010005500000a000000000555400
  | 3, 0 => 0xf3fffff879fff7ffffff0f3ffefff3fffff87fffffffffff0fffffff5dffdeff826ae7fe22e297f9d1554dffdfff82aaa7fe02aaffffd5d7aef2857512aca05650aca255d40a09a0055502aaa01400aaa05554025ff14ab2ad57502f295651aae80506500aa28555400a015450aaa8018eff2a235fb70d561fbff48bbaff8eff2aa7ffff4f5e1dfff0aaa8ff8ef8857786040856c785fffff3fa0ca00557800000160000ffffc1c2ae0280650220205600a0a255d00008000005000000040000a05540000004140cfbea9a81000090400100000000007aaa0800000000000000
  | 3, 1 => 0xf3c3c3f000006078787e00000c0ff3cffff80001f1f9ffff00003e3f3000c0c80000700000000f3003003000c0080000100000000f000300ffffeafb493775560c361fbaeb05b20feaa80001514004000faaab000c380007860608068781fffff3f00c000007800000060000ffffc1c08eff2a27dfb70d569fbffffffbff8eff2aa7ffff4f5e1dffffffe9ff0c080003060008060581f08aa0f00c000007800000060000f0aa80c01c0800078f0008068f91fffffbf00c000007800000060000ffffc1c08effefffdff74ffffdfffbfee9ff8effefffffff4ffffdffffffe9ff
  | 3, 2 => 0x300f02034020300004200fbaab00300f00000000100000000faa8300100020006d515801ad5148022aa0b20020007d555801fd5500002a28beffefffc47577ffe5646ffeebaabeffefff855557ffe554ffffebebfff16ab2cd57502e2d5659aaea05b6502aa28555500a055450aaaa017102d5dcb2eaf2a9f2ea8f7557007100d55802aab0a1e2aa0f5557000df28475022aa05600a28251d00009a0055502aaa01400aaa055540200000000000000000200040112000000000000000000000000000000f3fffffd7bfffff9feffae551ffffbfffffd7ffffffdffffaf557fff
  | 3, 3 => 0xc082007ffd518078781fffff3f00c000007fd5408060000ffffc1c000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff7300d5dcad5df2a9eb544f777f007300d5580555f0a1e3540f557f007ff14bb2ad57502fe95659aeee0536500aa28555500be15450aaaa01820020005d9508001d1d600228aa820020007d5548001d5500002828530102000d5740002956500a280502000000055540000154000028004df43d1fffff9faffbdff0c555ff4df01557fffeaebffbfff05554ff
  | 3, 4 => 0x3c3f3e0fffffbf810020f4c80b003c3f0007fffe1e000000f00002008200210004554001e544680620aa8200200005554001e55400002828be0feaefc6317d500420fffaab00be0feaaf800151400400ffaaab00f3cbd7fca048f2ffffff0f7ffffff3cffff80001f1ffffff0fffffffa00ea0494020355004200e100300b00fe0080000114004000f00030020000000108000001008000004000000000000000000000000000000ffffdfff822ae7feffff9fffffffffffffff82abf7ffffffffffffff71011200290ab0000a1214091e05710010000000b000020000001600
  | 3, 5 => 0xc0000078400000685006bf6e1a00c000007800000060000ffffc1c05c3d7e8fffffdfa9af51fdea2bf5fe7ffaafffff5febff55ffaaabfdb2002000799158001c1908022e00b2002000780158001c0100002a00000800030000000004000fbaa300000000000000000000000faa81005fffdeff8f7fe7fe2bf6d7fbf9554fffdfff87ffe7fe03fefffffdd7ffffebfbfdf77d7ffd7f7fbeefafb65feaaafd55594bfd555faaab29a3c281700000205650ae0215d40a018005500000a01400aa005554025d3048928d574028204051a040000410000285540000000050000000
  | 3, 6 => 0x7100d5d82048f2a96040000004007100d5580000b0a1e200000016007d00d5dda248f2afe2c0af75d7007900d55d0000b0a5e200af555700b20820034011500004000fbaab00b20020000001500004000faaab00f20ffaebed717ff9af715fbaabf5f65ffaaafd555febff555faaabfd7ff9dfffaf5ffaafefd7fffffff57f50dfff8555f0afe354ffffffc11ff000300d57400629564002e8000200000005554000015400002800affa857712aea05654aeaffff70a09a0055502aaa01400aaafffd5020000000200000000000001aaa0000000000000000000000000aa8000
  | 3, 7 => 0xc341c0f822a8780000090c001000c30000782aa06000000f00000000c000007860008008200fff553000c000007800000000000ff5541003000010079c05801f85908040e003000000078001801f80100000200120000000d5540002954400228000200000005554000015400002800710095542008b000420006555600710015500000b0000200005556000c080007020000060480affff30008000005000000040000afffc10000000000804000000000000000000000000000000000000000000000cff0fdffbfdfcfffffdffbf7f5ffcff0ffffffffeffffffffffffdff
  | 3, 8 => 0xbeffeaeb5fb77d561dbfffbaabffbeffeaafffff5f5e1dffffaaabff0c343c0fffff9f870080f2d5d1000c300007fffe0e040000f0554000000c10007baa9800028194091250000000007aaa0800000000000000f3f7fff87dfffff9fd7f68062eaff3fffff87ffffff9ffff00003e3f0c000007860008060100f1eae1000c000007800000020000f0aa8000ffffeaffcf777d7eaff7fffffbf5be5feaaf8555514e0554ffffebc102000020000000000000000080000000000000000000000000000000eff29575bfeeaafffbfff255d4ff4df01557fffeaebffbfff05554ff
  | 3, 9 => 0x7100d5dcf9c8faa9fa590f755f007100d5587800b8a1fa010f555700ff0f3307fffff807ffffffffffffff0f3007fffff807fffffffffffcff3ffeefffffffd11ebbfffbbf55ff3ffaafffffff401eabffaabf144dfffeffffffbfff02a2f7f9d1554dffdffffffeaffe02aaffffd5d73000150ca048d281e040084407003000000000001001e00000000200b20431007fffd801fd5df8062eaab20020007fff5801fd5500002a280cf00514844402afe144604440aa0cf00557855406bfe154f05540ebfff3eff7fffff87ffdfffbfffeafbff02ff7fffff81ffdfff0fffe2b
  | 3, 10 => 0x1e014aa284114006010051aae80006000aa280014002000050aaa800cfff3f37ffff8ffffffff0cffcffcfff3ff7ffffeffffffff0fffcffb200210060515001e44008062e00b200200000015001e40000002a007d343c0fffffbf810200f4c117007d301007fffebe000200f0001600210a000012aaa80012ab940916500100000002aaa00000aa00001400300020007dd51801181960000e00300000007d5418001801000002003000d4cca048f28100000f7003003000c0080000100000000f0003008000a54d000007d1c4002a5401aa88a0e55d000007f5e400af5541ea
  | 3, 11 => 0x204010010000000000000000000000000000000000000000f30ffffffdfdfff9ff7d6fffffaaf30ffff87d55f9e1ff550fffff2820020000002020000020000000000000000000000000000000000000aff2857592aea056d2aeaf75d70a09a0055502aaa01400aaaf55550230000000000050000000080002003000000000001000000000000200710f020049223000083214080a05300f000000001000000000000200f30ffaeb6039f55006200fbbbf00f30ffaa80001f14006000faabf00710f7a8afffbffa9bffbddab3ff5f75ffaaaffffffebffff5faabffd
  | 3, 12 => 0xf3cbe3f07dd5787fffff6f3ffefff3cffff87d55f9ffffff0fffffff0000688a845147a9a54049a221a08650eaaa855547ebe5545faaa9e953f14ab00957402828560000080502500aa005554008015400002801000000000400000001004002200000000000000000000000000000002d34bd5fffffbf814000f2d555000d300557fffeae000000f0555400ffffebf35fb76d7effffffbffeffffffffffffffffffffffffffffffb200010000004000fd5d08062eaab200200000015001fd5500002a2800343c0879ff9781000000000000003000007ffe0e00000000000000
  | 3, 13 => 0x4380aed511f8100005080010004100002fd540e000000500000004df14ab28002002e000211a8c00504500aa28000000a000050aa80017100c1d000006028e2400f3556007100d5580000b0a1e2000f5557007d3cfddfffffffafe7c1fffff7f07d30d55ffffebea7e200ffffd7c00c00140fa6489a810000f0c001000c000007800000000000f0000000bffaa577fffff857fffffffffffabfa02557fffff817fdffffffffeaa3008554108ca000500c2255540a010005500000a0000000005554000ff008328d57000600065080c0000410000285540000000050000000
  | 3, 14 => 0x82c0c1f00000407ee5440b36e0aa82c0eff8000141ffe5540fffe9eb0000c5dc804042a9e0400b7441000000c558000000a1e0000f5541007d30dddead5ff2a9e2405ff557007510d55a8554b0a1e2005f555700000000000902000000001000000000000000000000000000000000000c300000000600000000000000000000000000000000000000000000ffffb7757ffff857fffffe5ffefffbaf35557ffff815ffffa0557e3ebff285757baeb85658bfa255de0a39a005557aaab81418aba055560200000000020008000000900000000000000000000000000000000000
  | 3, 15 => 0xfff2f5fdfffffaffffffef77ffaafba0f55d7ffff8b5ffffaf557f2afff0fdffa45df7ffe7446ff7f7aafff0ffff8555f7ffe754ffffffeb710f12037baab8001ebb9fbbbf55710f10007aaab8001aab0faa9714edfeb55dffeebffffffffe5557fffdfff55ffffebfffffffff5557ff000000000000080000010000020000000000000000000000000000003201caea0011700000000fbaab003200caa80001500000000faaab002d363c0fffffbf8110aaf0c115000d300007fffeae0000aaf0001400000800078000000086000ffff300000000000000000000000fffc100
  | 4, 0 => 0x41f7def8002aa7f800220000000541ffdff802aaa7f802aa00001417a20000000000000000000000000000000000000000000000000000000c000005820000068280af75d30008000005000000040000af5541000c000004860008068381f04550f00c000007800000060000f05540c012000000001140000000000228000200000000014000000000002800320001002d555001e95448062e003200000005555001e15400002a007100140ca048b281020004411700710010000000b000020000001600be3fffefffffffd1fd7dfffeafaabe3feaafffff5f41fd55ffaaab28
  | 4, 1 => 0xc301c0ead5f9281000050c001000410000285540000000050000000a20021007dd51801500c6004040a000000007d540800000000000000fff7ffffffffffff79fef3fffd0f0ff00ff7ffffee1e01fef0fffc033c343c0fffff9f811819f0c00f003c300007fffe1e001801f0000200affebd7fffffbfd7d7affffff7fa0db00557fffeae1600aaffffd5c2210610007baab80010aa90011400010000007aaaa80000aa000014002d30855512aea0004000a25554000920055502aaa0000000a0555400fffbc7f512aee07effffaf7ffefffbeffffd02abf1ffffffafffffff
  | 4, 2 => 0x2102855412aaa00050aa825554000100055002aaa00000aa005554007fffdffefffffaaffbffdfffff55775fdffafffff8abfbff5fffff15bff3cff712bfe05650aea3fffc0a0ba00ff502abe01400aaa0fffc02ae30050512ae8000500ca044040a0820000502aa00000000a00000005ff14ab78f57402e29d6f3fff8050e500aa78555400e0154f0ffe8017d0f12057baab8061abbb65dde55790f10057aaab8041aaba0555614710f1204fbaab8009abb9f7d5f55710f10007aaab8001aab0f555714a006b54870a8b7d150280000040af1aff5587aaabff1feab0000163e
  | 4, 3 => 0xc080005020008060281b65dd25008000005000000040000a05540007d3f1a02ffffb8001abbd4891e55751f1002fffeb8001aab500016140c000007860000060180f3fff0000c000007800000060000f0ffc0004df81517bfce8aafffdffffff7ff4df01557fffeaebffbffffffd5fffffffeffffffffff2d76fffaeb05be7feaafffff5f4a0554ffaaab017dff1714ffeebaaffbfff44d5eff7dff1557fffebebffbfff05556fffff7fffffffffff9787ef0c00d0ffffffffffffffff9fffff0003e3f7301dffea059f2a9e2400fffff007300dff80001f0a1e2000fffff00
  | 4, 4 => 0xff3f3f0fffffff81fffffccf3fffff3f3007fffffe01fffff0003e3c5ff14ab78f57482e2956f1eae9050e500aa78555400a0154f0aaa8010c000005020000000000a040000008000005000000000000a00000005ffd7abaed575fafaf575daaebf5f65ffaaafd555febff555faaabfd000000000000000000000f300300000000000000000000000f0001000c30040512ae80060080a255d0000820000502aa00040000a0554000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x140400c02004006
  | 7, 0, 0 => 0x14260200409402005c240140c0200401802708c0c0380301802005c050300e018020042270140c0200401821071c050801f020060780170140c020030181d071c050301b068190080170600c0480404006009c0c05c0400c060081670540c0500404c03005c0503012044100180270140c03c0e02c06009c0d0300802c06008017014080100a00c06009c090200700c06008017
  | 7, 0, 1 => 0x1000c02004018210fdc050b80400c3e0080170140c0b80400c020f5c050303c020030180170140c0ec04018020e9c0503039010030180270e0370d80301802005c0503035020060080170d0050203300c060c9c050c4140101300c0170c0050300301802005c2f0142e010030082d70142c01003018020adc050300400c020042a7030080102900c02005c280200400c0609c017
  | 7, 0, 2 => 0x3008010060081c139c0c0204d00c060080171300c0200301802005c050304b01006008017128050200301802005c050300801002004497014081204701802005c230300800c060740170140c0200607401089c3401446010030f80170140c1140400c02005c4011008010060840170140c020040180110dc3401408010030f83270140c0500404c030f5c050300801003108417
  | 7, 0, 3 => 0x14580206015c03019c050205f00c06008017178050300801003019c05030080105d00c0670140400c020045c16dc5a0140c020040080170140c1640800c06009c05160080105700c567014310200400c42005c050300400c061543d70200400c0600801151c5303008148030185170bc050b80400c27005c2f014081404f0080170a0080104701802005c050301100c060083d7
  | 7, 0, 4 => 0x61030081805700c067
  | 8, 0, 0 => 0x140c1d4080180200422818c050300f020030087481cc0c1c00400c060080181c80c02004018020042280140c0200400c021c40181940503014010030186e80140c1c00400c6f008018030140106200c060046e80146d0200400c060080180140c1b008018020046b8014080106a00c0600801818c05030080105700c6980e00c0106800c0600801801408010030080119c6681946418c050300801003819063030080106200c018
  | 8, 0, 1 => 0x140c1c01f018020046b820c0c0208200c0600801808c0c1d40800c060080180140c0206000c060080180140c0200400c810080180140c2000800c060080181fc0503008010030087e8014080107d00c06008018014080107b00c060080180d0050200400c06004678194050300400c060085b80147c0107b00c060080180300418803018020045b81e805030081e4030180280bc051e00800c020047780140c0200400c061d8018
  | 8, 0, 2 => 0x140c010030180200493818c9201408010020049182400c1e00800c060080180140c1e00823c060088e80140c0200404c032340180140c020040400600801819405030080108c0180280300801062230060080180140c1e00822c062280182240c0200400c06008018190050300400c060045b82204003008010060080180140c21c0400c8600801818c7221408010030080180140c0200400c060088480140c1c00400c06008518
  | 8, 0, 3 => 0x1408010030182700467819005030080108c0180180300801006008011386b80140c0200400c060840180140c26c9a00c0600801820c0c0209900c060080180140c0200400c980080180140c25c0400c060080180140c0200400c0625801808c0c21c0400c060080180140c1e08700c060080180140c02004254060080182500c1c00400c0600801818c0503008010030083f8014200200422c060080180140c0200400c42004668
  | 8, 0, 4 => 0x2a0050300801003018018014a70200400c060080180140c2980400c6f0080180142602004018020042280140c1c0a500c06008018030080108b0188a0044e80140c02004018a40080180140c1c03600c060080180140c0200422c0628c01818c051c0041ec030080180140c2880800c06008018194050300801006008a18014081487b00c0600801828005030080100327c0182780502004274030087780140c2700400c06008018
  | 8, 0, 5 => 0x140c2d40800c02004b482cc0503008010030080180140c2c80400c060080182c405030b0010060080181c8af0200400c060080180140c020a523c060080182400c0380400c060080180140c2b80800c060080180540c1e00800c060080182b4050300801006008018194050300801003018ac8030080106200c062b00180142007c08018020046b8014080107b00cab00801801408010aa00c060080182a405030080108f018028
  | 8, 0, 6 => 0x140c0200400c06008bf82f8bd03008010060080182f00c0200400c06008bb80140c1e00804c0327c0180140c1c004018020042280140c0200402c060740180140c1c00400c860080180140801003018020045c8194ba0140c01003018028014b90200400c060080181947303008010030180281940503008010031bc028030080106200c6f008018014b80200400c060080180140c020b700c060080182d80c0200400c06008018
  | 8, 0, 7 => 0x140c3180400c06008c58278050200400c0609c01818c0511008010030080180bc050200400c020045c80140c0200422c0631001830c0c1c00418806008018014371c00400c0600801808c0c1c00400c060080180140c1e07000c06008018190730300801003018018194050301f020060086b8030080106200c060085180301f02062018020046b8014080107b308c10080180140c02004300020046681900503008010031bc018
  | 8, 0, 8 => 0x140c1c01100c06008018014080107b3300600801820c050300e00c0600801830c050300801056008018190c30140c1c00401801832c0c0200400c060080180140c0201a00c062b00183280c0200400c0600801819494030080100301802819005030080100301851832405030080108b0180180140c298a500c06008018190050301f020060046b830c05030080cc060080180140c020c800c0600801830c0531c0801006008018
  | 8, 0, 9 => 0x600c1c00400c06008018194050300829403018028030082946200c060080180140c010d300c0600801814cc70200400c06004cd8194d2014043440301802819094030080100301801834804188d100c060080180140c020043400300801819463014080107b00c02818c080107b188030080180140c02004308cf0080180140c0b00400c060080180140c0480801003338028014310200400c062b001830c530300801006004cd8
  | 8, 0, 10 => 0x140c26cdb00c060080180140c3680400c06008018014201e00800c060080180140c0200400c0636401819005030082940301801830c0503008010060740180140c3600400c060080180140c03c0802c06008748014140107b00c060046e81c8d70200400c06008018030080108f018020044e819063014080107b00c0180140c1180400c060083280140c020d600c06008018060d50200400c06008018350050300801003008018
  | 8, 0, 11 => 0x1408010e500c060046780d00502004230060046780140c05c0400c06008018030080106200c860080180140c3900400c060080180140c0200415c03018e380140c3880800c06004e180140c3800400c060080180140c0500400c06004df80140c1e0a600c0600801834805010d100c020046680140c0200400c060083280140c2d40800c02004de803008010dd00c06008018014dc0200400c06008018014041ec03018020045b8
  | 8, 0, 12 => 0x140c020043bc06008018014080100301802004ee8194050307802003018028030780206200c060080180140c3b40400c060080180140c0200404c033b00180140c3ac0301802004ea8194050300801006008228030080106201802004228014080107b230060080181c8050b80400c060080180140c26c0400c060083d80140c0200400c063a401830c050307502006004e183a005030080100300801839c053980801003018028
  | 8, 0, 13 => 0x3ec0c0200400c060080180140c1c00400cce008018014c70200400cf300801818c05030080108b2280180140c020fa00c06008018030080446200c06008018014f9020f800c060080180140c020f700c060080180140c1d40800c06004f680140c020f500c06008018190050307802003018018014f40200400c0600801830c0503008010f30080180140c06c0400cac004f280140c3c40800c060080180140c020043c006008018
  | 8, 0, 14 => 0x140c1180400c060080180300801003018020584e818c05030081400300801840c0801003018020050280140c0200415c031586980140c0200400c06404018014080107b00c062b001819418030080100301802818cc30140c1e008008018015000200400c060080180140c0200400c06008ff80140c0200400cfe008018020041ec0301802004fd8014d50200400cce0080180140c0200400cfc00801818c900300801003008018
  | 8, 0, 15 => 0x4300503008010030190b8014080107b00c060085180140c0200400c064280180140c0200400c06008018030081890900c0600801818c050302e010030080180140c01003018020f45b80140c4200400c060080180140c1f00400c0600801830c0503008010060083f808c0c0200301802004748349070140400c060080184180503008010030080181901803008010030180180140c4140400c06008018015040200400c06008018
  | 8, 1, 0 => 0x14080111600c060080180140c1e008274030091584500c0200400c02005138015120200400c060080180140c02004444060080180140c01003018020051080bc050b80400c060080180e00c0d86800c060080180140c43cdb00c060080180140c06c0400c020046680140c1e00800c0609c0180140c0200400c6f0840180140c03c0800c0607474818c050310e0100300801830c051c0041ec060080180140c4340400c06008018
  | 8, 1, 1 => 0x140c0200448c060080181900503008010033380180140c0212200c060080184840503075020030180180140c4800400c06008018194050300801003338028030080106200cce0080180140c47c0400c0600801818c0535408010030080180151e0200400c06008018278050200400c064740280140c0211c00c0600801846c0c0200400c060080180311a0211900c0600801818c0503070010030080180140c4600845c06008018
  | 8, 1, 2 => 0x140c02004308c100801818c050800801003008018014780207b00c060080181000c02004018210052780d0051e00800c060046780140c0200400d260080180140c0203300c3e0080180140c02004230060083280e00c1e06800c060080184940c0200400c0600801830c05030080103e0080180140c020a500c0608401830c0511008010060080180140c0200400c062b03d80140801047018020045c8490050300801003018028
  | 8, 1, 3 => 0x313001062018020052f818c050312e010030080180140c1e00800c060840180140c020044b406008018020041ec03018020044e80140c02004330060080180140c07c08010060081c80140c1e008254060080180140c020044b006008018030080112b00c06008018014043452a00c060080180140c0200422c060081c82240c1e00800c0600801818cbc0300801003009298348050200400c0600832819005030044a003018018
  | 8, 1, 4 => 0x140c118042300600801830c2f01408010020047780d0050200400c06005358014d50480400c060093480140c0500400c060046e81c8050200413c060080180140c0200400c061080181900503130010060052f84cc050300400c06008018015320200400cab008018015310200400c060080180140c03c0800c06074018060080107b00c06008018194630140c0200400c02818c0c02004188030080181940503130010060092f8
  | 8, 1, 5 => 0x140c0200401802284018014581e00800c060080180140c0200400c060093e80140c0200400c060093d84f00503008010030080180140c1e00800c060083d84ec050300f020030180280140c0213a00c060080180140c03c0800c06008ea82500c0200400c060083284e5140300801003008018014080107b00c064e001820c050300802c060080180140c0200400c064dc018014310200400c020047780140c0480400c06009368
  | 8, 1, 6 => 0x140c5200800c060080180140c0200400d470080180140c02004040ce0080180140c0200400c062b001830c050302e010060080180140c02004300060080185180503008010060080180140c0114500c060080180140c1e14400c060080180140c0200450c0600801818c05030080100309c018348050114200c06008018014080107b00cce0080180140c02004018020054181840c1e00800c060080180140c5000400c064fc018
  | 8, 1, 7 => 0x30080114d00c060080180140c0205000c060082d80140c07c08018020046b80140c1f00400c060085181900503012010030193480140812003018020045c81cc0c0200400c0600801831c0801003018020052780140c0200400c6f0080180140c1e00800c060081c80140c0200400c065300180140c0214b00c0600801830c050310e010060080180140c5280400c0600801852405030080100301802818c05030080104f008018
  | 8, 1, 8 => 0x140c0200456006008018014080115700c060080180140c020a500c0600801818c0503008180030080185580503008010030180180140c5540400c060080182f00c0200400c0600954834805010d100c0600801854c050300801003005528015300107b018020052f85440503008010030186980140c0200400c0654001818c38030041a0030080182500c0200400c060080180140c0200400d4f008018014080114e00c06008018
  | 8, 1, 9 => 0x58c050300801002005628015610200400c06008018015600200400c060080180140c1c07500c06004e18030080115f018020052780140c02004578060080180140c02004018020042280140c0200400c065740180140c1e04600c060080180540c0500400c0600801818d5c014080100300801856c05030080100301802818c0503008010030840180140c02004568060080180143102004064060080180140c5640400c06008018
  | 8, 1, 10 => 0x14120107b00c060093480140c06c0406402004f280140c0200400c0600966830c0503008010020046680140c1c00f00c060087480140c0216500c0600801818c050200400c020045c80140c1c00415c03018698194050300801003158028194640140c1c00400c068030080106200c5600801801408010030f802004778030080116400c060080180140c0200400c020f47781940c1c004188030180280140c0206015c03018018
  | 8, 1, 11 => 0x140c5c00800c060080181947221408010030180280156f0200400c060080180140c5b80800c020056b8015320380400c060080180140c020045b40600801820c0c0216c00c060080180140c1c0b500c020056b80140c0200400d6a0080180e00c0116900c06008018030080106200c060082d80140c020045a00300801859c05030080105700c0680140c0200400c060082b81c8851c00400c0600801818c051600801003008018
  | 8, 1, 12 => 0x18c0503008010030080180140c4c004018020052f80bc050b80400c020047780140c0206000c560080185d5740140800c060080185cc0503008010060080180d0050203300c060046785c80c0200400c06008018194051c0041ec030180281c0041ec6200c060080180140c0200413c060082d80300801c03018020044e85c405030080100600801819072214080100301801803008010cc018020044e8030080106200c060083f8
  | 8, 1, 13 => 0x190080107b188030180185f80503008010060080185f4720200400c060080180140c0200400d7c008018194080107b1880301802819005110080100301801830c0502004018020045c81940511008010030180280157b0200400c060080180a00c0200400c060080180e00c0117a00c060080185e40c0200400c060080180140c0200425456008018014442980400c060080180140c1d40800c06005788014085dd7600c06008018
  | 8, 1, 14 => 0x194050300814003018028030870106200c060080180140c0200400c060098481949003008010030180280140c60c0800c0600801819405030080108b0188a830c0503008010060083280140c0481100c060080180140c1c004608030080180140c0200404c036040180140c4c004018020058085fc050300801003018028014370d80800c06008018014580200400c560080180140c020a5018020042280140c0206015c03018698
  | 8, 1, 15 => 0x140c0200415c03018698194640140c0200400c0680140c020030181d0046b80bc890200400c0200477818cd201404344030080180140c0201100cce0080180140c0200400d890080180140c0205000c0609c0180140c6209b00c0600801861c0503008010c2008018014440200400c0608401830c050307c01006008018014080118600c060080181900503008140030180180140c0200400c06614018190900300801003018018
  | 8, 2, 0 => 0x14580206000c06008018194050300801003018028014080107b0400600801863c0503008010c10080180140c0205000c060080180140c0200422c0622801818c83030086380300801819005030081800301801819405030081800301802819438030041a0030180286340c0200400c060080180140c0200400d8c00801819405030080100301827818c050300e010030080180140c62c0800d8a0080181946330c0503008010028
  | 8, 2, 1 => 0x1940503008010c230402818cc30140c020040080180140c5106000c060080181840c0206000c06008018
  | 9, 0, 0 => 0x140c11808010030180200640c06c080106200c06008019650050300801003018020064000d0050200400c060046780140c0219301003018020064630140c0200400c02005279014080107b00c0600992006405030080100301802005919640050300801003018020064c34500503008010060080192c4c30140c02004018020064050140c0200400c060080190140c5000801003018020064000e00c0106800c060080180140c0200427403018020064650140c1c00400c06008019
  | 9, 0, 1 => 0x18c050300801003018020064c31000503008010060080190140c0200466c03018020064650140c21408010030180290140c66808010030180200640c214080106200c06008019000050300818003018020060050300801003018020059990140c020046600301802006405030080119700c060080190140c6580801003018020064050300801003019380053496540503008010030180200642f0140c0200400c0200477900005020041ec03018020060650140c06c0801003018029
  | 9, 0, 2 => 0x19005030850200400c060065a430c05030080100600801919405031a30200400c0600a405030080100301802005a29000050300801010018020061a10140c0200400c060080190140c0200468003018020064640140c06c08010030180190140c0200400d9f018020064002240c0200400c060080180140c1f0080100301802006405020041ec03018020059e920c0503075020030180200659d0140c1e00800c0600801920c720300801003018020064050319c0200400c06008019
  | 9, 0, 3 => 0x30c050300801006008016b2405020046ac7b00c06008019014080107b00c060089f0064000140c0200400c060840186a8050300801003018020064c30140c0200401802005a990140c020045080301802006405030080100301802005a890140c0200400c3e0080119e40503008010033cc02004cd90140c0100301802005343ca4000140c02004254060080180140c0200469c0301802006405031a60200400c06008019694050300801003018020064384500c0200400c06008019
  | 9, 0, 4 => 0x140c0200400c066c4020064050300801003018020b40190140c0200400c0600801316405030080100301802005b09014080107b00c06008014be405020041ec8b00c0600801930c0503008010db018020064050307001003019af0080196b805030080100301802006405030701d40400c06008019194050300f0200400c0600a40c03c080106200c0600801924805020041ec0301802006405031ad0200400c06008019014080107b5dc03018020064630140c0200400c02004699
  | 9, 0, 5 => 0x190050307802003018020064050300801003018026e80190140c0200400c06008016e64650140c0200400c06008f2918c05030700200400c0200640c020041880301802004f29190050300f0200400c060065b80140c0200400c060080190140c020046dc0301802006405031b60200400c060080190140c6d40801003018020065b419005030080100301801919405030080101300c0600a405031b30200400c060080190140c0200400c06008016ca4530140c0200400c06008019
  | 9, 0, 6 => 0x140c0200400c06008013aa4000140801003018020045c80140c0200400dbf018020064054c0080107b00c0600801958c050300801003018020064050300801003019be0080190140c0200400c030180200640503008011bd00c06008019190050300801003018013ca46519405030080100301802930c0503008010060088a0064650140c020041e403018029278050300801003018026f240503008011bb00c0600801919005030080101300c06006405030080100301802005159
  | 9, 0, 7 => 0x140c0200434403018020064830140c1c00400c060080190140c1e00800c0630402006405030080100301802005c1930c05030080118e018020064000140c1e07000c060080180140c020047000301802006405020041ec7b00c060080190140c03c0800c06008011d24340140c0200404c030180190140c26c0801003018020064920140c02004308060080190d005030780200301802006405030080105700c060046994ec05030080100301802006465190050300801003018019
  | 9, 0, 8 => 0x140c0200400c06008017165c40140c0200400c0600801918c05030080108f00c0200657d0140c0200400c0600801918c050300801003008014a64050300801003019c300801919405030750200400c0600a40c1d4080106200c06008019544050300801003018020064050309b02003018020046b9708050300801003018020064050c4080100301802004f290140c0200400c06008020064630140c0200400c0200534918c05030080106200c02006405030080680301802004f29
  | 9, 0, 9 => 0x15ca0300801003018020064000140c0200400c06008328278050200400c06008011de40503008011c900c060080190141b020041ec03018020064050800c0200400c06008019000050309b36c03018020060635d40503008010030080190140c1c00400c06008015ae405031880200400c06008019720050300801003018020064c31c805030080100600801971c0503008010030180200640503008011c600c0600801919005030750200400c060064050300427403018020045b9
  | 9, 0, 10 => 0x140c02004748030180200646520c05030080100301802920c0c020041880301802006514030080100301802005ac90140c0200474403018020064001940503078020030180280000c1e0081880301802006005031d00200400c060080190140c021cf0100301802006405030080100301802005bc9738050300801003018020065cd0140c0200400c060080190140c02004730030180200640503008010c200cc10080191fc650140c0200400c0600a40503008011cb00c06008019
  | 9, 0, 11 => 0x39c0503008010030180200640503070010030180200467930c0503008010060080149e405030080100301802005d790140c1c00415c03018020064050310f0200400c06008019014080107b04c03018020064341c8050200400c06008019674630140c0200400c020065d60140c0200400c060080190140c7540801003018020064001900503078020030180180140c7500801003018020064900300801003018020047490140c020043300301802006405030080100301802005d39
  | 9, 0, 12 => 0x30c2f0140c02004018020064050300801003019dc008019194050300801003018025ae4000140c1180400c060080180140c0200476c030180200640503008011da00c060080197640503008010030180200640503078020c200c060080191cc050300801003018020065140140c0200404c030080190140c3187001003018020064650140c020041a003018029760640140c0200400c06006405030080100301802004e39014080107b00c06008013ca405030780200301802004e19
  | 9, 0, 13 => 0x30c05031e102004018020064630140c0200400c02005e090140c0500400c06008011ba405030080100301802005df9190630140c0200400c020065de0140c0200400c0600801925005030080100301802006405030080100301802005dd9190050300801003018015ae40503008010030180200513900005030080100301802006005030080108c00c0600801920c050300800c06008011d24050c40c0200400c06008019000050307c0100301802006005030080100315806008019
  | 9, 0, 14 => 0x24805030080100301802006405030080109900c060080190140c020045dc03018020064630d005030080100300801901475020041ec03018020064380140c1c00400c0600801979c050300801003018020064050307001003018020047490140c798080100301802006405030080100301802005e590140c0200400c56008011a6405030080100301802005e491940503008010030180242e40503008011e300c06008019788050300801003018020064050300801003018020059e9
  | 9, 0, 15 => 0x140c0200423c060080123a4050300801003018020f4f290140c7b00801003018020065141c80c0200400c060080190140c07c0801003018020064d201408010d100c060080190140c0200400c067ac020065ea0140c0200400c060080191940503008010030180219e4630140c0200400cc10080190140c0200400c06008017a6405030080100301802005e890140c1c00400c060080123a4650140c0200415c030180290140c0200400c06008014be40018c050307001003008018
  | 9, 1, 0 => 0x140c0200400c060093f006400014780207b00c060080180140c0200400c06008017ce405030700100301802004cd97c8050300801003018020064c30140c1c00400c060080190140c020047c403018020064050300f0200400c0600874930c050300801006008014d2405030080100301802005f090140c07c0800c06008011ae4640140c0200400c06005ef943005030080100301802006405020041ec0301802005ee90140c020047b403018020064640140c0200400c06004679
  | 9, 1, 1 => 0x140c1c00400c06008017da405031f50200400c060080190006518c05030080100300a00018c0c020041880300801830c05030080100600801246405020041ec6800c060080190000503008010cc01802006005030700500400c06008019194380140c0200400c0600a4050300801003018020fd27930c05030080108f01802006405030080100301802005f490140c1e19a0200301802006405030080107b00c060080190000503008010c2304020060c30140c0200401802005299
  | 9, 1, 2 => 0x3480503008010030080119a4630140c02004308030080190140c21408010030180200640503008011f900c060080190140c0200400c060080108a405030080100301802005f89450050307001003018020064000140c0500400c060046e81900503008010030180123a405030080100301802005809014080107b00c06008015ae405030b50200400c020056b90140c1c0b50100301802006405031f70200400c060080191940503008010030180223a40c0200418803018020048e9
  | 9, 1, 3 => 0x140c0200400d1701802006405031fd0200400c060080197f005030080100301802006405030080100301802005fb90145803008010030180200640503078020d100c060080196d0050300801003018020065750140c0217700c060080190140c1e09b02003018020065870140c0200400c060080190140c68c08010030180200640c020041880301802004cd90140c020047e803018020064c3014bd0300801006008019194c30140c0200400c0600a4c3030080106200c06008019
  | 9, 1, 4 => 0x140c0200427403008011de405030080120200c0600801971c05030780200301802006465450050300801003018029000730300801003018020060000140c0200400c6f0080180140c1c00400c060088a0064650140c0200400c060080190bc05030080101300c020064650140c2d40801003018029000050300801003018ac006005030080120100c06008019800050300801003018020065ff0140c0200400c060080190140c0200400c06008013ca5fe0140c0200400c06008019
  | 9, 1, 5 => 0x140c1d408010030180200640c020041880301802005ac90140c0200401802005271ae6080140c0200400c060080190140c1e00800c06008016f2438014080107b00c060080191cc0c020045dc03018020064002500c0200400c060080180140c0200481c03018020064050300801003018020060691000c020041880301802006405030080100301802814019000050301f02006008011ae0c30d0050300801006008019030080106200c0681002006405030080100301802006039
  | 9, 1, 6 => 0x20c050300801003018020064650140c02004638030180290300801062638030180200649e0140c0200415c030180290140c0200483403018020064000140c02004018020042280140c0200483003018020064720140c1c00400c060080190140c0200482c03018020064050300801003018020060a90140c0200400c0600a0900646318c0503008010030080190000503008294030180200600c0200436c6200c060080190140c0200400c064e00200640034805010d100c06008018
  | 9, 1, 7 => 0x140c0200400c060090b00640503070010030180200469910005020041ec03018020064650140c0200400c060086e9190720140c0200400c06006405030080100301802004f690140c1c00400c06008011ae405032110200400c06008019194720140c0200400c0600a405030780480800c06008019840050300801003018020064050300801003018020060f90140c1e00822c0301802006405030080101300c0627c0190140c0200400c060080183a405030080112a00c06008019
  | 9, 1, 8 => 0x140c020040640301802006405030080100301a150080190140c0200400c060083d006405030080100301802005ef90140c1d4080108b00c0600640c0200418803018020052790140c0200400c060080119e4050300801003018028500190140c0200415c03018020065670140c0200400c060080190140c0200484c0301802006405030780207b00c060080195d405030750200301802006405030a601003018020052790140c8480801003018020064640140c0200400c060046e9
  | 9, 1, 9 => 0x140c1e00804c03018020064630140c0200400c020059e919005030700200400c060064050307803c0800c06008019864630140c0200400c0200640018c0503008010030080180140c8600801003018020064000140c4c004018020052f80140c0200400c060080185e4380140c0200400c0600801919405030700200400c0600a405030080680400c0600801918cc30140c02004018020064050300801003018020053690140c8580801003018020064650140c0200400c06008699
  | 9, 1, 10 => 0x40c0c02004188030180200658f0140c0200400c060080190140c0206000c06008011a64532f00c0200400c060080190140c878080100301802006405030080100301a1d0080190140c0200400c06008017da472014850200400c0600801930c0503008010d10180200640c020048706200c0600801986c0503008010030180200640c868080106200c060080190140c1f00400c0600801336405020041ec03018020046e918c05030080117700c020064c30140c0200401802005159
  | 9, 1, 11 => 0x140c4607802003018020064000140c0200415c030186980006519005030080100301a2221900503008010030180190140c0200400c06008018864630140c1d4080100300801930c920140c0200401802006405030080100301802880019194050300801003018c100a40503008010030180287c019014080107b00c06008014a64940300801003018020046790140c020042741300c02006405030781c00400c0600801901470020041ec030180200659d194050300801003018029
  | 9, 1, 12 => 0x50300814003018020060000140c0200422c062280186740503008010030180200646334805030080100300801930c0503075020040180200660830c05030080100600801918c05030080105700c020066250140c0200400c060080190140c1c1a601003018020064d20140c06c0400c060080190140c0200400c06008011a6405030080122400c060080190140c0200400c0600a2300646320c0503008010030080191940503008010c200c0600a405030080101901802004f29
  | 9, 1, 13 => 0x140c02004308030180200640018cc30140c020040080181940503008010030180267a4001940503008010030180280140c0200400c0630402006405030080100301802005e09
  | 10, 0, 0 => 0x140c0200400c06008013ca405030850200400c060080190140c020041ec03018020064050301f0200400c060080190140c0200400c06008014be4920140c0200400c060080190140c020045dc03018020064000140c0200400c060080180140c0200400c06008016f240503008010d100c060080190140c26c08010030180200640503008010030180200515914c050300801003018020064630140c0200400c0600801900005020041ec0301802006005030080109d00c06008019
  | 10, 0, 1 => 0x503008010c200c06008019000650140c0200400c0600a0050300801003018c10080190140c0200400c06008011a640018c0503008010030080180e0050300801003018020064050300801003018020046790140c0200415c03018020064830140c0200400c060080190140c1d40801003018020064650140c0200400c06008019
  | 11, 0, 0 => 0x140c0200400c06008018
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

def symsG : List (List (Nat × Nat)) := [[(0x7ffffffffffff0000000000000007ffffffffffff, 51)], [(0x55505552aaaaa2aa0aaa5555545555505552aaaaa2aa0aaa55555455, 1), (0x14000000000000000000000000001400000000000, 50), (0xa000000000000000000000000000a00000000000, 52)], [(0x5545000000000000a000000000005545000000000000a00000000000, 1), (0x41554aaaaa8aa00000000000000041554aaaaa8aa, 50), (0x1000003000000000000000000000100000300, 51), (0x20aaa5555545500000000000000020aaa55555455, 52)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 112)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)

theorem ori_ok {u ys} (h : NatRun (mask 112) (goal 112) u ys) :
    NatRun (mask 112) (goal 112) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 11 0 (NN s)

def poolG : List Nat := [9017106793349236, 11267825450786980, 12394858105913507, 15772505159615605, 32663200724057201, 31535103908941992, 74320397697502320, 66439119909278833, 12395903873827030, 16897326058740899, 36040900397403248, 12395909282434160, 11268903401542769, 66458889640680560, 12394803340890224, 16899502479888496, 66440197861172336, 73195603765660784]

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
private theorem z7_64 : ∀ i, 64 ≤ i → i < 65 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 64 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 65 → Z 7 i = true := (range_split (range_split (range_split z7_0 z7_8) (range_split z7_16 z7_24)) (range_split (range_split z7_32 z7_40) (range_split z7_48 (range_split z7_56 z7_64))))

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
private theorem z8_528 : ∀ i, 528 ≤ i → i < 532 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 528 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 532 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_8) (range_split z8_16 z8_24)) (range_split (range_split z8_32 z8_40) (range_split z8_48 z8_56))) (range_split (range_split (range_split z8_64 z8_72) (range_split z8_80 z8_88)) (range_split (range_split z8_96 z8_104) (range_split z8_112 z8_120)))) (range_split (range_split (range_split (range_split z8_128 z8_136) (range_split z8_144 z8_152)) (range_split (range_split z8_160 z8_168) (range_split z8_176 z8_184))) (range_split (range_split (range_split z8_192 z8_200) (range_split z8_208 z8_216)) (range_split (range_split z8_224 z8_232) (range_split z8_240 (range_split z8_248 z8_256)))))) (range_split (range_split (range_split (range_split (range_split z8_264 z8_272) (range_split z8_280 z8_288)) (range_split (range_split z8_296 z8_304) (range_split z8_312 z8_320))) (range_split (range_split (range_split z8_328 z8_336) (range_split z8_344 z8_352)) (range_split (range_split z8_360 z8_368) (range_split z8_376 (range_split z8_384 z8_392))))) (range_split (range_split (range_split (range_split z8_400 z8_408) (range_split z8_416 z8_424)) (range_split (range_split z8_432 z8_440) (range_split z8_448 z8_456))) (range_split (range_split (range_split z8_464 z8_472) (range_split z8_480 z8_488)) (range_split (range_split z8_496 z8_504) (range_split z8_512 (range_split z8_520 z8_528)))))))

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
private theorem z9_464 : ∀ i, 464 ≤ i → i < 470 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 464 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 470 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split z9_0 (range_split z9_8 z9_16)) (range_split (range_split z9_24 z9_32) (range_split z9_40 z9_48))) (range_split (range_split z9_56 (range_split z9_64 z9_72)) (range_split (range_split z9_80 z9_88) (range_split z9_96 z9_104)))) (range_split (range_split (range_split z9_112 (range_split z9_120 z9_128)) (range_split (range_split z9_136 z9_144) (range_split z9_152 z9_160))) (range_split (range_split (range_split z9_168 z9_176) (range_split z9_184 z9_192)) (range_split (range_split z9_200 z9_208) (range_split z9_216 z9_224))))) (range_split (range_split (range_split (range_split z9_232 (range_split z9_240 z9_248)) (range_split (range_split z9_256 z9_264) (range_split z9_272 z9_280))) (range_split (range_split (range_split z9_288 z9_296) (range_split z9_304 z9_312)) (range_split (range_split z9_320 z9_328) (range_split z9_336 z9_344)))) (range_split (range_split (range_split z9_352 (range_split z9_360 z9_368)) (range_split (range_split z9_376 z9_384) (range_split z9_392 z9_400))) (range_split (range_split (range_split z9_408 z9_416) (range_split z9_424 z9_432)) (range_split (range_split z9_440 z9_448) (range_split z9_456 z9_464))))))

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
private theorem z10_24 : ∀ i, 24 ≤ i → i < 27 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 24 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 27 → Z 10 i = true := (range_split (range_split z10_0 z10_8) (range_split z10_16 z10_24))

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

end PEqualNP.Outside.L_meta_7404_aux

theorem PEqualNP.Outside.L_meta_7404 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_7404_aux.mainG PEqualNP.Outside.L_meta_7404_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩
