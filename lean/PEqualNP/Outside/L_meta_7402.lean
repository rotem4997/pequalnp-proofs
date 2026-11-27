import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

/- The circuit normalization and frontier replay are adapted from the checked
   proof of L-meta-722 by Digger-Rockwell. The finite data concern this graph. -/

namespace PEqualNP.Outside.L_meta_7402_aux

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

abbrev fG : BFn 8 := fun x : Fin 8 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

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

def rowsG : List ℕ := [1, 1, 1, 8, 8, 10, 12, 24, 28, 32, 32, 33, 33, 34, 34, 34, 34, 48, 49, 49, 49, 49, 49, 52, 52, 52, 52, 52, 97, 97, 97, 97, 97, 100, 100, 129, 129, 129, 129, 132, 132, 138, 138, 138, 138, 138, 156, 156, 2, 2, 2, 16, 16, 17, 20, 24, 28, 64, 64, 66, 66, 65, 65, 65, 65, 72, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 98, 98, 98, 98, 98, 100, 100, 130, 130, 130, 130, 132, 132, 145, 145, 145, 145, 145, 156, 156, 100, 3, 5, 9, 9, 40, 14, 44, 25, 60, 40, 160, 35, 37, 38, 42, 50, 162, 112, 51, 53, 57, 113, 177, 53, 54, 60, 116, 180, 99, 101, 105, 113, 225, 101, 108, 133, 137, 161, 193, 133, 164, 139, 142, 154, 170, 202, 157, 188, 3, 6, 18, 18, 80, 21, 84, 26, 92, 80, 192, 67, 70, 69, 81, 73, 193, 104, 75, 78, 90, 106, 202, 78, 77, 92, 108, 204, 99, 102, 114, 106, 226, 102, 116, 134, 146, 194, 162, 134, 196, 147, 149, 153, 209, 177, 158, 220, 228]

def xsG : List ℕ := [0x7c00220bd04285f7e1f8311e3e000001e0200079f07c1807, 0x85f7e1f8311e7c00220bd0420079f07c18073e000001e020, 0x38b1c5f1062c58b1c5f1062c5c1860f800140c1860f800140, 0x190011ffd0301fc28842087f8c0000ffe0180fe00000001f8, 0x1fc28842087f990011ffd0300fe00000001f8c0000ffe0180, 0x2408fe8440001224ffffffea10007f00000000007fffffe00, 0x3224ffffffea0408fe84400010007fffffe000007f0000000, 0x3fff210820801fff210820800fff800000000fff800000000]

theorem rowsG_len : rowsG.length = 194 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 97 := by decide +kernel

theorem maskG : mask 97 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 97 zs &&& lo 97) ≠ lo 97 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 97) (goal 97) s xsG) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 97) (goal 97) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 97) (goal 97) s xsG) :
    ¬ HasCircuitSize 8 fG 11 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 11 h
  have hr : NatRun (mask 97) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 6 => 2
  | 7 => 136
  | 8 => 1066
  | 9 => 888
  | 10 => 43
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0xd7bbd8a061460435
  | 7, 0 => 0x47a7d3394729672145d2737945ae89994434299743ca838443013eeb41fd45b040d28957408452113eea036f3e704d023bfcf5033bdcbafd3b600024384fd81f367bbf1a344e10f133e5e89d31b9222a304b918e2fe1627c2e57dcc82e238cf12d16d84f2cbf5bfe2b8a21ea2b7a55442902737427fb547f2662881024cc7a16248442bd22ae0bc4227164af2200e0b221df1c122194e6b21fba22b21fada83d1f6ac73f1efe1c8e1eeee64b1d3883e01b2eec831b06c23919ede80a197839611865f39816c16c2316b8d9f413d4b3800dd51ef60dbd4a640d8718d10d5b3f980a6b202509af1d1a096eb93608993a9904b9d2b60208293301b533eb01b33159
  | 7, 1 => 0xcbd43192cae699b0bff43054bc021fc8ba1c6e8ab9bc9dceb8648d4fb33bcce3b27db793ae4a0340adea4fe8ac3d30baa8a5df83a72179c0a70507909ceac49a9917908a988f72f39418974a936a4a208fe147048d28c27c8c4f37f68c4b4c4d8bdd66d589b5b86a850d197680efef34807baac17c3ca6f9788a755c77a00c52778806ec76c336e37451973d73c703fd7162b1fb7138a7d5710b71b56f3c809d6b51b20d6ad77e0f692379d46806b0ed65d4264a64464bb5636a019b61a7eb235eb9a91a5d1242205bcec7655b2b173859c01a9259462d2658deacb656b4bd2e557ac47c548f1a964dfd980d4c5429c24ba996534aa7e1484a19059b49f70fb1
  | 7, 2 => 0xf9945f9ff91ce1abf44c6b88e5429b95e0831805d5d9be3ed54c003dcf0f7b14
  | 8, 0 => 0x803872a07fc258507f6327507a7acdf078f23af0785757a0761034407443a5c0739a6f90693b60c066ef574064d6eb2064c13cf061b917d05fe136a05d3fbe505c54f9705a5f717058ffc65057f93bf055b7aeb05432aab04e4123f04b94b2a04a0c6020487c166046fd21b046a0c600447896d0426c32703c976d403bb60f103a6a7a0038b502f03470857032f3b7d03293d19031e8f56031a9db10314a76a02bf8a8f02b5620f022f5b960226ba0b01f7e40501f1852b01e24547018423f4017e9f6c0168a1d70163f2e10139f1890133928e0130a5dc00d3389300c0b8c400ac72b4009e518d005bd54500426b500030b569002e140b00203ea40002a385
  | 8, 1 => 0x10961ce1108d06c410798d8f106538bf1052745a105158d610432407102ca4de101175240fdd6c200fdc3b2c0fd7cfc00fbbe7f50f1d566c0f04d9830eec68520eda331f0e8dcf4e0e7d9ab00e6f8b3d0e4dda130e1870d80df760220d983c920d7402380d63662a0d492d3c0cee5d4c0cd866780c90e5e20c7b9dfb0c7051510c47b2dc0c314d6d0c2fb2900c048ef70bffc0af0ba6595a0b974be20b94b9010b73acef0b62b5bd0b612a6f0b3513fc0b1a6ff60af2f98f0a7e850d0a2bc39f0a083fcc09b4285b09ac4e8309556b9b09448c8b08d1197d08cf9f6c08bad27c08b69f2d0891d271088fae420884e81208427702083b7685080f3c17080a9119
  | 8, 2 => 0x18aecc91189cfc581883bb091863cd9c1853765a17f8368b17ebd5cc17e25848171d9b41171ac20e1712498616e0369d16a325001680495016716eeb16626d481634b457162c1e0716232c6715da5a3d158f70ea15843c58156fd5c915527efe154c24db153772eb153408cc152365c1151be7b814fad83614e013ce14921d4614532fb11444127814344d50142ce73e14180a1614132ba513c565a513be99b9138d52f9138b867f133a4b0c1327c71a1327c58f130c76c212fc7a5412f14d3912df759712d3987b126cf29f124f27dc121a26c61206977f11e8ee2a117473a7115e7f4c115429141147516c1117b86610c188e810b1a23d10afb53b10a9cfa1
  | 8, 3 => 0x2320966322f90fbd22d3a50f22781dcc22670f87224f9ba922271afb220e43d822089cf521ebc87021bc56202189c09220f3cadd20ca8c7c208679fb2079771a20778d6b2047100b203ff3df2039c324203915dd1fada83d1f897b391f2fd5d71f0f88e61ef863d11eda12e81ed02cad1ecc2c531e9274621e5ab54a1e54b46b1e4f15671e4cb7371e4844331dea59ac1d7e64101d2569ad1d0d4d2b1ce2dfb61cb76de41c8075831c7acd771c6c70561c60107a1bee757b1b3cbf6a1b23ff3d1b0f5e281aeda2f51ac2ecdc1a9de2b51a7464991a4af73d1a49ad041a3df52d19d3e8c119bee37d198733631921c2c319211ccc18d3b05918c0dc2618be603b
  | 8, 4 => 0x2c74621b2c4233992bead7fd2bcbb4d32b8c06032b57ba6a2b287f572b1eaf0c2b0e5def2acfa4ea2a7c92552a7a746e2a24a50c2a1812fa29ff991629de935e29de54ff29ace2402986cf2829682212293873ec28fb3a8328dafbbf289ef797286c978c283fd8cb282d6759280cf761280131e827d8369327c7273b278d3c6b2777385427701841273b93a62738f1822728123b27234a4326a9c8a2268956de264b7503262d8ed6261868ee25a3032725993d482591eeda256df99a256c5b00254169c0253944512530d71224dbd67424d2632b24bf30dc24a8419624499b1e242e280123ef298823d1768f23b2ba3b233f7659233725a12331daa223304003
  | 8, 5 => 0x36d4db9936c7add236b7ce1a36afbf4936aeac8c36a4fe5736a0612335c250ee35a21f9835898b2f3572e96e35454b6c34bef98634af84fe344378ed34332f6d34244088341fe0af3415a66333fbbe6533f9a53233a5c97733a5b66e339bc9743375eaa7335b9f993321b26a32f51d1f3266ab86324ec45a3242d9c0310cd90a30be0d00308ede2f305a361330597a663032910e302e2b3e3023fe283011805f300df6fd30078cae2fe1627c2f14afb62f0a9d5a2ef6ce872ef58a1f2ed18c692ebed06f2ebdc5cd2e3c4ea92e26bdea2e1023ba2e08601d2dbaab5c2d73a28a2d427df92d33992e2cf492462ce2af292cca4f672c8cdde72c852ee12c7cb966
  | 8, 6 => 0x43bb39e043adce54439893cf4330fa0f42c3fc0442c1db304260dcf1425e13f4424a49dd4244dbc042059d2241c53cf5418fc3c1415a392741563b00414b01754104951a40b1e214402282493fd5a6e43fb44a283f700d9e3f5348373f31927a3f24ef3b3ee5c9443edbe3563eb150203ea623403e6385983e5a12643dcc00503db688b33d86a96c3d50fda23d3f604b3cb7c56f3c28b5113be9ae373b24f47b3b029d0e3ac686f93a8a3b173a7461763a65057a3a4b50f539e9fae539bac40539a2002d3977e037396abb9b38b0e0143848e7173806916f3804c6b937e3768737d6280a37b1f85b375c41e53744ad6637424834372a19f6372058b4371aa564
  | 8, 7 => 0x4d16d8054ce5f2ae4cc803044cc0e99e4cbb00cb4ca0ab664c9a47064c589a294c010f164be1ff764b4331094b24a8824ac08d6e4a9d92c64a8b171d4a5e45874a21b63a49e0732449bb560949b6430a495d7e0a49555f7749552a9e493d3c6e493503dc49317c814907221e48e7797f48b60f17489bba3c484e96ca484ab61a4816535b47d4ce6d47835679476ade6b474edf1d473168c146db9a9646ad812145edc48445de6bf345db672945ad2c0245a56960456343444556005b453165d4452b20274528e51d4527127e451c29ef450c9f9a44ff7a0844f9e31a4481cb30445e3ee7443d1ff7443bc9c14425814b440a0b8f43ed4b5f43de86f343d4c1bd
  | 8, 8 => 0x5a89fbf65a1eea31598ab90459682b80591f21f358fddddc58c2052858644deb5849b5405831c3e557f9f50c57db7705576c5455575efb7d57585eac573a5c6957357746570145a556a605d656841521565e5e535612281855e5e9e255d289055573bf945528bb2154fd096254d18cd554b652d05466889753f0fe7c53f09fee538ec76653741bab5317621b5306ccca52c4f121529e862e5282c13b525e04d052537b87523acdf052082589517d7ed8517a5e565178443e510addbc50df27e5502223fe5013a4814fda41374fd5a40e4fb8fd2b4f9e955f4f7ba7d34f666d1b4f1ddec24f1c8a8b4f003a024eff44464ee85a9c4daf27e74d5c0ccf4d3828c2
  | 8, 9 => 0x661de78c65aa320b659e2b3d659cc2aa65203e67650e920f64d9a5a364b99be764accf2564a8800a64a6ef226476ca5b644781cb63a9d3586369ed27636108c8635addab6344febd6343c965631b47426313087f62fc6a5662550db9624c0b506246cf0761cd10326194857d61728b4261361afe6120e83760e2423060c6c0f860ab6702608450e05f9f12965f6240485ee914a45eca7e455ec8e2d85ec83f085ea6e39a5e8fd0675e4bf2285e3438935e3247c65e05d2ee5ddda5225dc096b45d87e2335cda16045cae67f35c99e0fd5c888bf65c0f0ba05c03affb5ba5140b5b8c95e05b64e0955b374e1b5b1dc2055b16a2d65aa9bb605a8fe69c5a8a8f16
  | 8, 10 => 0x723bf64f71bf24507178450271147ad1710acc9c70d3384770c7c45a70c58ced70c496cc70b2b3756ff877d16fdfb4036fb3569c6e570b726e4a868e6e0e57fe6debed8a6ddaa9f96d5a374f6d5937876d351b5c6d34e3d26d1e05616d01333a6cea1df46cced3ba6cbf5c4e6cb4929f6c72de6c6c5ecf716c36daf16bff64316bf7cbc96bf5b5fc6bd993a56ba5d1186b7d616a6b0540676aeb513c6abf48ab6a23a8af69edd77769c9f6a6698284a96969f24d694c3ba76938c8fc68d1134b68c1fafa68b389d768ad6861688f02446880ee0368627f0e6818ad2867f0a3af67abb9266772ad20676a0ea4670f3bf066f93a6f66f4dba466c54a1b6655042a
  | 8, 11 => 0x7fc64a0a7f9963f47f5803477ed33ad27ebcca0d7ea239667e712b0f7db8d3867db8bb7a7da609917d17059b7cf2530c7cb499c57c5aa4827c158c207b95a57e7b7ce4167b2ea7657b0cc3527afbed1f7af321aa7aabadd57a210b1879d6aff879981cdd798f9f0178df1981788b53a67868935077f14e5677dd8092777fec8a776ee183775654c7771d93b4770c9dd57703ce8e76f5076a76dd9e25768a2d317682e2ce7666d60c764ae8e775ec960275c9e24f7585f9b87582f37275680320755a727e751cbad474cdf40574c1995873ff0bc173f8f1ba73f496fc73e961cb73e1a65973ab65bf737f3a627356780a72d6706e72b3b905726c5ded724998bf
  | 8, 12 => 0x8f1bf8a68f1564c78ef36a7f8eb975508eb3cd178eacf6b18e85903e8e40fd4b8d6f4c748d1470ae8babd4288b640ec88aea179a8aa5db108a11b0c889ff520289f114f089ef5af089d9b5d089ca094c898adc3e897f53f18946a5d6891a6ea88914dace8894e008885958bf87fa84108762737887581c068747c77c872d1f3086fffd9086b4914f86b26cca866bfa278635e88785c6968b859af43585958487854c6cb38497628d846a3d5184643f6883e8618783ba6ee5838d86c9837fc968836cf0638369758d832c888a8310875982e10fd882da9ad282d20da781e9934581b8c669818ae8ea817d8dad816c621480fc721f807a339f805269d57fe8072a
  | 8, 13 => 0x9d4496d09d147f879d0e5ee59d0bc4839c51fdcc9c43b2839c15e3ab9b6a3b679b2006b79af5424d9aea7af49ae4fb159ac83c069a9889fe99ff91f299e34f0299c25f4699a9554a99882bf899607daa98cfede6986bfee79856e38b9806080297dafcdf97b81ffe97679de69734464696f4430996a7cfe196946741965e2f56965516e496031c9395dd3e38955913439558f49b9546aa2095259e2a9513e0a194943eaa940b712593ebdc8993dc14fd93bdf225926c93fb92610d7b9232944d9224ba4b91ace296918e5e6c915d802c91400044913dcb4f90fcdc6290f7984990b70ea4905318ad8fc22d038fb798a28faf61ad8f56ffe88f45cd4d8f27c105
  | 8, 14 => 0xb634de58b6180ec3b6053d39b5c4e97fb59eb91cb526b0bfb4debc56b3e335d3b36f68a3b2e7bb02b28acfe9b269c9a7b1ff1e0fb1b348ecb1aea90db0e41a5bb0cd9c5bb0bcda11b0333a85b01352e5af80b798af6f350aaee6596baebe9aa1ae9694e9ae07d338ad8d2fffac4a52faab28a0e6aad2789eaacda55ea9e519fea95c4681a952ca9ca9137294a8e458c1a865405aa8376cdba81b5073a7c90cd5a7adb495a6d3d6b7a5ae0c33a3c70458a3c5cd88a3a76972a3356e4da32a12dea2b4d27ea219a6aea163bb5ea0858ab2a06abc1f9f902d0c9efdf35f9ec3285a9eb577869ea544b59e7995059e60cd6b9df24f649da997aa9d89b55a9d54f289
  | 8, 15 => 0xd34e2ae9d22cfc33d22198e0d1443d71cff29c34cf15b4a0ced8c286ce549c5bcc106b13cbbb073dcb2ac27fcaa65c2ac9e207bcc9907ee9c915ec54c8ed69fdc8e1545fc8aed920c8689dbdc8686bf6c7bba2cbc7a1e199c6d0ca08c658f39dc63ea630c6358765c61a8e21c58a0b59c51ba784c511ed02c433534bc3bd26d2c39e60c2c318d17fc303449ac2a1e7a1c29518e7c279657ec155c8cfc0c5c86dbffcd662bfd58626bf76ed22beca5543beba81a4bea1a541be690c53be587d93bd7f6631bd51203abd30d0b0bc90573abb1e938ebb164658ba7eb032ba623c03b8de3e6eb85c8807b85582b8b844e1dbb8441380b6f0cdb7b6b3f3f9b65252c4
  | 8, 16 => 0xfe5e8275f91ce1abf39de580f30c5812f2eebaf6ef290e1beec082e6ed97e502ebd6f8d0eb76d5bce9895b3ee8bea0bde7868f07e7439118e6c924f9e6504ce7e52dbea1e523acefe4b3fe87e458036ae29f9157e26ea595e25e6c08e0dbabe9df6e466cde921846de30a86ddd2829fadc11665cdbfdc193da14b500d9e45857d8dc35f0d7c1dc58d6281482d607e605d4b78822d4503c1ad40a3b2dd3ec807fd3e8b2b0d37866da
  | 9, 0 => 0xa68d57b0a63708d0a62070f0a4f61f30a45b6510a2bc39f09c48b2309ac4e8309aab3990990533009861745096c220009667e8b093adaf4093975c208dbded008d959ec08d145f2085f7c11085f1af108427702083a0e4007f76d7507ba0d8b06c1a428068b9e1506861840066ef574062cd7b206283a0105dbec8605d3fbe505b01f8f0581ed820562a02f05467db0050acfb804e3fae604dd95720447896d0418c79e03f6cce403e8408303c86f1d038cd54f0384754e036dccb502acdce302abbbf20273898a01edfe7101e36d8401c5685501ba9e6e01b0b07201affdd101a18ddf0139f189012544c100e4334200ca2805006270ed002d3783000d1794
  | 9, 1 => 0x164d5e4c1620b2e515c4ea5a15843c58156f5f5b1538f80b14fc95a914902def1473708f147088c21424060614132ba513f560fc138f904013880266137aa341136f7501135ae3a613379fb212d1677d128c3700128569d9123eaac9123387d1120700701206f58c12010e3e11eb06e211e8ee2a11cfabdc11ce17d61131d7c610e4974710d94d7c108b13c2106837021055907f104310920ff9cfc30fd53b420fc942d00fae56150f9747e50ec9fc0a0e45cd060e4052470e145eab0dd9f20c0dcaf7530d7492b10d4b360b0cd5f0420cbd25730cba4b300c75ac720c6a367b0c5698550c3701740c3320c10bd327d00b7449fb0b64a1660b5dfb150aa0b789
  | 9, 2 => 0x220e43d821baab8f215d8e272133c71b20d15e95204c44cc20376b8a20162b471ffb3d9c1f897b391f8614c81f800bb01f5298961f3caa981f2484fd1ed64a501e83b5ae1e666dec1e54b46b1e539fe81e4b1c4d1de27e731d42a18d1d148be11caff9911c821f5d1c7b0d4f1c6c70561c6b6a991bee757b1bd3b0f31ba423cb1ba2c35c1b70addf1b6af0a71adde7441aa3cfc81a817c0f1a74649919ceb8a619c3450518d30872189d1906187073d118672502186312e81841b7311837c0d118323afc1828350317cb6b9917b10185179c5e0b179a8079179443c8176ae071174614a3170b2c7f170730a516ed7b6a16d454d316c006da1665d1091655e228
  | 9, 3 => 0x2c516a392bcd39f32b8c06032b74bd872b36f0a02b336a702ad4e2702acfa4ea2a84ec4b2a4642fc2a3d1ed32a1ebf332a1d0b9629d6c10229d3219529b62735296822122935bfd6292c6fe5292a77cb292991ef290e933028c0bf14289ef797288cddd92870e47728689760282e792c280cf7612801253827f8f36427ccc5c7279f12e3279def0f27564a682725a8f326b2ee6526b25b90269b2b9d268cedbf26714829265d92182648ddbb26346d9e26205876261f934b25c277fc2556630d2543d29b24dbd674248a7edd23e3057c2382bd9b237bce98236e2c452357f7b3234efde12328b3b72319628c22ee739722d0acc322b0ca9c2229a281221caf80
  | 9, 4 => 0x377ea3ce3774c87d37711432373eb616370285c936f9e9ed36e356d936da947a36c0a3a2366e0c563654389e36422e9535f8335d35c59a2335a21f98358a20263529690c34dd880934af0e313489f5633455bf0f342074643415a663340cb27633ecbbe7339d06363385f066337b9cef3375eaa73366ce4b332725bb326ce2a831c7742231c276b7316dfc69315724003150b3a43150624530d40c9330826d0c307aca4a306088bd305be80430597a66302e34c0300a48592fe1627c2fd3e9d22f8ea12f2f4f2dce2f44c2b92ec67ce42e8981e82e6f215a2d8d16932d5731c72d3349352cbcc0312cadfa9d2c93178c2c88de9a2c84a89d2c743a862c6bd44d
  | 9, 5 => 0x4461f59c44433efb442bc1dc4410d0b143ae3b674384882243776f15431406e042fa44bf42af191d4286b8774260dcf14232e9a64230621642059d2241f0f05a41a9c4a241a1cdf8419ab1fe4139fe4c40f2f3ea40cd6d713fda21df3fb0461d3f45b0543f03db853ec90e503e6b88703e471ac63dff89883dd7747e3dcc00503d9568fd3d8ff9473d3cfb3d3cec540f3c995c183c92d0703c67b9c43c5c8e443c53ccb63b845e593b6249f13b6006df3b5357193b2b79093b1f8e953abf71143a9983be3a89ec663a62e0b039fb299839f4aa4e39f312dc39d4b68a3966381e38efc6e4386f48663862ed49385e7e4c3853339d3839107b380c000e3804c6b9
  | 9, 6 => 0x504c0b98504b55285014c38c5001a1a34fd233b44fb299df4f3c1c034ea59da54e6fafee4e66db724e2a93db4e2a91a54dd696634da956fc4d8f98164d7bd7da4d6ce6344d45a22d4d3828c24d200f134d018c804cfcb81b4cf39c514c6b93d04c57e84a4c566dcb4c29632d4c2180f94b4af4174b2cbd954b11c71c4ae589544ad6fc654a9036bc4a60612a4980e14d496a0528493d3c6e492fca4f4920eb3948e7797f48bc295248b9ea46489d5e00488d9dc7486f81a5474da3b24721f278470d4b5c46a699c84681cb5d4667dcd64632738f4618554145bbdcd6459ced20457ea4b9453165d445081b0e44e4733744d748de44cefd4644987ec04481cb30
  | 9, 7 => 0x5d82e91a5d1e2f215cbf09575c8c34ab5c0828bd5bdc75195bcfdd4e5bc25b2c5bc00f655bae49bd5b35b3315aaabc295aa651da5a30e4015a13d78f5a002267595eac3959592664593ecf4959398f8858dce12f58da90b158d3754058cc2a905885cce5588091a45849b54057a9f79e5782d480575efb7d565fe37356576a8456499a04563f828c55bcf36d557de172556dd6255562460155193f7e54e74a5454e3a1a654cf183654b67ba854ac849b54a6677b549c4bfd54071364535067ed52b50c1b52a4aeb652a0b13a524969bd523acdf05235d1b151da4416517d7ed8517ac4d35101aaab50f3682550cccd7250a2ac00507eaec05070c86f506d2270
  | 9, 8 => 0x6cf7b1276ccf5b736ca3e4856c376a3a6c1a426f6ba5d1186b59b83e6b1ff0076abf48ab6a81d2ce6a767aa36a5e080a6a3cddd66a3b1c8e69c3c5cb69be6a7e696d69df69566b31693c011d690662c168e50ede68d674e768b389d768a2155968842345686c3e0b6828266467a9a2c1679aa58c6758995867467eb367444029670884dd66dca7966653c1296632a9a86631cbff662108db66045a2065af059e65aa320b64a2ed186496dd1c63aa11ac6238e334623862fa61fbb75161c731d76176ddfb614c1cad6117f06560e2423060c3605d60948264604f952c6045479b5fe196665fa1f5e95f8dd6785f2fba975eae2a0c5de88be05dcd65305db40c09
  | 9, 9 => 0x7f5641d67f4f65777f4b6b2e7f212a807ebe4f2d7ea597f67e5ba4e07dc1d6467d53f3ec7ca801537ca27b7e7c41a0bf7c158c207b6344667a83b53f7a4bbeac7a352adc7a210b1879df9a4b79cc705179a9388d79a4eecc798569b47928346d79025e5978e44db87843fd0a7840741677a1a1bf775654c77741a7ff76654ee1763995237639608075ec856175cc821675b9400d758db184751f2db374cdf405748db9b374361d25740ce6c57347c1377328fc2b731f52f072becce472670b6f71e472137198d160717845027121b324710b0b4870de90bc70db5a8c70aea48b6fb36dff6f6e33586f18be8f6e4a868e6e3af9296debed8a6da9b6446d75148d
  | 9, 10 => 0x8fb798a28fa4ea6d8f7d7f578f6274168f2068958f1bf8a68e7502958e1dd0088d927f388d03c7bb8d0125ba8cb62e328c69c7d88c3d67618c1d3d508be94e1d8b8749738b5111888b1958d28af785ea8aa8829c8a5561548a47d6a18a330168899b3d0f894dc47b88ad4f798888960788748f1a886e5671885958bf87ec0f1a87ebc50e87ac9d4b86e8db4d85fc4cd785f585bf85bbb0548598ae228593442c856256898530f70a84dc7c4a8497628d83f6554a83d93d9883c3ea67835273ba832c888a82d6ae6e82c882fa829821c6827c38b5827b391181f2a8f081e8e96481bd17f381b7921e818484a2817acdbc816c62148149bcfb7fe0ee617fcf871e
  | 9, 11 => 0xaa4c9558a9ee54f8a865afbba865405aa752f579a6f5a932a6b668c5a6b567eaa6473be8a5fc7f40a564cc3ca4b9a911a4429173a349cd04a1be679da163bb5ea161b40aa14f0e96a0a3a397a091a6faa087dceba046c717a0010a8f9fd28a739e75f4419d3849ee9d00db219ca950fd9c37537c9c15e3ab9c025a349b72c64b9ae9bb269a4317f69a21e42c986e23cf9864d9d097a354d99781448b9734464696eb5c9596dcc20a96031c9395fee55395d8b47f9567f79694f2ad8e94d2befd94d19895943e122f93fee1b193f0fe6393ab51e992586d0991ea495091ace296919daa4891288d0b910264929080a64d903e019d9024f9e08fd5f8ca8fc3d304
  | 9, 12 => 0xca8fd156c9dff10ac82a0e90c7f04e79c76d8307c754d024c73be04dc6b6b794c6b3c12cc66459bbc5802ce2c4cc9417c4af607dc2a8678fc2a1e7a1c279657ec2546b5ec19c7266bf001425bea1a541be5ec99dbe2bbe9dbe235678be1d8e45be0c4848bdfb3225bdbff159bc811d14bc53f7e3bbc61c26bb6d9320ba2d33efb9a93e31b8e03528b85707d8b852e344b46eac9fb465e382b44c7454b3e0dd2db3ac5c85b2e56fadb2d5368fb2cd6e10b2c7e83bb24fc653b1f975b1b09714e5af17c1dfaeac6164ae152952ae03bbe1ad8d2fffacfcff49ace41505acb17c07acae9164abcea641ab397f8eab1763d8aaac2491aaa08e4caa67e0c7aa5b4e46
  | 9, 13 => 0xff8ebb79fb873f83fb795490fa87bbb4f9806d37f973255af6882c40f6227e9cf616447df5cd910bf39de580f2eebaf6f2da0e2eef689247ef290e1beeef692dee694147eb76c673eb70b635eb1b6671e9db3e39e8e349cde857790ae7e7a7c3e7885e2de5b87607e523acefe4bb4818e43a9a86e4336287e26ea595e0dbabe9de742515ddb9c31cdcf69efbdce7897bdbb673bfdb7c8e19db756582db263ca7d99c010ed8f5155cd768223ad72bfb70d4cb3165d314347ed30ec467d1c8ce69ceee1ee0cdfe506ccdb6e068ccdc3de0cc7f8a6dcb9de4fbcb7c4cbccaa65c2a
  | 10, 0 => 0xddb9c31cc9dff10ac6b6b794c5802ce2bf001425be0c4848b1f975b1ae03bbe1ace41505a9ee54f8a6b567eaa4429173a163bb5ea14f0e9696dcc20a8fb798a2899b3d0f85bbb054816c621479df9a4b76654ee1614c1cad4721f2784481cb3040cd6d713d9568fd3c92d0703853339d36e356d9326ce2a82fe1627c28c0bf1426b2ee6525c277fc1f800bb01caff99119ceb8a618d3087217cb6b9917b1018509aab39905d3fbe501c56855
  | 11, 0 => 0x2fe1627c
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x640047ff40c07f0a210821fe300003ff80603f800000007e362cb9ce68ea162cb9ce68ea00000000000000000000000007f0a210821fe640047ff40c03f800000007e300003ff806038b1c5f1062c58b1c5f1062c5c1860f800140c1860f800140217df87e0c479f000882f410801e7c1f0601cf800000780807c00220bd04285f7e1f8311e3e000001e0200079f07c1807c893ffffffa81023fa1100004001ffffff800001fc000000372c31acf0801e6ea94a28fb8000000000000000000000000
  | 0, 1 => 0xff9aa528a3fe7420c7ff40c03f800000007e300003ff80603fffffffffea1fffff8c60801fffffffffe00fffff0000000237df8fe1c57bf4518c6fc11801e7c1f0601cf80000078083fff212824841fff651922804fff800000000fff800000000ffc71fc6fcb1e3fffffe1cf7ffe183e07858307fffff0651ffff210820801fff210820800fff800000000fff8000000009023fa1100004893ffffffa84001fc0000000001ffffff80286209a27491813fec2092cbd01860f83e60001fff0001e5f
  | 0, 2 => 0xd8b3ffffffa858b3fe3182004001ffffff800001fc0000003fffff8c60801fffffffffea1fffff0000000fffffffffe0070dc0d6c0bef1611f87e0c10307e03ff87f7ffe07c1f067e095f7e3f9311efc20a22bd15a0079f07c18073e000001e0201f004a93f410e97ff97e2def8f8000007808001e7c1f0601e3c8fca4fd043a7b81e07cfbf3e07f001e020007e0f83e6079bfcc3dfc2c000f6a528a3fe0ffe03ff8060007e0000007e3a7f7f1fa391e7c82220bd0420079f07c18073e000001e020
  | 0, 3 => 0xe3c71fc61cb1e3c71fc61cb1f06183e00050306183e000500fdf7e3fbf15efdf7e3fbf15e3e79f07df8273e79f07df8276fdc05eeffffb76c00000057bffe03fffffffffe0000007fdfd3cc730e7fd99155ffd6344fe00000001f8c0000ffe0180664557ff58d17f4f31cc39ff300003ff80603f800000007e37e42328bd842c5f7e1f8311e3e000001e0200079f07c1807ec90c7ffc2c07f2aa10821fe300003ff80603f800000007e3d0831ffd0301fe6a94a28ff8c0000ffe0180fe00000001f8
  | 0, 4 => 0x7f4f314c29ff660047ff50d03f800000007e300003ff80603a35ffffffea4488fea4440410007fffffe000007f0000000e3fffffe1cf7ffc71fc6fcb1f07fffff0651ffe183e078583fff318c60801fffa94a28ea0fff800000000fff800000000f423ffff40c07f9bfffffffe7001ffff80603f81fffffffe095f7ebfd311ffc28a62bd7fa0079f07c18073e000001e020e6c757d758b16bcf37cc39ff706183e00050306183e00050188cb24cf1ac3e4e2bf129e3ac079f07fff47fe79ff81ff3f
  | 0, 5 => 0xc082070103a84082070103a8706183e081f6306183e081f63324ffffffea0c4afe86401190007fffffe000007f0000000fffc84a2c2007ffca42882463ffe000000003ffe000000001fc013fffd343fdffe5f8b7fefe000fffe1a0fe79f07c19ff3f4518c6fc11a37df8fe1c578f8000007808001e7c1f0601da5ffe5f8b7be7c012a4fd0420079f07c18073e000001e020fffcc6b3c2007ffea528a3ee3ffe000000003ffe000000001ec013df6d34379df65d8b6e6fe000fffe1a0fe79f07c19ff
  | 0, 6 => 0xe6c717c658b163cf37cc18f7706183e00050306183e000501cb93b75462c4a953a0ef9c64c181ff800140c181f07fff40d8b0c631820058b2a528a3a80000000000000000000000003224a94a28ea04083084400000000000000000000000000007f0a298af5fea57dfaff4c478f8000007808001e7c1f0601fa66a94a28fb850830a4d00000000000000000000000000004ea1fd90f3b8286c0882f4473fe07fe0f9fe307e00007877dfc256b5d7007900cf080f4fffe07fffffe07c007f001fe7f
  | 0, 7 => 0xe99bffffffee1423fa9340004001ffffff800001fc0000003fffa94a28fb9fff31acf0800fff800000000fff800000000e9fffd7eafef9f20ca93f410801e7c1f0601cf80000078081fc28a42897fb94013ffd1302fe00000001f8c0000ffe018065004fff44c0ff0a290a25feb00003ff80603f800000007e09df7e3f9715efd34e33bf15e0079f07c18073e000001e020690a210821ee040042934000000000000000000000000000362c21082080162c210820800000000000000000000000000
  | 0, 8 => 0x9020c21100004892a528a3a8000000000000000000000000162c017bbfea162c017bbfea000000ffffe0000000ffffe00dfb08ca2f610f9fdfc7e8e478f8000007808001e7c1f0601ff2c31fff0b01feea94a28ff8c0000ffe0180fe00000001f8f92bfb1921ee4c93ffffffa84001fc0000000001ffffff8021b1d40ed61c47734db30e53d0186007e00c03f860f8000b8fffea528a3a87ffcc63182003ffe000000003ffe00000000362cff8c6080162cffffffea10007f00000000007fffffe00
  | 0, 9 => 0x3f08288af456a57df8fe4c478f8000007808001e7c1f0601f8f3cdf3063dd9b1c5f1962c5c1860f800140c1860f8001407f7ff97e2dffff004ffff4d0bf9e7c1f067fff8003fff86839b1c5f3063c59b1c5f3063c5c1860f8001c0c1860f8001c0fffc852882c07ffc852882c03ffe000000603ffe000000601fc299ffd87f9fc299ffd87f8fe000ffe01f8fe000ffe01f8ff2aa10821fe6c90c7ffc2c03f800000007e300003ff8060074ee4f926ac474ee4f926ac53e7e0f8001403e7e0f800140
  | 0, 10 => 0x9f208882f410e9fdfc7e8e478f8000007808001e7c1f0601fcb9e5f1062c5ab5e5f926ac5c1860f800140c1860f8001404866210821a98bdc4211bf3f807e00000001cffe00007f9ffe7f7f1fa391f7ec2328bd8420079f07c18073e000001e020eac737cc39b962c757d518b1706183e00050306183e000503fe6ffffffff9d08ffffd0301fe07fffffff8c007fffe018010d624e6de01d36c47ff4097807e03ffff81cffe03ff801ffbca76c6487f8b24ee002fda1fe07f00001f8c007f001ff80
  | 0, 11 => 0xd823fb1921a84893ffffffa84001fc0000000001ffffff801b4299ffd87b9fc298e6d87f8c0000ffe0180fe00000001f8fffca42882467ffc84a2c2003ffe000000003ffe00000000000e380e40d38700000078c200079f07e1e9f3e000003e6b87f0a631921fe6c0267ff61e83f800000007e300003ff80603224ffffffea1608fec6486a10007fffffe000007f00000005f02298af5b8a17dfa7f0c478f8000007808001e7c1f0601db0099ffd87a1fc298c6487f8c0000ffe0180fe00000001f8
  | 0, 12 => 0xead7ffffffb93267fad518114001ffffff800001fc0000003264ffffffea2448fe84c10030007fffffe000007f0000000660047ff50d07f4f314c29ff300003ff80603f800000007e0f1144117ac2408e382e44d783e000003e6b80079f07e1e9f6fdf7e318200376f7bdf7da87ffffc0000003fffffffff80191155ffd2305fc288620c7f8c0000ffe0180fe00000001f89223fa91101068d7ffffffa94001fc0000000001ffffff800000def7df7fe000def7df7ff0007ffffffff0007ffffffff
  | 0, 13 => 0xffbaa528a3fe7cb0c7ffc2c03f800000007e300003ff80601fc288620c7f991155ffd2304fe00000001f8c0000ffe0180ca93ffffffb83067fa5508014001ffffff800001fc0000003ab5e5f926ac5cb9e5f1062c5c1860f800140c1860f800140457dbf814c87e00a298ad5eeb01e7fe08661f0000000787630eebbee853dbf71c7d1bb287c1fffffc1947ff860f81e160b17dfa7f0c47df92adaaf7b8801e7c1f0601cf80000078083cb9f5f5462c5ab5edfb2eee5c1860f800140c1860f800140
  | 0, 14 => 0x80f5def7de019bffb800bf3fc07fffffff81cffffc007f9fc85fa0e85c6e07c0dcd7627bd007e0f83e7f83e07fffe1fdf650867ff40c67f0a218a61fe300003ff80603f800000007e2c4afe8640119324ffffffea10007f00000000007fffffe00e7c71fc65cb1e3cf3fce1cf7f06183e00050306183e0005037e4ab6abdee2c5f7e9fc311e3e000001e0200079f07c1807ec92e7ffe3e87f2ae31921fe300003ff80603f800000007e3af3cdf30e7fd9b1d5f5d62c5c1860f800140c1860f800140
  | 0, 15 => 0xd793f77d0bb8b15e026f0c47cf81ffff8788001f801f0601f02eb9ce40fb972081c078ea1c1fffffe1fdfff860f83e7f8040042934000690a210821ee0000000000000000000000002c19fe95420052a4ffffffee10007f00000000007fffffe00fffd94648a017ffc84a092103ffe000000003ffe0000000026ffee002fcfe03d77bdf78073ffff001fe7f01fffffffe07f423bdee40c03799def7de567001ffff80603f81fffffffe3ab5edfb2eee5cb9f5f5462c5c1860f800140c1860f800140
  | 1, 0 => 0x8d1b122ae74ed5ab17c418e6cf9f801fffafcf9f83e0002fffff2308a1803fff2308a1802fff800000000fff800000000b17df87e0c47df908ca2f610801e7c1f0601cf80000078083ebde5f926ac5ebde5f926ac5c1860f800140c1860f8001409123fa130400c993ffffffa8c001fc0000000001ffffff80240820739f7ff22421082095e00000fffffff0000000001ffd8b3ff39a3a858b3ffffffa84001fc0000000001ffffff8027fd759d4a844ea0901facde13ffffffe1e273f86007de678
  | 1, 1 => 0xd8b3ffffffa858b3ff39a3a84001ffffff800001fc000000393d664227b0793d664227b07c1fff001ff87c1fff001ff87a74ffa110057a74ffa110057fffffc00007ffffffc00007fcf9f7c3f3e15cf9f7c3f3e15c3e79f07df8273e79f07df8271b0a66f7613e1b0a66f7613e0f8003ff801e0f8003ff801e085f7e9fc311f7c08a62bd6e20079f07c18073e000001e0209423fa934000699bffffffee4001fc0000000001ffffff80306083c0c1ea306083c0c1ea3c1860f8207d8c1860f8207d8
  | 1, 2 => 0xb267fad518116ad7ffffffb94001fc0000000001ffffff803fff653926845fff653926844fff800000000fff800000000ffce250821fe66c447ff40c03fe00000007e306003ff806039b111ffd0301ff38942087f8c1800ffe0180ff80000001f8ffff97e49ab17fff97e49ab17fff83e000503fff83e00050070e380e78d3870e380e78d383e79f07ffebf3e79f07ffebfe2c46c1b654ee2c46c1b654eb0607c1fffaff0607c1fffaff83f23289d8437a05f17a391ec1f80001e020ff81f07c1807
  | 1, 3 => 0xeac717c438b162c757d418b1706183e00050306183e0005037e4ffffffee2c5ffe9fc311f3e07fffffe20007ff07c1807c8908ca2f6001021f810000000000000780000007c00000000400200810020400200810020000000000000000000000001d38e83be74e9d38e83be74e8f9e7c1fffafcf9e7c1fffafd900006290301942084200318c00000000180c000000001800000421100004802210821a800000000000000000000000008d14631870468d1463187046000000000000000000000000
  | 1, 4 => 0x376df8100057efdc0deeffffbffe7c00007ffffe03fffffff8b10100000018b1010000000c18000000000c18000000000376c00000057efdc05eeffffbffe0000007ffffe03ffffffd90011acd0001fc28842087b8c00000000000fe0000000000e2c717cc18f166c717c418b1706183e00050306183e00050383ffddf42fbd7a081e07cee1c1fffffe1fdfff860f83e7f87f0a218a61fe650867ff40c63f800000007e300003ff8060085ffe1f8311e7c012a4fd0420079f07c18073e000001e020
  | 1, 5 => 0x64004fff40c07f0a290a25fe300003ff80603f800000007e3fff230820801fff2308a1800fff800000000fff8000000005f000882f410a17df87e0c478f8000007808001e7c1f0601e408fc8440001224fdff7eea10007f00000000007fffffe00fffcc7ffc2c07ffea528a3fe3ffe03ff80603ffe0000007e02000220bd0000087e040000000000001e0000001f00000007f0820080046640004a240003f80000000003000000000003fffa94a28ff9fff31fff0b00fff8000001f8fff80ffe0180
  | 1, 6 => 0x15ad75c57800339ce7dffc001ffffffffc001ffffffffc85f7e1f0311e7800220bd0420079f07c18073e000001e020c8b3ffffffa81823fa93f4004001ffffff800001fc0078003224ffffffea6408fe844f4ff0007fffffe070007f001fe7f4802210821a800004211000000000000000000000000000037a081e07cee183ffddf42fbdff860f83e7f8c1fffffe1fdf000043df40c00002210821fe000003ff806000000000007e1900dfffdf7fffc2def7df7ffc007fffffffffe07ffffffff
  | 1, 7 => 0xff9bffffffa87423fe3100007f81ffffff803001fc00000000087e04000002000220bd0000001f000000000000001e000b17ffa7f0c47df93ffffffb8c01ffc1f0601cf81ffffff8820b145b1060448b1c411060c501860f800000018600000040d8b3ffffffa858b3ffffffa84001ffffff800001ffffff8008df7e1f8315efc00231bd0420079f07c18073e000001e0203f0048fef450bf7df87e2c578f80001f78080f9e7c1f0609d95f7fffd331ffc28a62bd7fac079fffe1987fe000001e1f8
  | 1, 8 => 0x480267ff61a8100262110000000003ff80000000000000003b24fffffffa1fcafec6487f9c007ffffff80fe07f00001f820451044080102000080101000000000000000000000000018808040002c180001f100200c00000000140c0000f800100ffcf37cc39ff66c757ff58f17fe183e0007e306183ff807039b111ffd4341ff3cd530a7fcc1800ffe0180ff80000001f87f0a252821fe740047ff40c03f800000007e300003ff80600100002090000842080200118000000000000000000000000
  | 1, 9 => 0x4e800580f3b8206c000000473fe003e0f9fe307e00000077c842080200118100002090000000000000000000000000000217c802000001f0000008000001e000000000f80000000003fff7f1fa391ffff2328bd842fff9f07c1807fff80001e0209bfc8000820000f4842082000ffe00000000007e000000003fffef082fcfffff77bdf7807fffff001fe7ffffffffffe07660047ff40d07f0a214c21fe300003ff80603f800000007e185ffe5f8339e7c002a0bd0420079f07c18073e000001e020
  | 1, 10 => 0xe9bbffffffee1c23fa93f4004001ffffff800001fc007800180001f1002018808040002c0c0000f800100c00000000140e6c757ff58f17fcf37cc39ff706183ff80703fe183e0007e07428842087f810010ffd03003e00000001f800000ffe0180216d785e0c478f000882f410801e7c1f0601cf80000078083fff651922801fff210820800fff800000000fff800000000657cc7ff40c07f0a2108a1fe301e03ff80603f800000007e27c832a4fd043a7fff5fabfbe3e000001e0200079f07c1807
  | 1, 11 => 0x200008010102045104408010000000000000000000000003fc28842087f992011ffd0300fe00000001f8c0000ffe01809423fa110000699bffffffa84001fc0000000001ffffff80190010e6d0301b428842087b8c00000000180c000000001801f00000020102000407e00400f80000000080000001f00001fc28a62bd7fb95f7fffd331efe000001e1f8c079fffe19870bdc0000bf3f8064000000018ffe00007f9fc07e00000001d900010800001fc2000000000c00000000000fe0000000000
  | 1, 12 => 0xc8820781f3a80023f2110000400183e0f9800001fc00000037a4ffffffee1c3fffdf42fbdff87fffffff8c1fffffe1fdf060000825010214d304c0847000000000000000000000000040088000000100011ffd020000000000000000000ffe0000ff2bfb1921fe6c93ffffffe87f81fc00007e3001ffffffe01bf7457bbfffeddb00200415efff80ffffffffff8000001ff5f000ca2f410b17df87e0c478f8000007808001e7c1f0601d3a081e07cee081bdcd7427bdff860f83e7f8c1fffffe1fdf
  | 1, 13 => 0x31f87e0c0018000882f40000007c1f06000000000078001fc2cc530a7f990011ffd0300fe00000001f8c0000ffe0180fffd9c668e01fffc8ca29610bffe000000003ffe0000000038b1d5f5462c5ab1cdf30e6e5c1860f800140c1860f800140600a210821fe440047df40c030000000007e300003ff806037ec210820801e7f2108208003e0000000000007800000000c8908420820010208000000000000000000000000000000038b9e5f1062c5ab1c5f1262c5c1860f800140c1860f800140
  | 1, 14 => 0xc893ffffffa81023fa1900004001ffffff800001fc0000003fff210820801fff2108a0800fff800000000fff800000000640157ff48c07f0a210821fe300003ff80603f800000007e1fc298e6d87f9b4299ffd87b8fe00000001f8c0000ffe0180224510c41811224510c418110000000000000000000000002224ee002fca00087684400010007f001fe000007f0000000dbffffffffbf90f7fef7de01cfffffffff9fc07fffffff81fa7ffffffffbe7c8fea4fd043007ffffffe073e07f001e020
  | 1, 15 => 0xa24712c4181162c717c418b1400180000000000183e00000383ffffff7fbf7ffefe07feffc1ffffffffdfffffff83ffffcb93ffffffb8b167fa570c01c001ffffff800001fc0000000800101f801007c00000080400000007c00003e0000000020a2c71044183102c516c41811406180000010006183e000002ddb20000015fbf7217bbfffefff8000001fffff80fffffff489005eeffa8102000000000000003ffff800000000000003bf7ffffffffeddbfe844015ffffffffffffffffff00001ff
  | 2, 0 => 0xe2c737c418b162c717c658b1706183e00050306183e000500a5f7e1fa311e7c82220bd0420079f07c18073e000001e0206000477d00c05e02010021b8300003ff80603f800000007e393ffdffd2fbdfe289e27cff9c1fffffe1fdfff860f83e7f8dbfc8420820010f4842082000ffe00000000007e0000000007c01224bd042a5f7e1f8b11e3e000001e0200079f07c18079f23fa93f410e9ffffffffefcf81fc007808001fffffff81c0047e1f830004000200000000001f07c1800000000000000
  | 2, 1 => 0x3d38e83be74e9d38e8bbe74e8f9e7c1fffafcf9e7c1fffafffff210820801fff290a20800fff800000000fff80000000093fd98009e1780f59ce6de01cffffc007f9fc07fffffff81e408fe8440001224bbeefdea10007f00000000007fffffe0000037bdf7da800037a1100004001ffffff800001fc0000003224ffffffffe408fef7df7ff0007ffffffff0007ffffffff7f08000000006400042000003f8000000000300000000000000056b5d7006000ce000f4ff0007fffffe070007f001fe7f
  | 2, 2 => 0xcc93ffffffa8312bfa1100004001ffffff800001fc00000018808060042c181145f102204c00000000140c0000f8001009823fa93f40048b3ffffffa84001fc0078000001ffffff8020bd77bdf7846effee112fcff01fffffffe073ffff001fe7fe2c737c418b162c757d518b1706183e00050306183e000503624ffffffea1408ff8c400010007fffffe000007f00000001000080000000011f87e0c0000000000000000007c1f060019f7015b02ffedd300000015efff80ffe1ffffff8000001ff
  | 2, 3 => 0x7f0a250821fe660047ff40c03f800000007e300003ff80600408108440001224897bbfea000000000000000000ffffe0048937fffffa810237a1100004001ffffff800001fc000000090011bdd0101fc28842087f8c0000ffe0180fe00000001f85802210821a8400047ff4080000000000000000003ff80003224ffdffbea0408ba84400010007fffffe000007f0000000644447ff40c07f0a210821fe300003ff80603f800000007e2408200000001224210820800000000000000000000000000
  | 2, 4 => 0x600a210801ee440007814080300000000076300003e080603ffffddf4affdfa091fffcfe1fffffffe1fffff860fffe7f85f0a210821fe6400477f40c03f800000007e300003ff80602c4afe86c111b364ffffffea30007f00000000007fffffe000075d8760c019b000800b410801e7c1f0601cf8000007808287f7fbff791e7ffee20bfcff01fffffffe073ffff001fe7f1f011882f410a17df8fe1c478f8000007808001e7c1f0601c000ded74f7fe000d6f5df6e70007ffffffff0007ffffffff
  | 2, 5 => 0x7f0a2108a1fe657cc7ff40c03f800000007e301e03ff80600dc2000000159900017b90300fe00000001f8c0000ffe01807f6e210821ffefdc47ffffffbffe0000007ffffe03fffffffffb81e07cfffbfffdffffffffffe0f83e7ffffffffffffffffde07effffff7fff77d0bffffff83ffffffffffffff87ffd8b10171062c4891000000044c1800f800140c18000000140efdf17eefffff7ef17c418f7ffff83ffffffffff83e0007fc64e3a0cf9c3a64e3a0cf9c3a3e79f07ffe3f3e79f07ffe3f
  | 2, 6 => 0xe2c715c418b122c516c41811706183e00050306183e00050190010c640301b008842087a0c00000000180c000000001807f0a210821fe64dc47ff4bef3fe00000007e307e03ff87f7e000c48000001020c5f10628100060000000000060f800000f2e7ffd518b16ad7ffffffb97061ffe000503061ffffffd03224ffffffea0408fe95420010007fffffe000007f00000007f4e210821ff66c447ff58f13fe00000007e306003ff807007c00220bd04385f7f1f8311e3e000001e0200079f07c1807
  | 2, 7 => 0xd18002ae74e9528000000468f9e001fffafcf9e0000002fe7c8200020001a7f2108208003e0000000000007800000000c08317c418a0000312000000400183e000000001800000003ab5ffffffee5cb9fff5462c5c187ffffff40c187ff800140c893ffffffa81023fa9340004001ffffff800001fc0000003fff2328bd843fff7f1fa391efff80001e020fff9f07c18071f0000809010217d906408010f8000000000001e000000002000fe8440001200fec6486a10007f00000000007f0000000
  | 2, 8 => 0xec90842082007f28800000003000000000003f80000000001fff017bbfffffff017bbfffefff80ffffffffff80fffffff640007c64080630a210800f6300003e000403000000000501fc28842087f990431ffd0300fe00000001f8c0000ffe01806400010800c06400010800c03000000000603000000000601fcaa842087f9b0011fff0300fe00000001f8c0000ffe01801f0000008000217c802000000f8000000000001e0000000026bfec002ecfc03d75bd768053ffff001fe7f01fffffffe07
  | 2, 9 => 0x9823fa1120004893ffffffa84001fc0000000001ffffff803224ff8c60800408fe84400010007f00000000007f0000000376f7bdf7dffefdf7ffffffffffffffffffffffffffffffff8f1c5f1062c58f1c5f1062c5c1860f800140c1860f8001400a000882f4102065f854080100000000780000007c00000037bd210820801eff210820800fff800000000fff80000000000d404e6de01936c00000017807e03ffff81cffe0000001fd3e6016abdffad5b00000011efff80ffffffffff8000001ff
  | 2, 10 => 0xe2d797e418b172c717c418b1706183e00050306183e0005039b1c5f1562c58b3cdf3067fdc1860f8201c0c1860f8001d8ff8a2508a3fe64fcc7ff42c03fe00000007e307e03ff80600900103f90100fc20802081580000007c00003e00000000209a23fa93f41068f7ffffffa94001fc0078000001ffffff803fffa90820801fff318c60800fff800000000fff8000000007f4f394e2dffe7004fff54d0bf800000007e300003ff80601bf7897bbfffeddb10844015efff80ffffffffff8000001ff
  | 2, 11 => 0xe2c407c4008062c6050000b0306003e0004030600000005038f3cff3873df9f1c7f1972c7c1860f800140c1860f80014082c71000183100c516c41801406180000010006183e000003effeff12feff8bdf7fdf7ac7ffffff81ff7fc1ffffffff47400047ff4080100220000000000003ff800000000000000038b1e5f1062c58b1e5f1062c5c1860f800140c1860f8001406fdc05eeffffb76d10440857bffe03fffffffffe0000007fe408fc844000122481fbffea10007f000000000060ffffe00
  | 2, 12 => 0x800352110000488337cc39a8400180000000000183e000003408fec640201224ffffffea10007f00000000007fffffe00ff9aa528a3fe757cc7ff40c03f800000007e301e03ff806039b1c5f1062c58f3c5f1062c5c1860f800140c1860f80014080f5def7de01dbffb908bfbfc07fffffff81cffffc007f9ff224ffffffea0c08fe84400010007fffffe000007f00000009021fa1100004892adaaf7a800007c000000000000007800070c320cf9c2264e3a0e69d3a3e79f07ffebf3e79f07ffebf
  | 2, 13 => 0x9bbaa800b73e80f5de77ce01cffffc007f9fc07fffffff81c0c0022085042851461183006000000000000000000000000237df87e0c47bf440882f410801e7c1f0601cf80000078082dff210820801fff210820800fff800000000fff8000000009923fa93f400c9b3ffffffa8c001fc0078000001ffffff803fff210820801fff210a20900fff800000000fff800000000657ce7ff40c67f0a218ae1fe301e03ff80603f800000007e1fc288622c7f995f75ffd2304fe00000001f8c0780ffe0180
  | 2, 14 => 0xc89287a1f3a81023f2110000400183e0f9800001fc00000037a081e0fcee187ffddf42fbdff860f83e7f8c1fffffe1fdfe2c717e418b172c717c418b1706183e00050306183e0005009d3def7df7fe9d3def7df7fffffffffffffffffffffffffffffcc43082007ffc8420a2003ffe000000003ffe000000003224ffffffea0408fea4440010007fffffe000007f0000000fffc862082007ffe852082a03ffe000000003ffe0000000026ff2108208006ff2108208003ff8000000003ff800000000
  | 2, 15 => 0xfffc84a2c2007ffca42082003ffe000000003ffe000000002effee082fcfe7fd77bdf78073ffff001fe7f3ffffffffe07eac717c418b162c717c418b1706183e00050306183e0005037ee210820801f7f210820800fff800000000fff800000000e8fff77d8bef5ea28781f3b8707fffff87f7ffe183e0f9fe1f4e3a4ef9f3bf4e3a4ef9f3afe79f07fffbffe79f07fffbf80ffb0000b2f00800681d200407ffc000797c06183e0f9800c4288020011910011ffd020000000000000000000ffe0000
  | 3, 0 => 0xb023fa1900404c93ffffffa84001fc0000000001ffffff803408fec440281224ffffffea10007f00000000007fffffe0060dc056c0bef160000000010307e03ff87f7ffe00000007e203d779d678066bde6002fce701fffffffe073ffff001fe7fc893dff7ffa81023fa1100004001ffffff800001fc0000002000fe8440000000fe84400010007f00000000007f00000007f0a230821fe640247ff40e03f800000007e300003ff80600842181f801187c00020980400000007c00003e0000000020
  | 3, 1 => 0x7f0a210821fe6c0047ff40c03f800000007e300003ff80601f828842087f990011ff50300fe00000001f8c0000ffe0180cc93ffffffa8792bfb1921ee4001ffffff800001fc0000002c5f2008000017e42108208000078000000003e0000000000fffdb46c8a477ffc84a2d2103ffe000000003ffe000000001891c471062c589145f106244c00000000140c0000f800100ffcc0400000066c4042000003fe0000000003060000000003fff210820801fff212820800fff800000000fff800000000
  | 3, 2 => 0x440047914080680a210821ee300003e08060300000000076064e2a0029c3a00c320cf18023e79f001fe3f0079f07ffe0765086fff44c6ff0a298a65feb00003ff80603f800000007e203d77bdf78066c8ee002d043007ffffffe073e07f001e0202108280a0446850008824400800000000000000000000000085f6e1b8311e5c00220b50420079f07c18073e000001e020e99bffffffee9523fa934400c001ffffff800001fc0000003fe28942087f990011ffd0300fe00000001f8c0000ffe0180
  | 3, 3 => 0xff98842082007420842000003f80000000003000000000003a35ffffffea0488fe84400010007fffffe000007f00000001e000080f010207df07c08470f8000007808001e7c1f0601f7e083e0fdee387fffdfc3fbfff860f83e7f8c1fffffe1fdf7f0a631921fe640267ff40c03f800000007e300003ff80600599000000047af7015b2fffefff8000001fffff80fffffffe2c737cc18b162c717c418b1706183e00050306183e000501900def7df7ff900def7df7ffc007ffffffffc007ffffffff
  | 3, 4 => 0xa17df87e0c47df800c82f410801e7c1f0601cf8000007808085f280a001187c00020b00000078000000003e0000000000fffc842082007ffc852882803ffe000000003ffe000000001d0013ffd0301fc6fe5f8b7f8c0000ffe0180fe01f07c19f8e2c71fc418b162c71fc61cb1706183e00050306183e000501fc6a84a087f9d0011ffd0300fe00000001f8c0000ffe0180c28317c418b0204712440801400183e000000001800000003224ffffffea1608fe84400010007fffffe000007f0000000
  | 3, 5 => 0xfffc84208257fffc84208257bffe0000007ffffe0000007fd200def7df7fe000def7df7ff0007ffffffff0007fffffffffffcac2a8646fffc8ca2c600bffe000000003ffe000000001837dddf42fbc58080e05c6e1c1fffffe1fdfff860f83e7f8de824791f3b868fff77d2bef7fe183e0f9fe307fffff87f7c857001b8311e5c00000000420078007c18073e00000000206ffdfdfeffffbf6c0882f457bffe7ffffffffffe0000787ffa77fffffffbc588fea4d40410007fffffe000007f0000000
  | 3, 6 => 0x7fde25eefffff76c47ff40d7bffe03fffffffffe03ff807fc2f7ce002fcfe01956b5d70073ffff001fe7f01fffffffe07e0c717c418a1020312801010400183e000000001800000003a24ffffffea0408fea4400010007fffffe000007f0000000440047ff4080790a210821ee000003ff800000000000000038f1c5f1062c58b1c5f1862c5c1860f800140c1860f8001407f0a210821fee55c47ff4cc7bf800000007e301e03ff8661f7a4a1e87cee1c3ffddf42fbdff860f83e7f8c1fffffe1fdf
  | 3, 7 => 0xfbffbc00bf3fe2f5def7de01fffffc007f9ff07fffffff81fa24fffffffa0508fe84400010007fffffe000007f00000009022a00000004890c7ffc280000000000000000003ff80003264ffffffea0408fe84c00010007fffffe000007f0000000640047ff40c0370a210821fe300003ff80603f800000007e2488fe8440041a24ffffffea10007f00000000007fffffe00240042ff40407f0a210821fe0000001f00000f80000000081bc20042087f8900000000100fe00000001f8c00000000180
  | 3, 8 => 0xe0c7174408a14282078010b0706183e00050306183e0005038bffdff46ffdfb1c5f17eee5c1fffffe1fdfff860f83e7f81f0118c6fc10a17df87e0c478f8000007808001e7c1f0601ffff216ab0b01fff294a20b18fff800000180fff8000001806fdc04208200376c000000003ffe000000003ffe000000003fff217bbfffffff21082095efff80ffffffffff8000001ff217c882204009f0008028400801e000000000f800000000001400220910028420a028111a000000000000000000000000
  | 3, 9 => 0xd893ffffffa81033fa3100004001ffffff800001fc0000001b0011ffd8301fc29846087f8c0000ffe0180fe00000001f87f08010800c06400052800c03f8000000060300000000060376ebbcef9fbb76ebbcef9fbbffffffffffffffffffffffffbfffb800bf7feffddffffffffffffc007fffffffffffffffdfc28a42a97fb95f33ffd1302fe00000001f8c0780ffe0180de800400820060fc842002003fe000000000307e000000003fffa1e87cee1ffffddf62fbdfffe0f83e7f8fffffffe1fdf
  | 3, 10 => 0x240043df40c06f0a210821fe300003ff80603f800000007e2448fe8440001224ffffffea10007f00000000007fffffe001c000001e3080038e039034e0f800000f9ae001e7c1f87a7d95157ffd3307fc28a628d7fac0000ffe0180fe00000001f8f6e4c7ff40c07fdea528a3fe306003ff80603fe00000007e390031ffd0301fc2a842087f8c0000ffe0180fe00000001f8172800000056eddc056eefefbffe0000007ffffe03fffffffa75ffffffea64c8fea4c50430007fffffe000007f0000000
  | 3, 11 => 0xc8b3ffffffa818b3fa11bf284001ffffff800001fc007f8039b1c5f1062c59b1c5f1062c5c1860f800140c1860f800140000313c418b1000313c418b1400183e00050000183e0005038b1dff7df7ff8b1dff7df7ffc187ffffffffc187ffffffff1d3bfbffffff9d3bfbffffffcf9fffffffffcf9fffffffffe43d2108208016ff21082080001f8000000003ff8000000005f00098af490a17df87e0c478f8000007808001e7c1f0601c85f7e9f8311f7c08260bd2c20079f07c18073e000001e020
  | 3, 12 => 0x660047ff40c07f4e210821fe300003ff80603f800000007e000002209d0420005e178311e00000001e0200001f07c18071f037bdffdffa17ffbff7dffcf81ffffffffc01fffffffffcfc20220bd04295f7e1f8311e3e000001e0200079f07c1807e7fcc7ff40c07fce2508a1fe307e03ff80603fe00000007e085f761d8311e7c00220bd0420079f07c18073e000001e020faf4842082007af484208200306000000000306000000000383ffddf42fbd7a089e27cee1c1fffffe1fdfff860f83e7f8
  | 3, 13 => 0x9023fa937410c893ffffffefc001fc0078080001ffffff81c85f7e3f9311e7c00a20bd0420079f07c18073e000001e020170008827410a15d787e0c478f8000007808001e7c1f0601d7428842087b8100108ed01003e00000000b80000007e00806400463100007f0a210821a83000000000003f80000000002408ee000000002477bdf78010007f00000000007fffffe009bfffa11bf3fc8f7ffffffa9cffffc007f9fc07fffffff81d9b111ffd63c5fd38842087fcc1800ffe01c0ff80000001f8
  | 3, 14 => 0x217cc07e00401f000000a010001e001f00000f800000000808428842087f810010f7d03000000000001f800000ffe0180e2c514c4181162c514c41811306000000000306000000000190019ffd0301fc28862987f8c0000ffe0180fe00000001f87f0a218a71fe654d77ff48c73f800000007e300003ff806007c08a20bd04285f7e9fc311e3e000001e0200079f07c1807eec737cc39f966c757dd18f1706183e00070306183e000701ac28842087f990011f5d0200c00000000140c0000f800100
  | 3, 15 => 0x6edc05ecfbff366c000000573ffe03fffffffffe0000007fffcaa842287f9b7f31fff0b00fe00000001f8c0780ffe0180c8f5def7de019bffb800bf3fc07fffffff81cffffc007f9fc000dcf75e7fc000dcf75e7fd0007ffffffff0007ffffffff210b7bdf7dff84037bdf7dffc001ffffffffc001ffffffffd95711ffd331ffc28842087fac0780ffe1987fe00000001f8193bb800bf3f8031daf7de01cf9ffc007f9fc01fffffff81ff2c210820801fee210820800c00000000000fe0000000000
  | 4, 0 => 0xfffc852082807ffc852082803ffe000000403ffe00000040005f6e000301e0000220b50020079f000180700000001e000bbfff87ebf7f9ff5def7fe11cffffc1f7f9fcfffffffff89c742080208538100100ed01003e00000000b80000007e00807f3ae93be7fefd38efffe7cebf9e7c1fffffff9e7fffffefd94211ffd0301fc28842087f8c0000ffe0180fe00000001f80810e83be7081020e811000000007c1fff8000007c000000376efffffffba74efe8ef9d3b3e7ffffffebf3e7ff07ffebf
  | 4, 1 => 0x7f000fc6f490e37ff97e0cf7bf8003e07848301e7c1f0651cfc00222bd14295f7e1f8311e3e000001e0200079f07c1807ddb8ec3be74e9d38e83be74e8f9e7c1fffafcf9e7c1fffafe608fe846000122cffffffea10007f00000000007fffffe009dfdfeffff4f9ffff83bff7fcfffffffffafcffffc1fffbfffcab8c6487f9b24b9fff8fa0fe00000001f8c0000ffe0180fffcc73982c07ffea528a3e83ffe000000603ffe000000603224ffce68ea0408fe84400010007f00000000007f0000000
  | 4, 2 => 0xa17df87e0c479f008882f410801e7c1f0601cf80000078082c5bfe974211d3a4ffffffee10007f00000000007fffffe00fffc842082407ffc8528a3fe3ffe000000603ffe0000007e07400200b900204e3a0e8111a3e000001e0200079f07c18071f38e8bbf75ebd7df87fef4f8f9e7c1fffafcf9e7c1fffafe03d77bdd78066a0ce002fcff01fffffffe073f87f001fe7f1f000882f410e97df87e0c478f8000007808001e7c1f0601cddb00000015e9f70139b795efff8000001fffff80fffffff
  | 4, 3 => 0x1d38ea3be74edd3ae93be7ee8f9e7c1fffafcf9e7c1fffaff87f7f1f8311e7c00220bd0420079f07c18073e000001e0203f000882f410a17df8fe0c478f8000007808001e7c1f0601ffff211920801fff210820840fff800000000fff8000000007f0a210a21fe650047ff40c03f800000007e300003ff80601204fe5f8b6a04001284400000001f07c1800000000000000070008825410a14d384e0c478000000000000000000000000040def7df7fe040def7df7ff0007ffffffff0007ffffffff
  | 4, 4 => 0x440047bb40c07d0a210821ee300003ff80603f800000007e2effee022fdfe13d77bdf78073ffff001fe7f01fffffffe07000001ce7dff800000000057800003ffffffc0000000007ff7a0dff7fffff83fffffdffffff87ffffffffc1ffffffffff80b0ceb3d60099ffb800af2fc07fffffff81cffffc007f9fdbf7037bbfffeddb02008115efff80ffffffffff8000001ffe2c717c418b162c717cc18b1706183e00050306183e0005026ffffbdffcfe6ffffbdffcff3ffffffffe7f3ffffffffe7f
  | 4, 5 => 0x121f812040089000882f40080007c00000000000000780019808042003c190001f300300c000000001c0c0000f8001801f1088a2f410b17df87e0c478f8000007808001e7c1f0601c7c000200c040811541f821043e00000000200000007c0000dbffbc20bf3f90f5def7de01cffffc007f9fc07fffffff81f7bdf7fdffee7effffdf6ffffffffffffffffffffffffffff600047d500806a02210821b8300003e000403000000000500000deb5df4fe000deb5df4ff0007fffffe7f0007fffffe7f
  | 4, 6 => 0x377df87e0c57ffdc0deeffffbffe7c1f067ffffe03fffffff8b10120040418b1451102004c18000000000c1800000000000026b9b75fe80037b5f6defc001ffffffffc001ffffffffcddb56b5d715fbf7cf7bbffffffffffffffffffffffffffffc8b3ffffffa85823fb9bf5a84001ffffff800001fc0078001fc28a42087f990013ffd1300fe00000001f8c0000ffe01809bffb802bf3f81f5def7de01cffffc007f9fc07fffffff81e6ffee202fcfe83d77bdf78073ffff001fe7f01fffffffe07
  | 4, 7 => 0xb023fa5500004a93ffffffb84001fc0000000001ffffff802dff77bdf795ffffef7bbffffffffffffffffffffffffffff9023fa1304004893ffffffa84001fc0000000001ffffff8000447e1f830024400200810020001f07c1800000000000000de820580f3b820fdd6750a477fe183e0f9fe307fffff87f7d7c08842086e0800109fc01003e00000000200000007c0000657c842000007f0800008000301e000000003f8000000000085b00000011e3c00020bd0420078000000073e000001e020
  | 4, 8 => 0x902392000000489397e49aa0400180000000000183e00000383fed5b02fbc5a001a074841c1fffffe1fdfff860f83e7f882c716c4183102c716c41831406183e00010006183e0001006c28800084f800011bdd00003e000000007800000ffe0000ffffb908bfffe4f5dfffdec1fffffc007ffff07fffffffe1c00080e05c6e0000dcd7427bd00060f83e7f80007fffe1fdf8023fa1100000803fa93f4004001fc0000000001fc0078000ddb08020015fbf7017bbfffefff8000001fffff80fffffff
  | 4, 9 => 0x136f38003d3f80d55ef7de01cffffc007f9fc07fffffff81f2247f1fa38004082200000000001f07c1800000000000000fefff7fdfbff7efff7fdfbff7fffffffffffffffffffffffe408b88440001224b9fff8ea000000000000000000ffe00000021fa1100004802298af5a800007c0000000000000078003fff650820801fff212824800fff800000000fff800000000ffeea50821fe6ed4c7ffc2c03fe00000007e306003ff8060203d759d428046a080002cce101fffffe1e073f860001e678
  | 4, 10 => 0xead48420820072e4840000003060000000003060000000001bf7097bbfffeddb00209015efff80ffffffffff8000001ff620007c410906247114408b1300003e0004030000000005018b1c5f1062c4891c4f1062c5c1860f800140c1860f800140da820701b3b840f7d7750ba97fe183e0f9fe307fffff87f7ec19fe84400012a4ffffffea10007f00000000007fffffe001538c833c6469d38a82ae74e8f9e7c1fffafcf9e7c1fffafc0001a06d953a0001a06d953a0001f07ffebf0001f07ffebf
  | 4, 11 => 0x2037bdf7dffa0477bdf7dffc001ffffffffc001ffffffffe448fe8440001264ffffffea10007f00000000007fffffe00c2c717c418b162c7174418b1706183e00050306183e000500840121f811027c00200890420000007c00003e0000000020650047ff40c07f0a210821fe300003ff80603f800000007e2408f68440001224ffdf6fea10007f00000000007fffffe009020ca1100004893fd7eafa800000000000000007c1f06001fc288620c7f990055ffd0300fe00000001f8c0000ffe0180
  | 4, 12 => 0xfefc842082007efc842082003ffe000000003ffe0000000039b155ffd2305ff389620c7f8c1800ffe0180ff80000001f81f000882f410e17df97e0cc78f8000007808001e7c1f0601ffff214a28ff9fff210820900fff8000001f8fff800000180c893b7ecbba81023d2110000400183e00000000180000000190019ffd0301fc28842087f8c0000ffe0180fe00000001f8680a210821ee440047914080300000000076300003e0806039b1c5f3963c59f3cdf3063ddc1860f8001c0c1860f8001c0
  | 4, 13 => 0x217df87e0c479f00288af410801e7c1f0601cf80000078081bf7017bb0b00ddb000000158fff80ffe0180fff8000001f8d8b3ffffffa858b3feb3f6004001ffffff800001fc007800203d66002780603d66002780701fff001fe0701fff001fe07274c00000057a74c01ce7dffbffe0000007ffffe03ffffffc5000220900008467e1f831180000000000000001f07c1800c093f77d0ba81002020100004001ffff87800001800000003a3ffffffffbd7a8ffe47cee1c1ffffffffdfff87ff83e7f8
  | 4, 14 => 0x2129f81800460c000882f40000007c0000000000000078001fff3b7fffffefdf3a0ef9d7efff9fffffffffff9f07fffff7f0a218821fe640047ff40c03f800000007e300003ff80603f7fffdffbfbf7eebbeefdffbffffffffffffffffffffffff336c00000057ced405e6ffb9bffe0000007ffffe03ffffffc9d300000015e9d300000015efff8000001fffff8000001ff7f0b310821fe640047ff50c03f800000007e300003ff806025bd77bdf7847effef5b2ffffffffffffffffffffffffffff
  | 4, 15 => 0x7b0a210821fe440047f740803f800000007e300003ff8060054a1a06d953a3461a0ef9d3a3e79f07ffebf3e79f07ffebf7f0a2108a1fe6420c7ff40c03f800000007e300003ff806008157e1f830044800220040400001f07c1800000000000000c893bdeeffa81021da1100004001ffffff800001fc0000003428ff8440001224ffffffea10007f00000000007fffffe00fffffe3182007ffffe3182007ffffc0000003ffffc0000000000def7df6a0000def7df6a10007fffffe000007fffffe00
  | 5, 0 => 0xbf7ffafffc57ffffffffffffcf9ffc1f7e09cf9fffffff89c400000000000000101f800000000000000000000007c00003f0820082056240040fe40400f80000000080000001f000038b1c5f146ee58b1c5f146ee5c1860f8207d8c1860f8207d81d38e83ae4469d38e83ae4468f9e7c1f7e09cf9e7c1f7e09e6fffef7ffffe03dfffffffff3fffffffffff01ffffffffff1d38802082001d38802082000f9e000000000f9e000000003fff3b0ef9d3bfff3b0ef9d3afff9f07ffebffff9f07ffebf
  | 5, 1 => 0x4083a04400002043a0ef9c200001f00000000001f07ffe007f2bf91821fe6c004ffff4c03f807c00007e300003fff860000080000000100001f10020000000000000000000f8000003f7df87e8c47bf7c88a2f4108f9e7c1f0601cf9e000078082811c491020050a0c5f1062c100060000000000060f800000207df07c08471e000080f010001e7c1f0601cf800000780817808040086e180011df40300fe00000001f8c0000ffe0180
  | 5, 2 => 0xc282078010b060c7174408a1706183e00050306183e000503c08fff540201aa4ffffffee1c007ff800100c007ffffff40ffffffffffb97ffffff59ab17fffffffffd03fffffe00050004e3a0e8111a7400200b90020079f07c18073e000001e020b023fa7f00405f93ffffffb84001fc1f00000f81ffffff8808197e15020042800220bd0400001f000000000000001e0009003fa1100004003ffff40804001fc0000000001ffff80000900000000101bc20042087f8c00000000180fe00000001f8
  | 5, 3 => 0x9000882f4008121f812040080000000780000007c00000038ff210800001ff1010020000c1f800000000ff8000000000f6e7ffff58f17fdfffffffff7061ffff80703fe1fffffffe3220c7f1bf280008fe840000100060f81e0000007f00000009003fa1100000013fa7f0c004001fc0000000001fc1f06001bf711ffffffffdb8842087fefff80ffffffffff8000001fffffffeb3f610ffffffffffeffffffc0078083fffffffff81f920d5ffd6381fc2ccc2087f9c0060ffe0180fe06000001f8
  | 5, 4 => 0xe203130000b0608317c418a0700180000050300183e00040188081f1002c188081f1002c0c0000f800140c0000f8001400000401000000800000020000000000000000000000000003fffffce68ff9ffffffffffa1fffff00001f8ffffffffff802044000000000200000000000000000000000000000000000c5ffe1f8311f7c013fffd2420079f07c18073e000fffe0201f00080020102011f87e0c400f800000000800007c1f06003cb9ff8440001ab5ffffffea1c187f0000000c187fffffe00
  | 5, 5 => 0xe2d7fffe1cb172c71fc418b17061ffff0650306183e000503ffffddf62fbdfffa1e87cee1fffffffe1fdffffe0f83e7f8c093fffe1ca010031a0000004001ffff06000001800000000400000000001000010800000000000000000000000000000ffff97e49aa07fff962082007fff83e000003fff8000000000190000000062f700002fcfe01f8000000073ff80001fe7fdf93ffffffa8317ffa3100004f81ffffff80001ffc000000243dffbdf78076ffffffffeff01fffffffe073ffffffffe7f
  | 5, 6 => 0xfffc8ca2f6007ffdfc3082003ffe000078003ffe7c000000185f7fffd331e7c08a20bd0420079fffe18073e000001e02000011000000000000080100000000000000000000000000006c002002d04201d761d830063e000001e0200079f07c180722440000001162c405c418b1306000000050306003e000503fff7f3fbf95ffff7f3fbf95efff9f07df827fff9f07df8271f0220002010600047ff40c00f8000000008000003ff8000285ffe9fc311e7c0fea4fd043007ff07c18073e07f001e020
  | 5, 7 => 0xdfffbf81ffbfe0ffffffdfefffffffe0fffff07ffffffff7d85f7fff8331ffc08260bd2c2c079fffc1907fe000001e160400001080080000000000000000000000000000000000000054a00000011a346000ab9d3a3e78000000bf3e78007ffebf9f23fa1120106893ffffffe84f81fc0000080001ffffff80203145b1060040b1c400060c501860f8000000186000000401f000000a010217cc07e00400f8000000008001e001f00001fc29bfffd7fbfdfffffdb7fefe000fffe1f8fe79fffe19ff
  | 5, 8 => 0xf000082f410a16c000000478f8000007808001e00000001c8000008000007c00000000000000000000003e00000000003f7df87e2c57bf0048fef4508f9e7c1f0609cf80001f780802047e3fbf0004087e04000000001f07df8000001f00000007f7dfffffcd7ff7ff9fefdffbf9e7ffffe69ff9e7c1f7e7fcfdb0220bd15fbff7f7fbfffefff80001e1fffff9ffffffff317df87e0c479f11f8fefc10801e7c1f0601cf807c1f7e0839b1c5f9062c5ff3c5f1062c5c1860f800140ff860f800140
  | 5, 9 => 0xffffffffffb8fffffe7f8e47ffffffffff883ffffc1f0601ffff31fff0a01fffa90820800fff80ffe0000fff8000000000002210821fe000043df40c000000000007e000003ff80603fb1c5f17eee58bffdff46ffdff860f83e7f8c1fffffe1fdfeac71fc6fcb162e7ffd418b1706183e078503061ffe000501fc00328bd043fdf7e1f8311efe000001e020fe79f07c1807c803fb1921a80003fa1100004001fc0000000001fc00000027c0c6a0bd04387fffff8739f3e060001e020007ffffc1807
  | 5, 10 => 0x8021da1100000893b800bf284001fc0000000001fc007f803ffffffffffffffffffffffffffffffffffffffffffffffff600047fe00c07f02010020b0300003ff00403f800000005808467e1f831185000220900000001f07c18000000000000000003735d09ef0002038171b84001ffff87f7c00183e0f9fe07c0020089042840121f811023e00000000200000007c0000900332000000408357ff58a0400180000000000183ff80003fff33fffdb43fffff5fabffefff80fffe1a0fff9f07c19ff
  | 5, 11 => 0xffffffffffffff23fffff4d0ff9fffffffffff81fffff868081b00000011d3a001603cee0c1f8000001dfff800f83e7f8657df97e0cc7ff00098af4d0b01e7c1f0661ff80000078680f5f7e1ffbd3e7ce3a2efdd7a3e79f07ffebf3e79f07ffebf9f23fa11800069ffffffffa84f81fc000000001fffffff8000007e04000000000200000000001f00000000000000000000c000882f4002129f818004600000000780000007c000000085ffeffdf7fe7c0def7ff7ff007fffffffff3e07ffffffff
  | 5, 12 => 0x604517c408816202018010b0300003e000403000000000500000000000000000080200000000000000000000000000000b76ffa110057efdffffffffffffffc00007fffffffffffffffff21082095ffff217bbfffefff8000001fffff80fffffff0400403b40401d082008214e0000001f80200f800000002e3ffff5fff6bc5fffedfb2effdfffe0ffe01c0fffe0f8001f88000800000000000800000000000000000000000000000001fc28040002c190001f900200fe0000000140c0000f800100
  | 5, 13 => 0xffc40c82f410e3fdfc7e0c47bfe000007808307e7c1f0601f83f2108008017a0010020800c1f800000000ff8000000000dfb3ffffffb8f9ffffffffefcf81ffffff88001fffffff81ffffef7bbfffedff77bdf795fffffffffffffffffffffffffe40357ff40c07f8b37cc39fe700183ff80603f8183e0007e1900014a00301fc2004200300c00000000180fe0000000180e2f7dff7deb1fbffbfc4bfbff07fffffffd1ffffffe07fdfd2008a62bd6a00087e844000000000001e0000001f0000000
  | 5, 14 => 0x8003120000000003120000004001800000000001800000000fdf200820000fdf2008200003e78000000003e7800000000ffc717c498b163ff97e418b17fe183e00050307f83e000503c3fffdf42fbd7a4ffffffee1c1fffffe1fdfff87fffffff8217df83000001f000882f400001e7c0000000f8000007800000000000015e00000739f7fe0000000001ff00000fffffffff9bfffffffe7f2bffff61fe7f81fffffffe3f81ffff807e3fff7f1fa3801fff230820800fff9f07c1800fff800000000
  | 5, 15 => 0x6247114408b1620007c41090300000000050300003e000402400808040001024fddf42ea10006000000000007fffe1e0001000000000000000002000000000000000000000000000000000220b500205f6e000301e00000001e0000079f0001807ff8a2789f3fe64fff7ff4bef7fe183e0f9fe307fffff87f7c408fe040000120013fffd2000001f000000000000fffe00064000000000064000000000030000000000030000000000038b1d5ffd62c5cb1cdf1062c5c1860ffe0140c1860f800140
  | 6, 0 => 0x9d3bfa3be74eddbbffffffeecf9ffc1fffafcf9fffffffaffff1c5f10e2c58b1d5ff863c5ff860f800160c1860ffc01400800000080000020800000000000000000000000000000003800c5f1002018a0c5f1062c1c0060f800100c0060f800140fffffffefcf7fffffffefcf7ffffffff7e59ffffffff7e59feffffdf6ffff7bdf7fdffee7ffffffffffffffffffffffff0000421100000002200000000000000000000000000000001fc211ffd0301fc2894a087f8fe000ffe0180fe00000001f8
  | 6, 1 => 0xc08317c418a0408317c418a0400183e00000000183e000003fff7ffff3b1ffffab6abdffafff9fffe1987fff80001e1f800002000000000000082400000000000000000000000000038b1fff5462c58b1fff5462c5c187ff800140c187ff800140ff7ffb7f2dffff93fffffff8ff9ffc1f067fff81ffffffe804008a00000010047fffd32000000000000000001fffe1800657dfc7e0c47ff080882f410b01e7c1f0601ff80000078081fc200002000195f210800000fe0000000000c07800000000
  | 6, 2 => 0xedffffffffefff2bfb9bf5fef01fffffffe1ff81fc00787e1f4e3bfff9f3bfceba4ef9ffafe79ffffffbffe79f07fffff80f7ffffffff9bfffbdfffffc07fffffffffcfffffffffffc7c002002000085f7e1f830003e00000000000079f07c18007f7ea12821fe7f0047ffc0c03f9e0000007e3f8003ff806007c00220bd0408087e1f801003e000001e0200001f07c0000214d304c08470600008250100000000000000000000000000000020000000000020081000000000000000000000000000
  | 6, 3 => 0x6fdf7fffffffb76f7bdf7dffffffffffffffffffffffffffffca200000001b24210820800fe0000000000c00000000000ffbbfffffffe7cb3ffffffe87f81fffffffe3001ffffffe01b008842087a190010c640300c00000000180c00000000180fffffffffffe7fffffffc2c07ffffffffffe3fffffff806018c28842003d990001f190200c00000000140c0000f8001007f0a298af5fe6421ffff40c03f800000787e30007fff80603d5fffffd331ffe6ffffffffbc07ffffe1987fe07fffffff8
  | 6, 4 => 0xa17ffa7e0c47df831fc6fcb0c01ffc1f0601cf8183e078082008fc844000122081e07cea10007f000000000060f83e600e6c4042000007fcc040000003060000000003fe0000000003fff311fa0901fff210828840fff8007c0000fff8000000209023fbdf7dffc893ffffffffc001ffffffffc001fffffffff224ffffffea1428fff5462810007fffffe000007ff800000f420842000007f98842082003000000000003f8000000000190011ffd0301d00884200300c0000ffe0180c00000000180
  | 6, 5 => 0x7f0a27cc21fe660247ff40f03f8003e0007e300003ff807027fd77bdff846efffe1fafdff3ffffffffe273ffff07dfe7f0400000000002108000000000000000000000000000000003ff5ffffffee7cffffffc73dfff87ffffff60c1fffffc1947640005ee40c0370800000056300003ff80603f800000007e1fc2010800001fc2010800000fe0000000000fe0000000000ebffffffffffffe7ffd7fcb1f07fffffffd1ffe1ffe078580004200800000400000000000000000000000000000000000
  | 6, 6 => 0xc88337cc39a8000352110000400183e000000001800000002000000000001020010000000000000000000000000000000e893ffffffa87223fb1100b07001ffffffc03001fc0000503fffffff8f7ffff1d7ffff3c7fffffffc19ffff860fffe1e0eed7fffffff97fefffdd39ff7061fffffff03fe1ffe0007e3b24ffffffea1fcafe8440001c007fffffe00fe07f0000000200000440000020000000010000000000000000000000000387fffdfc3fbf7e083e0fdee3c1fffffe1fdfff860f83e7f8
  | 6, 7 => 0x6400447e00407f08000020103000001f00003f80000000083fff21f920a01fffa14820ac0fff80f800100fff800000140fffffffe9ef7ffff9fe6feb1ffffffff0651ffff83e078581fc299ffd87f9d0099ffd0300fe000ffe01f8c0000ffe01809023fa1100004893fe3182004001fc0000000001fc0000002000fe8440001020fff5462810007f00000000007ff800000ec93ffffffe87423fb1900c07001ffffffe03001fc0000600a5f7e3fbf11e7c87e24bd0420079f07df8073e01f001e020
  | 6, 8 => 0x7f0a20000000640047ff40803f8000000000300003ff800000000000000000004411020000000000000000000000000006400417e00c07f00010820d03000001f00603f80000000683ebdffffffee5ebdffffffee5c187ffffff40c187ffffff40ffcf77ff79ff7fcf77ff79ff7fe183ff807e3fe183ff807e110011ffd0200c4288020011800000ffe0000000000000000dfbaefbbf7fefdffff7fefefffffffffffffffffffffffffffffb9fff8ff9fffb9fff8ff8fff80ffe01f8fff80ffe01f8
  | 6, 9 => 0x7fdc0deeffffb77df87e0c57bffe03fffffffffe7c1f067fdfdf200800001fc0010820000fe7800000000fe0000000000ff0bfb1921fe6403ffff40c07f81fc00007e3001ffff80600100000000000800000200100000000000000000000000000fe8247fff3f87ffff77d2bff7fe183fff9fe3fffffff87ffe7fffe0effdfe77f7fbfffd3f3ffff07ffeff3ffffffffebf600004000000620000000000300000000000300000000000110001e0502018028842007b8c0000f820180c000000001d8
  | 6, 10 => 0x7f0047ff60d07f0a617e21fe3f8003ff80683f80001f007e0400128440001204fe5f8b6a00000000000000001f07c1800d893ffffffa85023ffff40804001ffffff800001ffff80001fc28a42087f99047fffd3300fe00000001f8c001fffe1980e7ffffff5cf7ffcf3fcefdfff07fffff8671ffe183e0787e100011ffd02016008842086a000000ffe00000000000000007202210000b0600047ff4080300000000050300003ff80400000008000001000804000280000000000000000000000000
  | 6, 11 => 0x2000000000000000008000000000000000000000000000000040000000000040000000000000000000000000000000000f7ef17c418f7efdf17eeffffffff83e0007fffff83ffffffdddb11ffd035fff7897bbfffefff80ffe01fffff80fffffff9020880000004891fc7e8e0000000000000000007c1f060012000000000000000000000000000000000000000000000009033fa7f0c005893ffffffa84001fc1f06000001ffffff8038b18140002c18b101f100200c18000000140c1800f800100
  | 6, 12 => 0x3fffffffffea1fffffffffea1fffffffffe00fffffffffe0060000100008060000100008030000000004030000000004038b1c5f1062818b1c58000001c1860f800000c18600000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x100200c0501c0660140400c02004006
  | 7, 0, 0 => 0xa004090140400c2870000a0240700827098257000010140400c130902370000a00405024020882170000a0240101c0200c2070000a0040501c1f0781d70000a02401008030701b7000090140400c1a0640e700005010030081805c1670000a0040501c0400c1570000a00405010140241370000a0040501c0400c1270000102405010030081170000901c040081003c0e7000010240501c0d0300b70000a0240101c04008087
  | 7, 0, 1 => 0x70100200c390243870000a0040500c370241370000a0040501c030083670000501003008070043570000400803014340241870000a02407010010a83370000901c04008030283270000a00409014070340b70000a004070140400831700009004070100200c3070000a004090140707c2f7000090140400c2e0b42c700004008030040f0241870000a024070142b0982570000901c040082a0280f7000010140402402088297
  | 7, 0, 2 => 0x10240501c030084870000a0040501c0d02c1d70000a00409014030ac1b700004008030143401c4770000a0140701003008467028010240501c0400c02800005010030081800440700005010030040911444700007010020142a02840700007010020040310c3e70000a0040901403008427000070100200c051044070000901c04008030fc3e70000901c040080a03c3d70000a024010103c0ec1e70000a004090140b01c3a7
  | 7, 0, 3 => 0x901c040083f1744d70000a00409014070345c70000a010030085b1682370000a0240400c59160527000010140700c571581670000a024070100200c5570000501c04004091145470000a024070082a14c5270000101403024020842970000a004070100200c5170000901c0400c4f0283470000a004070100200c5070000901c0400c4f0044170000a024070084e0fc4d700001024030084c12c4a700007010030084905c167
  | 7, 0, 4 => 0xa0240700c6e1b40b70000901c0500c1a1b00e70000a02401014040086b70000a0240101c050086a70000a02401014030ac6570000101402028071a46870000a02407008030706770000a024070141f1981e70000a0240100c270086570000a0240101c050086470000101407010030086370000a024010142b188257000010140700c610300b7000010240501c1f078607000070100200c5f1045270000a0100200403178437
  | 7, 0, 5 => 0xa0240501c0d1b40b70000101c050087c1ec2570000a024010142b0947a70000a00405010030087970000901c02028050f4787000010240501c0d02c6070000a024010104f1d44d70000a0240101c2b0947770000900407014040087670000a00404008751d04d70000a00409014140dc2c70000a024010141e01c7370000901003028051c87170000a004090140d1940b70000a02407008010a87070000400c02004091106f7
  | 7, 0, 6 => 0xa0040501c030088770000101407010832181e70000101407010572141670000501c03004091148470000101403008370284770000a004050103b20c1e7000010140701003008827000070100200c0905c6f70000a0240101c1f0f01e70000400803028051c48170000a0040901c0400c8070000a02404004030cc5e70000a0240501c0400c7f7000050100301c130043870000a0240101c051f825700005010030087d028177
  | 7, 0, 7 => 0x10240501c030089170000701002028050f4817000010140300837024247000010240501c0400c9070000501003008070908f70000a00409010030088e7000010240501c1f2181e70000a01407010030088d70000a00409014070108c70000a0240700c5914c5270000a004070142b0941d70000a00409010030088b70000a00405010132282370000a00405010142242c70000901c04028050f47270000a0040901407010887
  | 7, 0, 8 => 0xa00409014070789870000a004090140707c1e7000010140700c0225c9670000901c04008030fc4170000a00409014070ac0d7000090040200c952509370000a00409014072481e70000a0240101c1f078777
  | 8, 0, 0 => 0x24070100200c77028348004050100302402028a4802809004020140301ca38028010240501c032889b8028010240301c020dca18028070100200405024a080280901c03014020049f80240501c0400c9e0289d802809004070109c0f01e8028090140301c020b89b8028010240501c040083a802809004020100309c628028010240400c022684a80280901c04008770042a802801010030089916c2380040501c0300809158608
  | 8, 0, 1 => 0x240400c021e80101441800405010032880901c248004090140400c022c4b080040700c0226c0a024498024070140201003098608028010140400c02024af80040501c0400c02024ae80280400c021e8010145f8024070100300405028ad8028010140701003008ac802405010030082e028ab80240501c0400caa2786080240101c04008032a4a880240101c02014031385d802807014040080900ca78024070140200ca624ca58
  | 8, 0, 2 => 0x280900405010022e4b8801c0400803024010286f8028010140401c02050898024070100200c01014b78028010240501007008b6802809010021e8010142a80280701404008b2024b58024070100200c0a014b4801c0400803014b30284080280900405010030ac628028010140400c0220c7a801404008032940a02418802809004070100500c4f80280900407014b20102b80040501c0400c022181d8004090140300804250608
  | 8, 0, 3 => 0x240400c0200407028c18004090140400cc00b42c8028090100301c022842e8024070100200c012fca880040501c030089b0746080280101c05008be2f49b80240101c020100309c7b8024040080300405160608028090040700c05008bc80240400c021e80a014348028010140400c0901c138028070100200c39024bb80280901c0400ca21dca5802809010030087a2cc528028010240701002014ba802809004070100200c778
  | 8, 0, 4 => 0x240101c04008b21dc6080280101c05010022f8cf80280900407010023384d80240701404008cd330a58004090140400c0232cca8028010240301002014c980280901c0201404004c8801407010030081d0281780280901c02004030e49b8028010240400ca201ca18028090100200c0531cc68004090140700c0207c868028090040701402314258028010240700ca2310c38004090140302802010c280280901c0326c01014598
  | 8, 0, 5 => 0x280901c0400cdb368a58028010140400c02264d9802801014040240704c8a80040501003008d82ac1d8024050100200c010646080240101c05010030ac7b802807010020240500cd7802801010021dc0901c8a80040901403008d63546080240101c0200c0a010d48028090140400ca21e8a5802407014040080a004d38024070140201003004d280240101404008b2028d1800405010030280711cd08024070140200c0a0046c8
  | 8, 0, 6 => 0x140400c02024071686080280901c050109c078a580240100803028042547a80280901c050100239ce680040501c032880a024568028010240500c2c010e5801c04008031dc0a0044080280101c0200c9b390e380280101c050080400ce280280901c042880500c3f8024050100300407028e180040501c040080a024e08004090140700cdf02c6080040700c0202404028de8004050100301c02028dd8028010100301402024dc8
  | 8, 0, 7 => 0x280701404008f0024ef80280101407010020346180280901c0201003004ee800409014070100200ced802801014022c80901cec80240101c02014031749b80040700c0202809158498024070140400c010686080040901c0400c0a008eb80280101407010020341d8014070100302402004ea80140400c0201c47004e98028090140401c02050a580240101404008b21e8608004070140202403028e88028090080301c05130a58
  | 8, 0, 8 => 0x280102405008031e8fb801c050100200c0a024fa80280501c0400c023e4f8801c0500803028011b04080280901002014031d4a5800409014032880a010948004090140700c040080c802809014072880400c268028050100301c02024f780240101c0400803014f68028090140201003004f580280101003024021f4f480280900407008033cc1c8028090140400c023c8f180280901c02014031383f802801014040087a0248a8
  | 8, 0, 9 => 0x28010140401c030250280140400c020280711ca58028010140400cc00241380240101c04008030f0608014070100300817028168028010140400c022642380040501c03009010285680280901c04009003c0778028010140700c02024ff80240101c05008b22989380280102407010033f8da80280901c0501003008fd8028090140700cdf1b40b80140400c021e80a0044080040501c040081d0288580280901404008fc2e0a58
  | 8, 0, 10 => 0x24070100200cce00441802407014040080342d0a80240101c0400803425088028010140700ca226c1d8028090100328801014588028010240501c03008f380280701402010031f0a580280101c02014030250780240501c04004020290680040500c0226c0901c2480280102405010034150480280901c0400c4f004b38028090140301002194a580240501003008070050380280901c04008030fc3980280901c040082a014528
  | 8, 0, 11 => 0x280901c02004050a85380280701002004030e443801c040080302405029128028010140700d114049b80280900407010b22887780280901c0200c9b1dca580280501c0400c01009108004050100301c0222460802809004070080500d0f800405010030280915c18802407008030040514c418004050100301c020250e8028090100200c010150d802807008030040514c5f800405010022c80a024188028010140700c040090c8
  | 8, 0, 12 => 0x28010140400c0704c1d802401014020100302919801c050100200ca5460168024050100301c020291780280101c04008031dc1d802405010032880a004198028010240700c02458c38028010240301c022849b8028010140400899228238028010240500ca2358d580280901c0200cb314c528024070100200cce0283480280501c0400c02454a580280901404009003c07a8028010240700c04009148028070080300405025138
  | 8, 0, 13 => 0x280900407010b236cda80280101c04008ce1341d801407010030080a0251d8028090100200c010151c8028070100200ce30051b802805010032880901c5a802809014030089b1e8a580280101c05008c50941d8024040080301c0512ca58028090140700c040091a80240701002014030fc5d8004090140400c070082d802809010030040516458802801010030080901c5b800405010030087d0291880280101c0301002184778
  | 8, 0, 14 => 0x2809004070100248d228028010240501c030340b80280101c05010030252180280901c04008030f06680280101403010021847a80000a00409014070340b7028010140400c021e81d802809004070080307c7780280901c02014030fc9b8028010240501c1e02c25802407010021dc0a004108004090140400c070092080140700c020740a0046c80040900c0201c040291f8028050100200c072951e80280901c0200c01014538
  | 8, 0, 15 => 0x280901c05008030989b80240701002004050a84180280101c05010024acbd80280102407010a200c3c80280701002004050a85f8014070100328801024388028010140700c024a929802407014040080329460802801024030080501d28802801024070100349d2680040501003024021f460802809004070080400d25802809004022c8070144c801c04008030040517c418024070100200c0a0d00f80280101c040140200d248
  | 8, 1, 0 => 0x280901c040080100d3580280501c03009344cca580280501c0301002025328024070100200c0a0040f8028040080301458024bb80280901c0200c04295318004070100302405029308024070100200c051043480040901c0400c024bc60802405010021e80a004108024070100200cb310452800409014030089b028948028070100200cb317c5280280901c04008034b92d80240701402028010406c80280901c05010024b0f08
  | 8, 1, 1 => 0x280101c05008b20107c80280900407010030ac778028090080326c010145880040501c03010021840c8004090140700d3a01139802809004052c8040086580280501003008074e0bb80040501c03010020301d800405010022c80a01c478028010140400ca201c89802801014030080901d378028010100200c4a0253680280900407008c509c258028050100301c022242e80280901c04008b30a8528028010240501c03008928
  | 8, 1, 2 => 0x4090140700d414e89b802801024050103b0081e8028010240501003009408028010140701003008838028010140700c024d13f8028090140301c020dca580040501c0400c094f93a8024070100200c01014418024070140200d3d4f060802809004020100309c7a80280701002024032d4778028070100200c010145f80140400c02028090601780280101402010031887c80140701003009010043880280701002014030253b8
  | 8, 1, 3 => 0x280101c050080400d48802405010030080151cab80280501c0400c02518bb80040500c02010d5024248024070100200c0a014348028010240500c02514d5802807014042c8010091580280900407008030101c8004070100302402029448028010240400c0250c4a80040901c0400ca2424a88004070100202403029428028010140700c023cc1d80280901c02004030147080280900407008b226c7780280900407014c50ac258
  | 8, 1, 4 => 0x2401010022c8070144b80140700c02004090288480240101002028033447780280701003014020054f80140701003008bb0294e80240701404008035340e8004090140700c020294c80040501c0400d1815c1680280501002024032d47a800409014070109c2181e8028090140700c9e0114b80040501003008230284780040701404008b24601680240101c040080500d4a80280900405010030ac7a80280101c0400803391498
  | 8, 1, 5 => 0x2809004070140400c7e802801010030080716c1d8024050100301cab0041a8028090140701003288a5801c04008030040502552802801024070100200d518024070140326c0a0041a8028010140400cc00b01d802809004070104f00c4d8028010140400ca20247d8028010240501c0400c0280280900405008b226c7a8028070100200c010155080040701402010031f07b8028010240500c650080b80280500c0226c0901c5a8
  | 8, 1, 6 => 0x280900407008030f09b802809004050080301d5680240101c05010022c86080140700c0226c010243880040901c03010021b86080280901c0201403138a580240101c040080a2c955802801008031dc0901cec80240101c0200c0a010958028010240501002550b8802807014030040400953802807008030040514c1d8024010100200c771e860801c04008032940a024498004050100202809214188004050100301c020b41d8
  | 8, 1, 7 => 0x240101c0200ca624c77802809004070080500d608028090140700ca24f53c80040901403008d50295f801407010030081d2946080280701404008be2f4a5802801024070140200d5e8028010240500c025755c802801014040080901c8a802405010030095b318608028010240501c0407c1e80140700c02004090295a80040501c0400c0915c608028010140700c040095980280501c0400c01009588024070140200403029578
  | 8, 1, 8 => 0x2401010020280500d6980040901c0302804009688004050100300889028ab802801014030087a024ec80240701002028050043d802801014030080759d33801c050100200c0a004408028040080301c050056680280901c04008030e4a58024070100300402029658004090140301c02029648028010100200c0901d63802809014030100201d6280280901c0400c05164a58028010240501c033cc2b8004050100201c03029618
  | 8, 1, 9 => 0x40500c0201c0402571800409010030080501d70802809004050080400d6f801c0400803004051041d8028070100200ce438ca580240101c0200c9b424a8802801024070080d014c380040501003008d82ac47802809004052c8070083780280900407014035b80b80040901407010020296d8024070100200c010156c80280901c052c8040086d80280701404004030096b8004090100301c020156a800404008031dc0a024188
  | 8, 1, 10 => 0x28010140400cb8024138028010240400ca21e87780280901c05010b2008668028010240501002034658028070100200cb31481d80280101003009431281d8024070140200c9b3a40e8028010100301c022848980240500c02004070297580140701003008010257480280701002004050a81d8004050100201c030257380240101c04008cd33077802807014020100302572801407010030091805c1680280901c0501002400f08
  | 8, 1, 11 => 0x240101404008cd3307a80240101c050080400d7c80280102405010a200c3b80240501c0400c0a0057b8028010140700c0207c83802801024052880400c628028010240501c04288b2802801024030080501d7a8028010240501003301798028010240700ca20106e80280901c050080326ca5802809014042c8070082e80280101c04008035e0e38028090140400c020ec66802407014040080a2c9778028090040501007009768
  | 8, 1, 12 => 0x40500c02028070246880140701003009822ec6080280100c0201c040258180280901c03008da004538028010240401c0205077800407010030280915c4980280501c0400ca2074a580280101407010030081d80280900404008b8015808028090040200c7701c4c8024050100301c020057f80040901c03028024bc9b802401014040080a00d7e80240700803004050297d802809004070109c078778028090140400ca256cc68
  | 8, 1, 13 => 0x40700803028042541d80240101c0200c04624a880280501c0400d11404a580280900404008031d47780240101c0201003015888028010140400d114047d802801010020140301d878028010240400cdb3687a802807008030140400586802809004040140313c7580280101407010034458580280900407008b20144e801407010030080905c608028010240400c070098480280901c040080500d838028010140700c04008618
  | 8, 1, 14 => 0x280102405010020507a800409014072880400c7b802809004070100200d8e80280100c02024073b05b8028090100301c02284a5802805010030240201d8d8004070140400809630cc8028010240501c030081f80240501003028010681980280901c042c8010145980280901c0200cc430ca5802407014040080a0041080040701404008b20746080040501c04009182141680240101c020140400d8b80280900407008030158a8
  | 8, 1, 15 => 0x280901c020140300599800409010030080501d988004090140701002034608024070140400803198868028010140400803025978028010240500c023599680280101404024021f422802801024040140200d9580280901c040080100d94802801024070101e0159380280900404008ce1d44d802801014040080901d9280280101c02010031f07780280901c040140200d9180240700803004040299080040400c02024070298f8
  | 8, 2, 0 => 0x28090140700c026853c8004070100200c774601680140400c0202407029a080280101402010031f07a8024070100200c0167ca880040701002014031d0608028010240501c02034c580240701003008da00441801c04008030040f0251880240701402010030299e80280900407014046759c80040901407010a200c8680280400c02024070059b80280901c040080500d9a801c0400803014a802417802809004070080400c278
  | 8, 2, 1 => 0x28010240501c9c078f380280501c0400ca2608bb80280901407010020346d8028010140400c07691018004090140700ca226c608028010140700c02025a380280901c03010c3004598028090040200c9b1dc7a80240701003008da02834802807014040080900cb58024010100200c7701c4b802809004070140400c2b8004050100301c130291880240101c04008b20145d801c050100202801040408024070100200403029a28
  | 8, 2, 2 => 0x24070100200c410045280280101407010a22c81d8028070140200c9b2941d8028010100200cb80245b800405010022c80901c2480280101407010026a9a9801c0400c02028091241780240101c040140313c6080280901c020140400da8800405010030087a4601680040501c0202404029a780240101c04008cc015a680040501c0326c0a0245780040400c0201407025a58028010240700c021b89b801407010032880a024178
  | 8, 2, 3 => 0x280101c03009344cc77802407014040080a005b080280101c05010b24450180140701003009010281780280901c04008b21dca580240501c0400d414e8a58014070100300801025af8024050100200ce90640e802401014040080a00cd18024070100200c01015ae800405010030240704c6080040901c040140200dad80040501c0400c0a025ac80240101c04008031dc60802801014040080901dab8004090140400ca2360ab8
  | 8, 2, 4 => 0x1407010020740a0041080280901c05008036d53c80280901c0201003015b48028050100302402005b38028090040700803015b280140400c02004090e0448028010240501c0d0100b8004090140401c020502d80240101c05008031ec9b802809004042c807008a180240101c04008ce1346080040901c0400d414bd3a8024050100200ca50281980280102405010c00502c80280901c0400c01009b180280901403008d6354a58
  | 8, 2, 5 => 0x4090140700c022189b800409014030080a011bf80280101403009344cc7a802809010020140301dbe8004070100200ce3029bd80280901c0400803015bc800405010030080a025bb80280101c0301002015ba8028010140400c02025b980280101c0400c026e1b78028010240301c020dc7780280901404008b21e8a580040501c042880a024858028050100301c13004bb8028010140700c0207c1d800405010030080a025b68
  | 8, 2, 6 => 0x28010240501c0371dc680280901c05010b22a89e80280901c04008030f0a5801c050100200ca50243880140400c02028070248f80040501003008180241680280901c0501003005c5800409010030140201dc4801c050100200c011011880040501c0400c0270dc28004090140701002704cc802801024050102c00dc080280101c020140313874800407014022c80a024568004090140700c02298938004050100202807024698
  | 8, 2, 7 => 0x280101c05010030ac1d802801024070100328877800405010030089908c6080140700c0226c0a0241780280501c030089b608bb8028090100301c020b877802401014022c80a0109480140701003004090e04580240101c0402803009ca80280901402010031882680240101c0501002725c880240101c0200ca62549380280901c05008b20102680040501c0400901028858028010140202407228ec8028010240500c020dc7a8
  | 8, 2, 8 => 0x280901c050080400dd180240101c0501002334cc80280101c05008b226c1d802809014070100200dd080280901404008031987a802809010022c801014588028010240501ca2314258014070100302402029cf8028090100301402005ce802801014070109c20c1e802809004070140313c4e8004090140700c023cc608028050100301c02224a58004090100300807734a88028010240501c03009cc8028090140400c0272cc68
  | 8, 2, 9 => 0x28010140201c04025d880280101c04008be2f4778024050100200c0a005d7802801024070100336cda80280101c0400803015d680240101c05010b25053a8028090040701402315d580280102405010032887a8028090140400c020b87a80240700803028050d078802801024050100200dd480280102407010a23384d80040500c0202404029d380140400c0200409029d280280102403009431304a80240101c0200c4e028a88
  | 8, 2, 10 => 0x28010240501c042701e8028010240700cdf1b80b8028070100200c091dddf80040900c0201407029de8004090140700c02775dc8004090140700c0276c93802405010022c80a0041980040701002014031d05d80040501002028033441d80280900407008ce1384d8028010240501c020349b80040400c021e80a024498004070100200c091ddda80240701002004030143e8028090100301c05005d98004070100200c77074608
  | 8, 2, 11 => 0x280901002004030e47a8004090140700ca20100c802809004040080500c75800405010030087a0746080280101404008be2f47a80280501003024021f4a5802801010030240201cf48004090140701003799e580240101c0401403029e48024010140201003029e3802805010022c80901c5a802407008030040514c6080280901c0400801015e2801c050080300404025e1802801024030080501c4c8028010140400c0901de08
  | 8, 2, 12 => 0x28010240501ca200cf380280901c0201003005f080280101c050080400c7c80240101c04008031747780040501c0400c0a009ef8028090140401c02005ee80280101403024021f4218028010140400ca2264238024070140400c0a005ed80280901c0200c04005ec80040501003008ab025eb8028010140400c027a9e9800405010030080711c168028010140300809011e88004090140301002029e780280101403008073b01d8
  | 8, 2, 13 => 0x409014030080a011f9802809004070080326c77802801010030087a390e380140400c0202407005f8800409010030094312c4a80240101404008b8029f780240101c040080a00df68004090140700c02029f580280900404008030f03b8024070100200c0103c608028010240501c033cc0b8028010100201403025f4802809004070140313c9b8028010240301c04009f38028070100300405025f280280900c0200407015f18
  | 8, 2, 14 => 0x28010140701003009ff80280900407008ce1349b8004070100302402029fe8028010140700c023cc9780040501c0400c0220c608028090140400cc00b82c80040501c0400c024601680240101002014031747a80040501003024021f4298024070100200c0a005fd8004090140701003009fc80240101c040080500dfb800405010030081d028188028010140326c0901c138028090040700c27008df8028010140400803075fa8
  | 8, 2, 15 => 0x1407010030040202a0c802809004070080382cc380040400c02028070260a800404008030240501e09800405010030087a02424801c04008030240502a08802401008030140401e078028050100200c0101d1e802801024050100281a058028090040700803812038024070100200c050d06080040501c020280921456802401010020140302a02800409010030094312860800409010030080501c4b80280901c0500803806008
  | 8, 3, 0 => 0x28090040200cc430c7a80280901c040084d0043980280901c05010022c8a580280901c03010021b8a5800405010030240702a11802801014042c8090087d802805010030080901e1080240101c04008030f0868028010240500c0283cd580280901c04008030e4528028090100200c771e8a580040901407010030086080240101c04008030295580240701404008b23a40e802809004040140301e0e8024070140200c0a0060d8
  | 8, 3, 1 => 0x2807014040080319883801c05010020240102a17801c050100200c090e01780280101c020140400e1680140701003009822ec388024050100200c07296158028010240501c0385213802801014030089b2642380240101c042c80a0092f8028010140700c024d133800407008031dc0a024568028090140400c020eca580040901c0400c0a00a128028010140401c020501d8028090140201003188a580280901c04008030fc778
  | 8, 3, 2 => 0x2407014020040402a1e80280900407010030161d802401014020100301e1c80280101403010021946180280901c05008b24f53c80040500c021e80a024568028010240400c0201e1b80280101403010021941d80280901c0400805868f080280901002014030fc7a8028010240500c0700837802809004050100301e19800409014070100300a1880280901c04008ce0fc4d8028010240501c9c07c1e8004050100202407228608
  | 8, 3, 3 => 0x28090140400c070082e801c0400803014b302438802809004070080400e2380040501003008990281880280701003004051645f80240701404008030297780280101403010d502413802801014070100300a2280280100c0201407026218028010240400c028804a8028090100200c7700458802801014030080901e1f80280901c0400ca22cc528028010240400ca250c4a80280901c04288010142a80280901c05008c5098258
  | 8, 3, 4 => 0x280101c020100309c7c800407010030080a0244980280901c04008010e42a80280101403008d5026298028010240700cdf02c77800409010030080501e28802809004050080400e278028010240500c0b01ce5802809004040080500e2680040501c0400c024622580040400c020240716c248028010240501c0400ca280240101c0501002890cc80240701404009003c0608024070100300405164418028010240501c1f0081e8
  | 8, 3, 5 => 0x28010240500cdf02c7a80280101c05010022f8bd800407014042c80a024578028010140700c02010978028010240500c0400a308004090100301c022842d80280101407010028bcbd80280102403008078b8c3802407010031dc0a0041a802407014040040302a2d80040901407010a22c8608028010140300837024998028010240501c042702f8028010240700cda0122c802405010030080a0062b80280900407010028a84d8
  | 8, 3, 6 => 0x280901c040083f0144d802405010031e80a0041a8024070100200c0a016348028050100201c030263380280101c0400c0202632801c04008031dc0900438802805010030087a0245a80240501003008d82aca5801407010032880a00440801c040080301441024bb8028070100200c05025df80280901c040080100c39802801024050100300a3180280901404008b256cc680240400c0201cab0040f8024070080326c0a0040f8
  | 8, 3, 7 => 0x2404008030143401cab80240101402010031887b8024070080326c0a0143480280501c03010021846d802801024030089b50c4a80280901c05010f000a3c80280101c0400803390e3802801014040080901e3b80280901c0400cda0063a80240101404008038e4ab8028010140700c0220c9b80280901c05010028e2378004090140700c0207c608004090140700c028d89380240101c050080400e35802809004070142b00c258
  | 8, 3, 8 => 0x2801024030080501e4580280701404008031981d8028010240501c030089b8028010240400c029124380240101c05010023364280240701003028050d072801c05010022940a0248580240101c020100309c6080280701002014031d0a58028070140400803904bb80280901c040080500e40802801014020100301e3f80280901c04008038f85280280900404008030f07a80280701404008030063d8004090140700cdf0300b8
  | 8, 3, 9 => 0x280400c020240716c5a8028010240501c049341e8028010240501ca200c1f80280901c05008c5094a58028090040700803310c380040400c020140702a4c8024070140200ce91b00e802801014040080792cbd80040701402010030264a80140400c020280711c8f800409010030087a424a880040700c020240402a49801c0501002024032d460802801024070100336e4880040501c030093302a478028010140400c0901e468
  | 8, 3, 10 => 0x4090140700c023cc9680280101c04008b20147480040501c030080a0265480280901002004050a858802801024050100700a53802404008030280103c19800407014020100302a5280280901c0200c01016518004090140700c0229a5080040501003009180601680280901c040080500c3f802801014040240201c2280280701003004051641d8024050100200c0a0064f8024070140200ca50286c80240701404008f002a4e8
  | 8, 3, 11 => 0x40501c0400c0202a5e802809004070080500e5d8028010240501002970b88024010080302804254948004090140400c0202a5b8028010240300865014c380280101c040080500e5a8028010240501ca22c89b80040701002014031741d8004050100301c0202a5980240501c0301002030a580280901c0301002006588024070140200c0195c9380280101c040080500e5680040501c040280915c858028010240500c02954d58
  | 8, 3, 12 => 0x2801014032880901cec80280101003014070266580040901c0400cdb3686080280400c020240716ca58004070100300809016648028070100200c772941d80040900c02014071304b802407008030140402a6380280900402010031887780280701404008be2d4bd80040501003008070901d80280901002014030066280280901c0400c0128a6180280900407010b20144f802801024030140201e608004090140700c0400a5f8
  | 8, 3, 13 => 0x405010032880a0241880040400c020280711e0a80240101002014031d460802809004070100200c3c80140701002028092141780140701003008010243880140700c02004090e084800409014070100300a6780240101c02010031ec7780040900c020140713060800409014070109c07860802809004070084e00c4d802809004070080309c9b8024070140400c0a0041a80280901c04008030fcb38024010140202803012668
  | 8, 3, 14 => 0x240101c0200c9b1dc608028070100200c0517ca580240101c0400803181f680280901c030086d014c3801407010030080a0266b8028010140400d0101e6a80040500c02028042501d80040701402010031f06080280701402010030981d802809004070141e0116e80280901407010039a66880040501c0400c02181ef80240101c04008032187780240101402010031ec7a801c050100200c090e00e80280701402024032d49b8
  | 8, 3, 15 => 0x28010240501c039d00b8028090140400c0700a7380140701003004090284580280501c0400c0260a7280280101c020100302671802401014042c8070082d80280901c040080100e708028090140401c020502e8028010140401c020266f800405010030080a01e6e8004090140700c020109680240101c0400803424a8801c0501002028030266d8028070100200c77608bb8004050100300901028188028010240400c0250e6c8
  | 8, 4, 0 => 0x280901c05008f00127c8028010240700cdb3689b80280101c05010b200883802809004070080307c3c80240101c0400c4f028a88004090140301c020dc60802805010030080901e7b801c05008030040402a7a801407010030080a9e4bb80140701003008010267880240701404008b2294608028010240500ca20106580280101c04008bd016778028010140700c029d933802801024030100201e75800405010032880a01c478
  | 8, 4, 1 => 0x240701404008a5028108004090140700c02a068080240700803010c30283480040701003028024bc1d80280900405008072c95680280101c05008031f09b80280901c0200c0126dec80280501c0400c02074a580280900404008ce1347a8028010240400c0700a7f8024070140200c0a0067e8028010240700c040086e80040500c02028091581880280900404008031dc7a8028010240501c9c0789b802407010030040202a7d8
  | 8, 4, 2 => 0x28010240501c0300a8480000a004090140707c1e70280501c0400c02608bb8028010240501c0300a838004090140700c0226c6080040901407010030088680040501003008070911880040900c0226c0501c4b8004090140400c02a08ab80280900407008033cc778
  | 9, 0, 0 => 0x2809004070100200c05a2240a01c0501002004033c01d9028070140400803294090764010240501c0400ca20294190280901c0400803004052ce40a00409014030100202c7a902801024070100336c0236a40a0240101c030140400a2c902801014070100300809a1e400028010240501c032889b80280501c0400ca20040960a40a004070100301402026869028010240501003008a21ea40a00405010030087a02423902809004070100200c05a1640501c0400c0200409028389
  | 9, 0, 1 => 0x280101c040080900c05a3640a0040700803014040268c90280101c050080400cc51f240a004070100300805075b7902805010030080901c9916a40a0040501c0300804075299028010240501c030089b85240002809004070100500c4f80280501c0400ca2004092ee40a00409014070109c0081e900409014070100a00803a2e40a0240100803014043107a9028010240501003288070b24010140701003024024046090280101c050080900c04a2a40a00409014070100328a899
  | 9, 0, 2 => 0x280901c050080100c046d640a0040500c0201c043541d90240101c04008031dc0a42640a004090140700c0237c9b90000a0240101c05008c5096009004070100200d09028a890280900407008030100581240a0240101c04008031de8f9028010140700c0201009a3a40a0040501c042880900cbe90280102405010a201c032e2400028010140400c0901c1380280901c0200c0530c014f24090040701402010030946090040501c0400c094040a4ea40002809004070100200c778
  | 9, 0, 3 => 0x2809004070140201003a5240a0240701003004020163a90280900404008070140360240a004050100201c0302693902809004070100233803136400024070140200c0a0046c8028010240400ca20140750e4000280900407010023384d8024070140400803028013a640a014070100300901004bb902801014070080901003a4a40a01c040080300405026919028010140700c020113307640a024050100200c0101e9090040501c030089b0280946240a0240101c05008c500c259
  | 9, 0, 4 => 0x280501c0400c0100809a6e4010240400c021e80a01509901c050100200ca50280905a40901c04008031dc0a0040e9028010140400c0202407a6a40a0040901c0328805010c39004090140400c020287a32a40a00405010030240201c7d90040501c0400c090080aa6640a0240501c030089e0113c9028010240400c020140788240a02405008030040401e98902809004070140200c04a5e40901c050100200ce90280e902801014030080701009a5a40901c05008030040402a959
  | 9, 0, 5 => 0x280901c050100100c02a7e4010240501c03028040093990040901407010030086018240a014070100300982024bb9028010140400c07008c022640900407014020100302a9e902801014030080701009a7640a024070140200c0126e009028090140700c0400801a724010240501c0300804181dd90040901407010030089c18240a0240500c0201c04358a5902809004040080700cfc1de40a0240101c0201003014279004070100200c0a014096f640a00409010032880501c4a9
  | 9, 0, 6 => 0x4090140400c0201cd818240a0240101404008033f07a90280901c05008034f4044f240a0140700c0226c010258290040501c0400c090080a4fa40a0040701002024032f47790280101c040080901403a8a409004070100200c0a0150890280101c0400c0901402a864010140700c0202804026a090240101c050080400cc51824090140400c021e80a0040e9000010240501c030100203200a0040501c0400ca202501901c050100200c0a004e910240a00407010022c809014e39
  | 9, 0, 7 => 0x40501c030080a0251815a40a004050100201c03026a590280501c030089b004092ee400028010240501c03008f38028010240300807010058ba40a004090140301c020b09b9004070100200c090140aa9240a0140701003004022a81d9028010240501ca20100309640a0240101c0200c0526e0390240701404008030280142e400028010140400c022642380280101c05010022c8090764010240501c03028025049b9028090100200c770040731a40900407014020100302aa39
  | 9, 0, 8 => 0x2809004050080700cb826e409014070100302802006a99028090140400c020040756e40a0040901c0400c05008da90280101c040080302477aa240a0040501002024032f47a9004090140700c020280494240a004070080302405012a790280900407014020100375640901c0500803004044f06090280901c050100200c1e29640a0040900c0201407012a69028010140701002024036aa409004070080302804298779028070100200c01014b307640a0240101c05010030096e9
  | 9, 0, 9 => 0x28010100200c071280938e40a0040900c0226c0501d439004090140700c020109318240a004070100201403024749004070100200c090140aab240a024050100301c02300a590000a004070100200c770760010240501c0400c0a0093a90240101404008032e00a2ae40a0040501c0300809011349028090140400c021e80131a40901c05008030040402aab90240101c04008030147718240a024070100200c01016aa90240101c0400803014a818240a0040701402024032f89b9
  | 9, 0, 10 => 0x280101c0400c0900805ac640a0240101c0200c9b014c390000a02407008030040514e0010240501c030080402a81901407010030081d028013a640a0040901407010a200c9c902807014040080900403ac240a024010100200c7701c7a90280900407010020140313640a0240501c0400c02278a590280901c050080100c04abe400004090140400c070082d80040901407010030080aaba40002801010030080901c5b80280901c050080400c01ab640a024070140400803270669
  | 9, 0, 11 => 0x901c050100200ca518200102405010032880a01cd89028010140400c0201c1da6a40a004070100200c77024e490280900405008b201c0435a40a00409014072880400cc59028090140400c0256c0731a40a024010100201403338759028010240501003008070ee400028010140400c021e81d802801024030089b0140712a40a024070100200c010145290040701404008b20280905a4010240501c0400c0202ab2902809004050080400c0718a4010240501c0400ca2028609
  | 9, 0, 12 => 0x240101c0400c0a01402ae6400024070100200c0a0040f8028010240400c0700805ae240901407010030040202ab790280901c05008030113d29640a0040501c03024024049b9028090140701003004a29a640a02405010020040700eb690280101c050080400c09ad640901c05008030053c0289390240101c040080a00ccc1de4010140400c02028072ac47902801024050100301c02ad240901c0501002028013a41090280102405010030087a1ea40a024070140200c04296b39
  | 9, 0, 13 => 0x28090100200c0701401af64090040701402010030287b9024070140400803004a518240a024070140200c01012bc9028010240501c030100202e40a0040901c0400ca20147790280101c0400c0500809aee40102407010032880a014a8902809004070080301077aea40a024070140400803400a5902801010030087a0240539240a0040901003008051ea4490280901c0500801010039f240a0240101c05008030949b9028010240501c0400c0228a40a0240501c03288010113c9
  | 9, 0, 14 => 0xa0040501c0400c0220e00a024070140400803006c4902801024050100300807b0e40a024070140400c02296c290040501c0400c090091118240a0240101c05010b20081e902809004070080301404312400024070100200c010144180280901c0400c02368012ce40a0040501c040240200ec1900409014030080a01c04b024090040501002028033307a90000a01c04008030040517e00a02401014040080700ebf90280501c0400c02024013e640a004090140201c0400ebe9
  | 9, 0, 15 => 0x280101c0400c05008da07640a00409014030082c010d590000901c0400803028050d200a0040501c0400803075aa902801024050100301ca241240102405010030280700aca90280901c0400801014030aa400028010240400c0250c4a8028070100200c0901401b2640a00405010022c80901c99902407014040080a00ccd29640a0040501c030240400ac8902801014070100302402b1e409004050100201c0302ac6902801024070100500803b164010240501c032880a010939
  | 9, 1, 0 => 0x28010240501c030089c26e4090140400c020040702ace9004090140700c020109b18240a024010140200cb8010d590280901c05010b20040227a4010140701003028024e81d9028090140701003004a29a2409004070100200c05182cd902809004070140200c04b324010240501c0400c0202886902801024070100336c0536a40a0240701003004050085990280900405010b201c0230240a0240501c0300402012cb90040901c0400c05008db18240a0140400c020040756c1d9
  | 9, 1, 1 => 0x28010240501c0400c02a3e40a0240101c04008031dd229004090140400c0201c0a32a4010240501c0400c0a00ad3902809004070100500c02b4a40a0040701002014031341d9024070100200c0a014010d24010240501c030089b0286090280900407014040080300e40a004070080301404026d190280901c04008032cc0114a400028090140701003288a58004090140400c070080ab424090040701002014033386090000a00409014070100300a00901407010030040202acf9
  | 9, 1, 2 => 0x280901c050100200c0100640a0240100803014c301cd590240101c050100200cb218240a024070140400cf00089e9004070100200c0938c0a2a240a01c0400803004051481d9000090040701404008b218200a02407014040080329638901c050100200c013a4094624010240501003008d801cab90280101c0501002024034ae40a02401014020100301ed59000090040700803028042560010240500c0226c0a01cd890280901c040080101403b52409004070100200c0a015099
  | 9, 1, 3 => 0x28090140700c04008df29640a0040501c0400ca20251190040501c030080a0100991e40a004070100200c770241d90280901c050080326c014f240a01c050100200403026da90240701404008030280103a40501c0400c02004092ec389028090140400c0101c02b664010240501c0400c0a009e590240101c050100200c60b6240a004070100200c091ded79028010240500c070100283e4010240501c0400c02182d690000a00405010020240722a00a02407014022c8010113d9
  | 9, 1, 4 => 0x40901403008070100ab8a40501c0400c020040902ae19028010140701003008a207640a00405010030080708c1d90240101c0200c0a01005b8240a024070100201403006df902809014070100300402b7a40a024010100201c0500edd902809004070140201003b724090040400803014a801cab9028010240501c03010a271a40a0240101c0200c9b01477902809004050100201c033f2409004070080326c0a014a890040501c0400c0a00809b6e40001c050100200c0a004408
  | 9, 1, 5 => 0x28090140400c020040731a40a004090140700ca20109b90280901c0501002004038de40a0040501c0400d110090190280501c0400c020041d3e640a00407014040080900cbd90280501c0400c02024013e240a024040080301c05004c79028010140400c021e80907640a004050100301c02026e69004090140700c0226c0a24e40a01c050100200c09296e59028010140700c040080b07640901c050100200c0102ae49028010240500c0201c9bb8e40a0040901c0400ca2014db9
  | 9, 1, 6 => 0x280101c040080301409aa240a0240101c02014033384e9004090140700c0a01002bbe4010240501c0400c0a28aee90280501c0400c0900801bb64010240501c030080a010a69028010140400c0202407bb240a0040500c020240401eeb9024010100200c0a01407baa40102405010032880a01cab902809004070080301077ba640a024070100301402006e8902809004050080700c04b9e4010140400c020280901deb90040901407010030280279a4000280901c0501002400f08
  | 9, 1, 7 => 0x240101c0200c0a010a625640a0040501c0400c02026f490040501c0400c020240a70e40a00409014070100328ad690040501c040080a02403bce40901c050100200c0a006f290280900407010031340236a40a024070140400900004f09028010240501c04288032ca409014070100302802504a59028090100200c0701401bc6400028010240501c04288b280280901c050080400cc509a40901c05010020040302af090000a024070140200c9b29600a01c050100200ca5025829
  | 9, 1, 8 => 0x4070100200c0a0150907640a0240501c0400caa0089e9024070140200c0a004041b240a0040501c0400c020768f90280101407010030080920e40102405010030080a01cb09004090140300807010d518240a0040500c020240401e2990040901407010030080abda400028010140700c04008618004090140700c0a00804bd640a01c050100200ca5024bb9028070100200c010140917e4010240701003028025052f9028090040701402314040964000280101407010030081d8
  | 9, 1, 9 => 0x280101c040080500c09bea40a024040080301c0550ca590040701404008b20280946240901c05010020280100c109028010240700c04008df1ba400028010240501c030081f8028010240500c02010d61ea40a0040501c03024024449b90000901c0501002028010420010240400c020140702af9902809014030080101c04be240a0140700c0202404006f790280501c0400c01008aa45640a024010140200cc501cd590280901c050080326c0129640a004090140400c0201c7a9
  | 9, 1, 10 => 0x240101c040080500cce17640900404008030280501f0090000a0240101c020100309e0010240501c030080a011db902809004070080500c04bfe40a004070140400803026fe902801014040080700cfc07640a0040901c030140236c9b902809004070100200c1e1de40a01c050100200403026419028010140400c020247a7a640a00409010030080501e6c902809004070100200c05bf640a00409010030080701644902809004070100300877bf240a0240101c0400803016fb9
  | 9, 1, 11 => 0x28010140400c022640708e40a0240701404008012c8e690240501c0400c0a0080127640a0240101c02014033389b9028010240400c07008c01de40a0040901c0400c0500a489028010240501c030089b26e40a024040080301c05128a590280101c04008032f40538e4010240501c0400d410093a9028010240501c0300804c0e40a00405010030240726413902801024050100301c02c0a40a0240501c042880100cf09028010100200c770240726640a0140400c0202407007019
  | 9, 1, 12 => 0x407010030080a0240512640a00405010030087a0249990280102407010030080549e40a0040501003024024047d90000a01c0501002024032d600a0140400c02004073181d9028010240501c03008043ce40002809004070140400c2b80240501c0400c01008aa18240a0040501c03008040270790280101407010030240261640a0240101c04008032703c9028010240700c0500804c1a40a0240101c0200c05012ba90240501c0400c010080ac1640a0040500c0202407013049
  | 9, 1, 13 => 0x280501c030080102404c3240a0040901c0400c02015269028010240501c030089bb5a40a0040701002014030270b90040501c030080a010a607640a0040701003014020270a900409014040080a01c03c2640a004090140400c023007a90040901c0400c050080ac224070140400803028010244090240101c05010b20280250640901c0501003028010081a902809004070140200cb226e40a0040501c0328809011339028010240500ca201c0435640901c0400803004052cc609
  | 9, 1, 14 => 0x280101c05010022c8092fa40a0240101404008b201cb890040701404008092f40a33240a0240701404008012c8e79004090140700c020280477240a0140700c02004090130f90280901c0200c010113d1de40101407010030080a075c39028070140400809004033be409004050100201c0302b0e90000900405010020280334600a004090140400cc001c2c902807014040080900c012d64000240101c04008031dc6080280900405010b201c020b240a0040701002014030270d9
  | 9, 1, 15 => 0x28010240400c020147a90e409004070100200c0a0171590040501c0400c0a02402c5240102405010030080a1e8cb9028010240501c030081e3ce4090040701002028030171390280900407010020140348a40a0040501003008071e81d90280901c0400c0101402c4a40a024070100200403400779024070140400803004e918240a02407008030040501053902809004070080501003c4640a0040501c0400c02027109028010140700c02404044ce401024050100301c020282d9
  | 9, 2, 0 => 0x2809004070080400c05c6a40a0040501c0400c020241d90280901c050080400cc5296400004090140700c0229893802809014040080100d001ea40a0240101c05010022c99c90280101c040080301409b5e40a0240701003004020171990280101c0400803014e407640901c050100200ca50286090240101c040080a00ccd1de40a004050100201c030271890280901c050100200c9c29640a0240500803004044f47a902809014040080700c01c5e40a00409014030080401f169
  | 9, 2, 1 => 0x28010240400c0250c0712a40102405010030080a01cb19028070100200c0101409c7640901c0400803004050284190040501c040080a0251821640a0040501003008091e9ea9028010240501c030089b84e40901c050100200c011810b90000a0040901c0400ca21de0090040501002028033347a902809010030080101c05c7240a0040400c02024072645b9024070100200c010140ac6e40a00409014070100237c0d9028010140700c040080918640101c0501002028033301d9
  | 9, 2, 2 => 0x280900407008033100530e4090140400c020040756c6090040901c0400c05008da18240a0140700c020240400722900405010030080901c0ac8640a0240101c0200c05012e99000090040701404008cd33200a02404008030040501f2090040501c0400c0202809c7e40a0240701003004052cc599028010140700c02024049da40101c04008030240502b1e902809004070140400c0267640901c0400803028052a0a590280900407014022c8040964010240500c02010d5028ab9
  | 9, 2, 3 => 0x2801014070100300809c9a40a0040901c030100237c7790040901403008070100ac9640a004090140700c020100490280102405010030080701e40002801024070100336cda80040901407010030093a18240a02407014040080100d2c90000a004090140400ca21ea00901c05008030280424ca5902401014040080700c0ac924010140700c02024044d060900407014040080900c0a63240101407010030080a027239028010240400c0700805286409004070100202803014a99
  | 9, 2, 4 => 0x28010240500c04008df1ea40a0240701402010030072990000a0240101002014031d600a004050100300807025e99024070100200c010145218240a01c0400803014b3024bb902407014040080100c0aca240a0040501c020240400f2790280102405010070080305240901c040080302805004bf9028010240501c0202c0309640002801024030080501c4c80240101c040080500c4d182400028010240501c042701e8004070100200c77028094624090040701404008030280a9
  | 9, 2, 5 => 0x4090140700c024e80424e40a0240101c0400c021df2e90280101407010030081d076401024050100301c0202b2d90240101c040080a0140369a40a0240501c03010020072c902809004070100301402bf24000280101c050080400c7c80240101404008b2028073624010240501c030080402a809028010140400c0202407cae40a024070080326c01014b390280101c0400803014e307640a0240101c05008b2010c5900405010030087a028094624010240400c020140702b2a9
  | 9, 2, 6 => 0x28070100200c77024012ee4000040501c0400c0246016802801024050100301c0230240a02401014020100301f319028010240400c070082c1de4010240501c0400ca20293a90280900407010022c8051de40a00409014070100200f30902801024030080701005cbe4010240501c030100237c0c9028010140700c020249ba3a40a014070100302402444a59028090140400ca20040756e40002809004070080326c778028070100200c770240160a40a0040901407010030081e9
  | 9, 2, 7 => 0x280901c0400ca20040514a40a00409010030140201c9a902809004070080400c05cd240a024070100201403338a590280102405010030082c1ea40a0240500c0201c040073390280901c05008030109b2964090140400c02028070073290040901407010030089c21a40a0040701002024032f877902809004040080700cb81de4010240501c0400c0a28aae9000010240400c020140712e0090140400c0201cab004e99004090140700c0a008048da409004070080301404310609
  | 9, 2, 8 => 0xa0240701404008b229600a0240101c0200c0430c779028010140300807010d60764010140700c020240402b36900409014070100a0080370640a00409010030080701643902809014030080701001cd640a01407010030080102672902801014040080900cbe1ea40a0240101404008032e07a9004090140400c0201c0a32e40a024070140200c01012b39000010240501c0400c0218200101407010030081d0281690280900404008031dc0750e4090140400c02028072aca59
  | 9, 2, 9 => 0x28090040200c05010c31ea40a024040080301c05007399028010240500c0201c0465a40a0240501c040040200f3890280901c0200c0501001cde40a02407014040080100d009028010240501c0400ca228a40a004090140700c020101f9028010140400c023000926640a00405010032880901c2390280901c050100200ca5b5a400028010140700c024d13380280900404008031dc0712a40501c0400c020040902a799028010140400c09008076924010240501c0400c021828f9
  | 9, 2, 10 => 0x4090140400c024e8072ae4010240501c03028024e89b9028010140400c0201c097aa4070140400803028010273b9028010140400c024040708e40a0040501c030089b0253490280101c05010b20240244640a01c0500803004040273a90240101c05010020280333640a0240500c0226c0101d5b9028010140400c0201c1dcae40a024070140400c0100ac290280901c05010022c80129640901c050100200c010386090000a004090140301c020de00a004070100302402404779
  | 9, 2, 11 => 0xa00409014070100328a00a0240101402010030947a902401014040080a00c07cfe4010240501c0400c02181e6902405010030080101cc6182400028090140400c070082e80280901c050100200cf029640101c0501002024032f46090280900407010b20140236e40a0240501c03010020046d9028010140400c09009011ea4010240500c0201c0402b3e90240101c050080400c0acf640a0040501003008072641d902809004070100200c7748e40a0240400c02004070173c9
  | 9, 2, 12 => 0x2809004070140201003d064090140400803028013a419902809004070100200c9c1de4010240400c020140702b4090040901c0400c0a008054be4010240501c0300804298609024070140200c010100a95e40000407010030080a024498028010240501c0400ca2a3e40a0240101c04008b2014ce90280901c0200c9b0040514a40a0140701003004022781d90280101c0400c020141d6e240901c0400803014a80040e9004090140700c020289ba0640a004050100301c2c025019
  | 9, 2, 13 => 0x2809004040080500c07d1640a0240101c0200c9b014c49028090140400c020040772e4010140400c0202423028ab9028070140200c0101009d12401024050100300807180b09028070140200c010113d0764000280901c040080100c3980040501c0400c024600905a40a004090140700c04008df90000a0040701404008be2f600a02401008030140401f439028090140400c0100807d0a40a0140700c02024044cca590240101c04008031dc0a18240a0240500c0201c04354a59
  | 9, 2, 14 => 0x28010140700c024d0094ce40a014070100300801025829004090140700ca20280429a40a0240501c0400c022a8a59028090140200c010113c1ea40a0240101c0400c0500b2e900405010030080a0240706240900407008030280424c779004090140700c022980a24e4010240501c03008a6010939028010140700c0400809d1a409004070100200c77028a89028010240501c0400c020be4000280101c0400803390e380280102407010050080364e40a0240700803004044f0779
  | 9, 2, 15 => 0x240701404008032940a3a640a00409010030080501d439024070140200c9b0280103a400028090040700803310c38028010240500c0201c04d2a4010240500c0201c0402b49902809004050100201cb2d2240a00407014040080900cbe90240101c05010023340a3324070140400803024bb0280e902801014030080901c993b240101c0400c02028090174790280501c0400c02004092ee40a004090140700c0226e8f900409010030087a028052a2400028010240501c030089b8
  | 9, 3, 0 => 0x2809014030089b0040731a40a00409014030080b01cd590280101c050080900cbd26e40a00409010030080501c4a90000a0240701002014030fe0010240501c042880a00ccc90280900407008030140430e40a004070100201403338749028050100300807318092ee40a004090140400c07289059028070100200c0900405d3640a004070100328809014e49028010240400c0700805d3240a0040900c02014070104c9004090140700c020106077240a0240101404008072cb4b9
  | 9, 3, 1 => 0x409010030080501c0a12e40a004070100200ce4024e39028010140400c070082c07640a024070100301402368a590280901c04008b2004052ce409004070140400803029c990240101c04008033380a2a240900407010020140302b4e90280900407008030109b1de40a0240101c04014033384f90280901c040080500c010fe40a0040701404008be024bd90280101404008072e0092f64010240501c030089b028a690280101407010030240240640900407014040080a00e249
  | 9, 3, 2 => 0x240701404008033c00a3a640a0040700c02024040175190040901407010030080a182400024070140400c0a0041a80280101c0400ca20240538e40a0240101404008032c87a9004090140700c020280477640a0240101c05008042ca979028010240501c0400c0227240a0040500c0201c040275090280901c0200c0430c012ce40101407010030080a075c290240701404008b2028013a64010140701003008091832390280101407010030081dd3e40a0240101c04008031ded69
  | 9, 3, 3 => 0x2801024050100301c025e64010240501c030080a0109390280102407010030780536a4010240501c0400c02078609028070100200c0901401d5640a0240501c030100202ca590280101c0400c0900805d52409004070100200c0a014a8902809004050080400c07d4e40a0240501c0400c02288a590280901c0500803004044f240a0140400c020040901f529028010240500c07008040de4010140400c0201c990291890000a0240101c04008030f2000014070100300801024388
  | 9, 3, 4 => 0x280501c0400c020040951a40a024050100201c033f0a59028010240501c030089c07e40a004090140700c1e0100b9028010240400c023680712a40a01c050100200403027599024070100200c0a01509296409004070080302805013589028010240400c0500807d5e40a004090140328807010d69028090140701003008019a240a004050100301c020275690040501c0400ca20280905a4010140400c02028094601890280101c05008b2024044d24000240101c0400803424a88
  | 9, 3, 5 => 0x2809004070140400c020ae4010240501c030080a26e8090000a01407010030081d29600a0240101c0200cc4010c39028010240501c0400c02b5a40a0240501c040040200e3c90000a0040901c03010021ba0000280900404008031dc7a80040501c0400c0a00809d6e40a004090140700c020109b902801010030080901c0516e40901c04008030040502b5a90280901407010032880127a40a004070100200c051dc1d9028010240500c04008df196409004070140400803334609
  | 9, 3, 6 => 0x24070140200c0a00404d8240501c0400c02004092ec6090000a0140701003009822ee000004090140700c0226c6080140701003008010258218240a0240101c02010030175f9000010240501c0400c0221a00a004070100200c0901549900409014030080a010072524010240501c0400c0202b5e900405010030080901c9909240a0040901407008df00cc590280901c050080300404d7640a024050100200c0101f5c902801024030080501d4313240a004090140700c020789b9
  | 9, 3, 7 => 0x409010030080501c4a18240501c0400c020040902b62900409010030080501d4318240a0240400c021e8010145290040901407010024e80333240a00409014070100300a4d9028090040200c0501007d864010240400c020140750c4b9
  | 10, 0, 0 => 0x2809004050100201c033f240901c050100200c0a0040e90240101c040080302805426400028010240501c0400c0280280900407008030140431240a004090140700c040080b9028010240501c0400c0228a40a024070100200c01014529028090040701002014031364010240501c0400c0a0093a9028010140700c02024044d240a02405010030080101d5b90280102407010030140236a40901c050100200c0a004e990000a0240101c04008031de00a024070100200c01014b39
  | 10, 0, 1 => 0x280501c0400c02004092ee400028010240501c030089b80280501c0400c020040960a40a004090140700c04008df90000a00409014070100328a00900407014040080a00ccd90280901c05010020040340240000409014070100300860802801024050100301c0230240a0040901407010030081e90280101407010030080907640a004090140400c0201c7a90000a0040501c0400c020760010240501c030080a010a69028090140400c020040731a40a00407014040080900cbd9
  | 10, 0, 2 => 0xa004090140700c020109b9004090140700c020280424e409004070100200c0a014a890280901c0500803004044f24010240501c0400c02028609028010240501c0400c0227240a0040501c0400c09009019028010240400c020140712a40a0240101c0200c05010c39028010240400c020140750e40a00407014040080900cbe9
  | 11, 0, 0 => 0x28010240501c0400c028
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 64
  | 7 => 84
  | 8 => 84
  | 9 => 94
  | 10 => 94
  | 11 => 84
  | _ => 0

def idWidth : Nat := 10

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 194 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dA : Nat := 0x1fffffffffffe000000000000ffffffffffff

def dG : Nat := 48

def setA (xs : List Nat) : List Nat := xs.map (moveBits dA dG)

theorem runA {s ws} (h : NatRun (mask 97) (goal 97) s ws) :
    NatRun (mask 97) (goal 97) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 17 0 (NN s)

def ori (zs : List Nat) : List Nat :=
  let az := setA zs
  if hk zs ≤ hk az then zs else az

theorem ori_ok {u ys} (h : NatRun (mask 97) (goal 97) u ys) :
    NatRun (mask 97) (goal 97) u (ori ys) := by
  unfold ori
  dsimp only
  split
  · exact h
  · exact runA h

def poolG : List Nat := [100250221231048801, 85641056362794085, 31545032786988181, 51864007668288661, 51811282599382117, 80011491320890514, 25915570824250466, 74329266781783139, 74329215292507283, 46234488756393115, 100224959316595819, 85593777404741778, 31603306844538978, 74329220650780819, 74329220600399971, 25915570784454754, 80011491381708946, 74376540449769569, 20280516823582817, 79958720136710243, 74334718211016851, 31597860834348194, 85588228315434098, 85588233628519521, 31597814708587617, 31597800758285411, 85588219719170195, 51836505859130514, 51889334007202914, 74329220600411235, 74329220650792083, 74329234560092257, 74329234610473057, 74329209863034979, 74329261452925075]

def Z (s : Nat) := bar 97 S NN idx ori poolG s

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
  have z0 : span (Z 0) (NN 0) 0 = true := by decide +kernel
  have z1 : span (Z 1) (NN 1) 0 = true := by decide +kernel
  have z2 : span (Z 2) (NN 2) 0 = true := by decide +kernel
  have z3 : span (Z 3) (NN 3) 0 = true := by decide +kernel
  have z4 : span (Z 4) (NN 4) 0 = true := by decide +kernel
  have z5 : span (Z 5) (NN 5) 0 = true := by decide +kernel
  have z6 : span (Z 6) (NN 6) 0 = true := by decide +kernel
  have z7_0 : span (Z 7) 6 0 = true := by decide +kernel
  have z7_6 : span (Z 7) 6 6 = true := by decide +kernel
  have z7_12 : span (Z 7) 6 12 = true := by decide +kernel
  have z7_18 : span (Z 7) 6 18 = true := by decide +kernel
  have z7_24 : span (Z 7) 6 24 = true := by decide +kernel
  have z7_30 : span (Z 7) 6 30 = true := by decide +kernel
  have z7_36 : span (Z 7) 6 36 = true := by decide +kernel
  have z7_42 : span (Z 7) 6 42 = true := by decide +kernel
  have z7_48 : span (Z 7) 6 48 = true := by decide +kernel
  have z7_54 : span (Z 7) 6 54 = true := by decide +kernel
  have z7_60 : span (Z 7) 6 60 = true := by decide +kernel
  have z7_66 : span (Z 7) 6 66 = true := by decide +kernel
  have z7_72 : span (Z 7) 6 72 = true := by decide +kernel
  have z7_78 : span (Z 7) 6 78 = true := by decide +kernel
  have z7_84 : span (Z 7) 6 84 = true := by decide +kernel
  have z7_90 : span (Z 7) 6 90 = true := by decide +kernel
  have z7_96 : span (Z 7) 6 96 = true := by decide +kernel
  have z7_102 : span (Z 7) 6 102 = true := by decide +kernel
  have z7_108 : span (Z 7) 6 108 = true := by decide +kernel
  have z7_114 : span (Z 7) 6 114 = true := by decide +kernel
  have z7_120 : span (Z 7) 6 120 = true := by decide +kernel
  have z7_126 : span (Z 7) 6 126 = true := by decide +kernel
  have z7_132 : span (Z 7) 4 132 = true := by decide +kernel
  have z7 : span (Z 7) (NN 7) 0 = true := (span_join (span_join (span_join (span_join z7_0 z7_6) (span_join z7_12 (span_join z7_18 z7_24))) (span_join (span_join z7_30 (span_join z7_36 z7_42)) (span_join z7_48 (span_join z7_54 z7_60)))) (span_join (span_join (span_join z7_66 (span_join z7_72 z7_78)) (span_join z7_84 (span_join z7_90 z7_96))) (span_join (span_join z7_102 (span_join z7_108 z7_114)) (span_join z7_120 (span_join z7_126 z7_132)))))
  have z8_0 : span (Z 8) 6 0 = true := by decide +kernel
  have z8_6 : span (Z 8) 6 6 = true := by decide +kernel
  have z8_12 : span (Z 8) 6 12 = true := by decide +kernel
  have z8_18 : span (Z 8) 6 18 = true := by decide +kernel
  have z8_24 : span (Z 8) 6 24 = true := by decide +kernel
  have z8_30 : span (Z 8) 6 30 = true := by decide +kernel
  have z8_36 : span (Z 8) 6 36 = true := by decide +kernel
  have z8_42 : span (Z 8) 6 42 = true := by decide +kernel
  have z8_48 : span (Z 8) 6 48 = true := by decide +kernel
  have z8_54 : span (Z 8) 6 54 = true := by decide +kernel
  have z8_60 : span (Z 8) 6 60 = true := by decide +kernel
  have z8_66 : span (Z 8) 6 66 = true := by decide +kernel
  have z8_72 : span (Z 8) 6 72 = true := by decide +kernel
  have z8_78 : span (Z 8) 6 78 = true := by decide +kernel
  have z8_84 : span (Z 8) 6 84 = true := by decide +kernel
  have z8_90 : span (Z 8) 6 90 = true := by decide +kernel
  have z8_96 : span (Z 8) 6 96 = true := by decide +kernel
  have z8_102 : span (Z 8) 6 102 = true := by decide +kernel
  have z8_108 : span (Z 8) 6 108 = true := by decide +kernel
  have z8_114 : span (Z 8) 6 114 = true := by decide +kernel
  have z8_120 : span (Z 8) 6 120 = true := by decide +kernel
  have z8_126 : span (Z 8) 6 126 = true := by decide +kernel
  have z8_132 : span (Z 8) 6 132 = true := by decide +kernel
  have z8_138 : span (Z 8) 6 138 = true := by decide +kernel
  have z8_144 : span (Z 8) 6 144 = true := by decide +kernel
  have z8_150 : span (Z 8) 6 150 = true := by decide +kernel
  have z8_156 : span (Z 8) 6 156 = true := by decide +kernel
  have z8_162 : span (Z 8) 6 162 = true := by decide +kernel
  have z8_168 : span (Z 8) 6 168 = true := by decide +kernel
  have z8_174 : span (Z 8) 6 174 = true := by decide +kernel
  have z8_180 : span (Z 8) 6 180 = true := by decide +kernel
  have z8_186 : span (Z 8) 6 186 = true := by decide +kernel
  have z8_192 : span (Z 8) 6 192 = true := by decide +kernel
  have z8_198 : span (Z 8) 6 198 = true := by decide +kernel
  have z8_204 : span (Z 8) 6 204 = true := by decide +kernel
  have z8_210 : span (Z 8) 6 210 = true := by decide +kernel
  have z8_216 : span (Z 8) 6 216 = true := by decide +kernel
  have z8_222 : span (Z 8) 6 222 = true := by decide +kernel
  have z8_228 : span (Z 8) 6 228 = true := by decide +kernel
  have z8_234 : span (Z 8) 6 234 = true := by decide +kernel
  have z8_240 : span (Z 8) 6 240 = true := by decide +kernel
  have z8_246 : span (Z 8) 6 246 = true := by decide +kernel
  have z8_252 : span (Z 8) 6 252 = true := by decide +kernel
  have z8_258 : span (Z 8) 6 258 = true := by decide +kernel
  have z8_264 : span (Z 8) 6 264 = true := by decide +kernel
  have z8_270 : span (Z 8) 6 270 = true := by decide +kernel
  have z8_276 : span (Z 8) 6 276 = true := by decide +kernel
  have z8_282 : span (Z 8) 6 282 = true := by decide +kernel
  have z8_288 : span (Z 8) 6 288 = true := by decide +kernel
  have z8_294 : span (Z 8) 6 294 = true := by decide +kernel
  have z8_300 : span (Z 8) 6 300 = true := by decide +kernel
  have z8_306 : span (Z 8) 6 306 = true := by decide +kernel
  have z8_312 : span (Z 8) 6 312 = true := by decide +kernel
  have z8_318 : span (Z 8) 6 318 = true := by decide +kernel
  have z8_324 : span (Z 8) 6 324 = true := by decide +kernel
  have z8_330 : span (Z 8) 6 330 = true := by decide +kernel
  have z8_336 : span (Z 8) 6 336 = true := by decide +kernel
  have z8_342 : span (Z 8) 6 342 = true := by decide +kernel
  have z8_348 : span (Z 8) 6 348 = true := by decide +kernel
  have z8_354 : span (Z 8) 6 354 = true := by decide +kernel
  have z8_360 : span (Z 8) 6 360 = true := by decide +kernel
  have z8_366 : span (Z 8) 6 366 = true := by decide +kernel
  have z8_372 : span (Z 8) 6 372 = true := by decide +kernel
  have z8_378 : span (Z 8) 6 378 = true := by decide +kernel
  have z8_384 : span (Z 8) 6 384 = true := by decide +kernel
  have z8_390 : span (Z 8) 6 390 = true := by decide +kernel
  have z8_396 : span (Z 8) 6 396 = true := by decide +kernel
  have z8_402 : span (Z 8) 6 402 = true := by decide +kernel
  have z8_408 : span (Z 8) 6 408 = true := by decide +kernel
  have z8_414 : span (Z 8) 6 414 = true := by decide +kernel
  have z8_420 : span (Z 8) 6 420 = true := by decide +kernel
  have z8_426 : span (Z 8) 6 426 = true := by decide +kernel
  have z8_432 : span (Z 8) 6 432 = true := by decide +kernel
  have z8_438 : span (Z 8) 6 438 = true := by decide +kernel
  have z8_444 : span (Z 8) 6 444 = true := by decide +kernel
  have z8_450 : span (Z 8) 6 450 = true := by decide +kernel
  have z8_456 : span (Z 8) 6 456 = true := by decide +kernel
  have z8_462 : span (Z 8) 6 462 = true := by decide +kernel
  have z8_468 : span (Z 8) 6 468 = true := by decide +kernel
  have z8_474 : span (Z 8) 6 474 = true := by decide +kernel
  have z8_480 : span (Z 8) 6 480 = true := by decide +kernel
  have z8_486 : span (Z 8) 6 486 = true := by decide +kernel
  have z8_492 : span (Z 8) 6 492 = true := by decide +kernel
  have z8_498 : span (Z 8) 6 498 = true := by decide +kernel
  have z8_504 : span (Z 8) 6 504 = true := by decide +kernel
  have z8_510 : span (Z 8) 6 510 = true := by decide +kernel
  have z8_516 : span (Z 8) 6 516 = true := by decide +kernel
  have z8_522 : span (Z 8) 6 522 = true := by decide +kernel
  have z8_528 : span (Z 8) 6 528 = true := by decide +kernel
  have z8_534 : span (Z 8) 6 534 = true := by decide +kernel
  have z8_540 : span (Z 8) 6 540 = true := by decide +kernel
  have z8_546 : span (Z 8) 6 546 = true := by decide +kernel
  have z8_552 : span (Z 8) 6 552 = true := by decide +kernel
  have z8_558 : span (Z 8) 6 558 = true := by decide +kernel
  have z8_564 : span (Z 8) 6 564 = true := by decide +kernel
  have z8_570 : span (Z 8) 6 570 = true := by decide +kernel
  have z8_576 : span (Z 8) 6 576 = true := by decide +kernel
  have z8_582 : span (Z 8) 6 582 = true := by decide +kernel
  have z8_588 : span (Z 8) 6 588 = true := by decide +kernel
  have z8_594 : span (Z 8) 6 594 = true := by decide +kernel
  have z8_600 : span (Z 8) 6 600 = true := by decide +kernel
  have z8_606 : span (Z 8) 6 606 = true := by decide +kernel
  have z8_612 : span (Z 8) 6 612 = true := by decide +kernel
  have z8_618 : span (Z 8) 6 618 = true := by decide +kernel
  have z8_624 : span (Z 8) 6 624 = true := by decide +kernel
  have z8_630 : span (Z 8) 6 630 = true := by decide +kernel
  have z8_636 : span (Z 8) 6 636 = true := by decide +kernel
  have z8_642 : span (Z 8) 6 642 = true := by decide +kernel
  have z8_648 : span (Z 8) 6 648 = true := by decide +kernel
  have z8_654 : span (Z 8) 6 654 = true := by decide +kernel
  have z8_660 : span (Z 8) 6 660 = true := by decide +kernel
  have z8_666 : span (Z 8) 6 666 = true := by decide +kernel
  have z8_672 : span (Z 8) 6 672 = true := by decide +kernel
  have z8_678 : span (Z 8) 6 678 = true := by decide +kernel
  have z8_684 : span (Z 8) 6 684 = true := by decide +kernel
  have z8_690 : span (Z 8) 6 690 = true := by decide +kernel
  have z8_696 : span (Z 8) 6 696 = true := by decide +kernel
  have z8_702 : span (Z 8) 6 702 = true := by decide +kernel
  have z8_708 : span (Z 8) 6 708 = true := by decide +kernel
  have z8_714 : span (Z 8) 6 714 = true := by decide +kernel
  have z8_720 : span (Z 8) 6 720 = true := by decide +kernel
  have z8_726 : span (Z 8) 6 726 = true := by decide +kernel
  have z8_732 : span (Z 8) 6 732 = true := by decide +kernel
  have z8_738 : span (Z 8) 6 738 = true := by decide +kernel
  have z8_744 : span (Z 8) 6 744 = true := by decide +kernel
  have z8_750 : span (Z 8) 6 750 = true := by decide +kernel
  have z8_756 : span (Z 8) 6 756 = true := by decide +kernel
  have z8_762 : span (Z 8) 6 762 = true := by decide +kernel
  have z8_768 : span (Z 8) 6 768 = true := by decide +kernel
  have z8_774 : span (Z 8) 6 774 = true := by decide +kernel
  have z8_780 : span (Z 8) 6 780 = true := by decide +kernel
  have z8_786 : span (Z 8) 6 786 = true := by decide +kernel
  have z8_792 : span (Z 8) 6 792 = true := by decide +kernel
  have z8_798 : span (Z 8) 6 798 = true := by decide +kernel
  have z8_804 : span (Z 8) 6 804 = true := by decide +kernel
  have z8_810 : span (Z 8) 6 810 = true := by decide +kernel
  have z8_816 : span (Z 8) 6 816 = true := by decide +kernel
  have z8_822 : span (Z 8) 6 822 = true := by decide +kernel
  have z8_828 : span (Z 8) 6 828 = true := by decide +kernel
  have z8_834 : span (Z 8) 6 834 = true := by decide +kernel
  have z8_840 : span (Z 8) 6 840 = true := by decide +kernel
  have z8_846 : span (Z 8) 6 846 = true := by decide +kernel
  have z8_852 : span (Z 8) 6 852 = true := by decide +kernel
  have z8_858 : span (Z 8) 6 858 = true := by decide +kernel
  have z8_864 : span (Z 8) 6 864 = true := by decide +kernel
  have z8_870 : span (Z 8) 6 870 = true := by decide +kernel
  have z8_876 : span (Z 8) 6 876 = true := by decide +kernel
  have z8_882 : span (Z 8) 6 882 = true := by decide +kernel
  have z8_888 : span (Z 8) 6 888 = true := by decide +kernel
  have z8_894 : span (Z 8) 6 894 = true := by decide +kernel
  have z8_900 : span (Z 8) 6 900 = true := by decide +kernel
  have z8_906 : span (Z 8) 6 906 = true := by decide +kernel
  have z8_912 : span (Z 8) 6 912 = true := by decide +kernel
  have z8_918 : span (Z 8) 6 918 = true := by decide +kernel
  have z8_924 : span (Z 8) 6 924 = true := by decide +kernel
  have z8_930 : span (Z 8) 6 930 = true := by decide +kernel
  have z8_936 : span (Z 8) 6 936 = true := by decide +kernel
  have z8_942 : span (Z 8) 6 942 = true := by decide +kernel
  have z8_948 : span (Z 8) 6 948 = true := by decide +kernel
  have z8_954 : span (Z 8) 6 954 = true := by decide +kernel
  have z8_960 : span (Z 8) 6 960 = true := by decide +kernel
  have z8_966 : span (Z 8) 6 966 = true := by decide +kernel
  have z8_972 : span (Z 8) 6 972 = true := by decide +kernel
  have z8_978 : span (Z 8) 6 978 = true := by decide +kernel
  have z8_984 : span (Z 8) 6 984 = true := by decide +kernel
  have z8_990 : span (Z 8) 6 990 = true := by decide +kernel
  have z8_996 : span (Z 8) 6 996 = true := by decide +kernel
  have z8_1002 : span (Z 8) 6 1002 = true := by decide +kernel
  have z8_1008 : span (Z 8) 6 1008 = true := by decide +kernel
  have z8_1014 : span (Z 8) 6 1014 = true := by decide +kernel
  have z8_1020 : span (Z 8) 6 1020 = true := by decide +kernel
  have z8_1026 : span (Z 8) 6 1026 = true := by decide +kernel
  have z8_1032 : span (Z 8) 6 1032 = true := by decide +kernel
  have z8_1038 : span (Z 8) 6 1038 = true := by decide +kernel
  have z8_1044 : span (Z 8) 6 1044 = true := by decide +kernel
  have z8_1050 : span (Z 8) 6 1050 = true := by decide +kernel
  have z8_1056 : span (Z 8) 6 1056 = true := by decide +kernel
  have z8_1062 : span (Z 8) 4 1062 = true := by decide +kernel
  have z8 : span (Z 8) (NN 8) 0 = true := (span_join (span_join (span_join (span_join (span_join (span_join (span_join z8_0 z8_6) (span_join z8_12 (span_join z8_18 z8_24))) (span_join (span_join z8_30 (span_join z8_36 z8_42)) (span_join z8_48 (span_join z8_54 z8_60)))) (span_join (span_join (span_join z8_66 z8_72) (span_join z8_78 (span_join z8_84 z8_90))) (span_join (span_join z8_96 (span_join z8_102 z8_108)) (span_join z8_114 (span_join z8_120 z8_126))))) (span_join (span_join (span_join (span_join z8_132 z8_138) (span_join z8_144 (span_join z8_150 z8_156))) (span_join (span_join z8_162 (span_join z8_168 z8_174)) (span_join z8_180 (span_join z8_186 z8_192)))) (span_join (span_join (span_join z8_198 z8_204) (span_join z8_210 (span_join z8_216 z8_222))) (span_join (span_join z8_228 (span_join z8_234 z8_240)) (span_join z8_246 (span_join z8_252 z8_258)))))) (span_join (span_join (span_join (span_join (span_join z8_264 z8_270) (span_join z8_276 (span_join z8_282 z8_288))) (span_join (span_join z8_294 (span_join z8_300 z8_306)) (span_join z8_312 (span_join z8_318 z8_324)))) (span_join (span_join (span_join z8_330 z8_336) (span_join z8_342 (span_join z8_348 z8_354))) (span_join (span_join z8_360 (span_join z8_366 z8_372)) (span_join z8_378 (span_join z8_384 z8_390))))) (span_join (span_join (span_join (span_join z8_396 z8_402) (span_join z8_408 (span_join z8_414 z8_420))) (span_join (span_join z8_426 (span_join z8_432 z8_438)) (span_join z8_444 (span_join z8_450 z8_456)))) (span_join (span_join (span_join z8_462 (span_join z8_468 z8_474)) (span_join z8_480 (span_join z8_486 z8_492))) (span_join (span_join z8_498 (span_join z8_504 z8_510)) (span_join z8_516 (span_join z8_522 z8_528))))))) (span_join (span_join (span_join (span_join (span_join (span_join z8_534 z8_540) (span_join z8_546 (span_join z8_552 z8_558))) (span_join (span_join z8_564 (span_join z8_570 z8_576)) (span_join z8_582 (span_join z8_588 z8_594)))) (span_join (span_join (span_join z8_600 z8_606) (span_join z8_612 (span_join z8_618 z8_624))) (span_join (span_join z8_630 (span_join z8_636 z8_642)) (span_join z8_648 (span_join z8_654 z8_660))))) (span_join (span_join (span_join (span_join z8_666 z8_672) (span_join z8_678 (span_join z8_684 z8_690))) (span_join (span_join z8_696 (span_join z8_702 z8_708)) (span_join z8_714 (span_join z8_720 z8_726)))) (span_join (span_join (span_join z8_732 z8_738) (span_join z8_744 (span_join z8_750 z8_756))) (span_join (span_join z8_762 (span_join z8_768 z8_774)) (span_join z8_780 (span_join z8_786 z8_792)))))) (span_join (span_join (span_join (span_join (span_join z8_798 z8_804) (span_join z8_810 (span_join z8_816 z8_822))) (span_join (span_join z8_828 (span_join z8_834 z8_840)) (span_join z8_846 (span_join z8_852 z8_858)))) (span_join (span_join (span_join z8_864 z8_870) (span_join z8_876 (span_join z8_882 z8_888))) (span_join (span_join z8_894 (span_join z8_900 z8_906)) (span_join z8_912 (span_join z8_918 z8_924))))) (span_join (span_join (span_join (span_join z8_930 z8_936) (span_join z8_942 (span_join z8_948 z8_954))) (span_join (span_join z8_960 (span_join z8_966 z8_972)) (span_join z8_978 (span_join z8_984 z8_990)))) (span_join (span_join (span_join z8_996 (span_join z8_1002 z8_1008)) (span_join z8_1014 (span_join z8_1020 z8_1026))) (span_join (span_join z8_1032 (span_join z8_1038 z8_1044)) (span_join z8_1050 (span_join z8_1056 z8_1062))))))))
  have z9_0 : span (Z 9) 6 0 = true := by decide +kernel
  have z9_6 : span (Z 9) 6 6 = true := by decide +kernel
  have z9_12 : span (Z 9) 6 12 = true := by decide +kernel
  have z9_18 : span (Z 9) 6 18 = true := by decide +kernel
  have z9_24 : span (Z 9) 6 24 = true := by decide +kernel
  have z9_30 : span (Z 9) 6 30 = true := by decide +kernel
  have z9_36 : span (Z 9) 6 36 = true := by decide +kernel
  have z9_42 : span (Z 9) 6 42 = true := by decide +kernel
  have z9_48 : span (Z 9) 6 48 = true := by decide +kernel
  have z9_54 : span (Z 9) 6 54 = true := by decide +kernel
  have z9_60 : span (Z 9) 6 60 = true := by decide +kernel
  have z9_66 : span (Z 9) 6 66 = true := by decide +kernel
  have z9_72 : span (Z 9) 6 72 = true := by decide +kernel
  have z9_78 : span (Z 9) 6 78 = true := by decide +kernel
  have z9_84 : span (Z 9) 6 84 = true := by decide +kernel
  have z9_90 : span (Z 9) 6 90 = true := by decide +kernel
  have z9_96 : span (Z 9) 6 96 = true := by decide +kernel
  have z9_102 : span (Z 9) 6 102 = true := by decide +kernel
  have z9_108 : span (Z 9) 6 108 = true := by decide +kernel
  have z9_114 : span (Z 9) 6 114 = true := by decide +kernel
  have z9_120 : span (Z 9) 6 120 = true := by decide +kernel
  have z9_126 : span (Z 9) 6 126 = true := by decide +kernel
  have z9_132 : span (Z 9) 6 132 = true := by decide +kernel
  have z9_138 : span (Z 9) 6 138 = true := by decide +kernel
  have z9_144 : span (Z 9) 6 144 = true := by decide +kernel
  have z9_150 : span (Z 9) 6 150 = true := by decide +kernel
  have z9_156 : span (Z 9) 6 156 = true := by decide +kernel
  have z9_162 : span (Z 9) 6 162 = true := by decide +kernel
  have z9_168 : span (Z 9) 6 168 = true := by decide +kernel
  have z9_174 : span (Z 9) 6 174 = true := by decide +kernel
  have z9_180 : span (Z 9) 6 180 = true := by decide +kernel
  have z9_186 : span (Z 9) 6 186 = true := by decide +kernel
  have z9_192 : span (Z 9) 6 192 = true := by decide +kernel
  have z9_198 : span (Z 9) 6 198 = true := by decide +kernel
  have z9_204 : span (Z 9) 6 204 = true := by decide +kernel
  have z9_210 : span (Z 9) 6 210 = true := by decide +kernel
  have z9_216 : span (Z 9) 6 216 = true := by decide +kernel
  have z9_222 : span (Z 9) 6 222 = true := by decide +kernel
  have z9_228 : span (Z 9) 6 228 = true := by decide +kernel
  have z9_234 : span (Z 9) 6 234 = true := by decide +kernel
  have z9_240 : span (Z 9) 6 240 = true := by decide +kernel
  have z9_246 : span (Z 9) 6 246 = true := by decide +kernel
  have z9_252 : span (Z 9) 6 252 = true := by decide +kernel
  have z9_258 : span (Z 9) 6 258 = true := by decide +kernel
  have z9_264 : span (Z 9) 6 264 = true := by decide +kernel
  have z9_270 : span (Z 9) 6 270 = true := by decide +kernel
  have z9_276 : span (Z 9) 6 276 = true := by decide +kernel
  have z9_282 : span (Z 9) 6 282 = true := by decide +kernel
  have z9_288 : span (Z 9) 6 288 = true := by decide +kernel
  have z9_294 : span (Z 9) 6 294 = true := by decide +kernel
  have z9_300 : span (Z 9) 6 300 = true := by decide +kernel
  have z9_306 : span (Z 9) 6 306 = true := by decide +kernel
  have z9_312 : span (Z 9) 6 312 = true := by decide +kernel
  have z9_318 : span (Z 9) 6 318 = true := by decide +kernel
  have z9_324 : span (Z 9) 6 324 = true := by decide +kernel
  have z9_330 : span (Z 9) 6 330 = true := by decide +kernel
  have z9_336 : span (Z 9) 6 336 = true := by decide +kernel
  have z9_342 : span (Z 9) 6 342 = true := by decide +kernel
  have z9_348 : span (Z 9) 6 348 = true := by decide +kernel
  have z9_354 : span (Z 9) 6 354 = true := by decide +kernel
  have z9_360 : span (Z 9) 6 360 = true := by decide +kernel
  have z9_366 : span (Z 9) 6 366 = true := by decide +kernel
  have z9_372 : span (Z 9) 6 372 = true := by decide +kernel
  have z9_378 : span (Z 9) 6 378 = true := by decide +kernel
  have z9_384 : span (Z 9) 6 384 = true := by decide +kernel
  have z9_390 : span (Z 9) 6 390 = true := by decide +kernel
  have z9_396 : span (Z 9) 6 396 = true := by decide +kernel
  have z9_402 : span (Z 9) 6 402 = true := by decide +kernel
  have z9_408 : span (Z 9) 6 408 = true := by decide +kernel
  have z9_414 : span (Z 9) 6 414 = true := by decide +kernel
  have z9_420 : span (Z 9) 6 420 = true := by decide +kernel
  have z9_426 : span (Z 9) 6 426 = true := by decide +kernel
  have z9_432 : span (Z 9) 6 432 = true := by decide +kernel
  have z9_438 : span (Z 9) 6 438 = true := by decide +kernel
  have z9_444 : span (Z 9) 6 444 = true := by decide +kernel
  have z9_450 : span (Z 9) 6 450 = true := by decide +kernel
  have z9_456 : span (Z 9) 6 456 = true := by decide +kernel
  have z9_462 : span (Z 9) 6 462 = true := by decide +kernel
  have z9_468 : span (Z 9) 6 468 = true := by decide +kernel
  have z9_474 : span (Z 9) 6 474 = true := by decide +kernel
  have z9_480 : span (Z 9) 6 480 = true := by decide +kernel
  have z9_486 : span (Z 9) 6 486 = true := by decide +kernel
  have z9_492 : span (Z 9) 6 492 = true := by decide +kernel
  have z9_498 : span (Z 9) 6 498 = true := by decide +kernel
  have z9_504 : span (Z 9) 6 504 = true := by decide +kernel
  have z9_510 : span (Z 9) 6 510 = true := by decide +kernel
  have z9_516 : span (Z 9) 6 516 = true := by decide +kernel
  have z9_522 : span (Z 9) 6 522 = true := by decide +kernel
  have z9_528 : span (Z 9) 6 528 = true := by decide +kernel
  have z9_534 : span (Z 9) 6 534 = true := by decide +kernel
  have z9_540 : span (Z 9) 6 540 = true := by decide +kernel
  have z9_546 : span (Z 9) 6 546 = true := by decide +kernel
  have z9_552 : span (Z 9) 6 552 = true := by decide +kernel
  have z9_558 : span (Z 9) 6 558 = true := by decide +kernel
  have z9_564 : span (Z 9) 6 564 = true := by decide +kernel
  have z9_570 : span (Z 9) 6 570 = true := by decide +kernel
  have z9_576 : span (Z 9) 6 576 = true := by decide +kernel
  have z9_582 : span (Z 9) 6 582 = true := by decide +kernel
  have z9_588 : span (Z 9) 6 588 = true := by decide +kernel
  have z9_594 : span (Z 9) 6 594 = true := by decide +kernel
  have z9_600 : span (Z 9) 6 600 = true := by decide +kernel
  have z9_606 : span (Z 9) 6 606 = true := by decide +kernel
  have z9_612 : span (Z 9) 6 612 = true := by decide +kernel
  have z9_618 : span (Z 9) 6 618 = true := by decide +kernel
  have z9_624 : span (Z 9) 6 624 = true := by decide +kernel
  have z9_630 : span (Z 9) 6 630 = true := by decide +kernel
  have z9_636 : span (Z 9) 6 636 = true := by decide +kernel
  have z9_642 : span (Z 9) 6 642 = true := by decide +kernel
  have z9_648 : span (Z 9) 6 648 = true := by decide +kernel
  have z9_654 : span (Z 9) 6 654 = true := by decide +kernel
  have z9_660 : span (Z 9) 6 660 = true := by decide +kernel
  have z9_666 : span (Z 9) 6 666 = true := by decide +kernel
  have z9_672 : span (Z 9) 6 672 = true := by decide +kernel
  have z9_678 : span (Z 9) 6 678 = true := by decide +kernel
  have z9_684 : span (Z 9) 6 684 = true := by decide +kernel
  have z9_690 : span (Z 9) 6 690 = true := by decide +kernel
  have z9_696 : span (Z 9) 6 696 = true := by decide +kernel
  have z9_702 : span (Z 9) 6 702 = true := by decide +kernel
  have z9_708 : span (Z 9) 6 708 = true := by decide +kernel
  have z9_714 : span (Z 9) 6 714 = true := by decide +kernel
  have z9_720 : span (Z 9) 6 720 = true := by decide +kernel
  have z9_726 : span (Z 9) 6 726 = true := by decide +kernel
  have z9_732 : span (Z 9) 6 732 = true := by decide +kernel
  have z9_738 : span (Z 9) 6 738 = true := by decide +kernel
  have z9_744 : span (Z 9) 6 744 = true := by decide +kernel
  have z9_750 : span (Z 9) 6 750 = true := by decide +kernel
  have z9_756 : span (Z 9) 6 756 = true := by decide +kernel
  have z9_762 : span (Z 9) 6 762 = true := by decide +kernel
  have z9_768 : span (Z 9) 6 768 = true := by decide +kernel
  have z9_774 : span (Z 9) 6 774 = true := by decide +kernel
  have z9_780 : span (Z 9) 6 780 = true := by decide +kernel
  have z9_786 : span (Z 9) 6 786 = true := by decide +kernel
  have z9_792 : span (Z 9) 6 792 = true := by decide +kernel
  have z9_798 : span (Z 9) 6 798 = true := by decide +kernel
  have z9_804 : span (Z 9) 6 804 = true := by decide +kernel
  have z9_810 : span (Z 9) 6 810 = true := by decide +kernel
  have z9_816 : span (Z 9) 6 816 = true := by decide +kernel
  have z9_822 : span (Z 9) 6 822 = true := by decide +kernel
  have z9_828 : span (Z 9) 6 828 = true := by decide +kernel
  have z9_834 : span (Z 9) 6 834 = true := by decide +kernel
  have z9_840 : span (Z 9) 6 840 = true := by decide +kernel
  have z9_846 : span (Z 9) 6 846 = true := by decide +kernel
  have z9_852 : span (Z 9) 6 852 = true := by decide +kernel
  have z9_858 : span (Z 9) 6 858 = true := by decide +kernel
  have z9_864 : span (Z 9) 6 864 = true := by decide +kernel
  have z9_870 : span (Z 9) 6 870 = true := by decide +kernel
  have z9_876 : span (Z 9) 6 876 = true := by decide +kernel
  have z9_882 : span (Z 9) 6 882 = true := by decide +kernel
  have z9 : span (Z 9) (NN 9) 0 = true := (span_join (span_join (span_join (span_join (span_join (span_join (span_join z9_0 z9_6) (span_join z9_12 z9_18)) (span_join (span_join z9_24 z9_30) (span_join z9_36 (span_join z9_42 z9_48)))) (span_join (span_join (span_join z9_54 z9_60) (span_join z9_66 z9_72)) (span_join (span_join z9_78 z9_84) (span_join z9_90 (span_join z9_96 z9_102))))) (span_join (span_join (span_join (span_join z9_108 z9_114) (span_join z9_120 z9_126)) (span_join (span_join z9_132 z9_138) (span_join z9_144 (span_join z9_150 z9_156)))) (span_join (span_join (span_join z9_162 z9_168) (span_join z9_174 (span_join z9_180 z9_186))) (span_join (span_join z9_192 z9_198) (span_join z9_204 (span_join z9_210 z9_216)))))) (span_join (span_join (span_join (span_join (span_join z9_222 z9_228) (span_join z9_234 z9_240)) (span_join (span_join z9_246 z9_252) (span_join z9_258 (span_join z9_264 z9_270)))) (span_join (span_join (span_join z9_276 z9_282) (span_join z9_288 z9_294)) (span_join (span_join z9_300 z9_306) (span_join z9_312 (span_join z9_318 z9_324))))) (span_join (span_join (span_join (span_join z9_330 z9_336) (span_join z9_342 z9_348)) (span_join (span_join z9_354 z9_360) (span_join z9_366 (span_join z9_372 z9_378)))) (span_join (span_join (span_join z9_384 z9_390) (span_join z9_396 (span_join z9_402 z9_408))) (span_join (span_join z9_414 z9_420) (span_join z9_426 (span_join z9_432 z9_438))))))) (span_join (span_join (span_join (span_join (span_join (span_join z9_444 z9_450) (span_join z9_456 z9_462)) (span_join (span_join z9_468 z9_474) (span_join z9_480 (span_join z9_486 z9_492)))) (span_join (span_join (span_join z9_498 z9_504) (span_join z9_510 z9_516)) (span_join (span_join z9_522 z9_528) (span_join z9_534 (span_join z9_540 z9_546))))) (span_join (span_join (span_join (span_join z9_552 z9_558) (span_join z9_564 z9_570)) (span_join (span_join z9_576 z9_582) (span_join z9_588 (span_join z9_594 z9_600)))) (span_join (span_join (span_join z9_606 z9_612) (span_join z9_618 (span_join z9_624 z9_630))) (span_join (span_join z9_636 z9_642) (span_join z9_648 (span_join z9_654 z9_660)))))) (span_join (span_join (span_join (span_join (span_join z9_666 z9_672) (span_join z9_678 z9_684)) (span_join (span_join z9_690 z9_696) (span_join z9_702 (span_join z9_708 z9_714)))) (span_join (span_join (span_join z9_720 z9_726) (span_join z9_732 z9_738)) (span_join (span_join z9_744 z9_750) (span_join z9_756 (span_join z9_762 z9_768))))) (span_join (span_join (span_join (span_join z9_774 z9_780) (span_join z9_786 z9_792)) (span_join (span_join z9_798 z9_804) (span_join z9_810 (span_join z9_816 z9_822)))) (span_join (span_join (span_join z9_828 z9_834) (span_join z9_840 (span_join z9_846 z9_852))) (span_join (span_join z9_858 z9_864) (span_join z9_870 (span_join z9_876 z9_882))))))))
  have z10_0 : span (Z 10) 6 0 = true := by decide +kernel
  have z10_6 : span (Z 10) 6 6 = true := by decide +kernel
  have z10_12 : span (Z 10) 6 12 = true := by decide +kernel
  have z10_18 : span (Z 10) 6 18 = true := by decide +kernel
  have z10_24 : span (Z 10) 6 24 = true := by decide +kernel
  have z10_30 : span (Z 10) 6 30 = true := by decide +kernel
  have z10_36 : span (Z 10) 6 36 = true := by decide +kernel
  have z10_42 : span (Z 10) 1 42 = true := by decide +kernel
  have z10 : span (Z 10) (NN 10) 0 = true := (span_join (span_join (span_join z10_0 z10_6) (span_join z10_12 z10_18)) (span_join (span_join z10_24 z10_30) (span_join z10_36 z10_42)))
  have z11 : span (Z 11) (NN 11) 0 = true := by decide +kernel
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
  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 97 s poolG xsG || found S NN idx s (ori xsG)

theorem rootChecked : span RootG 5 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 97) (goal 97) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

end PEqualNP.Outside.L_meta_7402_aux

theorem PEqualNP.Outside.L_meta_7402 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply PEqualNP.Outside.L_meta_7402_aux.mainG PEqualNP.Outside.L_meta_7402_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩
