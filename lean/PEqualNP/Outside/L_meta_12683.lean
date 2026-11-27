import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- NOT gates save nothing on this six-input function: an AND/OR circuit with 9 gates is given, and a
-- table of live-wire states, checked by the kernel, shows that no AND/OR/NOT circuit has 8 gates or
-- fewer. The checker (Run, exists_run, next, covers, bar, moves) is copied from the merged
-- PEqualNP/Outside/L_meta_8493.lean; the rows are all pairs of a zero row and a one row, and the
-- tables hold 64-bit truth tables that expand to those pairs.
namespace PEqualNP.Outside.L_meta_12683

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4240493760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 25, 0, 0, 0, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 6, 6, 6, 6, 6, 6, 6, 7, 6, 6, 10, 11, 6, 6, 14, 15, 6, 6, 6, 6, 6, 6, 22, 23, 6, 6, 26, 27, 28, 29, 30, 31, 6, 6, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 60, 61, 62, 63, 7, 7, 7, 7, 7, 7, 6, 7, 7, 7, 10, 11, 7, 7, 14, 15, 7, 7, 7, 7, 7, 7, 22, 23, 7, 7, 26, 27, 28, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 10, 10, 10, 10, 10, 10, 6, 7, 10, 10, 10, 11, 10, 10, 14, 15, 10, 10, 10, 10, 10, 10, 22, 23, 10, 10, 26, 27, 28, 29, 30, 31, 10, 10, 10, 35, 10, 37, 38, 39, 10, 41, 42, 43, 10, 45, 46, 47, 10, 49, 10, 51, 10, 53, 54, 55, 10, 57, 58, 59, 60, 61, 62, 63, 11, 11, 11, 11, 11, 11, 6, 7, 11, 11, 10, 11, 11, 11, 14, 15, 11, 11, 11, 11, 11, 11, 22, 23, 11, 11, 26, 27, 28, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 14, 14, 14, 14, 14, 14, 6, 7, 14, 14, 10, 11, 14, 14, 14, 15, 14, 14, 14, 14, 14, 14, 22, 23, 14, 14, 26, 27, 28, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 60, 61, 62, 63, 15, 15, 15, 15, 15, 15, 6, 7, 15, 15, 10, 11, 15, 15, 14, 15, 15, 15, 15, 15, 15, 15, 22, 23, 15, 15, 26, 27, 28, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 22, 22, 22, 22, 22, 22, 6, 7, 22, 22, 10, 11, 22, 22, 14, 15, 22, 22, 22, 22, 22, 22, 22, 23, 22, 22, 26, 27, 28, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 60, 61, 62, 63, 23, 23, 23, 23, 23, 23, 6, 7, 23, 23, 10, 11, 23, 23, 14, 15, 23, 23, 23, 23, 23, 23, 22, 23, 23, 23, 26, 27, 28, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 26, 26, 26, 26, 26, 26, 6, 7, 26, 26, 10, 11, 26, 26, 14, 15, 26, 26, 26, 26, 26, 26, 22, 23, 26, 26, 26, 27, 28, 29, 30, 31, 26, 26, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 60, 61, 62, 63, 27, 27, 27, 27, 27, 27, 6, 7, 27, 27, 10, 11, 27, 27, 14, 15, 27, 27, 27, 27, 27, 27, 22, 23, 27, 27, 26, 27, 28, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 60, 61, 62, 63, 28, 28, 28, 28, 28, 28, 6, 7, 28, 28, 10, 11, 28, 28, 14, 15, 28, 28, 28, 28, 28, 28, 22, 23, 28, 28, 26, 27, 28, 29, 30, 31, 28, 28, 28, 35, 28, 37, 38, 39, 28, 41, 42, 43, 28, 45, 46, 47, 28, 49, 28, 51, 28, 53, 54, 55, 28, 57, 58, 59, 60, 61, 62, 63, 29, 29, 29, 29, 29, 29, 6, 7, 29, 29, 10, 11, 29, 29, 14, 15, 29, 29, 29, 29, 29, 29, 22, 23, 29, 29, 26, 27, 28, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 60, 61, 62, 63, 30, 30, 30, 30, 30, 30, 6, 7, 30, 30, 10, 11, 30, 30, 14, 15, 30, 30, 30, 30, 30, 30, 22, 23, 30, 30, 26, 27, 28, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 60, 61, 62, 63, 31, 31, 31, 31, 31, 31, 6, 7, 31, 31, 10, 11, 31, 31, 14, 15, 31, 31, 31, 31, 31, 31, 22, 23, 31, 31, 26, 27, 28, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 35, 35, 35, 35, 35, 35, 6, 7, 35, 35, 10, 11, 35, 35, 14, 15, 35, 35, 35, 35, 35, 35, 22, 23, 35, 35, 26, 27, 28, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 37, 37, 37, 37, 37, 37, 6, 7, 37, 37, 10, 11, 37, 37, 14, 15, 37, 37, 37, 37, 37, 37, 22, 23, 37, 37, 26, 27, 28, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 60, 61, 62, 63, 38, 38, 38, 38, 38, 38, 6, 7, 38, 38, 10, 11, 38, 38, 14, 15, 38, 38, 38, 38, 38, 38, 22, 23, 38, 38, 26, 27, 28, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 60, 61, 62, 63, 39, 39, 39, 39, 39, 39, 6, 7, 39, 39, 10, 11, 39, 39, 14, 15, 39, 39, 39, 39, 39, 39, 22, 23, 39, 39, 26, 27, 28, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 41, 41, 41, 41, 41, 41, 6, 7, 41, 41, 10, 11, 41, 41, 14, 15, 41, 41, 41, 41, 41, 41, 22, 23, 41, 41, 26, 27, 28, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 60, 61, 62, 63, 42, 42, 42, 42, 42, 42, 6, 7, 42, 42, 10, 11, 42, 42, 14, 15, 42, 42, 42, 42, 42, 42, 22, 23, 42, 42, 26, 27, 28, 29, 30, 31, 42, 42, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 60, 61, 62, 63, 43, 43, 43, 43, 43, 43, 6, 7, 43, 43, 10, 11, 43, 43, 14, 15, 43, 43, 43, 43, 43, 43, 22, 23, 43, 43, 26, 27, 28, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 45, 45, 45, 45, 45, 45, 6, 7, 45, 45, 10, 11, 45, 45, 14, 15, 45, 45, 45, 45, 45, 45, 22, 23, 45, 45, 26, 27, 28, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 60, 61, 62, 63, 46, 46, 46, 46, 46, 46, 6, 7, 46, 46, 10, 11, 46, 46, 14, 15, 46, 46, 46, 46, 46, 46, 22, 23, 46, 46, 26, 27, 28, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 60, 61, 62, 63, 47, 47, 47, 47, 47, 47, 6, 7, 47, 47, 10, 11, 47, 47, 14, 15, 47, 47, 47, 47, 47, 47, 22, 23, 47, 47, 26, 27, 28, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 49, 49, 49, 49, 49, 49, 6, 7, 49, 49, 10, 11, 49, 49, 14, 15, 49, 49, 49, 49, 49, 49, 22, 23, 49, 49, 26, 27, 28, 29, 30, 31, 49, 49, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 51, 51, 51, 51, 51, 51, 6, 7, 51, 51, 10, 11, 51, 51, 14, 15, 51, 51, 51, 51, 51, 51, 22, 23, 51, 51, 26, 27, 28, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 53, 53, 53, 53, 53, 53, 6, 7, 53, 53, 10, 11, 53, 53, 14, 15, 53, 53, 53, 53, 53, 53, 22, 23, 53, 53, 26, 27, 28, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 60, 61, 62, 63, 54, 54, 54, 54, 54, 54, 6, 7, 54, 54, 10, 11, 54, 54, 14, 15, 54, 54, 54, 54, 54, 54, 22, 23, 54, 54, 26, 27, 28, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 60, 61, 62, 63, 55, 55, 55, 55, 55, 55, 6, 7, 55, 55, 10, 11, 55, 55, 14, 15, 55, 55, 55, 55, 55, 55, 22, 23, 55, 55, 26, 27, 28, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 57, 57, 57, 57, 57, 57, 6, 7, 57, 57, 10, 11, 57, 57, 14, 15, 57, 57, 57, 57, 57, 57, 22, 23, 57, 57, 26, 27, 28, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 60, 61, 62, 63, 58, 58, 58, 58, 58, 58, 6, 7, 58, 58, 10, 11, 58, 58, 14, 15, 58, 58, 58, 58, 58, 58, 22, 23, 58, 58, 26, 27, 28, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 60, 61, 62, 63, 59, 59, 59, 59, 59, 59, 6, 7, 59, 59, 10, 11, 59, 59, 14, 15, 59, 59, 59, 59, 59, 59, 22, 23, 59, 59, 26, 27, 28, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 60, 61, 62, 63, 60, 60, 60, 60, 60, 60, 6, 7, 60, 60, 10, 11, 60, 60, 14, 15, 60, 60, 60, 60, 60, 60, 22, 23, 60, 60, 26, 27, 28, 29, 30, 31, 60, 60, 60, 35, 60, 37, 38, 39, 60, 41, 42, 43, 60, 45, 46, 47, 60, 49, 60, 51, 60, 53, 54, 55, 60, 57, 58, 59, 60, 61, 62, 63, 61, 61, 61, 61, 61, 61, 6, 7, 61, 61, 10, 11, 61, 61, 14, 15, 61, 61, 61, 61, 61, 61, 22, 23, 61, 61, 26, 27, 28, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 60, 61, 62, 63, 62, 62, 62, 62, 62, 62, 6, 7, 62, 62, 10, 11, 62, 62, 14, 15, 62, 62, 62, 62, 62, 62, 22, 23, 62, 62, 26, 27, 28, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f000000000000000001151117033f333f01151117033f333f01151117033f333f000000000000000001151117033f333f000000000000000001151117033f333f000000000000000001151117033f333f01151117033f333f01151117033f333f000000000000000001151117033f333f01151117033f333f01151117033f333f000000000000000001151117033f333f01151117033f333f01151117033f333f000000000000000001151117033f333f00000000000000000000000000000000000000000000000001151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xfeeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc00000000000000000feeaeee8fcc0ccc0000000000000000000000000000000000000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc000000000000000000000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc000000000000000000000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc000000000000000000000000000000000feeaeee8fcc0ccc0feeaeee8fcc0ccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xfeeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0feeaeee8fcc0ccc0

def cMZZ : Nat := 0x1151117033f333f00000000000000000000000000000000000000000000000001151117033f333f000000000000000001151117033f333f000000000000000001151117033f333f00000000000000000000000000000000000000000000000001151117033f333f00000000000000000000000000000000000000000000000001151117033f333f00000000000000000000000000000000000000000000000001151117033f333f000000000000000001151117033f333f01151117033f333f01151117033f333f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f0000000000000000000000000000000001151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f01151117033f333f

def expandAB (w A B : Nat) : Nat :=
  ((A &&& cMZx) ||| (B &&& cMOZ) ||| ((w &&& 1) * cMOO)) |||
    (((B &&& cMxO) ||| (A &&& cMOZ) ||| (((w >>> 63) &&& 1) * cMZZ)) <<< 4096)
def expand (w : Nat) : Nat :=
  expandAB w (((((w &&& 4294967295) * cMC) &&& cSM) ||| ((((w >>> 32) * cMC) &&& cSM) <<< 2048)) *
    18446744073709551615) (w * cRR)
def xsG : List ℕ := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00,
  0xffff0000ffff0000, 0xffffffff00000000].map expand
theorem rowsG_len : rowsG.length = 8192 := by decide +kernel
theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel
theorem enc_goalG : encL fG rowsG = goal 4096 := by decide +kernel
theorem maskG : mask 4096 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]
theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 4096 zs &&& lo 4096) ≠ lo 4096 := by decide +kernel
theorem no_subG (noRunFull : ∀ s ≤ 8, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 4096) (goal 4096) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)
theorem mainG (noRunFull : ∀ s ≤ 8, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ¬ HasCircuitSize 6 fG 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 8 h
  have hr : NatRun (mask 4096) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 6 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 2 => 1
  | 3 => 12
  | 4 => 154
  | 5 => 415
  | 6 => 289
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xa5f213d5
  | 3, 0 => 0xcd442ea09c1eda529514a36290df18008fa8e9db8f700bde7068a425484a0c0645f5882339d4185e157553fd07f229d8
  | 4, 0 => 0x3ec1c1983e2d76313d6ffe8c36d201de357a7225352990b134b7b33033ee2fd7334baf58327d37d631ab27bd31335c492fb4cfc72f51b8092e1f866f2d35c6e92a53b1fd2988713f2947df422874325b284bd8be2841c2b92718105926e8b00124c9439b2454f10c22dbc7922297a8c3223aaabc217e5bc620b3df45204653281ebbc6be1d75fa0a1b67d4df1ae1dd2f1a504ab619950ba018a3ece91864c61717d5a37b17a307b0160ede1214eaf19d10cf027c0fd895e20fc76ec00d6256500c8b08cf0c7f4bce0c0b33970b69d35e0b2d17390a2df9410988caea0914c42a078bc58e0600ee5005849c6a056b3d35052df16b030832ed0264f22e01c28d42
  | 4, 1 => 0x9289167b925ce80591ec2a5291d69d8e8fbad8f28ee910398e4dbae18defdfd18d3c19938cd271d58ccdd4628a74fdab8845dd6c87f294fe872615748359e06182ca910b8266b5437ece80f37e929b6b7bbb9fca7aed32cd7a5d10097a01d87778f1efa077835e51766a21b16cbc94456b1fdac368c04ee36840422166efed8266ca781a658e96ab644ac480611098d85dbd83f5582fb44a56696ad0558cf93d54c2cebf52724a1c50d1049f4f473fa14f0aea3b4b0b2e244ae21ce849c2e5ec49a9032a48233bd647b844e446da5edd45949229454b55dd44812dd4435e20b44300754e42d08a9e425289b6411375dc40c285084036eca13fd4d1853f394682
  | 4, 2 => 0xf44459ddf3f35b2bf17021dce0bf309dd3fa0e6cd3f956a9c9a13033c9110887c87094c4c756b441c69a7448c50c6a2fc0bc67debec4fc02b6c226a9aea69fd2abdabe8aab19aa69a53cc1dca30bcaeca2bb6110a2b1da709f381c229abdf454999970e1930ccbb3
  | 5, 0 => 0x11695ffd1156c84310e563c3102ccb2e0ebd89500eb8785a0eacff810e90cc230e656b090e0fc52e0d2c040f0d17ef4d0cab2d170c52a1970c44b9290c3889d10c3597750b5fe1a50b1a65ac0ac4798e0a9aa4a20a2d24200a0c114e09fdccf209ee26ba09e365ff09bf57e3099d7632096d39ac09457e25091771cd08d0f17a08b53bdf0869052008609609084459bf083439b8082ea20308203baa07ebb7d107eb7c1207ea4b2607b61ba207281b7606fe8d0b06baa9c105e7fd6e05c951ff05a42896059756d7050d939204dc9a840496f0ac046a7030045fd5380430280e03f5e8cd03e8c72103ce60750385e7cd01a7e36001724c7100dc4c4b004aa674
  | 5, 1 => 0x24927b16241b969c2363bd412345b1942323d42023211afa22e0dd1022cb5c0c227a93ba22599a8e2221b93c221d06a721f442cb219487dd2192ff252126452e210a834520380ed41fe409761fa3adbd1ea359421e71cf431e68b8741e10b49e1e1023391d75fa0a1d720d741d50d4491c6c108f1c06c2781bd7c3501bc44d6a1b6b22971b5440941b0b12511a37e1cc19fa9eea19d2fb9d18f0bac0184b5b161834149217f88eee17dbb6c017d5a37b17c4d6721765fafd17581b2b173edec217397ebf16d4a96a16b6baf21646318e15f20d33154c96e414c1c7aa1432a50e13f3c30a13dc44fe13b84b61136b4625132870a9130dad79129181dd12896570
  | 5, 2 => 0x3fdafcda3fbb22473f5d76e13e64c9ad3e2d76313d1c1a9c3d0177523ca1ddb63b90d5b13b8aa0093b27b2513b1fb46c3affcbef3ab42ad43a044cd339ca00fd39941dc73903fbe2372458fd36d6482f35b294fa340e1b0133d61cf4334baf5833429a4431d773b8319141e831869244316a79bb313ac3623136aa7c31335c493114b4c33010281b300a14312f83f17d2f4c490e2f1bc0cc2eda39692eac552c2e1f866f2da6edc72d95aa3b2d905ddc2d353d7b2cb94aac2cb588cb2c7e6d572b7f28682b66924b2ae66e422a7c88022a6f766c29d11684284bd8be281dd77527bce9b5276182a5272b232626f8918d26b0b39025097b4524a8da51249ec44c
  | 5, 3 => 0x5ec30ea05ec1cc155d7453b95d6d9a6b5cf146365cee881d5bd002f45b27b3695a1a85885a0d7155598911da5847cf20582fa0cc581f42be57e44f9b57a2899c5779547a5713c9c1570f5bb956b945cb55ef8aaf5412ea1552724a1c51efaea351e9fad051e87f93513e3bb351389dee50136ef14fdb81d44f7feb604ecf4baf4ec225d14d07d87a4b67ebce4b426c3f49afd84e4930f98a4856a6f347d756064785b582477aa3cf477503d54737bfda472344be46da5edd46875093461fe77f45c2d0c045949229453c282344803d6943f65b6f43b0e821433760704300754e422ed25f41fb0afe41f193bc41a9de9b416d266040de2f674067fdab4008445d
  | 5, 4 => 0x8197ddb88084b4997fb6e1f47f27929e7e3411db7e0e22ce7de0ea707d7e66027c8ac3bc7bbe5a8f7bb547257a0775d779d7d4b27936247f774a346076ba119c7607218b7595028773d44e3b735e1fd972c7234471fdc76471c579417176c69970580cc16f3c93f36e7013e36de168df6c65c44a6c5d806c6a4d6a7e6a19a31d6963aaf8688695ca677cdc566765d45b673a134666df110b66ce746366bd29dd66914d8a658e96ab656e2cdb65200f71651d5076650594d864cf56286496dc31644ac480634cef15633e4c8b629ce9906278088461f5929661f1a18961eb983e612893f861112fa6611098d860a7c6135fe819ba5f42f11c5ef4e04e5ee3fb33
  | 5, 5 => 0xc4cd9657c44c9321c40d7c01c2bfab0dc1593ee9bf01bbd7bd780675bd196971bbc7174fbb21fd95b9911d75b94656d2b8147922b320f809b31f283cae7eaadaae08723da9919ccda7e0ae2ca776abfca67d0948a614d9f8a4f49dc1a1ca9dd9a1a62b919fc63a209f68cc7f9d85a2339d483a0c9b25a776971af5e796e967de968eac0295e690a0959c09549550e56694d134539497a27293724ff792a4281e9217c63191e88ca59020a38c9014851d8f69cd468f15423d8eed0c828ee6180e8eb9e9988eafe5a98e4dbae18d60079f8c17da858aeb747e8aaabc7489392f6d892ad5f588809a4c887ac4498845dd6c8790fa3d84a2deff8379f1428238517b
  | 5, 6 => 0xff9d84d1febbdb18fa804810f7851599f6eb5a4af15cf8b7ee7a03d7eade432ce4e182aee3994678e14ea188ded7a068de633c86dbe62fa4d953b44dd8c143b1d69d42f9d45a1d90d3f956a9d261aff1d0fcec6ad056583cccf92b58ca3d28a6c93e6098c916aa62c9110887c87094c4c7e4d23fc6d25e0ac56e0a1a
  | 6, 0 => 0x190c847e1863c40b18214efd17bd99fb17b14227176813e4170e8e6b16cc58a616849482166605ae147955ad141dd90e13c2fc901396805212a3332111a998771050c49d102ccb2e10154cf40f85723c0f6aaf0c0eee83700ebd89500e0fc52e0dc661900d4265560cac67210c89ccc10c3889d10b5fe1a50b1a8ae30b1579ed0aedcdb60a6cc6c109c0a1d5096d39ac09457e2509082eaa08afa32a083439b807bce3380777673f07217b2106fe8d0b066912e105f6842305ca3b3f057473600560565105123d720508f2040493a55204913b4b0448b964035b8e9e0317ab540244ff010226539202012a29016a952501399c1700f3f23f00bcd6cb0052ea60
  | 6, 1 => 0x3784b3e437112c6735f11f5a35b843cc3560fd75333349c2320f968d304c7558300a14312f0113ae2dee437b2dc77b4e2d97c4f52d93ac0f2cba22942cb588cb2c7e6d572c6d29ae2c56108e2be0f3102b839dff2b0956bf2a03ef5a29f090ac29923f0e29128a5e28db6eea27436fd526cc77ff268a0a532584c96024a8da5124a8476d247ad9082419eb4823be8438238824b921f442cb2078982f205edb301f80d5b31f7e1c8d1ee6ccb21eb69c211e7a083a1e51445e1df189701df000b81d8327ce1d75fa0a1d50d4491c57f5a71c00af501bfabc471bc44d6a1b5440941af30cbc1aced0d61ac5ba071a6d24cc19ed0dee19d2fb9d19cf0f0719add5dc
  | 6, 2 => 0x5e5294295e4ea31c5da50fb25d85958b5d6e31395cf74b905c451b4d5b51e1e15b2010335a47680759d1554c598911da5854c00e582d048757a2899c566a72e855e6136d548ca25f547c445153ff8b2f53d6560d5370cb5451efaea3506feba85019e08b4ecf4baf4d9b3d464d959f814c7070844c3883674bdcecf34b426c3f4b1f27644967ce774856a6f3479f6dd24594922944b3a8864434579943f65b6f43d7a56243d205684380465142e4522641f193bc40535d0240447f1e400de9b43f781db03f5d76e13e8bd3f23e64c9ad3e06e02e3dca27f33c6545f03ac1cb403a2437b0399c01f239791c2f395e78e53903fbe2384ab8d237edd74437e7a19c
  | 6, 3 => 0x9e279f6c9e032d249c233bb399e2a3c693ef469c9346697192ebad9591ade6f9912e35e690f4a4058eed0c828eafe5a98e74c7c48e458e388c7186b08b0ce73c8aaabc7489bd093287eb824487487611860d68aa84d7c5dc84a2deff7e0e22ce7ce1b62c7b9d0f2d7b65f3b97b317d5b7a91136e7a6b246178e7c54f781b5c22781248b87264231e71f2041a6fbb216c6e5ac8f76e227ad46dd3c82c6c5d806c6c385aab6b9995866acd15766a4d6a7e6a19a31d68c2c5dd6899f478688695ca673f8d5066aa6c1165200f7164e3975d63c2d5ee639714d9633e4c8b62ee4f1d61cb2e6e617d1104612c57bb60a7c6135f9b4e1e5ef9eb235ef4e04e5ed50a17
  | 6, 4 => 0xfbfa8664fb18dcabfa804810f6dd49a3f3e2172cf15cf8b7edb9fa4ae13e8441ddaba31bdb34a1fbdac03e19d8433137d69d42f9d5b0b5e0d51e4544d2fa448ccebeb184c9562cebc86887e8c7e4d23fc5c84452c441d3d2bdb6407cbb5ebd6ab5a35865b533b6c8aadbac6da5ee9e60a52cb160a43dafbfa2a7b756a271db8ba1519f54
  | 7, 0 => 0xf6dd49a3d2fa448cc441d3d28b0ce73c66aa6c11617d11045b51e1e155e6136d53ff8b2f479f6dd24594922941f193bc3ac1cb403560fd7529128a5e28db6eea1e51445e1c57f5a719d2fb9d19add5dc18214efd0c89ccc10b1a8ae30a6cc6c107bce33806fe8d0b05ca3b3f04913b4b
  | 8, 0 => 0x41f193bc
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ffff0000ffff000000000000ff000000ff000000cccc0000cccc0000aaaa00000000000055550000ffff0000555500005555000033330000333300000f0f00000f0f00000000ffffffff00000000ff00ff0000000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f0000000000000000
  | 0, 1 => 0x22aa22aa00000000222222220000000011111111333333330fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0a0a0a0a0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc0055005500ff00ff0033003300330033000f000f000f000f
  | 0, 2 => 0x50505050f0f0f0f04c4c4c4ccccccccc4444cccccccccccc44444444cccccccc44444444444444443f3f3f3f3f3f3f3f3f003f003f003f0033ff000033ff00003333ffff3333ffff33333333ffffffff3333333333333333333333330000000033330000ffff00003333000033330000303030303030303022aa22aa22aa22aa
  | 0, 3 => 0x88888888000000008888000000000000880088000000000077777777ffffffff77770000ffff000070707070f0f0f0f05f5f5f5fffffffff5f005f00ff00ff0055ff0000ffff00005555ffffffffffff5555ffff5555ffff55555555ffffffff555555555555555555550000ffff000055550000555500005500ff00ff00ff00
  | 0, 4 => 0xaaaaaaaa00000000aaaaaa0000000000aaaa8888aaaa8888aaaa888800000000aaaa0000aaaa0000aaaa000000000000aaa0aaa000000000aa00aa00aa00aa00aa00aa0000000000a8a8a8a800000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0000000000000a000a000a000a000a000a000000000008888888888888888
  | 0, 5 => 0xaaaaffff0000ffffaaaaaaaaffffffffaaaaaaaaffffaaaaaaaaaaaaeeeeeeeeaaaaaaaabbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa00aa00aaaaaaaa88888888aaaaaaaa88880000aaaaaaaa80808080aaaaaaaa80008000aaaaaaaa22222222aaaaaaaa0a0a0a0aaaaaaaaa0000aaaa
  | 0, 6 => 0xcccc000000000000ccc8ccc8ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc0000000000cc000000cc000000c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c000c000c000c000bbbbbbbbbbbbbbbbbbbbbbbb33333333bbbb000033330000afafafaf0f0f0f0faaaaffffaaaaffff
  | 0, 7 => 0xeaeaeaeac0c0c0c0eaeaeaea00000000eaeaaaaaeaeaaaaaeaaaeaaaeaaaeaaaeaaaeaaac000c000ddddddddffffffffccffccffccffccffccccffffccccffffccccccccffffffffcccccccccccccccccccccccc88888888cccccccc00000000cccccc00cccccc00cccc8888cccc8888cccc8888cccc0000cccc0000cccc0000
  | 0, 8 => 0xeeeaeeeaccc0ccc0eeeaeeea00000000eecceecceecceecceecceecccccccccceecccccccccccccceeaaeeaaeeaaeeaaeeaaeeaacc00cc00eeaaeeaaaaaaaaaaeeaaeeaa00000000eeaaaaaacc000000eeaaaaaa00000000ee00ee00ee00ee00ee00ee00cc00cc00ececececcccccccceccceccccccccccceaeaeaeaeaeaeaea
  | 0, 9 => 0xf0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeeececcccccccceeeecccccccccccceeeeaaaacccc0000eeee0000cccc0000eeeceeeccccccccceeeaeeeaeeeaeeea
  | 0, 10 => 0xfaaafaaa00000000faaaaaaaf0000000faaaaaaa00000000faaa0000f0000000f8f8f8f8f0f0f0f0f8f8f0f0f0f0f0f0f8f0f8f0f8f0f8f0f8f0f8f0f0f0f0f0f3f3f3f3f3f3f3f3f0fff0fff0fff0fff0f0fffff0f0fffff0f0fff0f0f0fff0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0f0f0c0c0f0f0c0c0
  | 0, 11 => 0xfafafafaf0f0f0f0fafafafa00000000fafafaf0f0f0f0f0fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafac8c8fafac8c8fafac8c8f0f0c0c0fafaaaaafafaaaaafafaaaaaf0f00000fafaaaaa00000000fafa0000fafa0000fafa0000f0f00000faf0faf0f0f0f0f0faf0f0f0f0f0f0f0faaafaaafaaafaaafaaafaaaf000f000
  | 0, 12 => 0xfefefefefcfcfcfcfefeccccfefeccccfefeccccfcfcccccfefe0000fcfc0000feeeccccfcccccccfe00fe00fc00fc00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf8fcf8fcf0fcf0fcf0fcf0fcf0fcf0fcccfcccfcccfcccfcccccccfcccccccfafafafafafafafa
  | 0, 13 => 0xff330000ff330000ff0fff0fff0fff0fff0f0000ff0f0000ff00fff0ff00fff0ff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff000000ff00ff00aa00aa00ff00ff0000000000ff00f000ff00f000ff00ee00ff00cc00ff00cc00ff00cc00ff00aa00ff000000ff000f00ff000f00ff000000ff000000ff00000000000000
  | 0, 14 => 0xffccffccffccffccffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff88ff00ff00ffaaff00ff00ff00ffaa0000ffaa0000ffaa0000ff000000ffa8ffa8ff00ff00ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff00ff00ff55ff55ffffffff
  | 0, 15 => 0xffff0000aaaa0000ffff000033330000ffff000000000000fffcfffcfffcfffcfffafffafffafffafffafffafff0fff0fffa0000fffa0000fffa0000fff00000fff0fff0fff0fff0fff0fff0f0f0f0f0fff0fff000000000fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffee00000000ffe0ffe0ffc0ffc0
  | 1, 0 => 0xffff4444ffffccccffff3333ffff3333ffff0c0cffff0c0cffff00ffffff00ffffff00f0ffff00f0ffff0055ffff00ffffff0055ffff0055ffff0000ffffffffffff0000ffffccccffff0000ffff0000ffff0000ffcc0000ffff0000ffaa0000ffff0000ff000000ffff0000f0f00000ffff0000f0000000ffff0000cccc0000
  | 1, 1 => 0xffffc0c0ffffc0c0ffffc0c0ffff0000ffffc000ffffc000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaa00000000ffffaaa0ffff0000ffffaa88ffff0000ffffaa00ffff0000ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa000ffff0000ffff8888ffff8888ffff8888ffff0000ffff8080ffff0000ffff5555ffffffff
  | 1, 2 => 0xfffff000fffff000ffffeeeeffffeeeeffffeeeeffffccccffffeeee00000000ffffeeccffffccccffffececffffccccffffe0e0ffffc0c0ffffccccffffccccffffccccffff8888ffffccccffff0000ffffccccccccccccffffcccc00000000ffffccc0ffffccc0ffffcc00ffffcc00ffffc8c8ffffc8c8ffffc8c8ffffc0c0
  | 1, 3 => 0xffffffffaaaa0000ffffffff88888888ffffffff55555555ffffffff55005500ffffffff0f0f0f0fffffffff05050505ffffffff00005555ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffff00ffffff00ffffff00fffffafafffffafafffffafa00000000fffff0f0fffff0f0fffff0f000000000
  | 1, 4 => 0xffffffffffffffffffffffffffffccccffffffffffffaaaaffffffffffff0000ffffffffffccffccffffffffff00ff00fffffffffafafafafffffffff0f0f0f0fffffffff0000000ffffffffeeeeeeeeffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffaaaaaaaa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x3dd964f3
  | 3, 0, 0 => 0x833dd824f48336d928f47bab0ec4f4943dd844f49436d448f46db2d444f4833a144974943a144974943bd864f46dae5449749436d927f4833dd5c764
  | 4, 0, 0 => 0x9536d447627aca1b6a2278b1624db5125c9eb136da892e4f59436d447f3b2b6d72a23b13d624db559d89eb2871a88ec4f56da88ec4f11aca1b6a24613d60cdb51214ecb1f6da88fc7658336d86893b2c19c8a23b13d60cdb4f1d89eb066e288ec4f5
  | 4, 0, 1 => 0x94385447627aca1b6a23b13d646db511d89eb287ba68ec4f58536d447627ac19daa23b13d650e8511d89eb066da88dc4f572b6d447627ac19b6c93f9d9650db5121cecb066daa0ec4f583288ec4f14ac11b6a23b13d640db511d89eb1e6da88ec4f5
  | 4, 0, 2 => 0x9436d867627ac45b6a23b13d5b6a23b13c6eb066da88ec5359136d447627aca1b6a23613d62edb599d89eb056da88ec4f56fb6d447627ac19b6a24593d650db5fa892eadb66288ec4f58cb6d447627ac55b6a24113d60cdb591d89eb066da889e2d5
  | 4, 0, 3 => 0x8336d449127ac19b6a2439d9650db5d9d89eadb5da7cec4f583349447627ac89b6c33b13d60cdb649b09eb066daa8ec4f58336d447f3b2bf9b6a23b13d656db512309eb0671a88ec4f58336d44760fac19b6c95fa5d60cdb512309eb0675a89184f5
  | 4, 0, 4 => 0x83329447627ac19dec33b13d63edb511fcecb0670a88ec4f58336d447627ac19b6bd3b13d602db511d89eadb67288ec4f5833dd347627abddcaa23b13d6712877b0cb4b296da88ec4f5833a1447627ab9dcaa23b13d5b6a23b1889eae75127cec4f5
  | 4, 0, 5 => 0x9436d4497262c19b6bb3b13d604db511d89eb286da892e4f59b351447627ac6db6bb3b13d60cdb512549eadb511d89e2858336d887627ac19b6c33b13d61edb511d89eb066da88f67659436d926627ac19b6c3439d9630db511d89eb316da80ec4f5
  | 4, 0, 6 => 0x86b6d447627ac194476278c160cdb51218ecadb56288ec4f57c36d447627aca1b4a23b13d650db612889eb0678288ec4f58a36d447627ab6d9aa23b13d60cf74c9d89eb066da891c76590b6d447627ab75b6a23b13d60cdb56a88ecadb5d288ec4f5
  | 4, 0, 7 => 0x7cb6d447627ac25b6a23b13d60cdb511b49eb066da891e7659436d447827ac19b6a24b93164cdb511d89eb0673aecec4f59c4a1eec22d2c55b6bf3b13d616db511d89eb0670a892e4f56da88ec4f112c19c2ab3b13d60ce3512089eb1d6da88ec4f5
  | 4, 0, 8 => 0x8db6d449427ac19b676278e964edb511d89eb076da88ec4f58336d82a227ac19b6a2278b9650db512509eb067ba74ec4f56da893e9427ac19b4a23b13d60ca23b13c70b0675accec4f594355447627ac19b6a93b13d60cdb512049eb067bb08ec4f5
  | 4, 0, 9 => 0x1b6a23b13c76b066daed284f58336d5ca23b2c19eeb03b13d60cf74d9d89eb066da89284f59c419eec12d2c5db6a23b13d624db511d89eb066aa88ec4f5
  | 5, 0, 0 => 0x8336d44763493da71066da88ec5168336d44762b93da0cdb511d89e166a04a1b6a23b13da71067ba68ec4f69436d449a3b13da0cdb69a88ec4f68336d78a23b13da70db511d8b42368336d44833b13da831f6da88ec5a68336d4476278f9a0cdb511d89e4d683379b6a23b13da95066da88ec4f6
  | 5, 0, 1 => 0x8336d4ea23b13da71066da88ec5469ac19b6a23b13da710670a88ec4f60041944762785d60cdb51230ec4f68336d66762791da0cdb511d89e4269436d7ca23b1699d2e66da88ec5a69436d44963b169a0cec6da892c7669c419b6a23b13da0cdb511d89e0c68336d62a23b13d801063b13c34175
  | 5, 0, 2 => 0x9c411b6a23b169a97066da88ec4f698419b6a23b13da0cdb63a88ec4f66dafd68a23b13da0cdb51200fc7668b419b6a23b13da71066da88ec5b66dad544762d13da0cdb511d89e1d69c479b6a23b169a0cdb5f9d89e4468336d447627901a71066da88ec5668336d44763013da0cef6da892e4f6
  | 5, 0, 3 => 0x8336d447627845a0cdb511d89e1969436d447627895a0cdb68a88ec4f60036d44762783d60cdb511d89e0d68336d4476278b1a0cdb511d89e1468dbf5b6a23b13da0cdb60288ec4f69c41944762d0a5a0cdb511d89e126a3c09b6a23b13d800db3b13c340f58336d44893b13da71066da8900766
  | 5, 0, 4 => 0x8336d449c3b13da89066da88ec57689b6d44762d13da50db64a88ec4f69c419daa23b169a0cf66da88ec4f69c419b6a237169a70e56da88ec5a697419b6a23b13da71066db0cec4f68336d447627809a06db511d8b44f68fc19b6a23b13da0cdb51234ec4f69f419b6a23b13da85286da88ec5a6
  | 5, 0, 5 => 0x9c47db6a23b13da0cdb5fa88ec4f6004a1b67627869651066da892e4f69d419b6a23b169a71286da88ec5a69c419b6a23b149a0cdb511f8ec6668336d9ea23b13da2edb511d8b44f68336d44893b1a9800e56da88ec4f59c48db6a23b169a0cdb5c288ec4f68936d44762d13da71287ba68ec5a6
  | 5, 0, 6 => 0x833adaea23b13da50db511d89e4468336d5ea23b169a0cdb511d8ec4f68336d44762782da0cdb511d89e0769436d447627821a79066da88ec5a6833edb6a23b13d801286da88ec4f583409b6a23b13da0cdb511d89e3368336d447627905a99066da88ec4f69436d4476278fda0cfd6da88ec4f6
  | 5, 0, 7 => 0x9c419b6a23b171a0cff6da88ec4f68336d4476278f1a71056da88ec5a69436d44983b13da0d006da88ec4f68336d44942d13da71066da90ec5a69c4a1b6a24b93da0cdb511e4ec4f68336d447627829a1d066da88ec4f68336daea23b13d801065113c4a175a4419b6a23b13da70df6da88ec5a6
  | 5, 0, 8 => 0x9c419b6a23e9d9a71066da88f876692c19b6a23b13da71066da89185a68336d44763613da71286da88ec5e600489b6a23b13d400db5113c4a0f59b4a1b6a23b13da0cdb511d89e1068336db2a23b13da71066daecec4f69c4a1b6c33b169a0cdb5fa892e7669c489b6a23b169a71286da88d85a6
  | 5, 0, 9 => 0x9c419b6c936169a0cdb51a88ec4f68336d7ca23b169a50db511d89e1a68336d447627939a21066da88ec4f69c3f9b6a23b169a0cdb511d89e18600419b6a24613d60cdb511d89e0468bb6d44762791da710671a88ec5a67eb6da2a23b13d80106511d868175a0419b6a23b13da0cdb51268ec4f6
  | 5, 0, 10 => 0x9dc19b6a23b13da0cdb511d89e2569436d447627931801286da889e25599c19b6a23b13da71066da88ec2068336d4476278d9801066da88fe7650036d44761a03d6710669288ec5a68336d4476278a9a71226db0cec5a69436d44762793da0cdb511d8e44f68336da0a23b13d8010671a88ec4f5
  | 5, 0, 11 => 0x8336d4476278e5a70db67288ec5a69c419ee9a3b169a0cdb64a88ec4f600419b6a2439d960cdb511d89e1569436d44763513da71066da88ec5d69a36d449f3b13da0cdb6c288ec4f6833dda2a23b13da50db5125cec4f68336d6ca23b169a0cdb511d89e2b69c419b6a13b1699b6a24f9d89e4a6
  | 5, 0, 12 => 0x964a1b6a23b169801066da88ec4f5833854476278fda710677b0cec5a68336d4476278fda50ec6da88ec4f69c419c2a23b169801067ba68ec4f59a4a1b6a23b13d801286da88ec3459c419b6a23b169a0cf46da88ec4f68336d447627889a71016da88ec5a69436d447627929a0cdb511d89e096
  | 5, 0, 13 => 0x9436d44762792da0cdb5125c9e4069c4a1b6c933169a0cdb51260ec4f69c36d447627889a0cdb511d8c64f68336d447627911a44db511d8d44f6a1419b6c33b169a0cdb511d89e00693419b6a23b13da0cdb51224ec5a6833cdb6a23b13d8010670a88ec4f58336d447627821a71316da80ec5a6
  | 5, 0, 14 => 0x833dd449a3b13da0cdb51210ec4f6833e9b6a23b13da71066da89107669436d4476278d1a35066da88ec4f600419b6c33b13d671066da88ec5e69c36d44762d0a1a0cdb511d89e4368336daca23b13da0cdb649d8cc4f69436d447627921a6d066da88ec4f6833a9b6a23b13da71066db0cec5a6
  | 5, 0, 15 => 0x8336d44803b13da0cdb511d8c24f68336d44763593da71286da892e5a69c419b6a24113da691b6da88ec4f68336d44762b13da36db511d89e4a69c4d9a8a23b169a0cdb51288ec4f68336d44762793da0cdb511d89e3d68336d8ca23b13da0cdb511d89e1b68336d447a3b13da0cdb511d89e1a6
  | 5, 1, 0 => 0x409b6a23b13d670db5d288ec5a68336d44973b13da19066da88ec4f6833b9b6a23b13da0cdb511d89e1c68336d90a23b13da71066daecec5a6a6ca1b6a23b13da4cdb511d8e84f6004a1b6a24b93d671026da88ec5a68336d44993b13da0cdb511d89e4c600419b6a22789560cf16da88ec5a6
  | 5, 1, 1 => 0x9a419d6a23b13da0cdb511d89e4a69c485b6a23b169a0cdb511d89e05683389b6a23b13da0cdb5ba88ec4f69c4a1b6a23b1659cadb511d8b44f69436d44763813d801066daecec4f58336d44763993da0cdb511d8d44f69c375b6a23b169a71066daccec4f68336d447627885a0cdb511d89e466
  | 5, 1, 2 => 0x8336d44763a93da0cdb511d89e136a1419b6a2451d9a7b066da88ec4f69c419ee993b169a0cdb619d8d44f68336d44763413da0cdb511d89e0168336d44763893da5f066da88ec4f69436da8a23b13da59066da88ec5a68336d4476278c5a50db511d8b44f69a419b6a23b13d801066da88ec345
  | 5, 1, 3 => 0x89419b6a23b13da0cdb511d89e0e69c475b6a23b169a710d6da88ec5a684419b6a23b13da0cdb511d89e3469c419b6a23b155a71066da89207668336d84a23b13da68db68a88ec4f66da88ec4f12889a0cdb5da88ec4f699419b6a23b169a71066da88ec5069c4a1b4a23b169a71286db09445a6
  | 5, 1, 4 => 0x9c425b6a23b169a0cdb511d8e04f600499b6a23b13d400db511d89e0859c4a1b6a23c169a0cdb511dcec4f69c499b6a23b169a71136da88ec4f69c42db6a23b169a0cdb5d9d89e4a68336d447627891800db511d89e2258336d4497278fda70db511d8b422600419b6a21a09562f066da88ec4f6
  | 5, 1, 5 => 0x8336da8a23b13da0cdb511d8b45468336d44933b13da87066da88ec4f68336d44763213da0cdb51274ec4f68336d4476278c9a0cdb512309e4768336d44763793da0cdb511e0ec4f68336d44763393da0cdb511d89e2669c419eec23b169a71066da88ec5869c419b6a23b165a70f96da88ec5a6
  | 5, 1, 6 => 0x8336d44943b13da8b066da88ec4f69436d449f3b13da71067ba74ec5a6943adb6a23b13da6f066da88ec4f694471b6a23b13da0cfc6da88ec4f60036d444f12889650db511d89e0f69c419b4a23b169a9d066da88ec4f69cc19b6a23b169a0cdb55a88ec4f69c419b6a93b169a0cf56da88ec4f6
  | 5, 1, 7 => 0x9c449b6a23b169a0cef75a88ec4f68336d4476278bda5b286da88ec4f68336d8aa23b13da0cdb511d89e0368336d449b3b13da71276da88ec5a6833ddb6bf3b13da71076da88ec5a68336d447627879a50db511d89e0668336d66a23b13da0cdb51248ec4f69c419b6c151169a51286da88ec4f6
  | 5, 1, 8 => 0x36d44783b13d651066da88ec4f6a3419b6a23b169801066da89284f5943ddb6a23b13da0ce56da88ec4f69c419b6a24a169a0cdb511d89e3568336d60a23b13da511b6da88ec4f68336d44762f93d801176da88ec4f500449b6a23b13d60cdb511d89e0f68936d4476278fda71176da88ec5a6
  | 5, 1, 9 => 0x20cdb511d8ca4f683419b6a23b13da0cf76da88ec4f69436d44763b13da0cdb512509e4a68dc19b6a23b13da0cdb511d89e49696c19b6a23b13da7f066da88ec4f683381b6a23b13da50db511d89e406833ddb6c93b13da0cdb52a88ec4f68336d44762789da50db511d89e4d6
  | 6, 0, 0 => 0x9c419b6a23b13c7ef388336d4ea23b169e0cec74b6d44762d380271066d9d89e1a6004e20ca23b1682ed388336d44762d109e71388336d44762d3ce20cdb511d8b40c79c419b6b1511d8b4e009c418ec5a0d05da71066da88ec692d3ce20cdb511d8b45779c419b6a23b1682cf409c4a1b6a23b169e71286da8934762d3ce20cdb5e288ec5a7
  | 6, 0, 1 => 0x9c419b6a23b16828f388336d80a23b169e71066da88ec4f2238020cdb511d89e406004e20cdb511d8acd479c409b6a23b169c01386d9d8b41a07b0000106511d89e175a5ce20cdb511d8b4f3898419b6a23b169e71066db1d44762d380271066da88ec4f69c45a0cdb511d8b4f498336d44762d13de71066da88ec5a203ce20cdb511d8c05a7
  | 6, 0, 2 => 0x9c4ba0cdb511d8b4e008336da2a23b13da71066da88ec5a013ce23f066da88ec5a79c419b6a2469d8b4f3e9c419b6a23b169c00006da88ec4f07a8020cdb60288ec4f69c419b6a23b16822f389436d44762d095e71066da89307627bce20cdb68a88ec5a7004e20cdb51200ecc00a5c19b6a23b13d801386da88ec5a07b4e20cdb511d8b40d7
  | 6, 0, 3 => 0x9c419b6a23b13c34f4c9c419b6a23b169e71067eb6d44762d3d2689066da88ec5a79c419b6bf511d8b4e009c4a1b6762d069a71248336d44762d3c19b6a23b1689e0f78e46a0cdb511d8b4f418336d447633169e63066da88ec5a27bc19dedb511d8b44f79c419b6b8511d8b4f388336d449c3b169e71286db2544762d3ce20cf66da88ec5a7
  | 6, 0, 4 => 0x833adb6a23b1689ee00004a1b6a23b13d401066da88ec4f19b0020cdb511d8b40669c419b6a23b1d8b4f1c8336d44762d13dc01067eb6d447627b0020cdb5fa88ec4f69c419b6a23b13c9ef388336d44762d01de71286da88ec5a043ce20cfb6da88ec5a700419b6762d0680cc009c4a1b6a23b169a71068136d44762d3ce20cdb511d8b4337
  | 6, 0, 5 => 0x9c419b6a24b9d89ee009c36d445a1283da71369436d44762d3ce20cdb511d8b41079c419b6d9511d8b4e008336daea23b13da71067fb6d44762d380271066da889e2569c4a1b6a24c1d8b4f3883401b6a23b169e0cdb5127cec5a27bce20cdb511e4ec5a79c43a0cdb511d8b4f388336daea23b169c013883288b4250bb52271066da88ec5a7
  | 6, 0, 6 => 0x419b6a24d1d89ed388336d46a23b169c01066da88ec5e0334e250db511d8b41a7004e20cdb511d868d388336d44762d061e71066da88ec5a023ce20cdb511d89e4a79c3f5b6d1511d8b4f409c419b6a23b169e71066da8934762d3ce24b066da88ec5a79c419b6a23b1b0b4f388336d44763513de51066da88ec5a27b80271226da88ec5a6
  | 6, 0, 7 => 0x9c419eed1511d8b4f388336d44762d0ade77388336d44762d38020cdb511684a0669c419b6a23b1684ae009c4a1b6a22d095a71338336d44762d3c19b6a23b1689e06700419b6be511d8b4d449c419b6a23b159e71066da88ec5a153ce250db511d8b44f79c419b6a23b1c8b4f388336da0a23b169e89388336d447627b80281066da88ec4f6
  | 6, 0, 8 => 0x9c419b6a23b13c68e009c419ee9a3b169a71349436d44762d38020cdb64a88ec4f69c419e8db511d8b4f388336d44762d089e71066da88ec5a04bce20cdb64a88ec5a78336d44762d13c8af388336d447627921e71066da88ec5a0abce250db511d8d45a700419b6a23b13c4ad388336d44762792de71346da893e762d3ce20cdb6c288ec5a7
  | 6, 0, 9 => 0x9c4a1b6a23b16896f067bb6d44762d13dc01066da88ec4f2234e20cdb51260ec5a7000020cdb511d89eb388336d44762d111e71226da88ec6a2d38020cdb511d89e3f69c419b6a23b16800f3893419b6a23b169e710679b6d44762d3ce20cdb511d8b4087004e20cdb511d8b4d388336d44762d0fde37066da88ec5a27bce250ec6da88ec5a7
  | 6, 0, 10 => 0x9c419b6a23b1689ef388336d8ca23b169e71066da88ec5a0dbce20cdb511d8b41a79c419eea24d1d8b4f388336d44843b169c01388336d44762f34e235066da88ec5a79c419b6a23b1c09ee009c419b6c33b169a71066db5944762d3ce20cdb649d8cc5a79c4a1b6a23b16890f389b419b6a23b169e71067536d44762d38020cdb51260ec4f6
  | 6, 0, 11 => 0x9c419b6a23b16838f388336d90a23b169c00db511d8b44f07b53671286da88ec5a79c499b6a23b1d0b4f066db0144762d13de71066da8932762d380271066da88b42569c419b6a2401d8b4f4b8336d44762d13de71066da88ec6b2d38020cdb511d89e4f68336d44762d13c80f388336d44762d159c01066da88ec4f0d34e20cdb51288ec5a7
  | 6, 0, 12 => 0x8336d44763a1689ef389a419b6a23b169c01066da88ec6a27b4e20cdb511d8b44a79c419b6a23b1680af3883389b6a23b169c01066da892e7627b4e250db511d8e05a79c419b6a23b1ccb4f388336d447635169e71066da88ec5a10b80271026da88ec5a69c419b6a24b9d8b4f3886419b6a23b169c00008336d444f12ace20cee6da88ec5a7
  | 6, 0, 13 => 0x9c36d44762d09444f388336d44763a969e71066da88ec5a09bcf671066da88ec5a79c419b6c33b1a8b4f388336d447634169e71066da88ec5a00b80250db511d8b44f68336d44762d13c66f3897c19b6a23b169e71286db5144762d380269066da88ec4f6000020cdb511d868b388336d44762d0c5c01066da88ec5a0230020cdb511d89e4a6
  | 6, 0, 14 => 0x4e24cdb511d8b4c009c36d44762d021a0cdb511d8b44f12bce20cdb511dcec5a79ec19b6a23b16866f388336d44762d091c01386da88ec5a1130020cdb511d89e3469c419b6a23b1681cf408336d44762d13de0cdb51268ec5a27bce20cf26da88ec5a79c4220cdb511d8b4f388336d44762d0d1e71066db0944762d3ce268db68a88ec5a7
  | 6, 0, 15 => 0x9c419f8db511d8b4e009c36d445a12889a71286da88ec5a07bd3a71066da88ec5a7004e1b6a23b0cc1ed38833d5b6a23b169e71066db5144762d3d0e71066da88ec5a79c419b6a23b190b4f388336d449d3b169c01388336d44762cb0020cdb511d8e04f69c419b6a23b1bcb4f388336d44783b169e71066da88ec5a133ce20cdb511d8e05a7
  | 6, 1, 0 => 0x9c419b6a23b1686af389c419b6a23b13dc01066da88ec4f07b419b6a23b1689e4b79c419b6a23b1681ef388336d8aa23b169e71066da88ec5a01bce250db511d8b40679c419b6a6511d8b4f38944a1b6a23b169e8b388336d44762d38020cdb511d8660669c4a1b6a24f9d8b4e009c4a1b6a23b0cda71378336d44762d3ce2511c6da88ec5a7
  | 6, 1, 1 => 0x9c41a0cdb511d8b4e00833ddb6a23b13da71067bb6d44762d3ce250db511d8ec5a70046e0cdb511d89ed388dc19b6a23b169e7f388336d44762d3ce250db511d8b44079c419eedb649d8b4f388336d4aa23b169e71066da88ec5a13b80251066da88ec4f69c4a1b6a23b1689ae009c36d44783b169a71288336d44762d3ce250f76da88ec5a7
  | 6, 1, 2 => 0x4e20cdb511d8ca5a7
  | 7, 0, 0 => 0x4e20cdb64a88ec5a7004e20cdb511d8b42570050271066da88ec5a7004e20cdb51268ec5a7004e20cdb6ba88ec5a7000020cdb511d8b40660000271286da88ec5a6004e20cdb511d8b4337004e20cfd6da88ec5a7004e20cdb68a88ec5a70000270db511d8b40f6004e20cdb60288ec5a70052e71066da88ec5a70000271066da88ec4f6004e20cdb511d8b4407000027106511d8b4176
  | 7, 0, 1 => 0x4e20cf76da88ec5a7004e251066da88ec5a7004e20cdb511d8b40f7004e20cdb511d8e05a7004e269066da88ec5a7004e20cdb511d8d45a70000271066da88b4256004e20cdb511d8b44f7004e20cdb511d8b41a7004e20cdb51260ec5a70000001066da88ec4f50000271066da88ec5a6
  | 8, 0, 0 => 0x271066da88ec5a6
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 2 => 31
  | 3 => 40
  | 4 => 49
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 85
  | _ => 0

def idWidth : Nat := 9
def wireAt (i : Nat) : Nat := expand (fld (dictB (i / 256) (i / 16 % 16)) 64 (i % 16))
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 1984), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 1984), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 4096)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat :=
  pickMin zs symsG zs (hk zs)
theorem ori_ok {u ys} (h : NatRun (mask 4096) (goal 4096) u ys) :
    NatRun (mask 4096) (goal 4096) u (ori ys) :=
  pickMin_run ys h symsG ys (hk ys) symsG_ok h
def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 20 0 (NN s)
def poolG : List Nat := []
def Z (s : Nat) := bar 4096 S NN idx ori poolG s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z0_0 : span (Z 0) 0 0 = true := by decide +kernel

private theorem z0 : span (Z 0) 0 0 = true := z0_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z1_0 : span (Z 1) 0 0 = true := by decide +kernel

private theorem z1 : span (Z 1) 0 0 = true := z1_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : span (Z 2) 1 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 1 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 12 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 12 0 = true := z3_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : span (Z 4) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_24 : span (Z 4) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_48 : span (Z 4) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_72 : span (Z 4) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_96 : span (Z 4) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_120 : span (Z 4) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_144 : span (Z 4) 10 144 = true := by decide +kernel

private theorem z4_a1 : span (Z 4) 48 0 = true :=
  span_join (f := Z 4) (a := 24) (o := 0) (b := 24) z4_0 z4_24

private theorem z4_a2 : span (Z 4) 72 0 = true :=
  span_join (f := Z 4) (a := 48) (o := 0) (b := 24) z4_a1 z4_48

private theorem z4_a3 : span (Z 4) 96 0 = true :=
  span_join (f := Z 4) (a := 72) (o := 0) (b := 24) z4_a2 z4_72

private theorem z4_a4 : span (Z 4) 120 0 = true :=
  span_join (f := Z 4) (a := 96) (o := 0) (b := 24) z4_a3 z4_96

private theorem z4_a5 : span (Z 4) 144 0 = true :=
  span_join (f := Z 4) (a := 120) (o := 0) (b := 24) z4_a4 z4_120

private theorem z4_a6 : span (Z 4) 154 0 = true :=
  span_join (f := Z 4) (a := 144) (o := 0) (b := 10) z4_a5 z4_144

private theorem z4 : span (Z 4) 154 0 = true := z4_a6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : span (Z 5) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_24 : span (Z 5) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : span (Z 5) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_72 : span (Z 5) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : span (Z 5) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_120 : span (Z 5) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_144 : span (Z 5) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_168 : span (Z 5) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_192 : span (Z 5) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_216 : span (Z 5) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_240 : span (Z 5) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_264 : span (Z 5) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_288 : span (Z 5) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_312 : span (Z 5) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_336 : span (Z 5) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_360 : span (Z 5) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_384 : span (Z 5) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_408 : span (Z 5) 7 408 = true := by decide +kernel

private theorem z5_a1 : span (Z 5) 48 0 = true :=
  span_join (f := Z 5) (a := 24) (o := 0) (b := 24) z5_0 z5_24

private theorem z5_a2 : span (Z 5) 72 0 = true :=
  span_join (f := Z 5) (a := 48) (o := 0) (b := 24) z5_a1 z5_48

private theorem z5_a3 : span (Z 5) 96 0 = true :=
  span_join (f := Z 5) (a := 72) (o := 0) (b := 24) z5_a2 z5_72

private theorem z5_a4 : span (Z 5) 120 0 = true :=
  span_join (f := Z 5) (a := 96) (o := 0) (b := 24) z5_a3 z5_96

private theorem z5_a5 : span (Z 5) 144 0 = true :=
  span_join (f := Z 5) (a := 120) (o := 0) (b := 24) z5_a4 z5_120

private theorem z5_a6 : span (Z 5) 168 0 = true :=
  span_join (f := Z 5) (a := 144) (o := 0) (b := 24) z5_a5 z5_144

private theorem z5_a7 : span (Z 5) 192 0 = true :=
  span_join (f := Z 5) (a := 168) (o := 0) (b := 24) z5_a6 z5_168

private theorem z5_a8 : span (Z 5) 216 0 = true :=
  span_join (f := Z 5) (a := 192) (o := 0) (b := 24) z5_a7 z5_192

private theorem z5_a9 : span (Z 5) 240 0 = true :=
  span_join (f := Z 5) (a := 216) (o := 0) (b := 24) z5_a8 z5_216

private theorem z5_a10 : span (Z 5) 264 0 = true :=
  span_join (f := Z 5) (a := 240) (o := 0) (b := 24) z5_a9 z5_240

private theorem z5_a11 : span (Z 5) 288 0 = true :=
  span_join (f := Z 5) (a := 264) (o := 0) (b := 24) z5_a10 z5_264

private theorem z5_a12 : span (Z 5) 312 0 = true :=
  span_join (f := Z 5) (a := 288) (o := 0) (b := 24) z5_a11 z5_288

private theorem z5_a13 : span (Z 5) 336 0 = true :=
  span_join (f := Z 5) (a := 312) (o := 0) (b := 24) z5_a12 z5_312

private theorem z5_a14 : span (Z 5) 360 0 = true :=
  span_join (f := Z 5) (a := 336) (o := 0) (b := 24) z5_a13 z5_336

private theorem z5_a15 : span (Z 5) 384 0 = true :=
  span_join (f := Z 5) (a := 360) (o := 0) (b := 24) z5_a14 z5_360

private theorem z5_a16 : span (Z 5) 408 0 = true :=
  span_join (f := Z 5) (a := 384) (o := 0) (b := 24) z5_a15 z5_384

private theorem z5_a17 : span (Z 5) 415 0 = true :=
  span_join (f := Z 5) (a := 408) (o := 0) (b := 7) z5_a16 z5_408

private theorem z5 : span (Z 5) 415 0 = true := z5_a17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : span (Z 6) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_24 : span (Z 6) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : span (Z 6) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_72 : span (Z 6) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : span (Z 6) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_120 : span (Z 6) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : span (Z 6) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_168 : span (Z 6) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : span (Z 6) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_216 : span (Z 6) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : span (Z 6) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_264 : span (Z 6) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : span (Z 6) 1 288 = true := by decide +kernel

private theorem z6_a1 : span (Z 6) 48 0 = true :=
  span_join (f := Z 6) (a := 24) (o := 0) (b := 24) z6_0 z6_24

private theorem z6_a2 : span (Z 6) 72 0 = true :=
  span_join (f := Z 6) (a := 48) (o := 0) (b := 24) z6_a1 z6_48

private theorem z6_a3 : span (Z 6) 96 0 = true :=
  span_join (f := Z 6) (a := 72) (o := 0) (b := 24) z6_a2 z6_72

private theorem z6_a4 : span (Z 6) 120 0 = true :=
  span_join (f := Z 6) (a := 96) (o := 0) (b := 24) z6_a3 z6_96

private theorem z6_a5 : span (Z 6) 144 0 = true :=
  span_join (f := Z 6) (a := 120) (o := 0) (b := 24) z6_a4 z6_120

private theorem z6_a6 : span (Z 6) 168 0 = true :=
  span_join (f := Z 6) (a := 144) (o := 0) (b := 24) z6_a5 z6_144

private theorem z6_a7 : span (Z 6) 192 0 = true :=
  span_join (f := Z 6) (a := 168) (o := 0) (b := 24) z6_a6 z6_168

private theorem z6_a8 : span (Z 6) 216 0 = true :=
  span_join (f := Z 6) (a := 192) (o := 0) (b := 24) z6_a7 z6_192

private theorem z6_a9 : span (Z 6) 240 0 = true :=
  span_join (f := Z 6) (a := 216) (o := 0) (b := 24) z6_a8 z6_216

private theorem z6_a10 : span (Z 6) 264 0 = true :=
  span_join (f := Z 6) (a := 240) (o := 0) (b := 24) z6_a9 z6_240

private theorem z6_a11 : span (Z 6) 288 0 = true :=
  span_join (f := Z 6) (a := 264) (o := 0) (b := 24) z6_a10 z6_264

private theorem z6_a12 : span (Z 6) 289 0 = true :=
  span_join (f := Z 6) (a := 288) (o := 0) (b := 1) z6_a11 z6_288

private theorem z6 : span (Z 6) 289 0 = true := z6_a12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 4 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 28 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 4) z7_0 z7_24

private theorem z7 : span (Z 7) 28 0 = true := z7_a1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : span (Z 8) 1 0 = true := by decide +kernel

private theorem z8 : span (Z 8) 1 0 = true := z8_0

theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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

def RootG (s : Nat) : Bool :=
  scr 4096 s poolG xsG || found S NN idx s (ori xsG)
theorem rootChecked : span RootG 4 5 = true := by decide +kernel
theorem xsG_len : xsG.length = 6 := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : NatRun (mask 4096) (goal 4096) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h
    rw [xsG_len] at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

def CG : Circuit := ⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
def vec (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool := fun i => [b0, b1, b2, b3, b4, b5].getD i.val false
theorem CG_mono : Monotone2 CG := by
  intro g hg
  simp only [CG, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem CG_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    CG.eval (List.ofFn (vec b0 b1 b2 b3 b4 b5)) = fG (vec b0 b1 b2 b3 b4 b5) := by decide +kernel
theorem CG_eval (x : Fin 6 → Bool) : CG.eval (List.ofFn x) = fG x := by
  have hx : x = vec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext ⟨i, hi⟩
    interval_cases i <;> rfl
  rw [hx]
  exact CG_vec _ _ _ _ _ _

end PEqualNP.Outside.L_meta_12683

theorem PEqualNP.Outside.L_meta_12683 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4240493760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4240493760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12683.mainG PEqualNP.Outside.L_meta_12683.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12683.CG, PEqualNP.Outside.L_meta_12683.CG_mono, by
      have : PEqualNP.Outside.L_meta_12683.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12683.CG_eval⟩
