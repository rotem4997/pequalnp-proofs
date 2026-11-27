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
namespace PEqualNP.Outside.L_meta_12447

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 3, 7, 3, 3, 3, 11, 3, 3, 14, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 25, 3, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 3, 43, 3, 45, 46, 47, 3, 3, 3, 51, 3, 53, 54, 55, 3, 57, 3, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 7, 11, 7, 7, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 11, 7, 11, 11, 11, 11, 11, 11, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 14, 14, 14, 3, 14, 14, 14, 7, 14, 14, 14, 11, 14, 14, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 15, 15, 7, 15, 15, 15, 11, 15, 15, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 19, 7, 19, 19, 19, 11, 19, 19, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 21, 7, 21, 21, 21, 11, 21, 21, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 22, 22, 7, 22, 22, 22, 11, 22, 22, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 23, 23, 7, 23, 23, 23, 11, 23, 23, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 25, 7, 25, 25, 25, 11, 25, 25, 14, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 3, 27, 27, 27, 7, 27, 27, 27, 11, 27, 27, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 29, 7, 29, 29, 29, 11, 29, 29, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 30, 7, 30, 30, 30, 11, 30, 30, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 31, 7, 31, 31, 31, 11, 31, 31, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 35, 7, 35, 35, 35, 11, 35, 35, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 37, 7, 37, 37, 37, 11, 37, 37, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 38, 7, 38, 38, 38, 11, 38, 38, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 39, 7, 39, 39, 39, 11, 39, 39, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 41, 7, 41, 41, 41, 11, 41, 41, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 43, 43, 7, 43, 43, 43, 11, 43, 43, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 45, 7, 45, 45, 45, 11, 45, 45, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 46, 7, 46, 46, 46, 11, 46, 46, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 47, 7, 47, 47, 47, 11, 47, 47, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 51, 7, 51, 51, 51, 11, 51, 51, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 53, 7, 53, 53, 53, 11, 53, 53, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 54, 7, 54, 54, 54, 11, 54, 54, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 55, 7, 55, 55, 55, 11, 55, 55, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 57, 7, 57, 57, 57, 11, 57, 57, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 3, 59, 59, 59, 7, 59, 59, 59, 11, 59, 59, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 61, 7, 61, 61, 61, 11, 61, 61, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 62, 7, 62, 62, 62, 11, 62, 62, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1517151715173777151715171517377715171517151737770000000000000000151715171517377700000000000000001517151715173777000000000000000015171517151737771517151715173777151715171517377700000000000000001517151715173777000000000000000000000000000000000000000000000000151715171517377715171517151737771517151715173777000000000000000015171517151737770000000000000000151715171517377700000000000000001517151715173777151715171517377715171517151737770000000000000000151715171517377700000000000000000000000000000000000000000000000015171517151737771517151715173777151715171517377700000000000000001517151715173777000000000000000015171517151737770000000000000000151715171517377715171517151737771517151715173777000000000000000015171517151737770000000000000000000000000000000000000000000000001517151715173777151715171517377700000000000000000000000000000000151715171517377700000000000000000000000000000000000000000000000015171517151737770000000000000000000000000000000000000000000000001517151715173777000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c8880000000000000000eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c8880000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000eae8eae8eae8c888eae8eae8eae8c88800000000000000000000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000eae8eae8eae8c888000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888eae8eae8eae8c888

def cMZZ : Nat := 0x1517151715173777000000000000000015171517151737770000000000000000151715171517377700000000000000000000000000000000000000000000000015171517151737770000000000000000151715171517377715171517151737771517151715173777000000000000000000000000000000000000000000000000151715171517377700000000000000001517151715173777000000000000000015171517151737770000000000000000000000000000000000000000000000001517151715173777000000000000000015171517151737771517151715173777151715171517377700000000000000000000000000000000000000000000000015171517151737770000000000000000151715171517377700000000000000001517151715173777000000000000000000000000000000000000000000000000151715171517377700000000000000001517151715173777151715171517377715171517151737770000000000000000000000000000000015171517151737771517151715173777000000000000000015171517151737771517151715173777151715171517377700000000000000001517151715173777151715171517377715171517151737770000000000000000151715171517377715171517151737771517151715173777

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
  | 3 => 14
  | 4 => 212
  | 5 => 581
  | 6 => 383
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xe9e572b
  | 3, 0 => 0xf6b8e135f0460aacda029465d0e5b20ac252a93c89c3f5d185f6295984ec8f3a7e875b9a53da88e34890a19d18d614d31614a278049e9ea5
  | 4, 0 => 0x3bca19383b512c5d399b3f5638ac5e58384ebc2a3723a94836cdb1e83676b58b355e6423353613c233db957c32a5dbd8322766bc305873902fb9702b2f3e440a2de1d3b22da0c2f22aa21fd729c16dfd28b124e5284026ac261babd525c36f96258cfaf02500a1e024b451502408ccb523335220222ec9be217627e71c4f100a1bc8354f172d298616d3093d161e4d151525a84d140e10191380f6dc120fc582116110fc0fb6d01a0f6883330f2cbd4d0cdb03670b45788f0a637bed09af3c4408f14b0408b3c43707fbc493062bf1dd05e6778805d95a0a052396e904490ab50403fe7f038d38c202a407f80291aeaa024656c700b4996400a1dc0900226ea0
  | 4, 1 => 0x822f7c807f4d1c0e7ec6d0247e92418c7e5457ed7da41f847c8e13e679c90394790428cc74178e80728e8d8d71b79a0e712f367d70d6e4936f9d335b6e413ed26ca656ca6bfc8af16ba213a56ae6bc146a2332eb6976127f68b0b3566768c0b964d814e063a730496320ec4a60f4b7915f732d155f2f8b4f5d6ad46a5d66cc105d29745a5cc53ff25b4972e157a438a356f9e7d65636c60254f436e35377db2e52dbd95452b787fe518a26654f7d897d4ea765884cfb823f4acba2ac4a6aac8a4730536c4665d1904539d5de44eff30444da5e2744c073a64436716a4430a27d43ee6a683f3fde983f35c26c3e715f793dd8968b3d1c0bc13cd55ff33cac6c4e
  | 4, 2 => 0xde07e79dd9b61368d9579fd3d8c8da3ed6da8e14d21f50a2d0a04163cf74e960cf4fb5a9cf3de4bbcf1ad4cdc918c13ec39715e5c370bd9dc1e128e1c187b7dfbd75178abd1cf446bc6e9b92b9698105b8a0d168b89c24bfb7abae6eb20189d4b1863c6faeb45b39adc43808abb52076ab8c68dea9eb859fa96e413fa7056544a682d943a5d632c0a5956e76a3a47384a32442279f9dbabd9eda2c8d9e62e3099c184b869bae71d398d08c5397d0b965958effe994b936a094a97dc790c00f79905229eb8fcf0ab48f53ccf08f2ff9738e8f04c78d5eb489894b212588dab3e086cbb6108694b5c48512ed4385084db084966d6e845990b0832614bb82b99658
  | 4, 3 => 0xfefbe618fed0ef0cfdb11549f98754bdf980fe0af86e8a77f62b9aa4f5d5a51ff36a6300eeb3b0cbec66bc79eae68bf6e9566891e706607de5d17b4de51e534ce4f7eebae28c69cce1b78593e1491900
  | 5, 0 => 0x1a75f5c11a0e81d719e7a07519ceed9b17f63bc117451cba16f6a69e169ab2ff1635107f15e82d1e15655a771558d65c14cd152d13fb889913e679bd136556601339595113361901130392a4112c078b0fdc40f50fbabf8c0facec280f3ccda20e9b5bb20da28ad20d3e61da0ce4331c0cdb03670c4d4ff20c06019b0becdca50b3777b10b251ebd0a623c790a289e4d0993ccee093673e70935df9108e004ac08c46b29082cf3b80825180607ee8d8007970c6907099c1606ca07ed059dbeee054abfb204e79bf00429d53e03e4380703d3f69f03b49854039679790351626d03247eea02945c390214d22401eb132001423a7d0129bd11011e07aa0081ef4b
  | 5, 1 => 0x2e7bda7c2e698b112dca88aa2da0c2f22caccf852c397d172c26839b2ba3b28d2af477882ad1bfe92acc505b2ab1c3a32a2aca8629f3c65a2939a90a291062e028ded7e828c64ca928b16792288a16f62887286628867d2a281ad99627df1fa427c7f84f271dddb726ab3009265f5a0a264fc0ab26346e9e254aebcb249313382450fd1d243f9645240c8fc52408ccb5238e563c2385d91f2333522021bbf5de217627e721185aa720cdd5cb20ba19142092ebd120910927208deaa42016765f1fc71f461fc71c071f9b41a21f3d86371f3a2e631f39a6601ef121221ddad5521dae334f1d7463bd1d3d911a1c752cda1c02d3201ae4f9391acdf47d1a77f6b1
  | 5, 2 => 0x4571b8a544de80d744c073a64456f7e34436716a42fbf4b742b580d94293d32541940037413ba18341238822400740ae3fa32ee73ecf05683eab3ef03ea095953e6248d93e60ee363db3176e3d1c0bc13bd992d83b49bfb13b32a0a73b1cf96b3af1081b3aee436439df96b239bef88c39ac8d10398a7bc3391713c238f3404538524b99381c31b337984a143787a18a3767ad743723a948363111d435bb41bb34d54e8733db957c3372faaf3335af06331cfbcf33165e12331304bf330e67f73305b58832fff98632f1b623325d52e9322766bc320965ec31ea577c313c7ef230decb9630bdc51f30587390304007752f69c9752efb94662ef707402ed63415
  | 5, 3 => 0x59a7ff2958e6985858d4583f58b1c39958ab3c3e585f681456c79ee156c5045c569074e8567c5817558691c955786748554fafb0551893b8548556d553d8c44a53a5e7bd5331881152fb8bac52bfb5c452be50a151da3b5051d40ff150c8ac165050846250462015503abda84ff91feb4fdf9a7d4fd4df024fc9b9bf4f3d4c874ea765884e6cef6f4e66e84f4e0579584d5533564ca207594c1846294be0475d4bd236c04b77799f4b5e883f4b15f9124b0511bd4978bfb6496b53784961018f49514dc3493e917a4929aab1489e9060489daae1489d735f482629db47ae293f478094bb4760c51e4757185046a73311467722b44665ab1345db9258458f41ac
  | 5, 4 => 0x7027d8456ff4c0766f9712586e19be1a6dc1536a6dbbac466d719bd86d4621ef6ceca1e76c2d8b666ba46fb36ba213a56b4afeb16af874fe6ab887426aa4622f6a6e72c26a6460526a5f4bcd6a19bb0f6a185b986830142467ba0cca67878b6466be268666b11aec666de4cb6624f0486596467e64d8784164d814e064c76c566462eef16443b14663cfb24863ba7f2a636fad5363540d19631da46c630efabf62ef65c362a90244623db03461d8f7aa61bbc063616ef5406113937860c23c50600ce1215f59bdc05f1571945f097c9a5ef64b935e780fb65e473b445e2fb9b65e0f123d5d5baaa05c949d705c3949565be3c6405b93b58b5a6de7a85a1396d4
  | 5, 5 => 0x8c4fb09e8b7acc658b1016388a79a65f89f4e98289e7e7bb89b9e2a1886c1014885c129787e86b1887e6bb0787b5c008875dba1986ffa1b38694b5c486079197859db15384f2f12284a2c6e0839e75fe83795a3a8333ebfa82d53ea48238c86f81c7a77580fbdde380f717fe80a193067f53066a7efa060d7e0c26b57cda9c4c7c0e00627bbf86697b75d4047b337d5d7b1841887adfe8f17a6388357938303278e1de7978de1b9f78bc2948789d57f5787d5abc78300748776465fd77540b0a7753fb6f76aec8cc76721bf6760d4a3c7524c35774df66e074cd8c08741b67c973e1e2a67395e89c72d500947299cc207240fedd723612f77123183d70cd2d7a
  | 5, 6 => 0xaf581511aee98be4ada0b071ad935b8cad562ab8ac099d94ab7fc805a983b094a77f3ce9a682d943a670e7b8a66e16f6a602e429a5a9be3ca54ad3f9a4b23260a42664b8a3d2538da34444dca2c1376ea2a92924a261f306a22a2714a1780c56a1081587a01d39109e62e3099e55fbf89df6f0779d8d152d9d21c90a9cdcca9b9c184b869ba5e8dd9b71ae249b0b475b9accfee69a760dd29a5ddb1299eca82c99c0c3c998e348af98ad68649831f14197d0b965979ba05a96b8b572962a034b94fce85b94a9d2c894a97dc7947fbbd3945b9cbe9319af63927eadba91da14fd91a03dca916846b390bfc06190b997c29030ba618f784d2a8ee19a1e8e2dde5a
  | 5, 7 => 0xcc192eb9cb396eb4ca7d60efc96d0c10c868cc25c7a6c844c74f9114c6f9cb4ec6d832adc69b6a8ac66dd9a1c6675e7bc64a17dbc6372b9dc61256d7c5aadc06c58b7c1cc564d951c533eb2fc4d572d7c3fc3851c370bd9dc302d6f8c29e6ad5c11d3f11c116a76ac108b0a8c0f83473c0bccdf0c096500ac04e9f4abfee9a49bf587e79bec911d7be3a2e37bd16d93abcc924eabbbd32eabbb790a3bb2457c9ba0f9fcdb97f3fcfb97b74edb92bca00b827ff15b7956f46b74b1f21b69e4a34b656d662b5fc1de3b5e8985eb5b8a788b5a3114eb52d0442b4fc4ebab36c155fb368c841b343176ab3390d7cb2fe3dc7b0f774fdb0e9093eafa368d6af6d8648
  | 5, 8 => 0xf6b7e53ff5e45c34f572f1bef556028ff42df357f1b05117f19fa88df1164e32efe9f7e3ef58691eedf9b837edf3e94aecc3dba5ea7bbf33e8f90939e8bf0514e834a646e706607de6faf2c8e6df528ee676e16fe5b1d8fce577164de514732ae2ce3ccce28c69cce2105ad5e04f0c70dfd9497fdfa1e4b1df55ce00de73191fde52aa1cdd9edc49dd8c767edd417ed3dd30fed3dd30d649dc9df77cdc317656dbeaad89db673b63da9e4f3fda5ea546da1bba5dd9b61368d9018ad7d7eb601dd7b1a302d76b750ad75acc80d547e543d384b4cad2a60fc2d2605552d2036d79d07f0b47cf74e960cf5041bdcf01d848cec3e8adce500d73ccf698edcc545503
  | 5, 9 => 0xfffa0ccfff192420fc0fa4bbfaa7a5c0f6bec90c
  | 6, 0 => 0x1d592f6e1d2e9d411d0e6b4e1be2253a1b8540eb1a90744c19eb1f1719e7a07519b80748195a592a18b4b7de180b014d17e8527417dd04ec17abc4a0177ef3181734e2aa170968c1169ab2ff15655a7714f6c32f1467a901145597e71422929f13dd01e113cc96f91213ec4711f35af6117d539c108b124310816d580f598d500f0da9480e9b5bb20e8ab3280d32f4250ce0eb3e0c4ccc380c00f7060be9da590be723ef0baf17aa0b251ebd0ad6da4a0a858322091d049208ccc36c083b5688080a821607d2590f07970c6906870dcd0556fc5d04d10bf404a84dfc049ee428048aab7903c2d84f039679790379803003247eea02d5f8d9026e8310003f9ee9
  | 6, 1 => 0x3ee7b15b3ea095953e4302a53e1ee3903d4bb8c23c9949623b63849c3b2b8d853aee43643a8307333a7cde9439f4013339e59bd1381c31b33787a18a363111d435f28d7435907b2434d35d0a346fa3c733165e1232fff986322f56e6321f596931ea577c31abb1ea31aa01d9315d2015312100eb3102046b30f15be12fcad8692f60f8252eb637f42e660db22caccf852c9885762c62133a2c1ead162bfc0f412b8aee472a85db7729f3c65a29ce7ad1295c804229164d3c28bd4cdf2738ff2a26346e9e2486b0972403946122a5254b227f701a21f34e1a2117424120ba19142092ebd120720f9e1ef121221ee80a291e8067501e0f1aaa1ddeae9b1da52978
  | 6, 2 => 0x631da46c622bbea961f4810561eb45e761b6c22360b8c69c60752bbf601a1d345f6658205ecf32325ec0d5695ebf958c5e54330b5e2090695dbfa2e25d2f5c315d065e3c5cfc544e5c39cdba5aac50105966afa8594e5f6a5937fade5930cd1a591b5be3583f57ad582258d45756a25e573a05c3567c581755430ed754019923536fbdda5346f76652e4d0dd514283bb5046201550315dc84ff91feb4f0e1acb4c2539d84acb5c5949e07fe248266d8347ef12b047ba374946e50fdc46caed2945db925845d9449d458f41ac45692faf4529227a44ce8e2d443954a4442121e443840a9b42a68f814270af3641f5381341940037416b2b9a407bfc443fa7ea5c
  | 6, 3 => 0x87894865875dba19874fbd508704c5a586f445a586f41d1b8673e12d86613e4e85f4bd28850ad6408482b61783795a3a8333ebfa81aea6ef8174e9d481398a20800e92557f0b2c157db5ce9b7cb4596f7c6956947c239c2478e9f3e5783007487813544578073e087753fb6f76e88fef75dc758b75a671b2716a0f167112d7e670cd2d7a700d5ead6ffa726f6f6e22d86f6790fe6ef732016e7fbcd76dbf7f236dbbac466cc61dca6c61b1a76bc743046b4b61396ae085e36ad9ee3c6a8014c26a185b986a11e61c69b1e11b691b231767fd7509668c6bbc65a43928658079bc657ad77564d896ed64d814e064c76c566463735563da51ea633ebbbf632dae8f
  | 6, 4 => 0xb900146fb765d19fb61096bfb5e8985eb5b02372b4fc4ebab4e8658ab3ebe51ab3390d7cb1e85ed3b0cce2e3b08d4ebaaf6105bbaf0e067faeaae2bdad59c046ad28f5eface7c5b7ac57a306aae14e77aa453618a983b094a96b6e5ea8d6cdc0a7259400a670e7b8a07b2c119fa7a3069f60afe29c3ffd539b7397e99b62ef5f9af059189ad9950499b2840797bdfefc97052ed296f7f894965ab4d4957807b3943f0605941657b893f3ad9e93b1cb2c92824be691a03dca90bfc061903a28418f751fce8f3a5d1f8d565cb38cd707c08c91839e8c4fb09e8bfec6e28b1016388aff6dae8adf36828a12534289652b838955a5c488365ff18815f0ee87e6bb07
  | 6, 5 => 0xfd692e8afc81976efb9756bef5db8cf6f4c8588af261d72df260f1aef2131603f1b05117f143db88ecbf3b84e863dc62e8258fa6e8243503e6faf2c8e6df528ee5b1d8fce577164de50d067ee4b44ee8e3a2dd7fe15b90e1e14ae857e04f0c70de52aa1cdd417ed3dcf8f5d3dcd9a4dfdcc8fc55dcc34053dc9df77cdc67fcc6dbeaad89dbad9e49d83f2149d76b750ad6701652d5e9ca68d547e543d4a94f00d2605552d1de2063d0e12484cdcfd692cb7f3cabcb396eb4ca56329eca544ff4ca513171c8b467efc7717a1cc700d7e7c4a84006c43b3d7ec3d1c8a4c3923468bff8574cbf1c1d29be905bfabdda40a2bbb790a3b99f87c2b97032f5
  | 7, 0 => 0xe863dc62e14ae857dcd9a4dfdbad9e49d6701652ca56329ec8b467efb4e8658aad59c0469c3ffd539b7397e9941657b88f751fce8b1016388704c5a586613e4e7f0b2c157c239c2464d814e0632dae8f5ebf958c573a05c35346f7663b63849c3a83073331aa01d93102046b2c62133a21f34e1a21174241177ef3180e9b5bb20e8ab3280ce0eb3e003f9ee9
  | 8, 0 => 0xe9b5bb2
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000f0f0f0f000000000cccccccc0000000055555555000000000f0f0f0f0000000000ff00ff000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xff0000ffff000000ff000000ff000000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000f0f00000f0f00000aaaa0000aaaa000033330000333300000000ffffffff00000000ffff0000
  | 0, 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f000000000f00ff000f00ff000f000f00ff00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff0000
  | 0, 3 => 0x33333333333333333333333333330000333333330000000033330000ffff0000333300003333000033003300ff00ff00330033003300ff0033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0f0fffff0f0fffff0f0fffff000000000f0f0f0fffffffff0f0f0f0f0f0fffff
  | 0, 4 => 0x555555555555ffff5555555555555555555555555555000055555555000000005555000055550000550055005500550050f050f050f050f0505050505050505044444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff33ff33ff33ff000033ff33ff000000003333ffff3333ffff33333333ffffffff333333333333ffff
  | 0, 5 => 0x88888888888888888888888888880000888888880000000088008800880088008080808080808080777777777777777777777777777700007777777700000000770077007700770070707070707070705f5f5f5f5f5f5f5f5f005f005f005f0055ff55ff55ff55ff5555ffff5555ffff5555ffff0000000055555555ffffffff
  | 0, 6 => 0xaaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00ff00ff00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a000000000a0a00000a0a00000a000a000a000a000
  | 0, 7 => 0xaaaaffff00000000aaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaabbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa00000000aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000aaaa0000
  | 0, 8 => 0xcc88cc88cc88cc88cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000c8c8c8c8c8c8c8c8c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaffaaff0000aaff0000aaff0000aaaaffffaaaaffff
  | 0, 9 => 0xcccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00cccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0
  | 0, 10 => 0xeaeaaaaaeaeaaaaaeaaaeaaaeaaaeaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0e0e0c0c0ddddddddddddddddcfcfcfcfcfcfcfcfcf00cf00cf00cf00cdcdcdcdcdcdcdcdccffccffccffccffccccffffccccffffccccffff00000000ccccccccffffffffccccccccccccffffcccccccccccccccccccccccccccccc88
  | 0, 11 => 0xeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecccccccccceecccccceecccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ee00ee00ee00cc00ececececececececececececececccccececccccececcccceaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaeaea0000eaeaeaeaaaaaaaaaeaeaeaea00000000
  | 0, 12 => 0xf0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccceeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaa
  | 0, 13 => 0xf0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c000f0f0f0f0f0f0a0a0f0f0f0f0f0f05050f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000ffff0000f0f00000f0f00000
  | 0, 14 => 0xf5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f3f3f30000f3f30000f3f30000f3f0f3f0f3f0f3f0f300f300f300f300f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0fafaf0f0f0f0f0f0f3f3f0f0f0f0f0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0
  | 0, 15 => 0xfaf8faf8faf8faf8faf0faf0faf0faf0faf0faf0faf0fa00faf0faf0faf0f0f0faf0faf0faf0c800faf0faf0faf00000faf0faf0f0f0f0f0faf0f0f0faf0f0f0faf00000faf00000faaafaaafaaafaaafa00fa00fa00fa00fa00fa00fa00f000f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0
  | 1, 0 => 0xfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf0f0f0f0fafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000
  | 1, 1 => 0xff00fa00ff00fa00ff00f000ff00f000ff00ee00ff00ee00ff00cc00ff00cc00ff000000ffff0000ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000fefefefe00000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0
  | 1, 2 => 0xff00ff00ff00ff00ff00ff00ff00fc00ff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00c000ff00ff00ff00aa00ff00ff00ff005500ff00ff00ff000000ff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000
  | 1, 3 => 0xff80ff80ff80ff80ff55ff55ff55ff55ff55ff55ff55ff00ff55ff00ff55ff00ff33ff33ff33ff33ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff0cff0cff0cff0cff05ff05ff05ff05ff00ffffff00ffffff00ff00ffffffffff00ff00ff00ffffff00ff00ff00ffaaff00ff00ff00ff33ff00ff00ff00ff0f
  | 1, 4 => 0xffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff88ff00ff88ff00
  | 1, 5 => 0xffeeffee00000000ffccffccffccffccffccffccffccff88ffccffccffccff00ffccffccffccccccffccffccffcc0000ffccffccff00ff00ffccffcc00000000ffccff88ffccff88ffccff00ffccff00ffccff00ff00ff00ffccccccffccccccffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ff00ff00ffaaffaaffaaffaa
  | 1, 6 => 0xfff0fff0fff0ffa0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff0cc00fff0fff0fff00000fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0fff000000000fff0ffa0fff0ffa0fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeeffee0000
  | 1, 7 => 0xffff0000ffff0000ffff0000fff00000ffff0000ff000000ffff0000fafa0000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffcfffcfffcff00fffcfffcfffc0000fffcfffcff00ff00fffcfffc00000000fffcff00fffcff00fffafffafffafffafffafffafffa0000fffa0000fffa0000fff0fff0fff0fff0
  | 1, 8 => 0xffffaaaaffff0000ffffaaaaaaaaaaaaffffa0a0ffffa0a0ffff8888ffff8888ffff8888ffff0000ffff8800ffff8800ffff8080ffff8080ffff7777ffff0000ffff5555ffff5555ffff5500ffff5500ffff3333ffff3333ffff0505ffff0505ffff00ffffff00ffffff00ffffff0000ffff000fffff000fffff0000ffffffff
  | 1, 9 => 0xfffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000ffffeeeeffff0000ffffeeee00000000ffffeaeaffff0000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc88ffffcc88ffffcc00ffffcc00ffffc0c0ffff0000ffffc000ffffc000ffffaaaaffffaaaa
  | 1, 10 => 0xfffffffaffff0000fffffff0fffffff0fffffff0ffff0000ffffffeeffff0000ffffffccffffffccffffffccffff0000ffffffaaffff0000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffafafffffafafffffafaffff0000fffffaf0ffff0000fffff0f0fffff0f0
  | 1, 11 => 0xffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffffa0a00000ffffffff88888888ffffffff55555555ffffffff55550000ffffffff33ff0000ffffffff33330000ffffffff11111111ffffffff0f0f0f0fffffffff0f0f0000ffffffff0c0c0c0cffffffff00000000fffffffcffff0000
  | 1, 12 => 0xfffffffff3f30000fffffffff0f0f0f0fffffffff0f00000fffffffff0000000ffffffffeeeeeeeeffffffffeeee0000ffffffffccccccccffffffffcccccc00ffffffffcccc8888ffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffaaff0000ffffffffaaaaaaaaffffffffaaaa8888
  | 1, 13 => 0xffffffffffff0505ffffffffffff00ffffffffffffff000fffffffffffff0000fffffffffff0fff0fffffffffff00000ffffffffffccffccffffffffffaaffaaffffffffff00ff00ffffffffff00cc00ffffffffff000000fffffffffefe0000fffffffffcfcfcfcfffffffffcfc0000fffffffffafafafafffffffffafa0000
  | 1, 14 => 0xffffffffffffcc88ffffffffffffcc00ffffffffffffc0c0ffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffff8888ffffffffffff8800ffffffffffff8080ffffffffffff5555ffffffffffff5500ffffffffffff3333ffffffffffff1111ffffffffffff0f0fffffffffffff0c0c
  | 1, 15 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff000ffffffffffffeeeeffffffffffffcccc
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x3ed427b3
  | 3, 0, 0 => 0xee5b9167b47d32d427b4ee3f5427b49336d427b4b738542764f73f9427b4ee519167b4ae38542764b5cbd167b497b7942764b5b79427b47d3d5427b49536d427b4b6385427b4
  | 4, 0, 0 => 0x97b8564a13daf72d4e1509ed71f6970a84f6bdc97b8d427b5f3cbdc2a13dafdbb8fe509ed64cd865a84f6be8a1b85427b5ee5bdc2a13dacbddae1509ed7dd2a70a84f6bdc97b7142765ee4bdc2b53daf72a4e1509ed7b92f70a84f8bef97b85427b5
  | 4, 0, 1 => 0xee5c25e8b3daebe5ee1509ed7b92f70ab942bf097b79427b5d84bdc2a13dae865efe509ed7b8e1509ec54bca97ab1427b5ee385427b35af7254dc509ed7b93c70a84f6bec97b85427b5ee5b9c2a13daf425ee1459ed7b95e6f284f6bcf97b85427b5
  | 4, 0, 2 => 0xc44bdc2a13daeb65ee1509ed7b8f56c284f6bdc97bfd427b582bd5c2a13daf725ef3459ed7b92f70a78f6bee97b6d427b5ee4e5c2a13daf72a0fe509ed7b9266f284f6bdcb2b85427b5ee4bdc2a13b2f7282e1509ed7b92f70a2cf6bdc97a85147b5
  | 4, 0, 3 => 0xd0cbdc2a13daf725ee1539ed78b7f7f284f6bdc92b85427b570b1172a13dafba5ee1509ed7b92f70abd42bdcbb385427b5ee4bdf8a13daf725ee15d9ed7b92c70a84f6bc297b85427b5ee4bd58a13daf7254e1509ed7637fa322cf6bdc7f2851c7b5
  | 4, 0, 4 => 0xf8571c2a13daf72dcde509ed75b6970a84f6be897b8542765ee475c2a13daf2a5ee1509ed7b92f6e284f6bdc97b85327b5ee49dc2a13daf725f12449ed7b8e1509ecaebdc97bad427b5ee4b5c2a13daf725efe509ed7d72f70a84ecb6eb5b85427b5
  | 4, 0, 5 => 0xee5b942893daf525ee1509ed7b93170a84f6bdc97b89427b5ee4bdc0a13daf71fccb509ed7b92f7c284f6bdc97b6d427b5ee4c9c2a13daf71c2a13d8ad7592f70a84f6bdc97b75427b5e84bdc2a13daf725e8b3d9917b8e15c284f6bdc9bb85427b5
  | 4, 0, 6 => 0xee4bdbea13dadca5ee1509ed7b92f79a84f6bdd97b85427b5ee455c2a13daf725ee1509b97ed2f70a84ecbdcb2385427b5ee4bdc2a13dacbdbca13d9d57b8f570a2cf6b8facb85427b5ee55dc2a13dae665ee1509ed7b8de509ecd2bf6b5b85427b5
  | 4, 0, 7 => 0x97bf9f4a13daf7350fe509ed7b8fe7aa84f6beeb8385427b595385b0a13dadae5f08509ed6d75070a84f6bdc97b65427b5ee4bd56a13daf725ea13d9257c92f70a84f6bdca2b85427b597b85b0a13b2f725ee4509ed65f1770a84f6b9b70ae5427b5
  | 4, 0, 8 => 0xe83d5c2a13daf7260e1509ed7b92f78284f6bdc70ab5427b5ee4bde2a13dafa25ef3509ed7b8ea70a84f6bdc97b85407b5b5b85428e3dafa25ee1509ed7b94684284f6bdc95b85427b5f85b9c2a13daf725ee15b1ed7b92f70acd42bdc70a84f6395
  | 4, 0, 9 => 0xee3d5c2a13daf725ee1509e97b92f6c22cf6b2f82b85167b5f7579c2a13daf725ece509ed7b92f8a22cf6bdc97b79427b5ee519c2a13daf725ee1489ed7b8e154284f6bdcab385427b5dbcbdc2a13dad71c2a13d9d56d72f70a84f6b2f622b1427b5
  | 4, 0, 10 => 0xf7499c2a13daf7e5ee1509ed6c12f70a84f6be297b85427b597b85427b2cacbdc2a14d9d97b92f509ecacbdcbc385427b5ee509c2a13dacbdc2a1411ed6d6e165a84f6bdca3b85427b5ee555c2a13dacbdf4e1509ed7b8e1509ec74bdc5cab1427b5
  | 4, 0, 11 => 0xee4bdc2bd3daf71c2b9509ed7b92f79284f6bdcaeb85427b5d45adc2a13dadb9c2a13d9d57b92f6b284f6bdcae385427b5ee4a5c2a13daf9a5ee1509ed7b93a70a84f6bdc70a84f66a597b85427b222cbdc2c4509ed7b92f74a84f6bdca2385427b5
  | 4, 0, 12 => 0xee4fdc2a13daf825ee1509ed7dce1509ecd2bdcb7421427b5bbcbdc2a13daf7254e1509d97b94650a24f6bdc70a84f6545ee50de6a13dacbe0ae1509ed7b9706f284f6bdc9b385427b5b5cbd42893daf7286e1509ed7b95170a84f6bdc97b8542785
  | 4, 0, 13 => 0xee3d1c2a13daf725ce1509ed65f0670a84eabdc9eb85427b5
  | 5, 0, 0 => 0xee4be28a1449edbb92f70ab1427b6db5fe5ee1509edbb92f70a84f6026dd5fe86e1509edbb92f70a84f6046ee4bdc2cb509edbb92f70a84f6506ee4bdc2a14d9edbb9ba97b85427b6ee5a65ee1509edbb9d770a84f6696d8e125ee1509edacf6297b85427b6ee4bdc2a13d971bb92f70a84f6366
  | 5, 0, 1 => 0xd8dfe46e1509edbb92f70a852c7b6e84be10e1509edbb92f70a84f6556ee4bdc2a1441edb637fabb85427b6ee6365ee1509edbb97fb4b85427b6ee6c686e1509edb637c97b85427b6ee4bdc2b4509edbb92f70b4d427b6d8d8a5ee1509edbb92f70a84f67b6ee5ce5ee1509edbb8e163ae5427b6
  | 5, 0, 2 => 0xd8dfe5ee1509b9bb92f70a85007b6f45fe5ee1509edb637fb2385427b6ee4bdfce1509edbb94f97b85427b6ee5a5c2d4509edbb98e97b85427b6d8dfe5ee1509edbb92f70a84f6386d8cbe0ae1509edb637f7ab85167b600772dce1509ed7b92f74385427b6ee4bdb0a1449edbb92f70a84f6136
  | 5, 0, 3 => 0xee4bdc2a14f9edbb92f70a84f6726d8e5e5ee1509edbb970a8385427b6d8e0a5ee1509edb632f70b45427b6ee4bdc2dc509edb638f97b85427b6ee4bdc2a1429edb632f70a85027b6d8dfe5ef3509edbb95497b85427b6ee4bdc2aa509edbb92f73385427b6d8dfe2ae1509edb637e97b85427b6
  | 5, 0, 4 => 0xbfda6cee1509edb632f70a84f63c6d8e6e5ee1509edb637f97b8562a16bfcbdc2a13f9edbeddcaf385427b6ee6825ee1509edb637f97a84f6496ee4be42e1509edbb95697b85427b6ee4bddce1509edbb92f70b15427b6f6f725ee1509edbb97097c21427b6e95fe5ee1509edbb92f8cb85427b6
  | 5, 0, 5 => 0xf46ea5ee1509edbb97fab385427b6ee5c1c2a1471ed801dcb2b85427b5fcf725ee1509edb357f97b85427b6007725ee1509d97b94697b85427b6007725ee1459ed6ff6b97b85427b6ee4bdc2a13d8c5bb92f70a84f6166ee4be10e1509edbb94a97b85427b6ee4be1ae1509edb677f97b85427b6
  | 5, 0, 6 => 0xee4bdc2a13d889b9b2f8d385427b6dddfe5ee1509edb637f7f3d5427b6ee5fe8ce1509edaff2f70a84f6516ee4ee5ee1509edaff2f70ac1427b6dfcbdc2a1499edbb9b497b85427b6dfea25ee1509edb817f97b85427b6ee76e5ee1509edb637fb4b85427b6cdcbdc2c7509edb637fb3385427b6
  | 5, 0, 7 => 0xee4bdc2a1491edb8b7fb8385427b6d8cbdfcf7509ed801ad97b85427b5ee6a25ee1509edb937facb85427b6ee4bdeae1509edbb92f70a852a7b6fb7c25ee1509edbb97f97b79427b6bfc0deae1509edaff2f70a84f6586ee52e5ee1509edb638c97b85427b6ee5365ee1509edb63a8bfbf9427b6
  | 5, 0, 8 => 0x7725ea1270bd7b92f70a84f6756ee5fdeae1509edbb9d597b85427b6007725eac509ed7b92f70a851a7b6ee5c25ee1509edbb92f70a84f6616ee4ce5ee1509edb638c97bcd427b60077254e1509ed7939f97b85427b6ee5f65ee1509edbb94997b85427b6ef7725ee1509edb637fa3421427b6
  | 5, 0, 9 => 0xd8dfe5ef1509edbb9c997b85427b6ee4bdc2e1509edbb92f70a84f62f6bfcbd84ac509ed801ee97b85427b5bfcbdc2a13d855bddc597b85427b6ee6e65ee1509ed801dc96385427b5f84bdc2d8509edbb92f70af9427b6ee74e5ee1509ed801dc97b85424e5ee6c6dce1509edb637f75385427b6
  | 5, 0, 10 => 0xee4bde6e1509edbb95ea8385427b6cfcbdc2a13d9cd801dc97bf9427b5ee4bdc2a14e9edbb92f70a84f6346ee4be44e1509edbb92f70a84f63b6ee4bdc2a13d871bb92f8d385427b6ee4bdc2893d97dbb92f70a8d427b6bfd65c2a13d9cdbeddc93385427b6d8dfe5ef0509edb637f70ab5427b6
  | 5, 0, 11 => 0xd8dfe5ee1489edbb92f70a84f62360072a5ee1509ed7638197b85427b6007725edc509ed7b92f70a84f6476bfcbdc2a13d8c9b637f70aa1427b6d8dfeace1509edbb9d997b85427b6ee4bdc2c9509edbdddc97b85427b6e25fe5ee1509edbb92f70a852e7b6ee4d65ee1509edbb92f70a84f63f6
  | 5, 0, 12 => 0xd8dfe3ee1509edbb92f70a84f6676ee4be20e1509edbb95e70a851c7b6ee4be12e1509edb637f97c51167b6d8dfe5ede509edbb9b197b85167b6ee4bdece1509edb637fa0385427b6fa7725ee1509edbb92f87b85427b6ee4be3ce1509edb638a97b85427b6d8dfe8ce1509edbb92f70a84f6736
  | 5, 0, 13 => 0x7425ee1509ed6ff5f97b85427b6ee4be08e1509edbb92f70b0d427b6ed58a5ee1509edbd72f70a84f6756ee4be10a13d991b4f2f70b51427b6ee5a25ee1509eda5ee1612fd427b6bfdd65ee1509edb997f97b85427b6ee5c1c2cb509edbb92f70a84f64c6ee6c65ee1509d9b637f97b39427b6
  | 5, 0, 14 => 0xee4bdc2a1419edb637f70a84f63a6e2dfebce1509edbb92f70a84f6416ee4bdc2a13d8a1b452f81b85427b6ee4bdc2a13d89db637f5cab1427b6ee4be24e1509edb637f7ab85427b6ee4bdc2a13d839bb9c197b85427b6bfcbdc2c4509ed8012f709ec7e095dadfe5ee1509edbb9d197b85427b6
  | 5, 0, 15 => 0xd8e4a5ee1509edb638997b85427b6f0f725ee1509edbb95093385427b6ee4bdc2a13d869bb9b197ab1427b6d8eaa5ee1509edbb92f70a84f6686ee6c654e1509edbb95e97b85427b6d8cbdeee1509edb637fa3b85427b6d8dfeaae1509edbb95c97b85427b6ee4bdcae1509edb63ad97b85427b6
  | 5, 1, 0 => 0xee4be26e1509edbb92f70ae5427b6d8dfe5ee15e1edbb99597b85427b6ee4bdc2a13d935bb92f70a84f6606ee4fa5ee1509edbb92f70a89427b6ee4bd8eac509edbddb197b85427b6e45fe5ee1509edb8d9897b85427b6ee5feb8e1509edbb9cd97b85427b6bfcbe2ce1509edbb9b196385427b6
  | 5, 1, 1 => 0xe34bdc2a13d9c1800e1509ec42095ee4bdc2a13d805bb96e70b61427b6ee7165ee1509edbb9b197bf9427b6ee4bdc2a13d991b632f80385167b6ee499c2a1471edb632f70a84f61f6ee421eae1509edbb97facb85427b6b85ae5ee1509edb637f97a84f6566ee4bdc2a13d82dbb95670a85267b6
  | 5, 1, 2 => 0xee6c65edc509edb657f97b85427b6ee72e5ee1509ed801dc709ec7e215bfcbdc2c2509edbb94397b85427b6ee6fe5ee1509edbb92f70a84f6036ee4bdc2a13d801b637197b85427b6ee4bdc2a13d8c1bb97f70ae5427b6ee4be06e1509edb62e15fae5427b6007725ee1509ed401dc97a84f62f5
  | 5, 1, 3 => 0xee4bdc2a13d865bb99697b85427b6ee579c2cb509edbb92f85b85427b6ee571c2a14d9edbb9dc97b85427b6ee4bdc2a13d829bb92f70b49427b6ee5b65ee1509edbefdc97b85427b6d8dfe5ee9509ed801dc97bcd427b5d8dfe88e1509edb95b197b85427b6ee4bdc2c6509edbb92f70a84f66d6
  | 5, 1, 4 => 0xee4bdc2a13d885bb92f70a85307b6ee56a5ee1509edb637f97be5427b6ee4e25ee1509edba1b197b85427b6d8e465ee1509edbb9a8b8385427b6ee4bdc2cd509edbb92f70a84f60d6f2f725ee1509edbb92f70a84f6076fb771c2a13d9a5b717f97b85427b6ee4bdc2de509edbb92f93385427b6
  | 5, 1, 5 => 0xee4bdc2a13e9edaff2f70a91427b6d8cbdd8e1509edbc7dc97b85427b6cdcbdc2c2509edbe12f70a85367b6d8dfe5ed6509edb637fae385427b6ee4bdc2a1431edb637f9d385427b6ee4bdc2a13d8b5b637fba385427b6fb4bdc2a13d9d5bb92f70a84f65f6ee4bdc2a13d8f9b63a297b85427b6
  | 5, 1, 6 => 0xee4bdc2a13d921bb92f70a851e7b6ee59e5ee1509edb1f2f70b51427b6d8dfdc2b9509edb639f97b85427b6ee4bdc2a1459edbb97097a85127b6ee4bdfca13d9a5a5ee16c284f675697c0e00e1509edb63a997b85427b6ee4bdc2a1439edbb92f79a84f65f6dedfe5ee1509edb639497b85427b6
  | 5, 1, 7 => 0xd8dfe86e1509edb637fa8b85427b6ee6c65ee1509edb6397acb85427b6ee4bdc2a13d9e5bb92670b2d427b6ee4bdc2a13d93dbb99e97b85427b6ee6fa5ee1509edbb99c97b85427b6ee4bdc2a1449edbb92f6c32d427b6f5f725ee1509edbe5dc97b85427b6007a25ee1509ed7b92f70a84f6456
  | 5, 1, 8 => 0xed5c25ee1509edb637f70a84f6546005ae5ee1509ed7b98097b85427b6ee4bdc2a13d899b637fa1bcd427b6ee5ba5ee1509edbb9b197bcd427b6ee4bdc2d0509edbb95070a84f6696ee4bdc2c7509edbb98597b85427b6ee4bdc2a13d841bd1dc97b85427b6d8dfe6ce1509edaff2f70a84f6436
  | 5, 1, 9 => 0x7728ce1509ed7b8e150a38f6696f4f725ee1509edbb99d97b85427b6d8e7ed2e1509edbb98397b85427b6ee519c2a13d991bd12f70a84f65f6ee4bdc2a13d831bb92f70a84f61d6ee6a2bce1509edbb92f70b01427b600772ace1509ed7b92f88b85427b6ee4bdc2a9509edb637fa3285127b6
  | 5, 1, 10 => 0xee4bdc2a13a97dbe1dc97b8542766d8dfe7ee1509eda5f0882b85427b6ee6c6d2e1509edbb92f70a84f6716d8dfdc2a13d8b1b758c97b85427b6ee4bdc2a1481edbb95397b85427b6007725ede509ed7b92f70b29427b6ee4be2908509edbb96b97b85427b6ee4be30e1509edbb92f83b85427b6
  | 5, 1, 11 => 0xee4bdc2a13d8ddbdd2f70a851c7b6ee56e5ee1509edbb92f70a84f6356f9f7258e1509edb637f97b856a7b6007725ee1270fd7b92f70a84f6696ee4bddee1509ed801dc7ab85427b5d8cbe00e1509edbb92f70a84f65d6e2dfdc2a13d9a58012f70a849c095ee5ee5ee1509edbb92f84361427b6
  | 5, 1, 12 => 0xee4bdc2a13d83dbb92f95385427b6eadfe5ee1509edbad7f97b85427b6ee4bdc2cc509edbb92f94385427b6ee4be28e1509edbb92f50a24f6646dfe425ee1509edbb92f80b85427b6fb7725ee1509edbb9a893385427b6f877254e1509edbb92f70a84f6466ee4bdc2a1461edbb92f70b5d427b6
  | 5, 1, 13 => 0xee4bdc2a13d821a5f2670b61427b6ee4bdc2a13d861bb94e97b85427b6fd7725ee1509edbb92f70a84f66f6ee4bdc2d8509edb637f70a84f66b6d6dfe5ee1509edbb92f96385427b6ee4bdc2a6509edb637f9e385427b6ee4bdc2a13d879b632f8db85427b6ee4bdc2a13d815b637fb7385427b6
  | 5, 1, 14 => 0xd8dfee12f459edbb92f70a84f6766ee4bdc2a13d929be1dc97b71427b6ee4bdc2ba509ed8012f70b11427b5ee4bdc2a13d895bb8e165a84f6696ee70e5ee1509edbb96197b85427b6d8e2e5ee1509edb8f7f97b85427b6ee4bdc2a13d969b637f97b855ca16ee4bdc2a13d9d1801dc70a849c215
  | 5, 1, 15 => 0xee4bdc2a13d85db637f97b85167b6d8e1a5ee1509edbb92f70a85387b697b85429b3d9d5bb9d897b85427b6ee69a5ee1509edbe3dc97b85427b6d8e62cae1509edbb92f70a84f6066e2e4e5ee1509edbb92f70a84f62e6ee4bdc2a13d9b1bb92f70a85427b6d8dfe5ea1451edbb92f70a84f6296
  | 5, 2, 0 => 0xee4bdc2a13d9958012f70a84f6095004bd427b178257b92f70a84f64e6d8dfe5eff509edbb92f70afd427b6ee5425ee1509edb637f97bcd167b6ee4bdc2a13d901801dcae385427b5d8dfe72e1509edb636570a84f6706d8dfea0fe509edbb95897b85427b6d8dfe5ee1509d9bb92f70b11427b6
  | 5, 2, 1 => 0xf9f725ee1509edb637f96385427b6ee4bdc2a13d849801dc97b84f63f5ee4be10e1459ed801dc979ec7e2f5ee4bdc2a1471edbb92f70a84f65b6d8dfe5eac509edbebdc97b85427b6ee4be0ce1509edbb92f70b69427b6d8dfe54e1509ed801dc70ae5427b5d8dfdfca1471edbb92f70a84f6536
  | 5, 2, 2 => 0xd8dfe5eeb509ed8012f82b85427b5e2dfe5ee1509edb637f97bf9427b6ee5e65ee1509edbb97a97b85427b6f87725ee1509edb637f97b854e7b6ee4bdc2cf509ed801dca1b85427b5ee4bdc2a13d979bb92f70a84f6096ee4bdc2a13d881bb9c697b85427b6ee4bdc2a13d98dbb92f70a84f61b6
  | 5, 2, 3 => 0xee4bdc2a1421edbb94370a84f65f6fc7725ee1509edbb92f70a84f6776d8dfe6ee1509ed801dc70a84f621500771427b178857b92f85385427b6ee4be0ae1509eda5ee163b11427b6d8dfe5edc509edb637f97b85327b6fb7725ede509edbb92f97b85427b6d8dfdc2a13d95dbb92f70add427b6
  | 5, 2, 4 => 0x3637f7f32d427b6f87ae5ee1509edbd5dc97b85427b6fb772e0e1509edb637f97a2cf6646
  | 6, 0, 0 => 0xd8dfe7d2f70a84f6fb1bfcbd8eac509edc01b1b14bdc2a13db773632f70a84f6097e6ec6ff2f70a84f6fb1bfd665ee1509edf637f97b85427e3dbf72ff2f70a84f65f7f9f73632f70a84f6fdcbfcbdc2a13d885c01dc97b8596a13db003b9b197b84f63f6007725ee150a6cf6ddcd8cbdc2a1471edf637f97b85427b0d3ec6ff5e97b85427b7
  | 6, 0, 1 => 0xee5fe5f2070a84f6e00d8dfe5ee1509ed801b1bfcbd427b17b717637f97b85427b7d8dfe5ee1509ecc8e00d8cbdc2a127059b637f843d5c2a13dbf73637a97b85427b7e6dfe5ee168284f6ff0ee6c65ee1509edc01dc97b8542963db6c6ff2f70a84f60b7d8dfeace150a4cf6fb1bfcbdc2b9509edf6395bfcbdc2a13dbec6ff2f70a84f6607
  | 6, 0, 2 => 0xd8dfe5ee1509ec14fb1bfcbdc2d2509edc01b1c7cbdc2a13db003637f97bcd427b6d8dfe5f2470a84f6fb1bfcbdc2a13d9b5fb97f97b8542893dbf2f637f97b85427b7006c6fee13d8fc42debee5fe5ee1509edf637f97b85427b25bec6ff4397b85427b7dfec6ff2f70a84f6fdcd8e625ee1509edf637f97b85427b003ec6ff2f81b85427b7
  | 6, 0, 3 => 0xd8dfe5ee1509ec1afdcbfcbdc2c7509edf637f97c31c2a13dbec65ee163afd427b7d8dfe5f0e70a84f6fb1bfcbe4ce1509edf637f97b85427b0cb803639797b85427b6d8e5aff2f70a84f6fb1bfd79c2cb509edfb9b197b85427b383803017f97b85427b60077362e1509ec42db1bfcbe16e1509edf637f97b85427b19bf73637f97b85427b7
  | 6, 0, 4 => 0x6c6ff6970a84f6db1bfcbdc2a13d989f637f97b85427b1ebec6ff2f70a850c7b7d8dfe5ee1509ec5afb1bfcbdc2a13d97df637f97b85427b10b803b92f70a84f6166007725f0870a84f6db1bfcbdc2a14c1edc01dcd04bdc2a13db6c6ff3897b85427b7d8dfe5ee1509ec48fdcbfcbdc2d0509edf63a8bfdc1c2a13dbec6ff2f70b35427b7
  | 6, 0, 5 => 0xd8dfe5ee1509ec90fb1bfcbdc2a1479edf637fb3cbdc2a13db803b9a897b85427b6d8dfe5ee150a2cf6fb1bfcbe40e1509edf8d7f97b8542933dbec6ff7097a85127b7d8dfe5efe509ecd2fb1d1dfe5ee1509edc01b1c64bdc2a13db773632f70b2d427b7ee6c65ee150a6cf6fb1bfcbdc2a1439edf637f97bcd427b2fbec7577f97b85427b7
  | 6, 0, 6 => 0xee5fe5ee1509ecd2fb1bfd325ee1509edf63b1bfcbdc2a13dbec7312f70b41427b700003b92f70a849ca00ee4bdc2a13d9d5b639ebfcbdc2a13dbefb637f97b85427b700772e12f70a84f6db1ce5fe5ee1509edf637f97b8542893dbf73632f70a852c7b7f5ec6ff2f70a84f6e00bfcbdc2a13d8458017f97a84f62f08b6c6ff2f70a84f6457
  | 6, 0, 7 => 0xde6c6ff2f70a84f6e00ee4bdc2a13d8fdb6380bfcbdc2a13dbec6ff2f70a84f6267d8e325ee1509ecbefb197b85a0a13d9c1f637f97b85a0a13dbec6ff5070a84f6697007725f1a70a84f6db1bfcbdc2c7509edf6385bfcbdc2a13dbec6ff2f70a84f6107ee5fe5ee1509ec22e00ee7265ee1509ed801dc97b85427b17b002ff2f70a84f6156
  | 6, 0, 8 => 0x6c6ff4670a84f6ddcc85fe5ee1509edc01dc97b85427b39b6c6fee150a38f6697ee6c7412f70a84f6fb1cedfe5ee1509edf6383bfcbdc2a13dbec6ff4670a84f6647d8dfe5ee1509ec18fb1bfcbdc2a13d875f63a8bfd79c2a13dbec6ff2f70b01427b7006c6ff5670a84f6ddcbfcbe28e1509edf637f97b8552a13dbfdbb97f97b85427b7
  | 6, 0, 9 => 0xd8dfecb2f70a84f6fb1bfcbdc2a13d9a5fb9b1d44bdc2a13dbec6ff2f77b85427b7006c6fef570a84f6db1bfcbdc2a13d975c01dce0cbdc2a13db6c6ff7b97b85427b7d8dfe5ee1509ece2fb1bfcbdc2a1481edf637fa9cbdc2a13dbf72ff2f70b61427b7ee73b632f70a84f6fb1bfcbe2908509edf637f97c61c2a13dbf73632f84385427b7
  | 6, 0, 10 => 0xd8dfe5f0170a84f6ff6d8dfe5ee1509edf6398c84bdc2a13dbec6ff2f70a84f6467d8dfe5ee150a30f6e00ee6c65ee150939bb9b197b85427b3abec6ff2f70b5d427b7d8dfe5ee1509ec6efb1bfcd25ee1509edfb9b1b84bdc2a13dbec6ff2f70a84f6357d8dfe5ee1509ec22e00ee57a5ee1509ed801b1bfcbdc24e1fb773632f70a85267b7
  | 6, 0, 11 => 0x7725ee1509ecc8db197c2200e1509edf937f97b8542963dbec6ff2f70a84f61e7ee5fe5ee1509ec9cfb1bfcbdcee1509edc012f70a84f61608b6c6ff2f70a84f60f7d8dfe5ee166284f6fdcbfd425ee1509edf8b7f97b85428e3dbec6ff2f8a385427b7ee727632f70a84f6fb1d75fe5ee1509edfb9b197b85427b17bec6ff2f50a24f6647
  | 6, 0, 12 => 0x5fe5ee161284f6db1bfcbdc2a13d9d1c01b1bfb85424e10b773afb197b85427b7d8dfe5ee1509ec30ffad8dfe5ee1509edc012f70a84f6160ab6c6ff2f70a84f66f7d8dfe5ee16c284f6fdcd8cbdc2a13d8fdc0000ee4bdc2a13da80001dc97a84f62f5d8e425ee1509ece0e00bfcbdc2a13d825b637f97b854ca13dbec7217f97b85427b7
  | 6, 0, 13 => 0x7725f2670a84f6db1bfcbdc2a13d9b1f637f97b8542a13dbec6ff2f70a84f6297bfcbdc2a14b1ece6fb1bfcbdc2a13d929f637f97b85427b293ec6ff2f70ae9427b700773b92f70a84f6db1bfcbdc2a13d895f637f70b2d427b34bf73632f70a84f6737d8e9eff2f70a84f6fc3d8dfe5ee1509edf637fb0cbdc2a13dbec6ff2f70a84f65a7
  | 6, 0, 14 => 0xd8dfe5ee150a68f6fb1bfcbdc2a13d939fb97fbfcbdc2a13dbf73635e97b85427b7d8dfe5ee15fa84f6fb1bfd425ee1509edf7f7f97b85427b383803b92f70a84f65f6d8dfeb12f70a84f6fb1bfcbe38e1509edc01dc97b85427b10b6c6ff2f70a95427b7d8dfe5ee1509ec2efb1bfcbdc2c1509edfb1b1bfcbdc2a13dbec74d7f97b85427b7
  | 6, 0, 15 => 0xd8dfe5ee164284f6e00f5f725ee1509edb637f97b85427b093803637f97b84f63f6d8dfe5f0870a2cf6e00d8dfe5e7b1f8bdb637f97b85427b333ec6ff2f70a851c7b7d8dfe5ee1509ecb6fb197c69c2d0509edfb97f97b85a8a13db803637f70ae5427b6006c73f2f70a84f6db1bfcbdc2a13d94df637f97b85427b32bec6ff6397b85427b7
  | 6, 1, 0 => 0xd8dfef52f70a84f6ff0d8dfe5ee1509edf637fa44bdc2a13dbec6ff2f70a84f6147d8dfe5ee167a84f6e00d8dfe86e1509edbab7f97c69c2a13db803b9b197b85427b600773632f509ec5edb1bfcbdc2a14a1edf637f97b85427b04bf1b637f97b85427b7ee6c65ee1509ecc8fb1bfcbdc2a13d86dfe7b1bfcbdc2a13db803b92f70a85127b6
  | 6, 1, 1 => 0xd8e92ff2f70a84f6fb1bfcbe14e1509edfafc9bfcbdc2a13dbec70f7f97b85427b7ee6c65f2670a84f6fb1bfcbdc2d5509edf63a5bfcbdc2a13dbec7517f70a84f6697d8dfe5f2f70a84f6fb1cc5fe5ee1509edfb9dcd8cbdc2a13dbec6ff2f81385427b7d8dfe5ee15ba84f6e00ee4bdc2d0509ed801dc97b858ea13db6c6ff7997b85427b7
  | 6, 1, 2 => 0xee5fe5ee1509ec2cfb1bfcbdc2a14d9edf75b1bfcbdc2a13dbec6ff2f70a84f65c7d8dfe5ee1509ec6ce00ee4bdc2a13d9a58017f97b84f63f08b773632f90385427b7ebdfe5ee1509ece6e00d8cbe00e1509edb637f97b8542843dbec6ff4370a84f65f7d8dfe5ee1509ec84fb1bfcbdc2a13d9c1c01b1bfb85427b10b003637f509ec5e216
  | 6, 1, 3 => 0xd8e3aff2f70a84f6fb1bfcbdc2a13d8e1f637f97ba1c2a13db803ab7f97b85427b6d8dfe5ee1509ec26e00ee4be28e1509edb637f97b8542963dbec6ff2f70a84f6557007dbb92f70a84f6db1bfcbdc2b4509edf637f97b85427b3dbec6ff7397b85427b7d8dfdc2c75ca84f6fb1bfcbe28a1449edf637f97b8558a13dbec6ff2f70b2d427b7
  | 6, 1, 4 => 0xd8dfe952f70a84f6fb1bfcbe1ae1509edf63a0bfcbdc2a13dbec6ff2f90b85427b7d8dfe5eee70a84f6fb1bfdc25f08509edf637f97c65c2a13dbec6ff2f70a84f6727d8dfee15070a84f6fb1bfcbdc2a1429edf637faa4bdc2a13dbec6ff2f70aa9427b7005fdc2a13d88422c00ee4bdc2d8509edb637f97bf9c2a13dbec6ff6970b51427b7
  | 6, 1, 5 => 0xee706ff2f70a84f6e00d8dfe5eac509edb637fb84bdc2a13dbec6ff2f70a85247b7000025ee1509ec12bb1d45fe5ee1509edf637f97bd5c2a13db803b92f70a84f64e6d8dc2c52f70a84f6e00ee5425ee1509edb637f9dcbdc2a13dbed3637f97b85427b7d8dfee0e150a38f6fb1bfd1a5ee1509edc01b1bfcbdc28b3db6c6ff2f84385427b7
  | 6, 1, 6 => 0x6c6ff2f7f284f6c00ee5ea5ee1509ed801f0ee4bdc2a13db6c6ff2f70a84f6347d8dfe5ee1509ec38fb1bfcbdc2893d97df637f97b85c2a13dbec6ff2f70a84f62f7007725ee1509ec12c00f9f725ee1509ed80000ee4bdc27b1faec6ff2f70af9427b7006c6ff2f70a849cc00d8dfe5ea1270bdb637f97b85427b3ab803b92f70a851c7b6
  | 6, 1, 7 => 0x1b1bfcbdc2a1419edf637f97b85427b143ec6ff2f70a84f6277d8dfe5f08509ecc8fb1bfdc1c2cb509edf637faf385428e3dbec6ff2f84b85427b7bfcbdc2a13d8582ae0000771c2a13d8857637f97bd9c2a13dbec6ff2f70a84f6477d8dfe5ee1509ec7efb1bfcbde6e1509edf637faf541c2a13db8038b7f97b85427b6
  | 7, 0, 0 => 0x6c7217f97b85427b7006c6ff2f8a385427b7006c6ff2f70a84f6117006c6ff2f70a84f6697006c6ff2f70b41427b7006c6ff2f70b1d427b7006c6ff2f70a85127b700002ff2f70a84f6116006c6ff2f90385427b7006c6ff2f70a84f65f7006c6ff2f70a84f621700773637f97b85427b700003637f97b85427b600003637f97a84f62f6006c6ff2f70a84f6647006c6ff5e97b85427b7
  | 7, 0, 1 => 0x6c6ff7097b85427b7006c7517f97b85427b7006c6ff2f84385427b7006c7417f97b85427b7006c6ff2f70a852c7b7006c6ff2f70b2d427b7006c6ff2f70a84f670700003637f70a84f6216006c7317f97b85427b7006c6ff7a97b85427b700003b9b197b85427b600003637f97b84f63f6006c6ff2f70a851c7b7006c6ff2f70a84f64e7006c6ff5097b85427b70000001dc97b85427b5
  | 7, 0, 2 => 0x6c6ff2f70a84f63f7006c6ff2f70a84f62f700003637f97b85424e6
  | 8, 0, 0 => 0x3637f97b85427b6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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
private theorem z3_0 : span (Z 3) 14 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 14 0 = true := z3_0

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
private theorem z4_144 : span (Z 4) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_168 : span (Z 4) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_192 : span (Z 4) 20 192 = true := by decide +kernel

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

private theorem z4_a6 : span (Z 4) 168 0 = true :=
  span_join (f := Z 4) (a := 144) (o := 0) (b := 24) z4_a5 z4_144

private theorem z4_a7 : span (Z 4) 192 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 24) z4_a6 z4_168

private theorem z4_a8 : span (Z 4) 212 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 20) z4_a7 z4_192

private theorem z4 : span (Z 4) 212 0 = true := z4_a8

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
private theorem z5_408 : span (Z 5) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_432 : span (Z 5) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_456 : span (Z 5) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_480 : span (Z 5) 24 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_504 : span (Z 5) 24 504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_528 : span (Z 5) 24 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_552 : span (Z 5) 24 552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_576 : span (Z 5) 5 576 = true := by decide +kernel

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

private theorem z5_a17 : span (Z 5) 432 0 = true :=
  span_join (f := Z 5) (a := 408) (o := 0) (b := 24) z5_a16 z5_408

private theorem z5_a18 : span (Z 5) 456 0 = true :=
  span_join (f := Z 5) (a := 432) (o := 0) (b := 24) z5_a17 z5_432

private theorem z5_a19 : span (Z 5) 480 0 = true :=
  span_join (f := Z 5) (a := 456) (o := 0) (b := 24) z5_a18 z5_456

private theorem z5_a20 : span (Z 5) 504 0 = true :=
  span_join (f := Z 5) (a := 480) (o := 0) (b := 24) z5_a19 z5_480

private theorem z5_a21 : span (Z 5) 528 0 = true :=
  span_join (f := Z 5) (a := 504) (o := 0) (b := 24) z5_a20 z5_504

private theorem z5_a22 : span (Z 5) 552 0 = true :=
  span_join (f := Z 5) (a := 528) (o := 0) (b := 24) z5_a21 z5_528

private theorem z5_a23 : span (Z 5) 576 0 = true :=
  span_join (f := Z 5) (a := 552) (o := 0) (b := 24) z5_a22 z5_552

private theorem z5_a24 : span (Z 5) 581 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 5) z5_a23 z5_576

private theorem z5 : span (Z 5) 581 0 = true := z5_a24

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
private theorem z6_288 : span (Z 6) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_312 : span (Z 6) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : span (Z 6) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_360 : span (Z 6) 23 360 = true := by decide +kernel

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

private theorem z6_a12 : span (Z 6) 312 0 = true :=
  span_join (f := Z 6) (a := 288) (o := 0) (b := 24) z6_a11 z6_288

private theorem z6_a13 : span (Z 6) 336 0 = true :=
  span_join (f := Z 6) (a := 312) (o := 0) (b := 24) z6_a12 z6_312

private theorem z6_a14 : span (Z 6) 360 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 24) z6_a13 z6_336

private theorem z6_a15 : span (Z 6) 383 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 23) z6_a14 z6_360

private theorem z6 : span (Z 6) 383 0 = true := z6_a15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 11 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 35 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 11) z7_0 z7_24

private theorem z7 : span (Z 7) 35 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12447

theorem PEqualNP.Outside.L_meta_12447 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12447.mainG PEqualNP.Outside.L_meta_12447.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12447.CG, PEqualNP.Outside.L_meta_12447.CG_mono, by
      have : PEqualNP.Outside.L_meta_12447.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12447.CG_eval⟩
