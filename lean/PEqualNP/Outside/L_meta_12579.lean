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
namespace PEqualNP.Outside.L_meta_12579

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 3, 7, 3, 9, 3, 11, 3, 13, 3, 15, 3, 17, 3, 19, 3, 21, 3, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 3, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 7, 7, 7, 7, 9, 7, 11, 7, 13, 7, 15, 7, 17, 7, 19, 7, 21, 7, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 3, 9, 9, 9, 7, 9, 9, 9, 11, 9, 13, 9, 15, 9, 17, 9, 19, 9, 21, 9, 23, 9, 25, 26, 27, 9, 29, 30, 31, 9, 9, 9, 35, 9, 37, 38, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 11, 7, 11, 9, 11, 11, 11, 13, 11, 15, 11, 17, 11, 19, 11, 21, 11, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 13, 13, 7, 13, 9, 13, 11, 13, 13, 13, 15, 13, 17, 13, 19, 13, 21, 13, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 15, 15, 15, 3, 15, 15, 15, 7, 15, 9, 15, 11, 15, 13, 15, 15, 15, 17, 15, 19, 15, 21, 15, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 17, 17, 17, 3, 17, 17, 17, 7, 17, 9, 17, 11, 17, 13, 17, 15, 17, 17, 17, 19, 17, 21, 17, 23, 17, 25, 26, 27, 17, 29, 30, 31, 17, 17, 17, 35, 17, 37, 38, 39, 17, 41, 17, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 58, 59, 17, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 19, 7, 19, 9, 19, 11, 19, 13, 19, 15, 19, 17, 19, 19, 19, 21, 19, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 21, 7, 21, 9, 21, 11, 21, 13, 21, 15, 21, 17, 21, 19, 21, 21, 21, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 23, 23, 23, 3, 23, 23, 23, 7, 23, 9, 23, 11, 23, 13, 23, 15, 23, 17, 23, 19, 23, 21, 23, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 25, 7, 25, 9, 25, 11, 25, 13, 25, 15, 25, 17, 25, 19, 25, 21, 25, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 26, 26, 7, 26, 9, 26, 11, 26, 13, 26, 15, 26, 17, 26, 19, 26, 21, 26, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 26, 26, 35, 26, 37, 38, 39, 26, 41, 26, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 27, 27, 7, 27, 9, 27, 11, 27, 13, 27, 15, 27, 17, 27, 19, 27, 21, 27, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 29, 7, 29, 9, 29, 11, 29, 13, 29, 15, 29, 17, 29, 19, 29, 21, 29, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 30, 7, 30, 9, 30, 11, 30, 13, 30, 15, 30, 17, 30, 19, 30, 21, 30, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 31, 7, 31, 9, 31, 11, 31, 13, 31, 15, 31, 17, 31, 19, 31, 21, 31, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 35, 7, 35, 9, 35, 11, 35, 13, 35, 15, 35, 17, 35, 19, 35, 21, 35, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 37, 7, 37, 9, 37, 11, 37, 13, 37, 15, 37, 17, 37, 19, 37, 21, 37, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 38, 7, 38, 9, 38, 11, 38, 13, 38, 15, 38, 17, 38, 19, 38, 21, 38, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 39, 7, 39, 9, 39, 11, 39, 13, 39, 15, 39, 17, 39, 19, 39, 21, 39, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 41, 7, 41, 9, 41, 11, 41, 13, 41, 15, 41, 17, 41, 19, 41, 21, 41, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 43, 43, 7, 43, 9, 43, 11, 43, 13, 43, 15, 43, 17, 43, 19, 43, 21, 43, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 45, 7, 45, 9, 45, 11, 45, 13, 45, 15, 45, 17, 45, 19, 45, 21, 45, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 46, 7, 46, 9, 46, 11, 46, 13, 46, 15, 46, 17, 46, 19, 46, 21, 46, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 47, 7, 47, 9, 47, 11, 47, 13, 47, 15, 47, 17, 47, 19, 47, 21, 47, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 49, 49, 7, 49, 9, 49, 11, 49, 13, 49, 15, 49, 17, 49, 19, 49, 21, 49, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 49, 49, 35, 49, 37, 38, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 51, 7, 51, 9, 51, 11, 51, 13, 51, 15, 51, 17, 51, 19, 51, 21, 51, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 53, 7, 53, 9, 53, 11, 53, 13, 53, 15, 53, 17, 53, 19, 53, 21, 53, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 54, 7, 54, 9, 54, 11, 54, 13, 54, 15, 54, 17, 54, 19, 54, 21, 54, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 55, 7, 55, 9, 55, 11, 55, 13, 55, 15, 55, 17, 55, 19, 55, 21, 55, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 57, 7, 57, 9, 57, 11, 57, 13, 57, 15, 57, 17, 57, 19, 57, 21, 57, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 58, 58, 7, 58, 9, 58, 11, 58, 13, 58, 15, 58, 17, 58, 19, 58, 21, 58, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 41, 58, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 59, 59, 7, 59, 9, 59, 11, 59, 13, 59, 15, 59, 17, 59, 19, 59, 21, 59, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 61, 7, 61, 9, 61, 11, 61, 13, 61, 15, 61, 17, 61, 19, 61, 21, 61, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 62, 7, 62, 9, 62, 11, 62, 13, 62, 15, 62, 17, 62, 19, 62, 21, 62, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115151711555577111515171155557711151517115555770000000000000000111515171155557711151517115555771115151711555577000000000000000011151517115555771115151711555577111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557711151517115555771115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577111515171155557711151517115555770000000000000000111515171155557700000000000000000000000000000000000000000000000011151517115555771115151711555577111515171155557700000000000000001115151711555577111515171155557711151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000000000000000000000000000000000001115151711555577000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88000000000000000000000000000000000000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa880000000000000000eeeaeae8eeaaaa88000000000000000000000000000000000000000000000000eeeaeae8eeaaaa88000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88eeeaeae8eeaaaa88

def cMZZ : Nat := 0x1115151711555577000000000000000000000000000000000000000000000000111515171155557700000000000000000000000000000000000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000000000000000000000000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000000000000000000000000000000000001115151711555577000000000000000011151517115555771115151711555577111515171155557700000000000000000000000000000000000000000000000011151517115555770000000000000000000000000000000000000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577000000000000000011151517115555770000000000000000111515171155557700000000000000001115151711555577111515171155557711151517115555770000000000000000111515171155557711151517115555771115151711555577

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
  | 2 => 3
  | 3 => 49
  | 4 => 261
  | 5 => 463
  | 6 => 275
  | 7 => 27
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x5e63b5a1321c4a132caf5fa6
  | 3, 0 => 0xf505868ef05c1f6fecc09a46d999a9f3d33a4d39cf83be7acb1b8f2db0cdd5adada0ae74a9e254e6a69984a6a485eb109d6839a598da441f8f4db6ba7d2c62dc721806fb6f0c62b96df91fd66df710e56b5510a5689f658f605663535d60b2f85d4644375a1cfaa95979495058b3913f5679f04552ddbb224ce4960541388c053d23c31c38493f2836245494353fb61e2495057a22691e1e2162c4d7207d7d8d1f5dcc8c1d535da81844a7ee11d3a2170c984a4a0979811804bd82420330270202a67dd3
  | 4, 0 => 0x208a651d203c97cd1fba5cdc1fa878251e9c566b1ca1a07c1c3227eb1bfb93cf1bfb88591b97fe431b92cd611b8e2da01a582570192136771908ef0e18f7cba218e9617c185eafd0174455b61605186f15b6130c15a85b1615762bb11500406113cdbd3f13c48acd1384dafd136a4bbc12abebd112672584123a772711bdba131170b77010cc972a10be2aba10af056010a930de1042e9bd10382e7a0f8a1a560f4955a60f382bd10c883ac80c1a5e100b4deac10ae2d9ac0ab0b71409e346a209698b39084e714405d1feed05b0707205aba1c9057e408c054895230544e83a04da5ab104b24a06041fc0870391f4eb02eef35b01194da500e35b9700812e2c
  | 4, 1 => 0x4cf76b754b571dd24ae0ee07488d67aa47f01103479a073247834dc5473f79e2470ae82246dd0f3846dae6be463a1e924613215b45783cf04468e7e24403cc2c43ffb7f94313e5a3416fba7a410f28894011e0853f6ab3bf3ed9870c3c2959323be2ba9e381a283c37969cd337398c6d36d9ce3d362454943504b107348544ec343275de33df37ca33cdf8bc33bc98563372176b328fec07326c06e53208ae0131faa82330267cc23017cd073006c7e62ef3d80c2e6e4d652cc73e772c0e3f852aece1662996cfea29299b002767c9e326bb1e1a267ae89125f0914525dab46d255ce46f24d2bb00244baa132346d3cd22db669d21edde8b219d53e12162c4d7
  | 4, 2 => 0x7f32c59f7f278d257ef43df77e1d73407dbd446a7d3060a27b0b169a7927910578ce274c7828265176a6781f76455f97751441927413b86373c686ac724554386fa353f86f505ca36e9505476e8bb9b56df710e56b5510a56ad7dc126a44029769062c6068a2d37c663f4dc26523a6c66357740662eb586362beac4b61f1c44c61dfc35260a6dee7605653846031ef645ea616065e6338ba5d9d5c3a5c74d9e85bd209e45b600dd85a892ec058b3913f57f49d3a57bded0757b5031257742b63573f17c2570336fa56d50f0c560154165353354d533939bd523223be511ddfc4503fd5974ffa5eed4fe2e2554fcef3644f7813e84e61314a4dde7b314d1958fd
  | 4, 3 => 0xe7968c94e5af7622e598026be41304ffe13b303ddefdce22def78806dceab57dd9a021ccd8c7c800d5426752d0cc1200ccde07a6ca82d143c79f62a8c73bc929c6cbdee7c63790eac4fd6268c4ef617ec2ac4e24c0172996bf6dece5be8cf8e9be8b580ebd7999d7bb126a65b8802faab6993d11b5663a05b2eec6b5b25be302af00a4fdae3aececa9694801a78e7962a65fbef7a13757eca058ba399cd9733d990d804298c42b11982a6e6a96b7325a9567aa2592c326df9282cdb0920dcac5907dd5659063adf68ebfa0568e633ced8c441d338c4239828a4246d789ed5ac8893fc01c8823271d87f4b33a87882c17866d8fca8590f028826b41ec80170328
  | 4, 4 => 0xfd7ef68af946739ff2370dcdf155d121ece92632
  | 5, 0 => 0x105c26c31042e9bd103d59360fc8dd4d0fb3ddf60f4955a60f358e210f10fae20ec93c0c0eac65b60e651e3b0d4024900d3043e70d1fc7a40cf1f5c10c6a132f0bf6922c0beeac210ba6b2f50b1ad72e0b14980b0b0221ac0aed95b709bf53c208cdf5d10858c7530819f3a307d73b3807b9ccd907583f1e0710b6fb070aa62606f9e11806c6d1b306978e3e067e18a8063cf2c40616912e06101e65056bab350557d8200548952305399b57051795b605070f5a04d36899049c9f60045ce4970433635703b7aa7503892d28035bdcf903374908028fcf370271e255025d2292021bfcae020e0cac02002c8901ffda3f00e7862400affdd0005f3870001a3ad4
  | 5, 1 => 0x238f5a742346d3cd227311e62272ed7322069ca92193679920f56fa920949901209496a420935c64207f84592043a391203003801f24b6671ee18b311ebf714e1e3897851de5a6931d8e50211b9b04d41b97fe431b07783a1a84be1a1a5e4c5b1a0e19b1199dd6f41929fbeb19234eec18e9617c185356881833a9d617fdef30179f9a4e1784a99d176d378a174455b616b34c4915f88630159e85481500406114e6a2ff143e35bb14275a8414215a9e1414549b136df2d3135a7dfb13343c901323b10012fa820812ceb65412abebd112a920501279615812162e3d11834a42117ffa4f11307d9a112f95ad10f11a5110c5ace910c3ba5c1099c617105f6b9a
  | 5, 2 => 0x3b0caef63a7b63d23a51cff03a1d03aa39df44a83989532f39455ba238f7480d38aaa534385bd20737d697ae37a08cbc3797cd453756ef013726395b36b80c1336930745368f54bd36653b4c35aaa34435952b0035177da534cbe65b348f2ff133dfc59633cc57023386bfdc332961fb32baf37132b1c0ff32903d61327bd169326c06e53208ae01312566da3052eeff2fc29c2a2fab60ec2f008e5f2e4f23b22ddfcb472dd49d322d8c41322cfd8e772ccd63352c0842832c02d6fe2b6863fe2ac9c3042a43e6cd29e38f7e2996c01b2989fd89295c9f052929606a27ccb48327b64e0c279ac7e12797b37b2752ceb5269cef58252cb052244d9ba8239098cc
  | 5, 3 => 0x59be41fc585691ac5812dd4f57a3a984579371345763b3e4573f17c256062cad55c40390550dbf73547fcc0e53f1e73953df6a0953c089d253bd748d5382b36e53727b1e5353354d523f230551c51cde4f1c6bcd4ed15cbf4dea3fd24db804664d223c5c4d1ef1194cab35bf4c6a8e474c37c7484b571dd24ad68d794ac068bc4a6c43ce48febd8d48f1b67a48cc657548c463614816d13247f926b947e0e74847834dc54759d65b46fdb10144ddc7774468e7e243bff132436a863b42d185cb416892e840f3f4b940a79e514098aaa23fdad1f73fafccc43ec2f3d73e9c59e83def257c3ddbed4c3da0a5453d6651b83d06f3433c82aed93c05f7ea3b8330f4
  | 5, 4 => 0x7c737f827c43af4e7bbb432b7af32ea379eb9e8379d582de77d9e97b777b598376a6baeb768bb5c175f4284875756a6e75309fa374d2f3ec74c9acdf73fdfaed73cd942772fd32be72c0ec0672a9b498729fe2bc724cc5127133ca0170eca779702785456feed3ce6fdf811d6fa02b8e6efe34bc6ea892246e9bee336d61c3af6ccbb1636c068f2f6b96a4ed6b5510a56a0cddad698fa644698f8a4c694be67a692d3aab68b94ca568531352677bf0f36711f87466619c7865919f2f64f6523664a7ed45647267e963f47223639fdd0563561e1463218d306304956962f1025e61912bbd60fe48af5f9ecd7c5e00ecac5df00b155bc33a475b4e375c5aec6ff3
  | 5, 5 => 0xa2e08e63a2a0b4aaa2026a3f9ed411959e9ef8659e5fd9659e1139a59de174299d4823d39c0ec97e9ab0da769a0f25de99e95b8198856f8f98226dda9598995394776314940177c492d4076c9282cdb0926c7afe925e88eb912881f990b450f58e908a2a8e83117e8e633ced8e3dceff8e3d92d58dc7a7858d5627aa8c98c3398c3f25608c28587d8bb0ffc48a54ade48a4246d788d9f8bc88ad68a78831d30e8823271d88005954879009ae860c5f4a859536f1849dc3298486c84884818187846e6ac68410dcf883b50b2f82d8095e81c09c418142e4d480ccf98480ab888280ab0cc1804fcb737f3684667e861f367e4c85297d5f43c77c943e637c8a926c
  | 5, 6 => 0xdf045fc8deb7038cdceab57dd9ffa097d9bfe8aad889c238d71ffa86d7066db6d644b8d0d59e5ed5d3bf57ead0f7e9f6d03a29d4d0025494cf126b7fcdf2b698cd1ddffccbe36173cb5fad2ecb5bc83acb5a7812c98bc5d0c9492975c8cad827c6bf6321c52aafa5c4fd6268c4dc43eec4284ff9c1b9a284c0957c8dbf6e7ee7be8b580ebd7ba553bd4f5f2dbbc6a96fbb67f002ba963db8ba2acdffb8d53194b8802faab87c99eeb875d66db85e66f8b7671effb62992c9b454e057b32daba6b24fe80cb248c9dfb20a5497aeefe2b9aed86f02ae3aececad537196acc3febcac4290bbabb9d6a5ab88afc3aaa133f2a840c0e7a7aa514ca6e1e96ca2fa9224
  | 5, 7 => 0xfd4f93f2f7b4fe32f42f9d84f260ceeaf01bae81eeeefad1ebbc4241ea3960d5e60e9dd0e598026be3ea989ae320855de23356e1e0e6017be0d3120a
  | 6, 0 => 0x1dc844c21d3253d01d1fd6a01cb2e7b51c7be5f61ae74d8e1a60023a199ae0061762fe061662a8f314ec9f72149f12ec13b2236913acb065135a7dfb1341d4a31272adc71232231111c7380811573dc91139935010c5ace9108553350f8da61f0f44b1170e1e340e0dc71f560caaf2d20ca352170c11f2620b1cd2f30b14980b09e80ae80964fdc10955e54c088e5584084a2cae072f921306e111dc05c31b7004c39d8b041823dc03e4f7b203bbd06903b7aa7503aab6ba0392005d0337490802ccd0fd02c9bfc60285c839027c2aa4025d2292021bfcae019c3e9e0186381001256e6b011704450106cbf50102b1b700f3faf900d839dc00affdd00066a5f2
  | 6, 1 => 0x478cf1c0478bd687469fb05e45d4aafa45caff0345b3ec1944ddc77744339b3a4315ef75411a56123fcc22583eb5d7053e710c3a3e1360833e0a19763da1b6513d3e67843d0e00be3aaa46e03a7b63d239455ba2386d7860382801b637d697ae36a2304636437c5c360c1dfa3546fbc635245a8534d7118432f3827e32cff6e332c13b60326da74231f1232a31a52dcf31937fe92fab60ec2ed20bc62e614a5b2de859dc2c968aab2c316ef52c2c3ee52c0842832c02d6fe2b4e1ab32ad198542a3eb54629a94ddf279ac7e12752ceb527415943273077ac27166d0222ae7d942196fe43212f7068207f84591fe115e91fc43f9c1f0470271e1098811de5a693
  | 6, 2 => 0x74fa433c74eb21e274c9acdf73d54c29724cc5126fad05126f9e02f96d70dd2a6d2b89d46d096bba6cdd55016ccbb1636c3afebb6c068f2f6a869a7d6a27913469840b0c67df64fc6688906a655038fa654f3615639fdd05634f927562f1025e5ed9a8c95ed905ea5ec474fd5db7cfab5d41e45b5bc33a475a25690159f4bd8c593f062257d0f6c157a3a984577dff6c5708141c56ad99665696944156277f92557f91f75568c51454f19292546acb455458cd5053f1e7395382b36e53727b1e51edd53e50d076454f540e1f4f4ccbe14ed5a3884daed75d4d51498f4c5e581c4c1875f54adae0cb4a8fa10c4a83516b4a0d661b49eb79584990380a4816d132
  | 6, 3 => 0xc0f56ac9c0ada4dbbeed50b0be59fdbbbd7ba553bd700a1bbd6b3eb5bb67f002ba3234fab95c1b18b8a8e8ddb85e66f8b82f6768b601c1a8b46f05b8b454e057b2b0740cb14bfb47b0d92184b04d4a0dafcfd155af4f0a67ad2b0531ac60f1f4ac4290bbab73c378a844cc5fa7f77023a4ffce6fa3400d2ea060671da02701329ec6dfda997a966b9942c12b98befb2e968f7c909523ce0a949c34d1940177c492cc32679289960c91723e359117abda8e908a2a8e633ced8e3d92d58d68bc908a4246d788aeeb7e879009ae849ce9638410dcf8836b3a9681bd068580ccf9847d954cee7c8a926c7c78bbf07b9054a3788bb68b77706a3176046b5375bdd81b
  | 6, 4 => 0xffcfc14ff8ebcd7ef7b4fe32f42f9d84ee6d1ce4e5217b57e3ea989ae0d3120adf045fc8dbb9cdead9ffa097d5d7dd4bd536febed0fa396bcf56fdc0ccc999bacb4046d1c6a9fb22c69cb32d
  | 7, 0 => 0xf8ebcd7ec0f56ac9bd700a1bb2b0740cad2b0531a844cc5fa3400d2e9ec6dfda8a4246d77d954cee6f9e02f95d41e45b57d0f6c1577dff6c5382b36e4a0d661b3e0a1976386d7860382801b637d697ae3546fbc62c316ef51d3253d01cb2e7b50e1e340e0285c83901256e6b
  | 8, 0 => 0x5382b36e
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff000000ff000000f0f0000000000000cccc0000cccc0000aaaa0000aaaa0000555500005555000033330000333300000f0f0000ffff000000ff000000ff00000000ffffffff00000000f0f0f0f000000000cccccccc00000000aaaaaaaa0000000033333333000000000f0f0f0f0000000000000000
  | 0, 1 => 0xa0a0a0a0a0a0a0a05050505555555550505050505050505030303033333333300ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000f0f0f000f0f0f000f0f0f00000000000f000f00000000000aa00aa00aa00aa000f000f00ff00ff000f000f000f000f0000ffffffffffff0000ffff0000ffff
  | 0, 2 => 0x303030303030303030303030000000002a2a2a2aaaaaaaaa222222222222222211111111111111110fff0fffffffffff0fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f00ff00ff00ff000f000f00ff00ff000c0c0c0ccccccccc0a0a0a0aaaaaaaaa
  | 0, 3 => 0x555555550000000055550000555500005500ff005500ff0050f050f0000000005050f0f05050f0f050505050000000004c4c4c4ccccccccc4444cccc4444cccc44444444444444443f3f3f3fffffffff3f003f00ff00ff003333ffff3333ffff33333333ffffffff333333333333333333333333000000003333000033330000
  | 0, 4 => 0x888800008888000088008800880088008080808000000000777777777777777777777777000000007777000077770000770077007700770070707070000000005f5f5f5fffffffff5f5f5f5f5f5f5f5f5f5f0000ffff000055ff55ff55ff55ff55ff000055ff00005555ffff5555ffff55555555ffffffff5555555555555555
  | 0, 5 => 0xaaaaaa00aaaaaa00aaaaa0a0aaaa0000aaaa8888aaaa8888aaaa0000aaaa0000aaa0aaa0aa00aa00aa00aa00aa00aa00aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a8a8a8a888888888a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a0000000000088888888888888888888888800000000
  | 0, 6 => 0xc0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c000c000c000c000c000c00000000000bbbbbbbbbbbbbbbbafafafafffffffffafafafafafafafafaf00af00ff00ff00aaffaaffaaffaaffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa00000000
  | 0, 7 => 0xcccccc00cccccc00ccccc8c8ccccc8c8ccccc8c8cccc8888ccccc0c0ccccc0c0ccccc0c0cccc0000cccc0000cccc0000ccc8ccc8cc88cc88ccc0ccc0cc00cc00cc88cc88cc88cc88cc00ff00cc00ff00cc00cc00cc00cc00cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c888888888c0f0c0f0c0f0c0f0c0f0c0f000000000
  | 0, 8 => 0xeaeaaaaaaaaaaaaae0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0e0e000000000ddddddddddddddddcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcf0000ffff0000ccffccffccffccffccff0000ccff0000ccccffffccccffffcccccccccccccccccccccccccc00cc00ccccccccc0c0c0c0cccccccc88888888cccccccc00000000
  | 0, 9 => 0xeeee0000eeee0000eeeceeeceecceecceee0eee0ee00ee00eecceecceecceecceecccccceecccccceeaaaaaaeeaaaaaaeeaa0000eeaa0000ee00ee00ee00ee00ee00aa00ee00aa00ececececececececececececccccccccececccccececccccececcccccccccccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaeaea00000000
  | 0, 10 => 0xf0f0000000000000f0e0f0e000000000f0c0f0c000000000f0a0f0a0f0a0f0a0f0a0f0a000000000f000f000f000f000f000f00000000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeeeecceeeeeecceeeeececeeeecccceeeecccceeeecccceeeecccccccccccceeeeaaaaeeeeaaaa
  | 0, 11 => 0xf0f0f0f0c000c000f0f0f0f0c0000000f0f0f0f0a0a0a0a0f0f0f0f0a0a0a000f0f0f0f0a0a08080f0f0f0f0a000a000f0f0f0f0a0000000f0f0f0f080808080f0f0f0f030300000f0f0f0f000000000f0f0f000f0f0f000f0f0f00000000000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0c0c000000000f0f00000f0f00000
  | 0, 12 => 0xf1f1f1f100000000f0fff0ff00ff00fff0f0fffff0f0fffff0f0ffff00000000f0f0f0f0fffffffff0f0f0f0fff0fff0f0f0f0f0fcfcfcfcf0f0f0f0fafafafaf0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0a00000f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0c0c0c0c0
  | 0, 13 => 0xfaf0f0f0faf0f0f0faf0f0f0aa000000faaafaaafaaafaaafa00fa00aa00aa00f8f8f8f8f8f8f8f8f8f8f8f888888888f8f8f8f800000000f8f8f0f088880000f8f8f0f000000000f5f5f5f555555555f5f5f5f500000000f3f3f3f333333333f3f3f3f300000000f3f3f0f033330000f3f0f3f0f3f0f3f0f1f1f1f111111111
  | 0, 14 => 0xfc00fc00fc00fc00fc00fc00cc00cc00fafafafafafafafafafafafaaaaaaaaafafafafa00000000fafafaf0aaaaaa00fafaf0f0fafaf0f0fafaf0f0aaaa0000fafaf0f000000000fafaaaaafafaaaaafafaaaaaaaaaaaaafafa0000fafa0000faf8faf8aa88aa88faf0faf0faf0faf0faf0faf0aa00aa00faf0faf000000000
  | 0, 15 => 0xfefefefeeeeeeeeefefefefe00000000fefef0f0eeee0000fefe0000fefe0000fefaf0f0eeaa0000fef0fef0ee00ee00fe00fe00ee00ee00fcfcfcfcfcfcfcfcfcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcf0f0cccc0000fcfcccccccccccccfcf0fcf0fcf0fcf0fcf0fcf0cc00cc00fcf0f0f0cc000000
  | 1, 0 => 0xff00fff0ff00ff00ff00ffccff00ffccff00ff55ff00ff55ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff000000ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00ff00aa00ff00f000ff000000ff00aa00ff00aa00ff000000ff000000ff00000000000000
  | 1, 1 => 0xffaaf0a0ffaa0000ffaaaaaaffaaaaaaffaaaa00ffaaaa00ffaa0000ffaa0000ffa0ffa0ff00ff00ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff00ff88ff00ff50ff50ff00ff00ff33ff33ff33ff33ff33ff00ff33ff00ff330000ff330000ff11ff11ff11ff11ff0fff0fff0fff0fff0f0000ffff0000ff00ffffff00ffff
  | 1, 2 => 0xfff0f0f0f0f0f0f0fff0f0f000000000fff00000ff000000ffeeffeeffeeffeeffee0000ffee0000ffe0ffe0ff00ff00ffccffccffccffccffccccccffccccccffcc0000ffcc0000ffc8ffc8ff88ff88ffc0ffc0ff00ff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaa00000000ffaaff88ffaaff88ffaaff00ffaaff00
  | 1, 3 => 0xfffaf0f000000000fffa0000ffaa0000fff8fff8ff88ff88fff3f0f0ff330000fff0fff0fff0fff0fff0fff0ff80ff80fff0fff0ff00ff00fff0fff0f0f0f0f0fff0fff000000000fff0ffc0ff00ff00fff0ff00fff0ff00fff0ff00ff00ff00fff0faf0fff0faf0fff0faf0ff00aa00fff0f0f0fff0f0f0fff0f0f0ff000000
  | 1, 4 => 0xffff3333ffff3333ffff3030ffff0000ffff1111ffff1111ffff0f0fffffffffffff0f0fffff0f0fffff0000ffff0000ffff0000ffaa0000ffff0000f0f00000ffff000000000000fffcfffcffccffccfffafffafffafffafffafffaffaaffaafffafff0ffaaff00fffafaf0ffaaaa00fffaf0f0fffaf0f0fffaf0f0ffaa0000
  | 1, 5 => 0xffffc0c0ffff0000ffffc000ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaa0ffffaa00ffffaa88ffffaa88ffffaa00ffffaa00ffffa8a8ffff8888ffffa0a0ffff0000ffffa000ffff0000ffff8888ffff8888ffff8888ffff0000ffff8800ffff8800ffff8080ffff0000ffff5555ffff5555ffff5050ffff0000
  | 1, 6 => 0xfffff8f8ffff8888fffff0f0fffff0f0fffff0f0ffffa000fffff0f0ffff8080fffff0f0ffff0000fffff0f000000000fffff0c0ffff0000fffff0a0ffff0000fffff000ffff0000ffffe0e0ffff0000ffffccccffffccccffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffc8c8ffff8888ffffc0c0ffffc0c0
  | 1, 7 => 0xffffffff11111111ffffffff0f0f0f0fffffffff05050505ffffffff03030303ffffffff00000000fffffff0ffffff00fffffff000000000ffffffccffffffccffffffaaffffffaaffffff00ffffff00fffffcfcfffffcfcfffffcfcffffccccfffffafaffffaaaafffffaf0ffffaa00fffffaf0ffff0000fffffa00ffffaa00
  | 1, 8 => 0xfffffffff0f0f0f0ffffffffeeeeeeeeffffffffccccccccffffffffcc000000ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaaaa00ffffffffaaaa0000ffffffffaa88aa88ffffffffa0a0a0a0ffffffffa000a000ffffffff88888888ffffffff88008800ffffffff80808080ffffffff55555555ffffffff33333333
  | 1, 9 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffff0000ffffffffffaaffaaffffffffff00ff00ffffffffff00aa00ffffffffff000000fffffffffcfcfcfcfffffffffafafafa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x13052190e809c321d0908643
  | 3, 0, 0 => 0x9843144644afce5086449848108644b5cf5086448e38508644bb4c108644b5ce4f2644bc4c108644b5c9908644b8ce508644abc3122844a54a922844a1d0108644b7cf508644bb3c10864498210c85f4
  | 3, 0, 1 => 0xb34a908644812d944644a54c908644b5ce508644b64e908644bb2d93484480ba908644b94e508644afce522844b5a7508644b5c31228448ead908644863ed08644a54e4fa644b5ce53c644b2ce4f6644
  | 3, 0, 2 => 0xb5ce52a644b5ca908644a54312a914b5ce54464480ad9486449e43108644bd4c108644a04a508644bb4c908644b5cd908644b5d18f0644b5c5d08644a0210c85a4b5ce5228449cbf508644b5cc908644
  | 3, 0, 3 => 0xa048108644
  | 4, 0, 0 => 0xb5c316c9c322d7618b6511916ecb6421d0c8b7a96ad908645a53e96c84322d0218c6421916950c5b270c8b5d902d908645a54f5b484322c5218b6421914016b421902694aa1ad908645a6c316c84322dae6f0c421916950c48a3108b4a9cb1922845
  | 4, 0, 1 => 0xa54e55a84322d2618b6421916d73980a10c8b66862d908645b5c316ca3322c316c9f421916953f86210c8b76a54c108645a54316c95322d7e730c421916950c5b28cc8b4a5b210c8495a5431c09c322c316c8642191694b64219046b0c5b210c8435
  | 4, 0, 2 => 0xbddae7284322d2a18ae421916d70c76210c8b92bb4c508645ab4316c84322db618ba421916950c6d29cc8b4a8636908645b5ce5086409adae72c2421916953946210c8b6b862d92a645a5431b284322d2a1891421516e90c5b1ecc8b4a9ca10e4645
  | 4, 0, 3 => 0xa52d93875322d2a42b6421916f71d63210c8b4a80b8508645a5431d0a2322dae7303421916cf395b210c8b96b74e508645a53e56c84322d6618b6421916952074210c8b6b9ca10c8285b5ce5087a322dae18da421916950c71a10c8b6eb5ce508645
  | 4, 0, 4 => 0xa54316c94322deeecc64d2116d73942190a8b6b92ad908645a54616c84322d02390c421916d7394219080b6ba243108645a54316c641cadead739421916bf4a9ca10c8b4a92ad908645a54317684322dea02b6421916b30c70210c8a00bb4c108644
  | 4, 0, 5 => 0xa52d92e84322d3a18b642191618fc5b210c8b5e862d908645afce5086e322d2a18b6499916390c5b210c8b6b86210dc645b2cc21884322dda04b6421916390c61a10c8b4aa1ba108645812d908642e2d2a18843205967d395b210c8b4a9cb5108645
  | 4, 0, 6 => 0xa54396c84322dae4ac6421916d90c5c210c8b4a8636108645b5c31d684322d2a18b63c9916950c5b1f8c8b0c5b210c8455a54e56c9c322d5618b8421916d73954a10c8b7b8131944645acad90875322802bf39421912d739421900cb8fb5ce508645
  | 4, 0, 7 => 0xa54316e84322d2a18e7421916570c5b210c8b5b862d908645aa4316c84322d6218b6421916af0c5b210c8b4a92ad922845a54ca1884322ce56c9f421916d74a8624508b68862d908645a5431ae84322d8618b6421916d73986210c8b6b9ca10c8105
  | 4, 0, 8 => 0xa54656c84322d2a40b6511916e10c5b210c8b6b86245086e5a5431c284322d2a18b647a116b3395b210c8b4a86ad908645b5ce55484322dae7284321816531c5b210c8b558636908645b5c31ce84322d2a18f748a116d73976210c8b6b9ca10c85a5
  | 4, 0, 9 => 0xb5ce65284322d2a72ce421916951a5b210c8b65862d8f6645a543108641e2d2a36ec421916d76b9ca10c8b6ba24e508645b5c3108640aadae32b6421916951b5b254c8a00b5c3122844c9d2a6684322d2a18cf42191695195b29cc8b6b8638508645
  | 4, 0, 10 => 0xb5d767284322dae72a742191694e1421d4c8b6f862d9086450052a6484322002d739421912950c5b2105ab4a9cbd1086459cc716c84322dae7284371916d70c421e0c8b6b9cbdd08645b34311884322c313e8c421916950c6f210c8b4a8625518645
  | 4, 0, 11 => 0xa5431d484322d6e72b6421916e96b9ca10c8b579cad908645a54556c84322d2a1884381916ed305b210c8b4a8da10dc6458fc316c84322c316ca24f9916950c4219090b7696ad908645b5ce5086428adae18b63e991602b642190beb5da54c908645
  | 4, 0, 12 => 0xbc4056c84322dda5d0142191694b64219cc8b6b862d908645b5cba1884322c316c88421916950c5b210c8b4a9cb8508645a54317c84322d2a5d0c421916d73942190bcb11862d908645a5431a484322d6604b6421916a50c5b210c8b6b86210c83a5
  | 4, 0, 13 => 0xa52d93a84322d2a18b648a11619015b288c8b4a863ddd8a75904056c84322d2a18b9421916950c78210c8b6b9ca10f0645a52d908641aadee02c6521916950c76254c8b769831908645bb5ae7284322d5e36b6421916ed015b210c8b558cad908645
  | 4, 0, 14 => 0xbb4c20284322d2a1eb6421916d7395b210c8b4a862f108645b5cc21884322802d73942101295045b210c8b6b8624508645a54c21884322dad6c84320896d73976a10c8b0c5b210c8255b5ce50880322dae18ec53a116950c4a9b8c8b6b862d922845
  | 4, 0, 15 => 0x5b210c825112dda3cb6421916cf0c5b210c8ab64fa6108645a5431a084322d4218b6421916d70c56a10c8b4a8623108645a54316c641c2dae7284320c94016b9c99064969862d908645aec31d084322dae72f842191695325b210c8b4a98210c85a5
  | 4, 1, 0 => 0x14a862d934845b5ce66084322d7e4ab6421916950c5b290c8b4a862d936645
  | 5, 0, 0 => 0xa54316c843214dad70c632d908646c5d2a18b642191a950c5b210f8646c6d2a18b642191af74a86210c8176a54316c8440991a950c5b2c108646a54316c8437991b114a9031908646bdd2a18d142191acb5d862d908646bdd2a18e142191af74a8630108646bdd2a18ba42191af75963210ea646
  | 5, 0, 1 => 0xb9d2a18b642191af75f862d908646b1d2a18b642191ad70c5b2c108646b5c316c8437991b234a862d908646a54316c8432051ad74a863b108646abc316c84321518014a862d938645a5431eab642191b114a8631944646bdc318c8432129af74a8cad908646a54316c8432065af71c63210c85a6
  | 5, 0, 2 => 0xa54316c8b42191afd4a862d908646bdd296c9842191ae76b862d908646a54ee18b642191a950c5b210c8446a5431d8b653a11ab34a862d908646a54316c9c42191a950c6330508646bdd2a18c63f191aed01632d908646a54316c84320d1b1b6b862d908646bddae953942191a950c5c210c8516
  | 5, 0, 3 => 0xa54316ca5421918010c5b27d08645a54316c8436991b156b8631908646a54317ab6421918014a862d92a645b5cee18b6421918010c4219050255ca52a76b642191b134a8631908646a54316c843207daf74a8731908646c152a18c642191b274a8631908646a5431eeec42191a950c5b210cc646
  | 5, 0, 4 => 0xbdd2a18ca42191af74a85b1908646a54316c95421918014a8636508645a543212b642191a950c5b210c8616bdd2a728437191a950c5b210c8526bdd2a18bf42191af7548631908646a54320cb642191a950c5b210d2646a54316c8432155af7578631908646a54e5dab642191a950c742d908646
  | 5, 0, 5 => 0xae52a18b642191a950c5b259086460052a7284320a14016b863b108645bdd2a18c442191a950c7f319086460052a72b6421014014a8636908645b5c316c8432155a18b653a7d08646c452a18e942191af72b8631908646a54316c9142191a952d862d908646bdd2a630c42191b09558631908646
  | 5, 0, 6 => 0xa54320eb642191a950c5b2bd08646a54316cb142191af77698c05086460056618b6421916950c5b288c85c6a54e56cb642191af74a86b1908646bdd2a18df42191a950c5b210c84e6a54316c8432071af7298e31908646005eed739421916f7538631908646a54c218b642191a95205b210c85c6
  | 5, 0, 7 => 0xa54318cb648a118014a92ad908645b2d2a72b642191af75f8631908646b5c316caf42191a950c5b210c80d6bdd2a32c653991b2b4a862d908646a54956c8437191a951c862d908646bdd2a32c642191af74a9031944646b5d2a188437191a9539922d908646a54316c8432119a950c6d210c8516
  | 5, 0, 8 => 0x52a72b6320c96950c772d908646a54316c8432045af74a8d31908646a54316c8742191a950c5b2d108646a54e56c843216da95396321100646a5431ee8437191afd4a8631908646a54316c8432061af74a6326108646a5d2a18b642191a950c5b210d4646a5431848440191a9f4a862d908646
  | 5, 0, 9 => 0x47218b6421914016b86210dc645c252a18db42191a9519862d908646c252a18b842191a950c80ad908646c6d2a18bd42191a95395b210c8326a5431aac642191a18c65b210c8256a54ba190142191af74a8431908646a5431feb642191a950c6329508646bdd2a18e242191af74a63210ec646
  | 5, 0, 10 => 0xa54316c8c42191a950c5b210c81b6a54316c84320bdaaf4a862d9086460052a1884200a16950c70a10c85a6a54316c8439191a950c5d210c85a6a54c218c642191ad70c80ad908646a54316c843218da950c6ead908646a54316c843204da950c612d908646b5d2a730c42191a950c5b2b108646
  | 5, 0, 11 => 0xb5c316c8432021a950c5b210c8286b5ce58cb642191af7418e43108646a543198c642191aed4a922d908646a54316c843d191a95395b2c108646bdd298c84320f5a95015b210c85a6bdd2a18b642191a950c74b9d08646a54316c843215daf74a89b1908646a54316c9842191a950c79ad908646
  | 5, 0, 12 => 0xbdc318ca24f991b194a8631908646cbd2a18b642191af74a8630508646bdd2a18c942191ad70c81ad908646c552a18c242191ad70c5b210c8286a8d2a18b642191af74a8638108646a54316c8432075ad70c5b210f4646bdc058c843217da950c5b210c85d6b75ae18b642191a950c5b210c8306
  | 5, 0, 13 => 0xa54316c8432029ad70c5b210c84060052a18b6200c96950c6e2d908646004316c84320216950c5b210c8546a54316cb542191af56b862d9086460055e18b6421916bf4a862d908646bdd2a2ac642191a950c5b210c8406005ae730c421916f54a862d908646a54316c8432091a9535862d908646
  | 5, 0, 14 => 0xc7d2a18b6421918014a8638508645a54318c8c42191a950c78ad908646a5431a8b642191af7598131908646bfd2a18c642191a994a862d908646a54a602b642191af75a8631908646bddda38c642191a950c5b210c8476b5c316c84321518014a8639d08645a546d8cb6421918014a8619064285
  | 5, 0, 15 => 0xbdde202c642191a950c6dad908646b5c316c8432019af76b8631908646c7dae18b642191a950c5b210c84d60052a32b6421916f74a97c3108646a54316c843f991af74a8631942646a54e56caf42191a950c5b210c8066a54316c84320fda950c72ad908646bdd2a48c64e191af74a8631908646
  | 5, 1, 0 => 0xcc52a18b642191a9520632d908646a54c2190142191af74a862f508646a543218b642191af76b9dc3108646a54314a8c42191a950c5b210c8106a54319ab642191a95195b210c8516a54318c843212da950c5b210c8586bad2a18b642191af77680b1908646bdd5632c642191acf0c632d908646
  | 5, 1, 1 => 0xa5431d8b642191a950c5b210c85a6bb43202b64219180000b5ce508644bdd6648c642191a9502632d908646b152a18b642191a9539612d908646a54b218b642191a18b64219050256a54316c84320b1a950c632d944646b5c316c8432041a950c5b210c8566a54316c8432031af74a86210c83b6
  | 5, 1, 2 => 0xa54316ca042191ad70c5b210c81a6c1d2a18c642191af70c80b1944646a54318cb842191a95378631908646bdd2a18c842191ad70c762d908646b5c316c8432169af74a8631508646a54e56c843d191af72080b1908646c2d2a18c642191a950c6d2d908646bdd2a18b342191a950c5b210c8336
  | 5, 1, 3 => 0xa543200b642191af70c63288f4646a54316c84320b9a950c5b210d0646bdd2a188438991a950c5b210c8126bbd2a18b642191af74a8631922846a54316c84320d9a950c74ad908646bdd2a188d42191ac94a862d908646bb4316c843d191a9510862d908646004316c8432041618b6421e8c85c6
  | 5, 1, 4 => 0xa54316c8432009a950c7bad908646a54319cb642191a951e862d908646bdc318c8432095a9529862d94e646a54a618b642191ad76b862d908646c052a18b642191800b64219034105bdd2a18c742191a950c69b1908646b052a18b642191a950c5b210c8046a549e18b642191ad74a862d908646
  | 5, 1, 5 => 0xa54316c843b991a950c5b210c8006b5c316c8437191a950c6d319086460052a18b64219170f4a8631908646a54316c8942191ad70c7bad9086460052a5d0c421916950c6cb1908646a54316c8437191a950c5b21104646a54e218b642191a950c632d92a646a5431eeb653991af70c4fa3908646
  | 5, 1, 6 => 0xa54316ca732145a950c5b210c8516ca52a18bd421918017680ad908645a54316c8432089ad70c5b29d08646b5daa18c642191a491c862d908646aed2a18b642191a95345b2bd08646005ae18b6421916f76b9cb1908646a54316ca742191a950c5b21108646a54316c9242191ad70c7631908646
  | 5, 1, 7 => 0xbdd2a18c6320e1a95395b210c85a6ba5ae18b642191afb4a8631908646a543214b642191a950c6021100646b5ce618b642191ae94a862d908646c752a18b642191a95295b210ea646a54317a8432181a9528862d908646005ad6c84320696d54a9dc3108646b5c316c8432145a950c5b210c85f6
  | 5, 1, 8 => 0xbc52a18b642191af70c6326508646a54316c8435991af7768f31908646bdd9e18c6421918014a862d922845bdb193e9842191a950c602d908646bdd2a18db42191b214a862d908646a54316c91421b98014a672d908645a54316c8432081a950c6b2d908646a54316c8432179a950c5b210e8646
  | 5, 1, 9 => 0x52a610c421916f74a8131908646a54c65d0c42191a950c5b210f0646bdd2a18c651191af74a8631948646a54316c84320f9b154a8630108646004316c84320957034a862d908646bb5ae18b642191af74a9031908646a54e652b642191af74a8631936646bb52a18b642191b254a98c3108646
  | 5, 1, 10 => 0xa54316c9532151a950c5b210c8506a54316c8432085a950c5b210c8016004310864140414010c5b21080105aec316c8432171a950c5b210c82a6bdd2a18c64d211abb4a9cad908646005ae72b6421916f34a8631908646a54316c84320dda950c6324108646be52a18c642191a9531862d908646
  | 5, 1, 11 => 0x52a18b6421014010c5b190641050052a188c421916950c76ad908646a54316c8432079af74a863192a646a54316c8432025a950c52a3908646a54316cab42191a950c5b210c83a6b3d2a18b642191a950c76210c8546a54316c843201da950c5b210c8056bddd98c843a191af7148631908646
  | 5, 1, 12 => 0x2950c5b2a108646a54316c84320c98014a862d8c8325a54e56c843c191a950c5b210c8646a54316c84320ada950c421b8c8546a54316c8a42191b0d4a862d9086460059e18b6421916950c5b2d908646a54316c8432131b334a862d908646a54314e8c421918014a86210c8285
  | 6, 0, 0 => 0xbdd2a18c642190c4f7bbb52a48c642191ef74a86319087a323dee950c53a39086470052a18b658210c8c00a54316c8437991af74a80b1908642d3dee950c5b210c8067bddba950c63210c8f7bbdd2a18c642191f1f7ba54316c84323d2a18ed75b1908647cb62a950c63210c8f7ba54318c843215dc017ba543180843235ee950c6326108647
  | 6, 0, 1 => 0xcbdee950c63210c8f7ba54318c843203de950c632d9086428bdee95238631908647cb5eedd0c63210c8f7ba8d2a18c642191ef74a8631908640ebdee950c63210c85d7bdd2a18c64219060f7ba54316ca942191ebb4a863196c84323dee950c63210c8287005ae18c65b210c8d7bb752a188437991e950c632d94e843238031b4a862d908646
  | 6, 0, 2 => 0xbf52a18c6421904ee00bdd2a18c6200c9af74a86319086414bdee950c63210c8547bdd2a18c65aa10c8e00a54316c8432155af74a862d90864083dee95128631908647a54e618c65b210c8f7ba54318c8432101ef74a8638908642d3dee950c63210c8247bddba953b86210c8f7ba54d618c642191c014a632d908640d3002953b862d908646
  | 6, 0, 3 => 0x5ee950c421004ed7ba54318c8432019ef74a8631908641fbe3ef74a8631908647bdd2a18b642190c0f4aa3c318cb642191ef74a863b16c84323dee950c5b210c85a7bdd2a18e663210c8f7ba54a602c642191ef74a863194c84323e52f74a862d908647bdd2a18c642190b2f7ba54318c8432029c017ba54c618843235ee950c63210e6647
  | 6, 0, 4 => 0xbdd2a32c642190a2f76a54318cb642191c017ea54318c84323002f74a6326108646bdd2a18c642190b0f7bbad2a18c642191ef74a914318c84323dee950c5b210c8277bdd2a18db63210c8f7ba545a18c642191c017ba54658c843235ee95378631908647bdd2a18c654a10c8f7ba54318c843f991ef74a864156c84323802950c5b2bd08646
  | 6, 0, 5 => 0xbdd2a18c64219016f7ba54b218c642191ef74a863190a84323dee950c7bad908647bdd2a18c64219058e00a543202b642191af74a863190864063dee9529862d908647cc5ee950c63210c8f7ba543218c642191ef74a863190864083dee950c5b210ea6470052a18c652a10c8c00bdd2a18e242191af74a6329d3084323dee950c66b1908647
  | 6, 0, 6 => 0xbdc318c843d190b8f7ba54318ca042191edd6aa54318c84323802950c5b210c82860052a18b6421e8c8d7ba54318caa42191ef74a863190864303802f74a862d908646bdd2a18c64219066f7ba54318c8436191ef74a863b18c84323dee950c63210c85a7bdd2a18b6421b8c8f7bbb43202c642191c017ba5430c83213b5eec54a8631908647
  | 6, 0, 7 => 0xbdd82950c63210c8f7ba54318cb242191ef74a863190864023dee95278631908647bddae950c63210c8f7ba543200c642191c014a862d908642035ee950c63210d0647bdd2a18c64219024f7bbbd2a18c642191ef74a863a58c84323deec94a8631908647bddda18c6421e8c8f7ba544218c642191c017b86319086408352a18f87b31908647
  | 6, 0, 8 => 0xbdd2a18c644a10c8f7ba54318c8437191e950c76b196c84323dee950c6321104647bdd2a710c63210c8f7ba54318c8432009ef74a863dd8c84323802f74a86210c8266bdd2a3d0c63210c8f4a863196c8440191ef74a863918c84323dee9529863194e647bdd2a530c63210c8f80bdd2a18c642191c017b63210c81a083002950c5b210c8546
  | 6, 0, 9 => 0xa54318cb65b210c8f7baed2a18c642191c017bb5c318c843235ee950c6329d08647bdd2a18c642210c8f7ba54318c843200def74a863192484323802950c63210c8286bdd2a18c6421dcc8f7ba54318c8432001ef74a86319086427bdee950c63210c80e70052a18c65b21080c00a54316c84320198017ba54318c843230031f4a862d908646
  | 6, 0, 10 => 0x52a18c65b19064d7ba543214c642191f1d7ba54318c84323e2a950c632d908647bdd2a52c6421d4c8e00bdd2a18bd42191af74a944318c84323802950c5b210c8106bdd2a18eb63210c8f7ba54318c843217de950c7c3196c84323dee950c6329cc8517bdd2a18c642190a2e00bddda02c6421918010c63210c8100335ee491c8631908647
  | 6, 0, 11 => 0xc85ee950c63210c8f4a863198cb642191c0000862d90864082dee950c63239086470052a6f0c63210c8d7ba5431dec642191c014a863190864033002950c65a10c8066bdd2a18f263210c8f4a863196c84320c9ef74a863190883323802950c762d908646bdd2a18c6421d0c8e00a54316c8432169af74aa2c318c84323e36950c6321100647
  | 6, 0, 12 => 0x2950c5b210c8b7ba54c618c642191c014a862d9086e323637154a86319086470052a18f75b210c8d7ba54318c84320f9f037ba54318c843238029529862d908646bddda950c63210c8e00b5d2a18b642191af755a54318c84323deef14a8631908647c6d2a18c65b210c8f4a863196c8437991ef74a863198084323dee950c63210c8427
  | 6, 0, 13 => 0xbdd2a18c642200c8f7ba54318c843201def74a86319086402be4a950c80b1908647bdd2a190263210c8f7ba54318c8432141ef74a86319086400b802950c5b210c8516005ee18c64210020d7baec318c8432171ef74a904318c84323dee950c63210c841700576950c5b210c8c00005ae18b6421914014a862d94e843235ee950c63210c8377
  | 6, 0, 14 => 0xbdd2a18f863210c8f7bb5c318cb642191ef74a863190865323dee950c63270c85a7a54318cb64219050f86bdd2a18c642191ef74a863196c84323dee950c63210c84c7005ee950c6da10c8d99bdd2a18c642191c017ba54318c84203002f70c6319064106a543202c65b210c8f7ba5431dac642191ef74a86319086404bdee95488631908647
  | 6, 0, 15 => 0xbdd2a18c64219064f7ba54318c84320c5ef74a863194484323dee950c5b210c8557005ee950263210c8c00bdd2a18c6320c9a950c632d908642a3802f74a8631944646a54318cb64219080f7ba54318c8432191ef74a9dc316c84323802f74a9031908646bdd2a18c64219056f7ba5431b68432145ef74a863b508642ab802ed4a862d908646
  | 6, 1, 0 => 0x2950c5b19064b7ba54318c8435191c014a86210c827033002950c5b2d90864600002950c4219050a000052a18b6421016f74a86319086430b802950c76ad908646a54318c8440190c0f7ba54318c8b42191ef74a8631908641a3e46f74a8631908647c5dee950c63210c8f7bb2d7618c642191ef74a8632d8c84323deeb30c63210c85a7
  | 6, 1, 1 => 0x17ba54318c843206def74a864058c84323802950c5b210c8326
  | 7, 0, 0 => 0x5ee950c63210c8517005eebb4a8631908647005ee950c6329d0864700002f74a8631908646005ee9529863190864700002f70c63210c8106005ee950c632a908647005ee950c63210c860700002f74a862d908646005ee950c63210c85a7005ee950c63210c8107005ee950c63210c80670063ef74a8631908647005ee950c63210c8407005ee950c63210f4647005eedd4a8631908647
  | 7, 0, 1 => 0x5ee950c80b1908647005ee950c63210c832700002f74a86318c8326005ee950c7c31908647005ee950c632d90864700002f74a8631908406005ee950c76b1908647005ee950c632110064700000014a862d908645005eeed4a863190864700002950c63210c8066
  | 8, 0, 0 => 0x2f74a8631908646
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 1792), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 1792), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]

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
private theorem z2_0 : span (Z 2) 3 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 3 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_48 : span (Z 3) 1 48 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 49 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 1) z3_a1 z3_48

private theorem z3 : span (Z 3) 49 0 = true := z3_a2

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
private theorem z4_192 : span (Z 4) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_216 : span (Z 4) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_240 : span (Z 4) 21 240 = true := by decide +kernel

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

private theorem z4_a8 : span (Z 4) 216 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 24) z4_a7 z4_192

private theorem z4_a9 : span (Z 4) 240 0 = true :=
  span_join (f := Z 4) (a := 216) (o := 0) (b := 24) z4_a8 z4_216

private theorem z4_a10 : span (Z 4) 261 0 = true :=
  span_join (f := Z 4) (a := 240) (o := 0) (b := 21) z4_a9 z4_240

private theorem z4 : span (Z 4) 261 0 = true := z4_a10

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
private theorem z5_456 : span (Z 5) 7 456 = true := by decide +kernel

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

private theorem z5_a19 : span (Z 5) 463 0 = true :=
  span_join (f := Z 5) (a := 456) (o := 0) (b := 7) z5_a18 z5_456

private theorem z5 : span (Z 5) 463 0 = true := z5_a19

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
private theorem z6_264 : span (Z 6) 11 264 = true := by decide +kernel

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

private theorem z6_a11 : span (Z 6) 275 0 = true :=
  span_join (f := Z 6) (a := 264) (o := 0) (b := 11) z6_a10 z6_264

private theorem z6 : span (Z 6) 275 0 = true := z6_a11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 3 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 27 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 3) z7_0 z7_24

private theorem z7 : span (Z 7) 27 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [9, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12579

theorem PEqualNP.Outside.L_meta_12579 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004162184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12579.mainG PEqualNP.Outside.L_meta_12579.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12579.CG, PEqualNP.Outside.L_meta_12579.CG_mono, by
      have : PEqualNP.Outside.L_meta_12579.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12579.CG_eval⟩
