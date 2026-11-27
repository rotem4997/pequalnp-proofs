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
namespace PEqualNP.Outside.L_meta_12459

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 9, 9, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 9, 9, 19, 9, 21, 22, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 35, 9, 37, 38, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 9, 9, 51, 9, 53, 54, 55, 9, 57, 9, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 7, 19, 9, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 21, 7, 21, 9, 21, 11, 21, 13, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 7, 22, 9, 22, 11, 22, 13, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 35, 7, 35, 9, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 37, 37, 7, 37, 9, 37, 11, 37, 13, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 38, 38, 7, 38, 9, 38, 11, 38, 13, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f151715171517157f151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea80000000000000000000000000000000000000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea80000000000000000000000000000000000000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea80000000000000000000000000000000000000000000000000eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000eae8eae8eae8ea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80eae8eae8eae8ea80

def cMZZ : Nat := 0x151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f000000000000000000000000000000000000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f0000000000000000151715171517157f151715171517157f151715171517157f151715171517157f151715171517157f151715171517157f151715171517157f

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
  | 2 => 6
  | 3 => 35
  | 4 => 186
  | 5 => 484
  | 6 => 314
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x9451c4195bd09b6455117bec2c7682c106dda150067052a9
  | 3, 0 => 0xe81b3c65dee08d47d36bdec5d1e57123ce6fa609c00e4dfcb8421bb0b2d23b57a99f013aa4ccc8ca9a158a4e9451c4199265e4998a39d8537e7f77f5683e806a603859aa4f3acb4b460334094542bbda430d0b6140a2c3cb3b14e0c3335903513240eb982f18a1f82e7e25f22d6b4d912777a128257bc2ef11c52c200ffda3b00e78970b0ac9511c0a53a75d
  | 4, 0 => 0x2a0550a629d4c16228d9effe28c686402828ffd227b4e84427a1843c26f38fb52686d1d925ef66272598a1ae24f3169e24596ad723f1ba7b2131db1d2116aaa3201805c51ff1de871f5e5bef1f3134b71f04384b1eea221b1bd4d905194483e118981bac180e6f7016c9601615a998ec13d7c64d139ea6ab12f700351282ac6210f14e1e109e02cb0fecb7a60f9b48db0f019d140efd4adc0e14db390db47b6b0cdf87d60cc320500b08dcf50b029a3f0ac7da560a5882570a55c986095649cd0953ecb408ac20060888c392085b763407caed0b0520434805096f290506c98a04db3090044ca61c02e9dc7401a84e7001953d8c0154bb64011c6943004f829d
  | 4, 1 => 0x7321102572dad4b3706c63296fb3f5dc6f36426b6c84d80e6c80b9ca6c65d4706c5ecd886962f5fc68d2dd3e683e806a6429c281620ecaf062003bb75e7d589f5dfd757b5d79d4205b8a13ae58c9726a57c3de54575cf12856c815cd568b30095631432f56211c2e55b217ea5541a82b51460d7f4a22a06149568f1148ef0cf2478e28b94750b08c46f8bb2d4642fe734287a1a04030c1823f0062ab3eb5bf6d3d81b6033cf868a43c3ff1e63c02aab63a47f2813a40c7d13a1a5b103a120ec93901850638a0dea136fb5d6c35c65c70353ac6ee3477e5a0340cf3b233fb89c7334a82d63240eb983205a98a2e1c31c42d9d72bc2b967d2d2b9050f62b672d8e
  | 4, 2 => 0xfd7cf34ffd07525bfa2c2fecf86a48c4f625b95bf3c12e07f02488aaed25600ee566be84e0fc32dbe0c408fcde91eb45d904083dd1ac3f4dd0c7e222ce7c21d6cc6d4d6ccb5a750bc3f22dbfc2744415c00e4dfcbf446a52beaa97dabd50294eb203311eb1dc7de0a8200059a78c1b38a6fae78da6d2426ea4c44e8ea46dea7ba261341ca0355d299e3f649a9bffbd2397e85db89499033a946618fd943a38b792cbca918f3873188dd696308c53f1bf8b657d548878f8f7860a63e4841195ad8041fd267f4afb5f7e2548dc7e1daa037cd22ddc79791a1c7932767c770cb17376f0972574fed631
  | 5, 0 => 0xfd6e1000f9c00a60eba07b30e1355250d83ef290d81dacf0d6a2d8a0d69a3990d28af110d1c81350cabdb1f0c6014100c242e3b0bdb67e90bc11e2c0bc0ec920bb5b7920b797d740b49fe370b38e3c90afd36540ac01e9f0a5d412d0a55c98609e6e74f095fc7fd093ac4a3091ecd0208b8768a088eae100888c392087332ed085bc6ac084b377807fed19007fd69220772ea08074aa8370744c1f907346d7d06a6b51c0661301c0637877f061d49e80593f954057adc30050a8c3904e7d88e04b6d886049d800004520e620423395a03e3c4f503938f35029102b7026ecc6a026bccfb025e6b6502308e2e019c77ee0154bb64014f09f5013b874a00c870d4
  | 5, 1 => 0x20fb62d920f64761202660f41ff315981fa2d5be1f9673971f60ab2c1f0504cc1f00ad141ec206a91ec1f00b1e3c645c1dc04c7b1db3946f1d5f7c611d4b8b251d3ef1491cd40dcd1ca8b7881c731dca1c1aaf5a1c1166fd1beb6aa21be06a611b5428491b532f3b1b369d481aeaf6f61ac1555b1a4c0f851a139114199d1564194483e1191fbd85187eda02185ff3031844ddd617f53a4217ef256717afba3d1797b8c4177d90bd1700ea6e15b530b815af8559157c578515697bec154028be152525f514b4c93b148f30671480da8a146298b614383f65141a826e141a0d2f140677011376e54e135150b8125452021228ae0911b103ab1187e7d41074b20b
  | 5, 2 => 0x353d1ea33503991c3499b2da3427e4a9340656a732ae353f32882ab931a8c14630390bc92ff0981d2f37bfc22e7643452e051a822dc46acd2d7c3eb02d7aefde2d09a8c72cbe3b8e2cb21be82b72b40e2aae6e7d2aade3fc2a658d532a3a03152a0af7832a0550a629a96b7629995c922954ca242948058f28c9b8412892ad0f288c20152888b798283fabf6282e40d3281520d127e4645e27e009f0279aa387273b6a212738869226622046265ffbfa261d59a1252fc05c2502005424f0a6c52496a93c247bfca2244d616d24209d8423f2d4c623f1ba7b2399548b23415bf523030d6d22d9be902263177b21e1528221b81f20219b9ba22116aaa32105b0ba
  | 5, 3 => 0x4ef443954eb26e3f4dafb2c14d96854d4c33c1154bf0adfc4ad769544aa037174a8c1fdd4a248f4e49e465cb49e3e57c49549ab5490a9ae2490914b048fdfe2648c374e047d7a1f34798d8af478aa6584750edb8473113734687ec684638fa8545984cb8455d9600451053f744f3473844ea0f0c44d6b76344c1703843a25419439bbf4042ccb00842c74bc942bf611f42b4775640aada2440987d194030c1823fdf73a53f93f07c3f6a74913df2ea573d5230c03d0d39a53cf76c013cd613073b729d543abae07339c31f4d39c2533538fc912237f92b3a37b0403a378825793755c406374b3ed637392045372ddedf36e36f5936b75791367105ea35fb8fc2
  | 5, 4 => 0x6da86e6c6d4425f96ce88bd26ccf06406c99fc326b2b75a76a4b9bd569764bbe690e1f7468d2dd3e689f424e67f3b35967cb828667c5e73e66659267662055cd66042b7365ae800c65850e07658319b864493d1c63b2f3d5637e392b636526a16351310b62c68034620ecaf061fea35561ee224d61535cad60990e8f6088d4e85f9fa6f35f7f6b075eb2ba6e5e017d3a5dfd757b5d4614b45d260aa05ca924775c9912b85c523bde5b5a97195b198c2c59c32a105844d69e580d6eb557f7c4ab57e8d59157c3de54575cf1285548d193552fe0e9552f902653bbc9f853ab590e534ea9ee532e6ce052f990f65258bc4e5135505d50d0caac5098a2304f266a46
  | 5, 5 => 0x90a2f0e58fbca7d68f3873188df32cd28dd696308d96c0018d78dd178d7577908cfafb468cd6d8d18a2a262b8a09d37c88e0f2ca87f32ef587134dc984e00f5384dfc21983b2176882f3a59782436cd18124b05f8036591f7fc23c957f4afb5f7f34a1dc7f2d08727ef1201e7ec823667e66bdb57e3ee3aa7e048f7d7dbc54fb7c85f7d87bc67fcc7ab49b5778267c7177a59ce3776f56a57743fcd8771d650f7623aedc760879ac75d6861b75a2363374e022ef73892507732ac77d72fece4872c46f0572a8d9467202b7657191a68f712d6b5e70cb3a1370bd3a9e70819716706e8dd06f9e3ecd6f36426b6f015e556f0071ce6eb709a16e91bf1b6e180e1d
  | 5, 6 => 0xc5e9d837c4967ab2c3bf97a5c330b834c2ffbab7c28b773fc275f62ebfa9c0b1bbaaceb1b99ff416b91246d9b6c773a9b61b2e81b3af0c90b344ce48b1c6edc7b17213c4b13d09abb11fd31eb0bf7ca2afa4068baf0962cbae3606adaccd3b72a97a2ee1a8b1e3d4a858b39ba7457147a676c848a5ba1485a5b61b13a47f7279a46dea7ba34e6d8da2ee3ed7a2b1eb33a2a39b99a0d903eea00197a29f2d656e9f2154489e8e48e59e82e7f59e188d689dedfc969d7587379cdf376f9cde77b19ccdd6ac9a844ab19a03b59b99f7b8039950125c9928a31a984161f1981b576b97b97dbf9708c55595f385b695506f28954c0ba2927816f2923def1991b43559
  | 5, 7 => 0xfe87bdf2fd07525bf97f935ff86a48c4f3c12e07f341748ff1c4725cef73c1e7ef3a0ef0ee636e1aeca20135e9d80265e984d2b2e89a6fbee85054c9e5c7a63ae20b862fe1a00e7ce0c00a08e0b76170df00e961ded2b8bcdca4e6e7dc61f0e5da5f949fd99510e9d9080ca7d39f1bf1d332f4e2d23a005bd06e95f6d00ff6decbccfb46c9565508c7f47820c75005f7
  | 6, 0 => 0x1a413eb31a3c59bf185ff30317f4be2e179ce8c1177d356e1732aa7916c37a6315d44dfa156b9095150daf4f1506c25c14ad58d314a3811a1480da8a1445b7a8142ebf63140677011376e54e133282551320555b12f73efc12f2c2f812bf73a9124aadc011954dda100674310fa737ab0ebd5f220d3abd320d07454b0cee4cfe0cb1f0450c468fcc0bdb67e90b49fe370b334d780a64a4790a4a40d8085bc6ac0819ffc4073c49be069fc7640637877f05db1615059fa3d905837179051b162a04b6d8860335deff02c40bbe02b9f195025e6f210253775a0238649b01dbd8c701d59e4101b111720166ceea00d0852300cd13a000cc53e200c4bda20042103d
  | 6, 1 => 0x3a23aab1397e9039385d771f36bf9389367d51f3367105ea36299106353134b83520fd0f32de3a3832ae353f31a8c14631923db52ff0981d2f4fe0d52e3595952cbe3b8e2c7ccad22c085ed72be254512b3de2282ab66fa928c9b8412888b798281d68cc27e4645e27ad73d627a09503279d6a0927990f73271e94652663d25f2618652625f25aa025d03b4024fbf63524f0a6c52460ef8623f57cb723979ce22367c456235b92f022899c762263177b21e649ad21cda8f2216f4a6920da805b2073d8ae20286b752005bff21ec206a91ea0a2001de081b91db3946f1d97406f1c869e041c3f7d6b1be3faf71b67272e1ad578401aa567821a529f761a4c0f85
  | 6, 2 => 0x622850d4610c610760c914095fafaecb5f5c8eb05e96a2ba5e252a1f5d5faa7d5d4614b45a9cf9515a6955de5a25e464593f5a4258f9d08b57f7c4ab572f50c0568f2bea55f8ae615546d7ff548ffbfb53e759d352a3df7951c758825142ff294e73f48a4e1f8b774dc5de964d56e7d44d0582a64ca271654c884bef4c33c1154b9e72b14b5305784b35fe504aa1213e49b5826b4940f45e490a9ae248dc5561485c67e947311373471588f545e7ae4745a4f872458deaad451053f743e6497543a254194209e2b940aada2440a4203b4092c318407b73f53fcbf74a3f9df0fc3f211d333e5caadc3e4d70d03d9f04303c34b0003c198ab73ba0aabc3b8bd633
  | 6, 3 => 0x954c0ba293de7449923bb1219168cc0a8e27df418df32cd28dd696308d42a6508cd6d8d18bd2408a8acf210b87e0b0f2873ffbf88677ad8b84f38ce684e00f53822a4088814d588d7fe3a4687fce468d7f54406d7f4204757f2479747ef1201e7eaf31877e39ebb17e048f7d7de6408f7d0d99b17c547f557c4dcf2f7bc67fcc7b9d9669792e04ea771d650f76d423c576168a3575d6861b759edfd77389dcd2727f5c61720131517191a68f710a5d6170db032970120a676f6759a06e178d8f6ce109ba6c4d8e336ac88aff6a3484936a2563ab69d94a6468f8686568d5b4ba689f424e683fea8e67cb8286674d71cb67022804643569fa63108d3662cca40e
  | 6, 4 => 0xfd3dee88fba759ebf86a48c4f3aa8402f1c4725cf0e8d772edf7afa8e8cdeb7fe2defc4ae1a00e7cdd38b1a7db5d32d1db450c94da5f949fda118b08d6ebb89cd5966ed3d205ea49d1964a98cd6427eacc8d1e7acbffcf83c9f2079fc972ea33c7f47820c75302cdc6b45c60c5ec7f81c4967ab2c330b834c275f62ec133f0e0bbe5a0d7b9350c94b91dbd15b91d6c52b8a1910db7a9a624b73c861ab3144672b2a04a6bb0219d41b01a7291af0962cbab3ec9e4aa75c894a94b722ca8fe3023a7903045a52ef5eea2e32ec49cdf376f9ccdd6ac9b7601a59b43a0329950125c98878f069815c0d5
  | 7, 0 => 0xfd3dee88f1c4725ce2defc4acc8d1e7ac133f0e0bbe5a0d7a790304593de74498dd696308bd2408a7bc67fcc70db03296a2563ab58f9d08b51c758825142ff294d0582a6458deaad43e649753e4d70d02be254512663d25f2618652612f73efc0b49fe37051b162a02b9f19500cd13a0
  | 8, 0 => 0xf1c4725c
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff0000000000000000ffffffff00000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa0000000000ff00ff0000000000ff0000000000000000ffff000000000000ff00000000000000cccc000000000000aaaa0000000000005555000000000000333300000000000000ff0000000000000000
  | 0, 1 => 0xff00ff0000000000ff000000ff000000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff0000ff000000ffff000000000000f0f00000f0f00000555500005555000033330000333300000f0f00000f0f000000ff000000ff
  | 0, 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f000000000f000f00ff00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0505050505050505030303030303030300ffffff00ffffff00ffffff00ff000000ffffff0000000000ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff0000
  | 0, 3 => 0x505050505050505044cc44cc44cc44cc3f3f3f3f3f3f3f3f33333333ffffffff333333333333333333330000ffff0000333300003333000033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff0fff000000000f0fffff0f0fffff0f0f0f0f0f0fffff
  | 0, 4 => 0x8800880088008800808080808080808077777777777777775f5f5f5f5f5f5f5f55ff55ff55ff55ff55ff55ff55ff000055ff000055ff00005555ffff5555ffff55555555ffffffff555555555555ffff5555555555555555555555555555000055550000ffff00005555000055550000550055005500550050f050f050f050f0
  | 0, 5 => 0xaaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00ff00aa00ff00aa00aa00ff00ff00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a000000000a0a00000a0a000008888888888888888
  | 0, 6 => 0xaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa00000000aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000
  | 0, 7 => 0xcc00cc00cc00cc00cc00cc00cc000000cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaffaaff0000aaffaaff00000000aaaaffffaaaaffff
  | 0, 8 => 0xcccccccccccccc00ccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00ccccc8c8ccccc8c8cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88
  | 0, 9 => 0xeaeaeaeaeaea0000eaeaeaea00000000eaeaaaaaeaeaaaaaeaaaeaaaeaaaeaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0e0e0c0c0cfcccfcccfcccfcccdcdcdcdcdcdcdcdccccffffccccffffccccffff00000000ccccccccffffffffccccccccccccffffcccccccccccccfcfccccccccccccccccccccccccccccccc0
  | 0, 10 => 0xeeeeeeee00000000eeeeee00eeeeee00eeee0000eeee0000eecceecceecceecceecceecceecccccceecceecccccccccceecccccceecccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececececececececec0000ececececccccccccecececec00000000ececccccececcccceaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaa
  | 0, 11 => 0xf0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f00000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeee00eeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000
  | 0, 12 => 0xfafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0fa00fa00fa00fa00f8f8f8f8f8f8f0f0f8f8f8f8f8f80000f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f0fff0fff0fff0fff0fff0fff0ff0000f0fff0ff00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000
  | 0, 13 => 0xfcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafafaf0f0fafafafafafa0000fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0
  | 0, 14 => 0xff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00aa00ff00aa00ff000000ffff0000ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcfc00fcfcfcfcfcfccccc
  | 0, 15 => 0xff55ff55ff55ff00ff55ff55ff00ff00ff55ff00ff55ff00ff11ff11ff11ff11ff0fff0fff0fff0fff05ff05ff05ff05ff00ffffff00ffffff00ffffff00ff00ff00ff00ffffffffff00ff00ffffff00ff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00aa00ff00ff00ff000000
  | 1, 0 => 0xffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55
  | 1, 1 => 0xfff0ff00ff00ff00ffeeffeeffeeffeeffeeffeeffeeff00ffeeffee00000000ffecffecffecff00ffecffecff00ff00ffccffccffccffccffccffccffccff00ffccffccff00ff00ffccffccccccccccffccff00ffccff00ffccff00ff00ff00ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ff00ff00
  | 1, 2 => 0xfffcfffcfffcff00fffcfffcfffc0000fffcfffcff00ff00fffcfffc00000000fffcff00fffcff00fffafffafffafffafffafffafffa0000fffaff00fffaff00fff8fff8fff8ff00fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff00000fff0fff0ff00ff00fff0fff0f0f0f0f0fff0ff00fff0ff00
  | 1, 3 => 0xffff5555ffff5555ffff3333ffff3333ffff3300ffff3300ffff1111ffff1111ffff0fffffff0000ffff00ffffff00ffffff00ffffff0000ffff00ff00000000ffff0000ffffffffffff0000ffffff00ffff0000ffff0000ffff0000ff000000ffff0000eeee0000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffc
  | 1, 4 => 0xffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffc0c0ffffc0c0ffffc000ffffc000ffffaaffffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffa0a0ffffa0a0ffffa0a0ffff0000ffff55ffffff0000
  | 1, 5 => 0xfffffafafffffafafffffafafffffa00fffffafaffff0000fffff8f8ffff0000fffff0f0fffff0f0fffff0f0fffff000fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeeeeffff0000ffffee00ffffee00ffffeaeaffff0000ffffccccffffcccc
  | 1, 6 => 0xffffffff00ff00ffffffffff00ff0000ffffffff00000000fffffffcffff0000fffffff0ffffff00fffffff0ffff0000ffffffccffffffccffffffaaffffffaaffffff00ffffff00ffffff00ffffaa00ffffff00ffff0000ffffff00ff00ff00fffffcfcfffffcfcfffffcfcffff0000fffffcfc00000000fffffc00fffffc00
  | 1, 7 => 0xffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffc0c00000ffffffffaaaaaaaaffffffffaaaaaa00ffffffffaaaa0000ffffffffaa00aa00ffffffffa0a0a0a0ffffffffa000a000ffffffff80808080ffffffff55550000ffffffff55005500ffffffff33333333ffffffff33330000ffffffff03030303
  | 1, 8 => 0xffffffffff00ff00ffffffffff00cc00ffffffffff000000fffffffffefe0000fffffffffcfcfcfcfffffffffcfcfc00fffffffffcfc0000fffffffffafa0000fffffffffa00fa00fffffffff0f0f0f0fffffffff0f0f000fffffffff0f00000fffffffff000f000ffffffffeeee0000ffffffffccff0000ffffffffcccccccc
  | 1, 9 => 0xffffffffffff8080ffffffffffff5555ffffffffffff5500ffffffffffff3333ffffffffffff1111ffffffffffff0f00ffffffffffff0303ffffffffffff00ffffffffffffff0000fffffffffffcff00fffffffffffaff00ffffffffffee0000ffffffffffccffccffffffffffccff00ffffffffffaaff00ffffffffffaa0000
  | 1, 10 => 0xffffffffffffff00fffffffffffffcfcfffffffffffffc00fffffffffffffa00fffffffffffff0f0fffffffffffff000ffffffffffffeeeeffffffffffffee00ffffffffffffccccffffffffffffcc00ffffffffffffc0c0ffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffff8800
  | 1, 11 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x25e79369ebcf85e38d9e4da7253d9b4f5e792f9b0d665d3
  | 3, 0, 0 => 0x8c2f4f26d4cbbd0f25f4d7cc0f26d497bd0f26d47a294f26d497b0d226d4d430d586d47a384f26d4973d0f26d4cbbd1345d48cb0d666d4b6cbcf26d47a301206d497b0cf26d4d7b0d685d4d7c65346d4
  | 3, 0, 1 => 0xd7b0d306d497b88f26d47a37cf26d497b7cf26d47a2f4f66d495b74f26d4d7b0d225f48c2f9226d4004bcf26d37a2f91e6d4c7cd4f25f492b55226d4d7b0d586d47a305226a4b6d9cf85e493b0d226d4
  | 3, 0, 2 => 0xcbcbcf26d47a30d1e6b4d7b35586d4
  | 4, 0, 0 => 0xcbbd1329136ae5d98c33e1b55e8d461a44dab1d7a30d226d57a2f5187936ae5f1ec3561b55e8df489e4daaf461acd226d57a3557a9136ae05e8c3489b572ef4701e4dab358d30d226d5cbbd1227a36ae25e8c3489b572f1461a44dabac6630d226d5
  | 4, 0, 1 => 0xcabd1869136aebf2ecd489b5736f461a44dab977a335586d5d7bd186ac36ae5de8bf489b572ef461a60dabaf78b0d226d5ca3d1869136aebde8c3471b5676f461a44dab977a30d246d5cbb0d226d15aebd86ac3696572f1561a44dab977a298f26d5
  | 4, 0, 2 => 0xd7c65868f36ae9de8c3479b564ac348a30dab798ab0d226d5cbbd186a048aebe0cc3489b56cef861a44dab9761a9d226d5cbb0d226d162ec5e8c3479b5740f461a44dab5d6630d226d5cbbd1be7936ae89e8c3561b575ec3489b4bab407a30d226d5
  | 4, 0, 3 => 0xcbbd1c47936aebe32c35a1b572f0261a44dab8c7a30d226d5c7cd586912faca5e8c3489b574f1861a44dab977930d226d5c7cad869136ade2cec3561b56ff2061a44dab9766b31226d5d7b31869136ae5de8be489b571f356b244bcbaf9330d226d5
  | 4, 0, 4 => 0xcbbd1868536ad75e8c33e1b575ecd61a44dab977a30d526d5cbbd1929136ab5198c3489b56db67981e4dab978c30cf26d5b13d1c47936a8025ec3489b532f267a1f0dabaf61a44da2a57a30d7a8e36aebe44c3489b55e8c34fa44dab3596b88f26d5
  | 4, 0, 5 => 0x95b75869136aebde8c33e1b572ef461ad0babb07a30d226a5b6d4986ac36ae3e6acd489b572ef450a44a8b977a1e4da555b6bd1be7936ae5de8c1489b575ef461244dabaf7a30d226c5d7db59a9136ae3ececd489b56a2f461a44dabaf8cb0cf26d5
  | 4, 0, 6 => 0x7a37d869136ae5de8c3521b575f1261a44dab9781b0d226d5cbc61869136ace5e8c3489b571f3566ab0dab497a30d226d597b7d869136abd1609a489b572ef461a7122b8f9ab0d306d5d7c95869136ac958691369a173ef461a44daaf461a44e46d5
  | 4, 0, 7 => 0xcebd1869136ae5e56c3489b572ef461a44d6bafc7b0d586d57a30d226d102cd65ec3489b572f0161a44dab5e7a30d226d597b89869136abd1cac3489b5754f461a44daa00d7b0d586d4d530d226d2cad4de8c3489b572efe61a44dab9695b0d226d5
  | 4, 0, 8 => 0xcbbd1869136abd194c3489b56db357a268baaf462b0d226d5cbcbd869136ae5de89136901714f461a44dab977a269226d5d6bd1869136ae5d869b489b572f307a1e4dab967a30d226d5c7cd64c7c36ae5de8b8489b56d8f461a44dab977e30d226d5
  | 4, 0, 9 => 0xd1bd18691352ebde8c1489b56db357a1e4beb977a30d3a9157a30d226d19ae5de8c3561b572eff61a44dab977a30d2e6d5d7bb9869136ad71e8c3489b5734f461a44dabaf7a388f26d5cbc3d869136ae5de8cb489b572ec3489b4b8b3596b0d226d5
  | 4, 0, 10 => 0x7a30d226d252ebe60c3489b565ef461a44dab977a309226d57a375b47936ae65e8c3489b55e8e161a44dab2e7a30d226d5cbbb1869136ae5dc6c3489b5400f46f9e4da9a87a30d226d5cbbd186ab36aebdeac3489b56c52d61a44daaf461a44da255
  | 4, 0, 11 => 0x32f1161a44daba27a30d226d57a389be7936aebde8c3489b572ec3489b4b4baf61a44da595d23d1869136aebe00c3489b572ef44d1b4a0b977a30d225f5
  | 5, 0, 0 => 0xc6cd5e8c3489b5b5f197a30d226d6cbc99e8913c9b5adb357a30d2e6d6006bde891368bd66b1c7a30d226d6c94d5e8c3489b5b116d7a30d226d6b6d9de8c3561b5b1ef461a44da1e6bcd21e8c3489b5b65af7a30d226d600625e8c3489b575ef461a450e6d6bf531e8c3489b5b1f657a30d226d6
  | 5, 0, 1 => 0xb6cd5e8c3561b5b0d359130d226d6cbd1de8c3489b5b2ef461b0d226d6006bd8691368856daf461a44da496c7d69e8c3489b5b1f3561a9d226d6c7cd58691368e1adb6761a44da5d60065de8c3489156db357a30d1c6d6cbcd640c3489b5adaf456a69226d6cbbd186913699db2ef461ad0da506
  | 5, 0, 2 => 0xcbd3de8c3489b5b2f137a30d226d6cbdb5e8c3489b5a9ef461a44da666b6cf1e8c3489b5adb357a30d3a916cbbd1869136865801978ab0d226d5bd59de8c3489b5b5ef461ad1226d6cbbd1869136825adb357a30d146d69acb1e8c3489b5b2ef461ad5226d6003d1a8c3489b570d597a30d226d6
  | 5, 0, 3 => 0xbd4d5e8c3489b5b2ef461a44da606b6cd5e8c3551b5b2ef461a44da1d6d365de8c3489b5b12f46d30d226d6bb4d5e8c3489b5b2f637a30d226d69cbd1869136885b2ef461a44da0a6b6cd65ac3489b5b2ef461a44da646cbbd18691368d1b2ef461a45086d6c3cd5e8c3489b5b5f5b7a30d226d6
  | 5, 0, 4 => 0xcbbd1867936941b2f7e7a30d226d6b6d89e8c3489b5adb679330d226d6be4d5e8c3489b5a8ef461aed226d6cbbd18691469b5b2ef45ea44f26d6b6bd186ad489b5b2ef461a44da2f6bc511e8c3489b5adb678330d226d6cbbd18691401b5801977a2448a2f5b6cf5e8c3489b5b04f461ad1226d6
  | 5, 0, 5 => 0x65d86a7489b572ef473b0d226d6c74d5e8c3489b5b2ef461a44da076d5bd186bd489b5b1f357a388f26d6a7bd186bb489b5b2f347a30d226d6aebd1a2c3489b5b31977a30d226d6cbcd5e8c33e1b5b2f577a30d226d6b6cd5fac3489b5b2ef47530d226d6b75b5e8c3489b58019761a448a215
  | 5, 0, 6 => 0xb6d9e32c35a1b5adb357a30d046d6c7cd62ec3489b5aff677a30d226d6cbbd186913a9b5b5fa77a30d226d6b6cd60ac3489b5b2ef461a44da186cbbd186a8489b5b5f687a30d226d6cbcdde8c3489b5adb6b9130d226d6cbcc1e8c3489b5b2ef461a45186d6b6b3998c3489b5b5ef461a44f26d6
  | 5, 0, 7 => 0xcbbd1b8c3489b5b2f3592b0d226d6b6d99e8c3489b5adb3561a44da5b6cbdb5e8c3471b5b2ef461a44da016cbd11e8c3489b5b2ef461a44da516b6d9e44c3489b5b2ef46b30d226d6cbc85e8c3489b5b2f8d7a30d226d6cbbd1869136845adb356630d226d6cbbd18691431b5b55837a30d226d6
  | 5, 0, 8 => 0xb6cd620c3489b5b21357a30d226d69c4d5e8c3489b5b073561a44da596cbbd186913b9b5801977a2f9226d5cbbd18691371b5b2f247a30d226d6d865de8c3489b5b07677a30d226d6bfcd5e8c3489b5b2f6d7a30d586d6cbbd186913e1b5b1f357730d226d6006be4cc3489b572f2261aed226d6
  | 5, 0, 9 => 0xd7e3e4cc3489b5adaf461a44da0d6cbd2de8c3489b5a6af461a8d226d6d7d9d869136965b2ef461a44da546b6cd5d8c3489b5b2f678cb0d226d69abd1869e489b5af1357a335226d6b6cd5c6c3489b5b2ef461a45126d6b6ccde8c3489b5b2f3e7a30d226d67a30d226d10881adb359130d226d6
  | 5, 0, 10 => 0xd7bd1869136985b5f677a30d226d6b6bd186ae489b5a6af461a55226d6b6bd1869136821adaf461a44da626b6d9d9ac3489b5b2ec35a29d226d69abd188c3489b5801977a388f26d5b6d05e8c3489b5adb2061a44da616cbc01e8c3489b5adb557a30d226d6c1cd5e8c3489b5b2ef461a44da066
  | 5, 0, 11 => 0xcbddde8c3489b5b2f6f7a30d226d6cbbd1e8c3489b5b2f3f7a30d226d6b6bd1c8c3489b5b5f357a30d226d6d7bd1c4c3489b5adb477a30d226d6bacd5e8c3489b5b2ef461a44da596cbbd1869136899b2ef461ac5226d6d7cd5869136965b5ef47830d226d6b6d9e32c33c9b5b2ef461a44da1c6
  | 5, 0, 12 => 0xc4bd1c4c3489b5adb677a30cf86d6c14d5e8c3489b5b2ef46cb0d226d69abd1c4dd3c9b5adb4a7a30d226d6c3cd598c3489b5b2efb7a30d226d6cbbd1ccc3489b5b45357a30d226d6cbdb598c3489b5b4d6d7a30d226d6c2cd5e8c3489b5b2ef461a44da306cbe01e8c3489b5a6b2d7a30d226d6
  | 5, 0, 13 => 0xd7bd18691369a9a6af46a30d226d69abd1869136891b5ef461a44da1069abd18691368c9adb357a30cf86d6cbbd18691368f18018f9ab35226d5b6d0de8c3489b5adb357a30d446d69abd1869136859adb357a359225e6b6bd186913690db2ef461a51226d6003d186912281d72ef461a44da4d6
  | 5, 0, 14 => 0xcbdb640c3489b5adb357a30cda3e6d3e5de8be489b5b5f9761a44da596cbbd18691399b5b2ef461a44da176cbbd186ac36965acef461a44da156b6da9e8c3489b5b2ef461a45106d6cbbd18691369a1b5ef461a44da456b6cd5e8c34897db2f587a30d226d6d15e1e8c3489b5b2ef461a44da216
  | 5, 0, 15 => 0xb6d9e24c3489b5b2ef461a44da1e6c7bd1b4c3489b5adb677cb0d226d6d7e5de8c3489b5adb367a30d226d69cbd186913687dadb3592b0d226d6d7bd18691368edadaf474b0d226d6b8cd5e8c3489b5b2ef478b0d226d6b6cd5e89a36941adb447a30d226d6ce65de8c3489b5adb287a30d226d6
  | 5, 1, 0 => 0xd7d21e8c3489b5801978c30d226d5004e5e8c3489b572ef479b0d226d6cbbd186913693db2f077a30d226d6cbbd1869136831b5ef461ad9226d6cbc39869136965adaf67a30d226d6cbbd1869136851adb6766a44da596cbbd186913f1b5b45977a30d226d6b9cd5e8c3489b5b2ef461a44da5d6
  | 5, 1, 1 => 0xd7bd1869136839b2ef461a44da036cbbd186913691db2ef477b0d226d6003d1bec3489b572f267a30d226d6b6cd63ec3489b5b1f357530d226d6cbbd18693489b5b2ef46a30d226d6d7cd64cc3489b5b2f067a30d226d6b6cd5f4c3489b5adb599130d226d69abd1bcc3489b5b2f0e7a30d226d6
  | 5, 1, 2 => 0xcbc65e8c35a1b5b2ef461a44da156cbbd1869136909adb357a244f46d6cbcd5e8e23c9b5b2ef467b0d226d6ba4d5e8c3489b5b2f467a30d226d6cbc35e8c3489b5b2ef77a30d226d60054de8c3489b572ef461a44da6d6c7cd660c3489b5b2ef461a44da2e6cbca9e8c3489b5b2ef46630d226d6
  | 5, 1, 3 => 0xcbbd1acc33e1b5adb357a298f26d6cbb0d227f36965b2f237a30d226d6b6cd598c33e1b5b2ef461a44da376cbbd18691368a9b2ef461a44da276c7db66ac3561b5801aa7a30d226d5cbbd1d0c3489b5b2f097a30d226d69abd186913687db2f227a30d226d6004e586913688572f0b7a30d226d6
  | 5, 1, 4 => 0xcbbd18691409b5b2ef461a44da566b6cd5e8c34c1b5b2ef461a44fe6d6c7d9d869136965801af7a30d22455cbc31e8c3489b5b1f358030d226d6cbbd186b2489b5b5ef461a44da676003d186913688172ef461b01226d6cbbd1c4913c9b59e8dd6d30d226d6d765de8c3489b5b2ef46330d226d6
  | 5, 1, 5 => 0xb6cd58691368b1b1f357a30d226d6cbbd18691368b5b1ef46730d226d6d2e5de8c3489b5b2ef461a44da416cbbd18691368d5b1f3561a44da596cbda5e8c3489b5b23357a30d226d6c7d9de8c3489b59e8c35a2c1226d6d7e5e4cc3489b5adb357a335586d6cbbd19ac3489b5adb2061a45086d6
  | 5, 1, 6 => 0xd7bd18691461b5acef461a44da0f6d7bd186913681db5f347a30d226d6cbbd1869136889adaf461a44da3a6cbbd1869136911801977a269226d5cbbd18691369a5b2ef46830d226d6cbcc5e8c3489b5b136d7a30d226d6cbbd18691379b5800c3489b442205cbdede8c3489b59e8c348a30da686
  | 5, 1, 7 => 0xcbe3d869136965b2ef461a44da006004d65ac3489b56db357a388f26d60065de8c3489b5761af7a30d226d6b0cd5e8c3489b5b2f257a30d226d6cbbd186913684db57977a30d226d6d7bd1869136805b2ef461a44ec6d6b6cd59acc489b5b5ef461a450c6d6cbd7de8c3489b5b47977a30d226d6
  | 5, 1, 8 => 0x9abd1bac3489b5b5ef461a44da596cbbd1b4c3489b5b2ef461ae5226d60065de891368bd6db357a325226d69abd1bec3489b59e8e26fb0d226d6cbc49e8c3489b5b65977a30d226d6b6cd64cf43e1b5adb607a30d226d6cbe3de8c3489b5b5ef461a44da546cbcc9e8c3489b5ae1357a30d226d6
  | 5, 1, 9 => 0x65de8c3561b572ef461a44da1b6b6cd5e8a148951b2ef461a44da366b6cd5e87936955b2ef47030d226d6cbbd1869136815b5ef47a30d226d6d13d18691369659e8d16730d226d6c7d9e4cc3489b5b2ef461af9226d6cbbd190c3489b5b4cf461a44fe6d60065d86913688572ef463b0d226d6
  | 5, 1, 10 => 0xbc59d869136965b2ef461a44da536cbbd186af489b5b2f687a30d226d6d7bd18691369a1b2ef461a44f26d6d7bd1869136885b43977a30d226d69abd1869136881adb2b6d30d226d60065d226d1788572ef461a99226d60065de86d1d8bd5e8c35ea45186d6003d5e8c3489b572ef461a44da466
  | 5, 1, 11 => 0xcbc9586bd489b5800f461a44da075cbd91e8c3489b5b2ef47830d226d6cbbd1869136881b5f0e7a30d226d6cbbd1869136985b2ef461a44da4b6c7d1de8c3489b5adb357a30d38916d4e5de8c3489b5b5faf7a30d226d6bc59de8c3489b5b2ef461a44da4e6cbbd18691368f5b2ef46fb0d226d6
  | 5, 1, 12 => 0xcbbd1869136811b3d977a30d226d6cbbd1869136955b2ef461a44da026cbbd1869136915b5ef461b01226d6cbbd18691369a9800c3489b442075d7bd1d0c3489b5add357a30d226d6b6cd602c3489b5800f4489b45e075003d186913680566b2d7130d226d6cbbd1c4c3489b5b2f0a7a30d226d6
  | 5, 1, 13 => 0x6bd86913696572ef461a85226d6b6cd5e8c3489b5b5fa37a30d226d6cbbd18691369619e8c3489b43e1e69abd18691389b5b2ef461a44da3f6d7cc5e8c3489b5b2ef46bb0d226d6d1bd18691369a1b67977a30d226d6b6cd5869b489b5b2f977a30d226d6b6cd660f43c9b5b5f697a30d226d6
  | 5, 1, 14 => 0xcbbd186913c1b5801a27a30d226d5cbbd5e8c3489b5801af7a30d226d5
  | 6, 0, 0 => 0x6366af461a44dad6d9abd1a4c3489b5edb357a34d869136bdb66af461ad1226d7cbcd66af461a44dafa3cbdb5e8c3489b5f2f357a389869136bdb66af46430d226d7005b5e8c3489b420c009bcd5e8c3489b5b1f357a30d226d17bdb6ad357a30d226d7005b66ac3489b442d6d9abd18ec3489b5edb357a30d226d0d3db66af461a44da0b7
  | 6, 0, 1 => 0xc7cd5e8d661a44dae00b6cd5226d17885801977a30d228436b0032f6d7a30d226d6b6cd5e8c353244dae00b6cd5e86d1d8bdb5797b6bd1869136b802db357a30d586d6b6cd5e8e2619e4daf6d9abd186913686dedb357a30d226d1b380001977a30d22455b6cd5e8c3489b4a4f8f9acd1e8c3489b5e6af461a44da170abdb6b7357a30d226d7
  | 6, 0, 2 => 0xcbdb5e8c348a1cdae00b6bd186ad489b5801977a30d226d17b63e6af461a45166d7b6cd5e8c3489b490f6d9abd186913c9b5edb357a30d6e9136be5f1f6d7a30d226d7003d18691368381ad799abd1869136985edb429abd1869136bdf6db357a30d226d7b6da2cef461a44daf6d9abd1b6c3489b5edb677a30d227936be126af461ae9226d7
  | 6, 0, 3 => 0xb6cd5e8dd61a44daf979abd18691368edc01977a30d226d03b5b66af461a44da127b6cd5e8c3489b49cf97b6c65e8c3489b5edb357a30d226d1eb8032f6d7a244da2f6c7cd5e8c3489b4a8fa7b6cd5e8c3489b5edb357a30d5e9136bdb66b157a30d226d7b6da26af461a44daf979abd1869136915c016db3c99869136b65ea1357a30d226d7
  | 6, 0, 4 => 0xb6d9de8c3489b4c2f6db3d9de8c3489b5edb357a30d226d1438032ef46b30d226d6cbdb6b6f461a44daf8f9abd1869136965c016d9ab31869136b4d5e8c3489b4421f7b6d366af461a44daf97b6bd186b4489b5f2f979abd1869136be5e6af461a44da667b6d166af461a44daf6daa4d5e8c3489b5c0197b6b0d226d10b0032ef461a45186d6
  | 6, 0, 5 => 0xb6d9e6af461a44daf6db3bd1c4c3489b5f01357a30d228736bdb5e8c35a2b5226d7005b66b2261a44dad8fc04d5e8c3489b5edb357a30d4e9136bdb66af461a44da4b7b6cd5e8c3489b470f979abd186b6489b5f1f357a3d1869136b802ff357a30d226d6c7db66b2661a44daf6dab3d186b6489b5edb679ab0d226d2cbdb66af461a44da397
  | 6, 0, 6 => 0x6becef461a44dad97b6bd186913c9b5edb359abd1869136bdb66af47130d226d7b6cd614f461a44daf6d9abd18691368a5c01839abd1869136b002daf461a44da0d6cbcd5e8c35da44dae00cbbd1869136951adb649abd1869136bcd5e8c35da44da667b6d3a6af461a44daf97a44d5e8c3489b5edb357a3c1869136bdb66af461a44da617
  | 6, 0, 7 => 0xd7e3e6af461a44daf78b6cd5e8c3489b5edb677a30d226d22bdb66af461a45226d7b6cd5e8c3489c0dae00cbe01e8c3489b5adb677a30d226d083db66af461a59226d7c7cd5e8c3489b42ef6d9abd1227936951c01af9abd1869136b002db477a30d226d6c7cd5e8c3489b442e00cbbd1869136965b2f357a30d226d073db66af461a44da577
  | 6, 0, 8 => 0x65de8c3489b442c00b6bd186913681d8016d9abd1867c36b65edaf47830d226d7b6cd5e8c3489b4aae00cbcd5e8c348915b1f357a30d749136be5edb677a30d226d7b6d9de8c3489b4ccf6d9abd1dcc3489b5edb357a30d226d22bdcadb357a30d226d7b6cd63cf461a44daf6d9abd1869136841edb357a361869136bdb66af461a44da237
  | 6, 0, 9 => 0xb6d21e8c3489b4c2f6db3d21e8c3489b5f1f35933d1869136bdb66af475b0d226d7d9db66af461a44dae009abdde8c3489b58016da23d1869136b5b66af461a44da4c7b6cd586b6489b4b2e00cbbd186913685dadb677a30d6c9136be3e6b0e7a30d226d7b6cd610f461a44daf97b6cd5e8c3489b5c01977a30d226d3435b66af461a44da3b7
  | 6, 0, 10 => 0xc7cd5e8e861a44daf6d9abd18691368c5edb35823d1869136be5e6af461a45186d7004d5e8c3489141cd979abd186913681dedb357a30d769136bdb691357a30d226d7b6cea6af461a44daf6d9abd186913a1b5edb357a30d226d1fbdb66af461ab1226d7b6cd5e8c35b244daf86b6d9de8c3489b5edb357a35d869136b8035f977a30d226d6
  | 6, 0, 11 => 0xcbcd5e8c3489b4a8f6d9ac59e8c3489b5edb357a30d226d31be2edb357a30d226d7b6d666af461a44daf97b6bd1869136999ef1357a30d226d2cbdb66af461a69226d70065e4cf461a44dac007a30d226d0b839af36d9abd1869136bdb66af461af1226d7b6cd5e8c3489f4daf6d9abd1869136839c0197873d1869136b5b66af461a85226d7
  | 6, 0, 12 => 0xc7cd662f461a44daf8f9abd1dac3489b5f2f6da43d1869136be5e6af461a44da597005b66af461a448ad6db3bd18691421b5edb357a30d226d33bdb66af461ad0da5070065de8e861a44dad6d9ac99e8913c9b5c01357a30d226d0fb5b6caf476b0d226d7d7d9e6af461a44dae00b6d9de8c348915adb357a30d228336bdb66af461a44da0d7
  | 6, 0, 13 => 0xb6cd668f461a44dae00b6cd58691228858018f9ab0d226d2cb0026ac3489b4421f6b6cd5e8c348a00dae00c7d9de8c3489b58016d9abd1224517b5b66af461a44da607cbdb5e8c3489b41cf6d9abd1869136875c01977a30d227f36b5b66af461a44da0a7005b5e8c3489b42ed6d9abd18691368d1edb3589bd1869136be4f1f357a30d226d7
  | 6, 0, 14 => 0xc6db66af461a44daf6d9abd18691431b5c016d61a44da210bb5b66af461a44da187cbcd5e8c3489b4d0f6d9abd186a8489b5edb379abd1869136b8032f317a30d226d6b6cd660f461a44daf6d9abd18691461b5c0197bdbd1869136b65e6af461a44da217b6cd5e8e761a44dae00b6bd1226d1785dadb357a30d226d03b8031f357a30d226d6
  | 6, 0, 15 => 0x65f1ef461a44dad6d9abd1869136965f2f35873d1869136bdb66af461a44da1c7b6cd586b453a44dae00b6cd5e8e23c9b580000cbbd1869136adb66b007a30d226d7006af2ef461a44dad6d9abd1869136951c018f9ab0d226d10b5b66af461a44ee6d70063e6af4489b45edafcbcd5e8c3489b5edb359130d769136b80347977a30d226d6
  | 6, 1, 0 => 0xc7d9e6af461a44dae00cbbd186913c9b5adb357a30d227336bdb66af461ab0da597b6cd5e8c348a20daf6d9abd18691369a1edb357a30d226d10bdb6cef461a44da177cbcd5e8e861a44dae000065d869136885401357a375869136b5b66afb7a30d226d7b6cd5e8e661a44dae000065de891368bd6db357a3d1869136bdb67f357a30d226d7
  | 6, 1, 1 => 0xb6cd5eef461a44daf6d9abd18691369b5c00007a30d226d03a8032ef47830d226d60065de8c3489b4c2d6d9ac99e8c3489b5edb35873d1869136be5e6b317a30d226d7b6cd5e8c3489b49ef6d9ac1de8c3489b5f2f357a3b5869136bdb66af461a44da0c7b6cd61cc3489b4b2f6d9abd1869136975edb357a30d226d0f3ebedb357a30d226d7
  | 6, 1, 2 => 0x9abd186bb48a1cdaf6d9abd1869136905f1f489abd1869136b8032ef461a44da456b6da66af461a44daf357a389bac3489b5c01677a30d226d0735b66af46330d226d7b6cd5e8d6619f0daf6d9abd186913689dedb357a3a1869136bdb6cef461a44da657b6cd632f461ad0daf6d9abd1869136909c01977a389869136b5b68d357a30d226d7
  | 6, 1, 3 => 0x16d9abd1226d17b5b66b127a30d226d7000035ef461a44dab6d9abd1869136801c016d9abd1869136b5b66af461a44da137b6cd5e8c3489d8dafa3b6cd5e8c3489b5edb3598bd1869136b8032f977a30d226d6
  | 7, 0, 0 => 0x2db357a30d22456005b66af461a44da0e7005b66af461aed226d7005b691357a30d226d7005b66af461ad9226d70065edb357a30d226d7005b66af461a44da3b7005b66af461a44da457005b66af47130d226d7005b66af461a44da617005b6cf357a30d226d7005b66af461a44f26d7000032f6d7a30d226d6005b6b7357a30d226d7005b66af461ad1226d700002db3561a44da216
  | 7, 0, 1 => 0x2db357a244da2f600002db357a30d226d6005b66b317a30d226d7005b66af47430d226d7005b66b267a30d226d7005b66b0e7a30d226d7005b66af461a44da217005b66af461a44da5970000001977a30d226d5005b66af461a44da547000031f357a30d226d600002daf461a44da176
  | 8, 0, 0 => 0x2db357a30d226d6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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
private theorem z2_0 : span (Z 2) 6 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 6 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 11 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 35 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 11) z3_0 z3_24

private theorem z3 : span (Z 3) 35 0 = true := z3_a1

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
private theorem z4_168 : span (Z 4) 18 168 = true := by decide +kernel

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

private theorem z4_a7 : span (Z 4) 186 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 18) z4_a6 z4_168

private theorem z4 : span (Z 4) 186 0 = true := z4_a7

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
private theorem z5_480 : span (Z 5) 4 480 = true := by decide +kernel

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

private theorem z5_a20 : span (Z 5) 484 0 = true :=
  span_join (f := Z 5) (a := 480) (o := 0) (b := 4) z5_a19 z5_480

private theorem z5 : span (Z 5) 484 0 = true := z5_a20

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
private theorem z6_312 : span (Z 6) 2 312 = true := by decide +kernel

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

private theorem z6_a13 : span (Z 6) 314 0 = true :=
  span_join (f := Z 6) (a := 312) (o := 0) (b := 2) z6_a12 z6_312

private theorem z6 : span (Z 6) 314 0 = true := z6_a13

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

def CG : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [7, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12459

theorem PEqualNP.Outside.L_meta_12459 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941132928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12459.mainG PEqualNP.Outside.L_meta_12459.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12459.CG, PEqualNP.Outside.L_meta_12459.CG_mono, by
      have : PEqualNP.Outside.L_meta_12459.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12459.CG_eval⟩
