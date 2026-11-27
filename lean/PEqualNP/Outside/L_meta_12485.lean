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
namespace PEqualNP.Outside.L_meta_12485

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 14, 15, 7, 17, 7, 19, 7, 21, 7, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 7, 7, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 14, 14, 14, 14, 14, 14, 15, 14, 17, 14, 19, 14, 21, 14, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 14, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 15, 15, 15, 15, 15, 14, 15, 15, 17, 15, 19, 15, 21, 15, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 17, 17, 17, 17, 17, 17, 17, 7, 17, 17, 17, 17, 17, 17, 14, 15, 17, 17, 17, 19, 17, 21, 17, 23, 17, 25, 17, 27, 17, 29, 30, 31, 17, 17, 17, 17, 17, 17, 17, 39, 17, 41, 17, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 17, 59, 17, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 7, 19, 19, 19, 19, 19, 19, 14, 15, 19, 17, 19, 19, 19, 21, 19, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 19, 19, 19, 19, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 21, 7, 21, 21, 21, 21, 21, 21, 14, 15, 21, 17, 21, 19, 21, 21, 21, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 21, 21, 21, 21, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 23, 23, 23, 23, 23, 14, 15, 23, 17, 23, 19, 23, 21, 23, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 23, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 25, 25, 25, 25, 25, 14, 15, 25, 17, 25, 19, 25, 21, 25, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 27, 27, 27, 27, 27, 14, 15, 27, 17, 27, 19, 27, 21, 27, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 29, 29, 29, 29, 29, 14, 15, 29, 17, 29, 19, 29, 21, 29, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 30, 30, 30, 30, 30, 14, 15, 30, 17, 30, 19, 30, 21, 30, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 31, 31, 31, 31, 31, 14, 15, 31, 17, 31, 19, 31, 21, 31, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 39, 39, 39, 39, 39, 14, 15, 39, 17, 39, 19, 39, 21, 39, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 39, 39, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 41, 41, 41, 41, 41, 14, 15, 41, 17, 41, 19, 41, 21, 41, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 43, 43, 43, 43, 43, 14, 15, 43, 17, 43, 19, 43, 21, 43, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 45, 45, 45, 45, 45, 14, 15, 45, 17, 45, 19, 45, 21, 45, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 46, 46, 46, 46, 46, 14, 15, 46, 17, 46, 19, 46, 21, 46, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 47, 47, 47, 47, 47, 14, 15, 47, 17, 47, 19, 47, 21, 47, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 7, 49, 49, 49, 49, 49, 49, 14, 15, 49, 17, 49, 19, 49, 21, 49, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 49, 49, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 51, 51, 51, 51, 51, 14, 15, 51, 17, 51, 19, 51, 21, 51, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 53, 53, 53, 53, 53, 14, 15, 53, 17, 53, 19, 53, 21, 53, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 54, 54, 54, 54, 54, 14, 15, 54, 17, 54, 19, 54, 21, 54, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 55, 55, 55, 55, 55, 14, 15, 55, 17, 55, 19, 55, 21, 55, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 57, 57, 57, 57, 57, 14, 15, 57, 17, 57, 19, 57, 21, 57, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 59, 59, 59, 59, 59, 14, 15, 59, 17, 59, 19, 59, 21, 59, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 61, 61, 61, 61, 61, 14, 15, 61, 17, 61, 19, 61, 21, 61, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 62, 62, 62, 62, 62, 14, 15, 62, 17, 62, 19, 62, 21, 62, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1515157f15553f7f1515157f15553f7f1515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f1515157f15553f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f15553f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac0800000000000000000eaeaea80eaaac080eaeaea80eaaac080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eaaac0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080eaeaea80eaaac080

def cMZZ : Nat := 0x1515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f0000000000000000000000000000000000000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f0000000000000000000000000000000000000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f0000000000000000000000000000000000000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f00000000000000001515157f15553f7f000000000000000000000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f00000000000000001515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f1515157f15553f7f

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
  | 4 => 223
  | 5 => 579
  | 6 => 378
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xb9284a69
  | 3, 0 => 0xfe693360f58ea77bf045a72cc80b04ffbf4f9d22a8281dac979b078992cd70915e5b4b875818b960545eacd546b4c3d2459bf27a32f174b1
  | 4, 0 => 0x3a7716723984a785384c44f13755fe6837174ac436faf4ba348a0d46335debcf3329517132b25b5c3207f7ca307089633024a1872fe0a6472eb479e62da2ce012c3de2892948a6bd2915d8df28567610279f10f9265fc357261119832528230324c21b8324342d1c224a8f80203206581fe54de01ec7c4dd1de20fe01dd898171d8c1e7f1d0895c61cbe10e51b4f5d341a5b2e931a3c651018a32509166f0f48160c5dce1473399f13f60ed110c15c670f4602c80ec25f860e736e230e32a6b80dcd9cf60d25fbb40c1bfee00c1087600acf6bdb0982b8a4073aabd2072f7f5f0709b1e9068000fc0530b00504acf4010426327f02ee212f026e1f63006f3b81
  | 4, 1 => 0x78dc01fd783ce0c077e113c97736e61a74866ba47473825d739d654c7338c0557191dfe2711babb1705868c76ff7dae86e66d5c26d7145c16c47b8146befe9276bcd1f386b9c0db36a8a56f269ebbf1b692d477d6917a96768112b7268022c9d64f4ec4f64562b65637b18e262018f79600207385f7f53ef5d24f8cf5ca1e8155bcec6ef582e1ecc573621435708fe8456e048e956cc285c56ca2ca756ad6a7d563c5b235543546853b17f1351fa420b514a8b494ff3ccff4f95a07b4f7fc7de4f5fbb0e4db8ea574da885364986de584931ab42489b26ef4863ddda47abeec846cf6b56453199a0403d47013fb584d73f3dcdc33e5442933bf256d23bb7c0ab
  | 4, 2 => 0xd25e5703d067d528cd3cc6a8c92e39c5c8a50045c650b470c24db3d4c18049a1be939f1ab899009fb70b152cb128e8d6b0170514aef68a4cabe081b4a7c101a1a7b1a5daa7569510a5d8cc44a5486593a4609763a300dc47a2b7e2e4a2514b8ca1d32c109e6d996b9e0eb2879ab3574299ac3f8c998babf7993d662498abbc039823dc5c9558e6a594dae26492d2a509919132f7912eafcb8e9c95068e7c71e58e7a4dd88de42bb28d7de8a28b6307ed8b3e4d6689ef5e4c8898a6e187008893867d95d383d1e01883a6e9d28269ea3d80c52f137f601ba57f2eed617de1ab487cc74dcb7c8036247c441a817b973fa47b6764cc7ac66dc1795fa2f7791588ec
  | 4, 3 => 0xfc6a1c6ffb97ae32fb7b517df9c6d953f982ee5ef9812408f8cd2294f8a499cff846c4fcf7153902f6bb5256f5928d59f4b6392af34fbd3bf0c5bc2bef3baeefedff8450ed71b44febc3a3e7e9951710e6931702e49a18ffe2d4b6b0e209be4adf0d33dedd6d58fddae589a2d6d98cd8d6c37096d6482f24d36d5d81
  | 5, 0 => 0x18a32509185b9a891799edbf173e39d515b8ec0c1403ab4313e0e52c13154a5512f305b112d459c512cc0b6811f2f89b11e1cd1c118b443c1156a6721150516f109b443d10948973105851310fcffde30fb69f290f8b5b900eec35690ea7e78e0e43bc3d0dcd9cf60d4d72850d13bdbe0cc3147c0cb515320ca4ff2f0c8ee2ed0c7e25840c417b5e0c13a17b0b94d3580b5f9e1a0ac04995084de4b80810c37e07c22c29067c1a0a05fafbdf053befc405142eea04b3b2ad048d60a703c016d403970254038800fa02fa1f5302ee212f02b053de0290b15f026e1f63023c63a101e9dbf901b3bd6201af95e8013351cd008b8f03006fe4b3001e2e880011e79c
  | 5, 1 => 0x2e2e70aa2e22ca472e1237532cfaea1b2cfa79162c3059422bd4504b2b0131842ae6c45f2a81ab812a77edb82a60688c2a2a32722a01bf622982ad64296988ed2953fafb290a5c1928e2957e2798fe85273763ec26fe118426a85bda2625a2432592cef9258e7ccd257dbff1250a11032430a1262425d07c24172d0e240110cc23b3a93d23770e3122a07c06224a8f8021ec1c30217938512172bb5f21635907207ad3d9206ecf782007c6ff1fb7e83b1f6089671f0a27b91e0ff9f31de20fe01d85f6971cfad50d1ceac1cf1c5e89591bf41e451bb680381ba3abfa1b764cd11b0930331aaa26931a658b5619a85d4d1998f9f01930245818bfbf4018aa9f96
  | 5, 2 => 0x458465324511751a44b5ee9a44a8c39c443ee07543cce6fe43990f4842f16e0642df5b7242915b2442377b7041dbf9b240d4117f409d5eb8409ade2d40920d233eac88fc3dfd407a3df508ef3d65b8f23cfaf1b13c4b734e3c0e77723bfba0833bc62ab23b838f953b7287053b61afdd3b1f05263ad354bb3aaf54853a8948793a5bc23c3984a785393a7a5a38b9938138a42189389d710c3813558a37b0ee3737a5daf037a374e837749f363764c84036f67f8136eb437b35c68a2f357146db34fa77dc345a7af034141e09335debcf333a8a94324689e532358ec63205861231f5d00931c5107c3167b4593146c3d431094109307089632ee821252e9894eb
  | 5, 3 => 0x5e512e985e21e8625d6a834b5c2b35a95bcec6ef5bce56395b4721e85b213b3c5b0b3d275af395555a8d8dd559c47214595cbfbb58492e53581601d257747ea455fd78aa55bcba9c55b7405255b0c03255323ab354f76ca553b901c253ad82325377563d535790d152bde404528983375265919351e1737c512ecefd511acf86510676bf50679343502e92a14fef81dc4fdc3e414fabbf944f95a07b4f619ae84f5e5c5a4f1e47524e897e564e6e975b4e6c099f4d0dcbee4c3a819a4c225be84c2060334bd7d0204b7abc674a0ddeed493246d648a49ca84848af8f48440567480f025247b1da04478c2f454738d217469e72974692420545d439fd45b1b26c
  | 5, 4 => 0x725eb7d971bdc924718332fd71612720714e0e6d711babb1705868c7704ae9f5704288c4702840166f882fb16f5019d76f3e1eb56f04665b6ecc5ece6ea424136e4cd5dc6df0f91f6d7145c16d2170ba6cf2ddb96ce2bd166cc6670c6cbb3c596c54a5016c1279c06bdb8ae86b8adf4b6b6f57ef6b1fb0116a911bfc6a6624ce6a63df2e6a24098469dce9bc6987e7c46957a44669295e21690037a668c3a93e68022c9d68010af966ae24d7663bfbb565e281b265e0c53a64e7d4c1649efb906482ff2a6480bbb3647fec38638f056c636e40536349178e624f4ea7622735d1612117f7611c1b3361088d545f7f53ef5f4bea0d5f19fc795ede3bd95e59a082
  | 5, 5 => 0x9154709291184cc5908e070c8fc57c0a8e4c123a8e491d308e46a03d8df9911e8d7cc3018cabbb3b8c959ef98be847cd8ad22115899b80bc8988cdbb88f39e64884dfbb8861fff20852b2d608502883b844bd33083845ca98381d58f82bd79148264582380edff91809b8c008085254e7fe290d57f3b22fe7f2eed617e6699417e42f2ab7e2f502c7dae29947d77611a7c8e6a9a7bd93ed97ad360487a3b9f8a7a32a8ab7914674878dc01fd78c12382788ad3c378800d4b785c0dc377ef23ae77d75b9e771f51767681295f766d66be7663ae637661b43d76430922762ddabd762704dc7608b95375f043b275b87a367580f7297541e1cc74cd290f73cb528d
  | 5, 6 => 0xa98f3a2da9872528a94646f2a8e44b29a8766f23a80832d7a75d5234a729c8baa713ffe6a6e71e03a623db19a5c34d3aa535cf68a4324814a3c1c59ea33cb813a309ff23a2b7e2e4a2514b8ca2441a7ea2362d53a19e3e3aa1678005a09f516aa09517729fd5fa379f11f0b39ef8b9cf9e32cb539dcd9eef9d62efa89d5b35dc9cd340ac9bc9a5079ad89d699aa36a829a62c5889a219db79a128f0e9a11b6ad99e53171998babf79984a07099468b34991cebdd9903ba0c98b3b2c5982ec8fe9823dc5c97cee60997cd01cb97a77f1897a38e98972e0b4d954ac64195229ce894dae264939323e19334b091932f908e92cef9c492c405e592b19cd0919a3941
  | 5, 7 => 0xcc3c27c9cb1aa55ccaa654b6ca8f907ec9e3561ec934cd5ac89e175bc81c4543c46f5dfec445c02ac36964bdc1ca2807c18f075bc12e7a3fbeca4c1dbe641933be05d581bd97b8edbd613db3bcda35e1bccbfae5bc7bc291baddf819ba959209b9f69d21b99d526ab925baa8b88ecaaab863d418b8355c8fb7c27bdbb7874173b6a6073fb60ee440b55ff838b557bdd9b51b71cfb4fa5fb3b3d43f12b3b9d33cb2fb101ab292c01db20f8cd3b162b1f6b10ccbfcb0ff7f07b0a3ab39b053e23caea7744fae210b1bae085312adac861bad26e35dad02586cac461cc3ac0cdf5eabdb1f8dab5f40c1ab25bd8eaaf1ca10aadc55ccaadc4571aad24514a99d48aa
  | 5, 8 => 0xfc1c26c2fa92f682fa348332f846c4fcf83f535ef7e0e00ef74bbbf3f39b7121f202a683f0028be4eff083a2ef95fab1eddf8273ed71b44fed214a72ecd6877eec9c1db9ec526707e807c705e6f45b28e6ab55f3e6560275e653cd9ae5f6b1b1e5e29124e458d229e321c027e2860591e10e32abe0bf7617e014f32fde7623d6dd49a656dc8caa83dc16e9bbdba43e96dace127bdab34589d9b4dab2d8cc4e99d8835536d81cbdded707e6bdd6d98cd8d6d2724cd6c37096d5de35d2d44c4351d414fec5d2a656f3d2553da3d23d4bc8d169d52cd11b62f5d0c0c6f7d087ba65d07ec994cf77b1decee73ba3cea528c6ce772e55ce71c884cdef4eaecdde9932
  | 5, 9 => 0xff819e50fcd7ace7fc33823d
  | 6, 0 => 0x185177e817dc3c08177d576b160d95e315e065861559e57914e43af51441962d1411386213c8981212b4272d12581cda124c090411e1cd1c118f88ba1156a672109984d20f8b5b900f804d090f4dbb970f1a21fd0ea86cbf0ea7e78e0e72142d0db665880cd359140ca4ff2f0c9de4a30c8ee2ed0c417b5e0c07ec530b9676d70b4375b70a9edde90a17d6170a17b5a809e0711c0947411f08d530df0871c94a085863790840dc2c0820affa0808be1f07fd53560735478306e6d54c068c394e056bab9105425c4704c4e1a904709b1d043d3adb03c016d403bd595d0397025402d4473c0290b15f02079a2001ec78a60160aac50134c0060111df480038b050
  | 6, 1 => 0x3a0e5c33398b892638b99381387bc630385c23b137f45294377b083a36fec41f363b570535dd59ee358198e0354d10a7353f731433e043313320315a32a31f3e3247fa4b31fef494312805df3109410930aa4812305f605d305e68d92ffff5892f2f7ba42f07c6312e7936972d5293652bb3c40c2ba5b8062966e3782854880d275f5ddb271962ec26f27ae826a85bda25cdfe3b25bbf5f9253d5f582515030224e0ab592425d07c23aaf4ca239ce88522679010224a8f8022195b4721ec1c3021b32f0f2163590720b96efe1fcf3e031fb7e83b1e7cbf981dd751471dd3395c1cc13d791c2174cc1c1f3ff11bc224081bae037b1a24448018ed327e18a6ede5
  | 6, 2 => 0x63f9e2fc63ee3c9962c5eb6861aad88d619fc29d602bdade5f1f6d4d5ed5ce6b5eae07d05e512e985d967d565d02d63e5cb4f6455c73ce2c59fc1378597f1b8f581601d257b78e825744aaa3573e2db1572ecb59563a41ca55835a8d53db6c4552c6475f52bde40451bf90975181f28a516f1e4c5141bf2350fdb705507598e54fce51904e8b31924d6560114b845e5e4a0ddeed49cf1d9549ba282a49ac577e48be78034848af8f47d096b847be6aed478c2f4546a1a9834666b68f4623c383457cf3944556cde2440f2e8f42e50ec042df3010428366c0412b106c408d07dd3db03d4b3d8d9e7b3d402c1a3b9887cf3b1d22a93b0762163adfa13c3a61de12
  | 6, 3 => 0x9199c88b8f8fe4668f28320d8d3ff0f68ac2def78984741488895656883103e586fa414f86d1e91185fa04f38529ceac84c30c958454f0a882d93e4081ebd28581462eb97fd9513f7e700efa7e46e13a7e1421e17e0f77b97d7d4c567d0444697b7d24be7b1025717a8160ec7998595078800d4b76a580a0765d7f7574f5238574d59e897477fb4e73e5fc0b71919d04716370ad709ec70d7054bacb6f882fb16f5019d76f29bc616f05ecac6ea0f9386e6f93db6e68e35e6df0f91f6ddec7dc6d7c60896cf5886c6cf2ddb96a25ed4269df905b69dce9bc6844a0d66811fc3767e62d8667c1425b673326ab66d4b35b663bfbb564b3937764a6c3f76415e883
  | 6, 4 => 0xc6e3bf17c0f39befbeca4c1dbebf10b6be05d581bd613db3bd48a2efbcda35e1ba174582b82fca75b7874173b6c246a6b6514265b5ae0327b5069550b3d43f12b2fb101ab259dcecb10ccbfcb00711dcaffe1afdae564615ae4b7f9dadba9600ada2cdf0ac4c9bb1ac38d910ac0e7b74abf94d0fabf2772eabbbb604aaf1ca10aad24514aa989b61a996c4dfa729c8baa71980bfa6e71e03a5f3b268a5099107a497d120a46f9665a3bc6b71a33cb813a2be500ba1ddec12a1a6fd3a9fa85c0e9e8f1b909dcc7d4b9b7cb4ee9aa36a829a4c2e059a128f0e991489e097a77f1896ec8a4996d3ffa6954ac64195175c5f941ca0ea939323e192b19cd0919a3941
  | 6, 5 => 0xffaec870fde7b795fa92f682f83f535ef7959a59f495be6ff32cb005f2a5a833f24734e3f0a96a6bf0028be4ee5a3cfceddf8273ec717991eae6e421e6d83e4ee66f1d8be5e29124e321c027e2f255afe1a691dfe12ab313e0f12fe0e0bd3c62e09db766e014f32fdf5aac7fdf52977ade7623d6ddd3a529db0141bad9b4dab2d98d37f0d8d57175d81cbdded80f8cd0d7d539c3d5a16c89d4dd6305d3fe3da5d326a82ed1951759d06edcd4d02e37dacfde0160cf5012c2cdfa3b50cd9a585bcd72f16acd6f00eacaee0f3acaa654b6c95e9633c90022e3c8fb02e0c87d0f22c81c4543c71fe2e4
  | 7, 0 => 0xfde7b795f495be6ff2a5a833e6d83e4ee09db766d06edcd4cfde0160cd72f16ac95e9633a3bc6b71a2be500b9fa85c0e941ca0ea888956567e1421e16f882fb16844a0d666d4b35b5c73ce2c581601d257b78e82572ecb5955835a8d4556cde2398b8926385c23b13247fa4b305e68d92f2f7ba425cdfe3b224a8f8015e065861441962d0947411f0134c006
  | 8, 0 => 0x581601d2
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3f3f00003f3f000033330000333300000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000f0f0f0f000000000c0c0c0c000000000aaaaaaaa0000000055555555000000003f3f3f3f00000000333333330000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xff000000ff000000cc00cc00cc00cc00c000c000c000c000aa00aa00aa00aa0055005500550055003f003f003f003f000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000ff000000ff000000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa0000555500005555
  | 0, 2 => 0x15151515151515150fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff0000ffff0000
  | 0, 3 => 0x3fff00003fff00003f3fffff3f3fffff3f3f3f3fffffffff3f3f3f3f3f3f3f3f3f3f3f3f000000003f3f00003f3f00003f003f003f003f003333ffff3333ffff33333333ffffffff33333333333333333333333300000000330033003300330030303030303030302aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a2222222222222222
  | 0, 4 => 0x55ff55ff55ff55ff5555ffff5555ffff5555ffff0000000055555555ffffffff5555555555555555555555550000000055550000555500005500ff005500ff0055005500550055005050f0f05050f0f0505050505050505044444444444444444040c0c04040c0c040404040404040403fff3fff3fff3fff3fff3fff00000000
  | 0, 5 => 0xa0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a00088888888888888888888888800000000880088008800880080808080808080808080808000000000808000008080000080008000800080007f7f7f7f7f7f7f7f7f7f7f7f000000007f7f00007f7f00007f007f007f007f007777777777777777
  | 0, 6 => 0xaaaaaaaa80808080aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8080aaaa8080aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa80aa80aa80aa80aa00aa00aa00aa00aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8
  | 0, 7 => 0xc0000000c0000000bfbfbfbfbfbfbfbfbbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaff0000aaff0000aaaaffffaaaaffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaaaaaaaaa8080aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888
  | 0, 8 => 0xc0c0c0c0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c080c080c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000c0c0c080c0c0c080c0c0c000c0c0c000c0c08080c0c08080c0c00000c0c00000c0c0000000000000c080c080c080c080c000ff00c000ff00c000c000c000c000c000c00000000000
  | 0, 9 => 0xccc0ccc0ccc0ccc0cc00ff00cc00ff00cc00cc00cc00cc00cc00cc0000000000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c8c8c0c0c8c8c0c0c8c0c8c0c8c0c8c0c8c0c0c0c8c0c0c0c4c4c4c4c4c4c4c4c0ffc0ffc0ffc0ffc0ccc0ccc0ccc0ccc0c0ffffc0c0ffffc0c0ffff00000000c0c0ccccc0c0ccccc0c0c0c0ffffffff
  | 0, 10 => 0xccccffffccccffffccccffff00000000cccccfcfcccccfcfccccccccccccccccccccccccccccc0c0ccccccccccc0ccc0ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000ccccccc0ccccccc0ccccc0c0ccccc0c0ccccc0c0c0c0c0c0cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8
  | 0, 11 => 0xeaaaeaaaeaaaeaaaeaaaeaaaaaaaaaaaeaaaaaaaeaaaaaaaea00ea00ea00ea00ea00ea00c000c000e0e0e0e0e0e0e0e0e0e0c0c0e0e0c0c0e0e0c0c0c0c0c0c0e0c0e0c0c0c0c0c0d5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfcfcfcfcfcccccccccfcccfcccfcccfcccececececececececcffccffccffccffcccfcccfcccfcccf
  | 0, 12 => 0xececccccececcccceaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeaeaaaaaaaaaeaeaeaea00000000eaeac0c0eaeac0c0eaeac0c0c0c0c0c0eaeaaaaaeaeaaaaaeaeaaaaaaaaaaaaaeaeaaaaa00000000eaea0000eaea0000eaea0000aaaa0000eac0eac0eac0eac0eac0eac0c0c0c0c0eac0eac000000000eac0c0c0eac0c0c0
  | 0, 13 => 0xf0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaa00000000eeee0000eeee0000eecceecceecceecceecceecc00000000eeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececec
  | 0, 14 => 0xf0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0a0f0a0f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0
  | 0, 15 => 0xfafa0000fafa0000fafa0000aaaa0000faf0faf0faf0faf0faf0faf0f0f0f0f0faf0faf000000000faf0f0f0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00fa00fa00f000f000f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f0f0f3f3f0f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0ffff00000000
  | 1, 0 => 0xfcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafaaaaa00000000
  | 1, 1 => 0xff00ff00aa00aa00ff00ff0055005500ff00ff0000000000ff00fa00ff00fa00ff00ea00ff00ea00ff00cc00ff00cc00ff00c000ff00c000ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0
  | 1, 2 => 0xff0fff00ff0fff00ff00ffffff00ffffff00ff00ffffffffff00ff00ffaaffaaff00ff00ff3fff3fff00ff00ff33ff33ff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff00c000ff00ff00ff000000ff00ff00fc00fc00ff00ff00fa00fa00ff00ff00f000f000ff00ff00ea00ea00ff00ff00cc00cc00ff00ff00c000c000
  | 1, 3 => 0xffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff00ff88ff00ff80ff80ff80ff80ff80ff80ff00ff00ff80ff00ff80ff00ff55ff55ff55ff55ff55ff5500000000ff3fff3fff3fff3fff3fff00ff3fff00ff15ff15ff15ff15ff11ff11ff11ff11ff0fff0fff0fff0f
  | 1, 4 => 0xffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ffc0c0c0c0c0ffc0ffc000000000ffc0ff00ffc0ff00ffc0ff00ff00ff00ffc0ff0000000000ffc0c0c0ffc0c0c0ffc00000ffc00000ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff80ffaaff80ffaaff00ffaaff00ffaaff00ff00ff00
  | 1, 5 => 0xfff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffee00000000ffee0000ffee0000ffeaffeaffeaffeaffeaffea00000000ffea0000ffea0000ffccffccffccffccffccffccff00ff00ffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffccff0000000000ffccccccffccccccffcc0000ffcc0000
  | 1, 6 => 0xffff0000ff000000ffff0000fafa0000ffff0000eeee0000ffff0000eaea0000ffff0000cccc0000ffff0000c0c00000ffff0000aaaa0000ffff00003f3f0000ffff000000000000fffcfffcfffcfffcfffcfffc00000000fffafffafffafffafff0fff0fff0fff0fff0fff0f0f0f0f0fff0fff000000000fff0ff00ff00ff00
  | 1, 7 => 0xffff8080ffff8080ffff8080ffff0000ffff8000ffff8000ffff5555ffff5555ffff5500ffff5500ffff3f3fffff3f3fffff3f3f00000000ffff1515ffff1515ffff0f0fffff0f0fffff0505ffff0505ffff00ffffff00ffffff0000ffffffffffff0000ffffc0c0ffff0000ffff5555ffff0000ffff0000ffff0000ffaa0000
  | 1, 8 => 0xffffcc00ffff0000ffffc0c0ffffc0c0ffffc0c0ffff0000ffffc0c0c0c0c0c0ffffc0c000000000ffffc080ffffc080ffffc000ffffc000ffffc000ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffaa0000000000ffff8888ffff8888
  | 1, 9 => 0xffffff0000000000fffffcfcfffffcfcfffffafafffffafafffffafa00000000fffff0f0fffff0f0fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000ffff0000ffffeaeaffffeaeaffffeaea00000000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00
  | 1, 10 => 0xffffffff00000000fffffff0fffffff0fffffff000000000ffffffcc00000000ffffffc0ffffffc0ffffffc000000000ffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffffc000ffffff00ffff0000ffffff00ffaaff00ffffff00ff00ff00ffffff00eaaac000ffffff00c000c000ffffff00aaaa0000
  | 1, 11 => 0xffffffff55005500ffffffff3f3f3f3fffffffff3f3f0000ffffffff33333333ffffffff33330000ffffffff15151515ffffffff0f0f0000ffffffff05050505ffffffff00ff00ffffffffff00aa00aaffffffff003f003fffffffff00330033ffffffff0000ffffffffffff0000c0c0ffffffff00005555ffffffff000000ff
  | 1, 12 => 0xffffffffc0c0c0c0ffffffffc0c00000ffffffffc080c080ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaaaa8080ffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a00000ffffffff88888888ffffffff80808080ffffffff80800000ffffffff80008000ffffffff55555555
  | 1, 13 => 0xffffffffffccffccffffffffffc0ffc0ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00ffffffffff00c000ffffffffff000000fffffffffcfcfcfcfffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeaeaeaeaffffffffccccccccffffffffcccc0000
  | 1, 14 => 0xffffffffffffffffffffffffffffff00ffffffffffffccccffffffffffffc0c0ffffffffffffaaaaffffffffffff0000fffffffffff0fff0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x6891c763
  | 3, 0, 0 => 0xcfdc57e8e4c24a594764f0e911c764ede991c764e66991c764b4c811c764d0dc51c764d7e8d94764cfca594764d04a51c764b8d317e8e4e46911c764d2e8d1c764d7e957e8e4
  | 4, 0, 0 => 0xd7dfe528e3b2ebee32f471d975f71a0a64ecbafbb4a51c765b8d4a528e3b2ebee322471d975f7194a38e8b9fb8d191c765d7dc69ebf472e96cf29471d972b7194a38ecb9fb8a751c765e1dfe528e3b2dc6ab29471d975f297fa38ecbafb8ca580765
  | 4, 0, 1 => 0xd7b55a28e3b2ecae329471d96e36594a38ecb81b8ca51c765d7ca5c4ca3b2dc652ae471d97877194a38ecbafb8ca51c755d7d6e528e3b2ebee329649d97837194a38ecbafd34a51c765b8b65a28e3b2ebee329611d975fa56ea38ecb71903a11c765
  | 4, 0, 2 => 0xd7dce528e3b2f2ee329471d977b7194a38ecbafb8ca91c765b8ca6288e3b2e9652a6471d97c3a476ab0ecbe1b4ca51c765d7dc6628e3b2ebee2bf4718d75f7194a38ecbaf94a38ec205e5696528e3b2ebee338471d975f7194afd1cb719023912765
  | 4, 0, 3 => 0xd7dc53c8e3b2e12e329471d97557194a38ecbbfb8ca51c765d7dc6508e3b2dc6528e3b13575f2965214ecb7194b2d1c765d7ca594c53b2ebee3295ea3975f8894a38ecbc8b8ca51c765d7ca51c76292dc698dd471d975f7b94a38ecbdbd2ca51c765
  | 4, 0, 4 => 0xcfca51c7633ada6531d471d96e32969a38ecbafb8cc91c765e669ee28e3b2ed2e329471d975f7192a38ecbafd25c51c765d7da2528e3b2ebee33c471d97c3dbd3a38ecbb8b8ca51c765d7dc6368e3b2ebee32963a39653047fa38ecbafd2d191c765
  | 4, 0, 5 => 0xb8ca6088e3b2da6528e3b1b975f296aae4ecbafb8ca570765d2e7e528e3b2e7f1d29471d97479fb8a38ecbafd3ca594765d7dc6948e3b2ebedd29471d975f6794b28ecba594a3912765d7e5e528e3b2ebefd29471d975f7191a38ecbafb8ca518765
  | 4, 0, 6 => 0xd7db2528e3b2ec6e329471d975f71a1238ecbafb8c9d1c765b8ca51c7a3b2dc69329471d975f7147208ecbaf94b151c765b8ca5828e3b2ebf0529471d975f71a0238ecb9cb8ca51c765d7dc682ca3b2f66e329471d96e34ca3238ecbcfd1dc51c765
  | 4, 0, 7 => 0xd7dc5788e3b2ebee28e3b1216e329471d848baf94bf91c765b8d66528e3b2ebee2bf5e23975b7194a38ecb9fb8a3902765d7dc6388e3b2ebee2f8471d97997194a38ecbc5b8ca51c765d7dc5ee8e3b2ebed329471d975f7194adcecbccb8ca57e8e5
  | 4, 0, 8 => 0xd7dc652973b2ebf468e3b19d75f7f9ca38ecbafb8c491c765b8ca51c7629aebee329441d975f8994a38ecbafc74a50e765d7dc63c8e3b2f2348ed561d97617194a38ecbc8b4ca51c765d2e8ddaac3b2ebf13295fa3975f8a94a38ecb2965b151c765
  | 4, 0, 9 => 0xd7dc6728e3b2de6e329471d975f71a0a38ecbafd25a51c765dcdc6528e3b2ebf4d20471d96e32949238ecbc3b8ce51c765f0e8ee28e3b2e8252ed561d975f7195a38ecba8b8ca51c765d7e8f1c8e3b2dc596bc471d975f7192238ecbafb8d191c6a5
  | 4, 0, 10 => 0xe45c652993b2ebee360471d975f29471e4ecbafb8aed1c765d7dc63abf472f22e341471d975f7190238ecb9fb8ca51c765d7dc6528e35aebe52c4471d975f29471d87ebafb84a51c765e469e528e3b2ebee3294c9d975f7194a38dab71ae4a51c765
  | 4, 0, 11 => 0xb8d9e408e3b2ebee329470c97998994a38ecb71a623902765b8ca58c8e3b2ebee32c471d96e3296b238ecba3b8a38ec6e5d7b15788e3b2ebee337471d9747718ea38ecbafb94a51c765d7dc652be472f36e329471d975f71949d886bafd2a3902765
  | 4, 0, 12 => 0xd7d62528e3b2e3b0929471d975f7194b28ecbcab8c811c765d7ca6268e3b2e12528e3b19d7a97194a38ecbafbc4a51c765dd5c6528e3b2f6ae329471d975f8794b28ecbafbeca51c765d7e96528e3b2ebf4771471d978d7194a38ecbafb8a38ec515
  | 4, 0, 13 => 0x772e329471d97917194b28ecb719aca51c765b8ca51c76202ed6e329471d97b77190238ecbafb8a38ec155e4dc6528e3b2dc69929471d975f7199a38ecbafd3dc57e8e5e15c6528e3b2edae329471d979f6994a38ecbccb8c811c765
  | 5, 0, 0 => 0xd7ca5dad5561d9b097194ab11c766d7dc652ed4d1d980171aaca51c765d7dc6528e3b0a5b5f7194a38ec0b6006be52ff471d975f7194a391a766d7dc68d2967239ae329783b558766e06bee329471d9b5f7194c191c766d7dc652ed561b1b5f71974a51c766d7dc652ed551d9b5f7cb8ca51c766
  | 5, 0, 1 => 0xd7dc652ed5a1d9b5f7194ae958766e35c652ed561d9b5f7194ad91c766d7ca5c48e3b19db5f6d94bb558766d7dc6d529471d9bbdafb8ca51c766de6bee329471d9b5f7194b0d1c766d7dc652ed599d9b5f7194b651c766d7dc67d29471d9b5f8bb8ca51c766d7e36e329471d9b5f7194a391c766
  | 5, 0, 2 => 0xd7dc652f8471d9b5f7194bb540766d7dc65316471d9b5f71a7d191c766cfdc5dadd561d9b5f7194b6d1c766d7dc652e7561d9b5f7190bb558766d7e4ee329471d9801afbfca51c765d7dc69e9d471d9b5f83b8ca51c766b8ca5dad9471d9b5f7194a3906766d7e9652ed561d9b5fa3b8bb558766
  | 5, 0, 3 => 0x70ee329471d975f7194af11c766d7dc6528e3b0b9b5f7194bcd58766d7dc6528e3b025b5f7194a38f6766e3ebee329471d9b5f7194bb546766d7e76e329471d9b5f7194bb528766d7e3a52e2471d9b5faeb8ca51c766d7dc65303561d9b5f7194bfd1c766d7dc652ed4f9d9ae329803b558766
  | 5, 0, 4 => 0xe7dc6cf29471d9b5f7194c611c766d7dfee329471d9b092976ab0ec676d7dc652d0471d9b5f7194b791c766d7dc6528e3b065b5f7194a38ec616d7ca5dad5471d9b4f9fb8ca51c766ea5c652ed561d9b5f719d3b558766d7dc646ac471d9b5f718ea3902766d7dc6528e3b005b5f71a9bb558766
  | 5, 0, 5 => 0xd7dc652ba471d9b9dafb8ca51c766d7dc652e0561d9801afb8ca51c765006be528e3b05d75f7194a38ec136d7dc6a929471d9b5f87b8ca51c766d7dc652e5561d9ba3afb8c851c766e45c65303561d9bc3afb8ca51c766d7ca626ed561d9b5f7194c291c766d7dc6ad29471d9801afb8ca57e8e5
  | 5, 0, 6 => 0xd7dc65303471d9b5f7194b991c766d7dc6531f471d9b5f8f94bb558766d7dc6528e3b031b5f71a74a51c766d7dc68d29471d9ae329823b536766d7dc6528e3b03db5f2947214ec676d7dc652eb561d9b777194bb558766d7dc6528e3b001b5f7194a751c766d7e9652ed471d9b5fa3b8bb51c766
  | 5, 0, 7 => 0xeaebee329471d98017194a38960b5b8d3252ed561d9b5f8e94a390a766d7dc68c8e3b18db5f8eb8ca59c766d7dc6528e3c1d9b5f7194ac51c766b8d8652ac471d9b6d7194bb558766d7dc53a8e3b18db5f7194a38ec5d6d65c652ed561d9b5f7194b691c766ecdc652ac471d9b5f7194a38ec2a6
  | 5, 0, 8 => 0xd7dc6528e3b0e9b5f71a0ca51c766d7dc652a7471d98017194b2d1c765d7dc6728e3b161b5f7194a38ec4e6ee5c652ed561d9b5f2962ab11c766d9ebee329471d9b5f7194a4d1c766d7dc6e329471d9ae33594bb558766d7dc6528e3b05d801c8b8ca51c765d7dc6528e3b021b5f7176ab0ec156
  | 5, 0, 9 => 0xe65c652ac471d980184b8ca51c765d7dc652ef471d9ae35594bb558766d7e1ae329471d9b0f84b8ca51c766d7dc6530b471d9b5f7194a38ec186d7dc652ed4c1d9b5f719cca51c766d7da652ac471d9b5f7194a38ec706d7dc6528e3b049b9fcab8ca51c766b8ca5f6ed561d9b5f71a84a51c766
  | 5, 0, 10 => 0xd7dc6528e3b059b5f71a64a51c766d7dc652f4561d9b9f7194a991c766cfdc68ced561d9b4b6794bb558766d7dc5a2ac471d9b5f7194a38ec426e9ebee329471d9b5f7194bf158766d7dc5f0ed4d9d9b5f7194ad51c766d7dc5f0ac471d9b5f80b8ca51c766d7dc652ed651d9b5f7194a38ec276
  | 5, 0, 11 => 0xb8d3252ed471d9ae2ed6cb4558766d7d9e528e3b19dbb7cfb8ca51c766d7e95dadd561d9b5f7194ba91c766d7dfe52ed561d9b5f7197bb558766d7dc578ac471d9b5f71aeca51c766d7dc65320471d9b5f7694bb558766d7dc6bf29471d9b5f7194b311c766b8d4a52ed561d9b5f7194a38ec2b6
  | 5, 0, 12 => 0xd7e8ee367471d9b5f5b94bb558766d7dc6528e3b019b5f7194b391c766d7e2652ac471d9b5f71aaca51c766d7dc6531d471d9b5f7194a38ec116d7dc65307521d9b5fa794a38ec676d7dc652ed521d9b5f7194a851c766d7dc6528e3b069b5f7194b511c766d7dc6528e3b155b5f7194a38ec1f6
  | 5, 0, 13 => 0xd7dc6828e3b19db5f7194bb552766d7ca60eff471d9ae36194bb53e766d7dc6528e3b0a1b5f297fbb51c766006bee323471d975f7194bb55a766f0dc6cf29471d9b5fa7c74a51c766d7dc6528e3b079b877194bb558766d7dc652a8471d9b5f7194a38ec666d7dc652ed561d5b5f8eb3ca51c766
  | 5, 0, 14 => 0xd7ca5daac3b081ba5afb8ca51c766d7dc652993b19db95a594bb558766d7dc652fa561d9b5f7194a38ec026d7dd2e329471d9b5f7194bb57eac6d7dc6528e459d9b5eed6ab4558766d7dc6528e3b1b9ae36594bb558766d7dc652f6471d9b5f71a0bb5b0766d7dc6531a471d9b037194bb558766
  | 5, 0, 15 => 0xd7dc652e2471d9b5f71953b558766b8ca628ed561d9b4b2976ab14c766005c65304471d97b1afb8ca51c766d7dc652ed679d9ae3296732d1c766d7dfe52ed471d9bc36994bb558766d7dc662ed561d9b5f719fca51c766d7dc6528e3b041b5f9ab8ca51c766d7dc652ed561d9b6fafb8ca51c766
  | 5, 1, 0 => 0xd7eaee329471d9b5f7194b711c766d7dee52ed561d9b5f7194ab132766ede9652ed561d9b5f71b7ca51c766d7dc65302561d9b5f719cab11c766d7dc6528e3b1a5b5f7194a38ec416e26bee329471d9801d9b8ca51c765d7dc5b6d1471d9b5f719a4a51c766d7dc682ac471d9b87afb8ca51c766
  | 5, 1, 1 => 0xd7dc652bf471d9b5f7194b351c766e8ebee329471d9801afb8ca4963c5d7dc6528e3b039ae32976b2d58766e7dc6528e449d9bc3cab8ca51c766006be52c5471d975fafb8ca51c766d7dc652ed559d9b917194bb558766e86bee329471d9b877194bb51c766d7dc652ed489d9b5f7194bb54a766
  | 5, 1, 2 => 0xe7ebee320471d9b5f7194c5d1c766006bed329471d977f7194bb558766d7e6ee329471d9b5f71943b558766b8ca5daac3b135b5f71902b11c766cfdc652ac471d9b5f7194a38ec626006bee28e2588975fa7b8a3902766d7e32e329471d9b5f7194bb57e8e6d7dc652df561d9b5f7190ba558766
  | 5, 1, 3 => 0xd7dc65301471d9a53047fbb558766d7e968ced561d9bc7afb8ca51c766d7dc6c529471d9801afb8be11c76500732e329471d975f7194a38fa766d7dc5daac4f1d9b5f7194c391c766d7dc652ed471d9b097194bb558766f0dc652a6471d9b5f7194a38ec396d7dc6528e3b1d9b5f7194a38ec6a6
  | 5, 1, 4 => 0xd7dc6528e3b141b5f7194b151c766f0f6ee329471d9b5f71984a51c766d7dc6528e421d9b5f7194bb52c766d7e8ee329471d9b5f7194a38ec4f6e46bee329471d9bc3dbd3bb558766d7dc6d729471d9b5f7194ae558766dc5c652ed561d9bbfafb8ca51c766d7dc68929471d9b5f7194a38ec656
  | 5, 1, 5 => 0xd7dc652ee561d9b5f7192bb558766e45c652ed471d9b5fa4b8bb558766d7dc6d329471d9b5f71a7a3902766d7e46e329471d9bcdafb8ca51c766d7dc652ec471d9b5f7194b2d1c766006bee2bc471d975f71ad4a51c766d7dc6528e3b051b5f7194a390a766d7dc65321471d9ae36794c751c766
  | 5, 1, 6 => 0xd7dc6530d471d9b5f7194ab0ec466cfca5daac3b19db5f7194a38fe766d7dc6528e3b11dad3298ebb558766d7dc6528e3b0e1b5f7194a38ec076b8d9e528e3b1b9ae34fa64a51c766b8ca5dacb471d9b5f7194a3914766d7dc63add471d9b5f84b8ca51c766006bf1329471d97697194bb558766
  | 5, 1, 7 => 0xe55c6531d471d9b5f7194a38ec1c6d7dc6528e401d9b5f29673151c766d7e26e329471d9b5f7194afd1c816d7dc6528e3b191ad32976ab0ec6e6d7dc6528e431d9b4b9f94bb558766d1e7ee2ed561d9b5f7ab8ca51c766d7ca5dad86a9d9b5f71a44a51c766b8ca5b2ac471d9bc3afd3ca51c766
  | 5, 1, 8 => 0x6bee339471d96e3298ea991c766ce5c652ed561d9b5f71b3ca51c766edebf4f71471d9b7dafb8ca51c766ecdc652ed561d980171471d8440b5006bee341471d9401afb8ca51c4b5006be528e2585d75f7194a38ec726005c652761e02d75f7194a38ec3d6d7dc6528e409d9ae329823b558766
  | 5, 1, 9 => 0xd7dc646ed471d9b957194a38ec6e6f0dc6528e449d9b5fa7b8ca51c766d7dc6528e3b08db5f8294bb558766d7dc6528e3b089b5f7194bc51c766d7dc652ed581d9801afb8ca532765d7dc6528e3b0ddb5f71a03b558766d7dc653036c1d9b5f7147204ec636d7dc65310471d9b5f7194a38ec1b6
  | 5, 1, 10 => 0xd7dc6528e3b131801afb8c811c7650067ee329471d96e32953238ec6e6d7e62e329471d9b5f7194a38ec596d8dc652ed561d9b5f71672f11c766d7dc653034c9d9b5f7194a38ec736eddc6531d471d9ae32976ab0f4766d7dc652e3471d9b5f2976b1558766d7dc6528e3b075b5f7194b851c766
  | 5, 1, 11 => 0xb8ca60f04471d9bb77194a38ec6e6d7dc65295471d9b5f7f94a38ec586d7dc6528e3b15db5f7194a38ec496d7dc638ed561d9b5f7194bb56a766d7dc6528e3b151b5f717c3b558766e65c652ed561d9b8b7194bb558766ecebee329471d9b5f717bbb558766d7dc6528e3b085b5f6994bb558766
  | 5, 1, 12 => 0xd7dc5dabc561d9ae36194bb51c766d7dc5daac3b121ae32976ab0ec246d7dc68d1d471d9b5f297f3b558766d7dc6528e3b011ae357aaca51c766d7dc6528e3b00db5f7194a38ec056ecdc65317471d9b5f71a7ca51c766d7dc6528e439d9b5f7194b211c766d7dc6528e3b16db5f7194b28ec676
  | 5, 1, 13 => 0xd7dc68b29471d9b99afb8ca51c766d7dc6528e3b111b5f7194a38ec3b6d7dc65b29471d9b5f8994bb558766d7dc652e9561d9b877194a38ec586d7dc6c729471d9b5f718f3b558766d85c652ed561d9b916994bb558766e56bee329471d9b5f7194a38ec3e6d7e7ae329471d9b5f7194a38ec5a6
  | 5, 1, 14 => 0xd7dc6528e3b0b1b5f7194a38ec6f6d7dc6528e3b1618017194a38ec0b5d7dc68ced561a980129471d82e0b5d7dc6cd29471d9b5f7194b911c766d7e5ae329471d9b5fa376ab0ec676d7dc652ac479d9b5f7194c551c766d7dc6528e3b1a1b5f71893b558766d7ca5aaba561d9b5f7194a991c766
  | 5, 1, 15 => 0xf16bee329471d9b5f7194c651c766d7dc682ed561d9b5f7194a38ec566d7dc6528e3b029b5f719dca51c766d7e92d2ed561d9b5f7194a38ec636d7dc69729471d9bc3a3b8bb558766b8ca63a8e449d9b5f7194ca51c766d7dc652f9471d9b517194bb558766edebee329471d9b5f71923b558766
  | 5, 2, 0 => 0xd7dc65308471d9b5f71a1ca51c766d7ea6e329471d9b5fa7b8b751c766d7dc6528e3b0d5b5f7194a711c766d7dc6528e3b099801afb89d878225d7dc252ed561d9b91a794bb558766d7dc652ca471d9b5f7194a38ec256b8d7252ed561d9b5f8794a38ec676d7dc672ed561d9ae32947224ec6e6
  | 5, 2, 1 => 0xd7dc6528e3b0bdb5f7194a38ee766d7dc65290471d9b5f2976ab0f2766eeebee329471d9b5f94b8ca574766d7dc6528e3b0f1b9171a0bb558766d7dc640ed561d9b3f7194bb558766d7dc6528e3b181801afd2ca51c765d7dc6528e3b129801afd1dc51c765d7e3b0f29471d9b5f77b8ca51c766
  | 5, 2, 2 => 0xe45c6528e3b19db5f7194a38fc766d7e7ee329471d9b5f7294bb558766d7dc652ed591d9b5f75b8ca51c766f26bee329471d9b5fa5b8ca51c766d7e3ae329471d9b5f719b4a51c766d7dc6528e449d9bcbafb8ca51c766d7dc6528e3b0c5b997194a3902766d7dc6528e3b12db5f7194a38ec676
  | 5, 2, 3 => 0xd7dc658ed561d9801afb8a38ec225006bd1c761105d40171a64a51c765006bee3293b0f1401af949d878175d1dc5daac3b1b9b5f7194c991c766d7dc69b29471d9b5f7194c451c766d7e16e329471d9b5f8994a3902766e7ebee329471d9801afb8ca594765d7dc68f29471d9b47718ebb558766
  | 5, 2, 4 => 0x35fa7b8d191c766d7e96531d471d9b95afb4ca51c766
  | 6, 0, 0 => 0xd7dc652ed692b0ecfafb8ca618ed561d9f5f7194bb54c8e3b3ebee32976ab0ec257d7e1e52ed561d8cee00d7dc6528e471d9b5f719eca5daac3b38035f2976b5558766005c652ed3b0d816c00d7dc6528e3b02dbc5afb8ca5daac3b3ebee3297ebb558767d7dc6530f76ab0ecfafb8d5e52ed561d9f5f7194bb5d2ac3b3ebee36394bb51c767
  | 6, 0, 1 => 0xd7dc652ed471d858fafb8ca5da8e3b161c017194bb51c7605b6beef7194bb558767d7dc6530876ab0ecfafb8ca5dae8561d9f5f7194bb5587638bebee34394bb558767d7dc652ed561d85afafb8d9252ed561d9f5fa9b8ca5daac3b3ebf4f7176b7558767d7e52e32976a38ecfafb8ca5daac3b0d5f5f7194bb5589c3b3ebee32976ab0ec267
  | 6, 0, 2 => 0xeeebee32976ab0ece00d7dc652db471d9b5f7194bb558761e3f835f7194bb558767d7e42e32976ab0ecfd6d7dc652ed561d9c01afb8c85daac3b36bee32976ab0ec457d7dc6bd2976ab0ecfafb8ca5daac3b181c01afd2ca5daac3b36bee32976ab0ec4a7006bf477176ab0ecc00d7dc652ba561d9bb7afb8ca5da8e3b3f5f5f7194bb550767
  | 6, 0, 3 => 0xf2ebee32976ab0ece00d7dc652ac258b1b5f7194bb55876183ebee32976ab0ec0d7d7dc652ed561d896fafb8ca5da8e3b18df5f7194bd5daac3b3ebee32976ab0ec677d7dc652ce56238ecfafca5c652ed6d9d9f5f7194bb5aaac3b3ebee32976ab0ee767d7dc6531d56238ece00d7dc65303561d9b5f7194bb558a43b38035f7194bb53e766
  | 6, 0, 4 => 0xd7dc6530976ab0ece00d7e1ee329471d9b5f7194bb5d08e3b3ebee32976ab0ec5c7007875f7194a38ecdafb8ca5daac3b0d1f5f7194c15daac3b3ebf3f7194bb558767d7dc652ac471d8dcfafbadc652ed561d9fc9afb8ca5daac3b3ebf4b7194bb558767d7e3ae32976ab0ecfafb8cda52ed561d9f5f7194bb558893b3ebee35794bb51c767
  | 6, 0, 5 => 0xb8d8ec32976ab0ecfafb8d4652ed561d9f5f7194bb51c761e38035f71a34a51c766d7dc6531176ab0ecfafc2dc652ed561d9f5f7194bb5587c3b3ebf337194bb558767d7dc6532376ab0ece00d7dc6529d471d9b9fafb8ca5daac3b3ebee32976b5d58767e45c652ed561d8cee00006bee329471d975f7194bb558ac3b380001af94a38ec175
  | 6, 0, 6 => 0xd7dc652ed561d86cfcad7da652ed561d9f5f7194bb55eac3b38035f7194a38ec176d7dc652f276ab0ecfafb8ca5da8e449d9c01afb8bb558761130035eed561d844176d7dc652ed6eab0ecfafb8d5e52e1561d9f5f92b8ca5daac3b3ebee32976a38ec4b7d7dc652ed471d8cefafb8ca5daac3b179f5f7194c99daac3b3ebee329712b11c767
  | 6, 0, 7 => 0xd7dc6530756238ecfafb8ca5daac471d9c0171aaca5daac3b36bee32976ab0ec297d7dc652ed561d816fafb8ca62eac471d9f81afb8ca5daac3b3ebee329833b558767d7dc65d2976ab0ecfafbe5c652ed561d9f5f7176b75587631bebf4f71a33b558767d7dc652ac51238ecfd1d7dc652ac471d9f5f8eb8ca5da8e3b3ebf4b298ebb558767
  | 6, 0, 8 => 0x6bee329769d878dafb8ca5dadb561d9f5f93b8ca5daac3b3ebee32976ad4ec2c7d7e0ee32976ab0ecfafb8ca5588e429d9f5f2976b89587633b8035f71769d86c226ebebee32956238ecfbcd7dc652ed561d9f5f7194c45da8e3b3ebf297194b9158767e7ebee32976a38ecfafb8ca5dad9561d9f5f719f4a5daac3b3ebee32983bb536767
  | 6, 0, 9 => 0xd7dc652ed471d816fafb8ca5daac3b005f5f7194bb55876173ebee32976ab0ec097006bee32967238ecdafb8ca5daac3d9d9f5f7194bb51c761b3f1f5f7194bb558767d7e76e32976ab0ece00d7dc6531d471d9801afb8bb51c761136bf5d7194bb558767006bee32976a90ecdafb8ca5dadd471d9f5f7194be1daac3b3ebee3298b3b558767
  | 6, 0, 10 => 0x6bee32976ab0ecc00d7ca5daac3b05db5f7194bb5587609bebee35494bb558767d7e1ee32976ab0ecfd1d7dc642ed561d9fc3afb8ca5daac3b3ebee35694bb558767d7dc6531876ab0ece00d7dc6528e3b1b9b5f7194bb5a0ac3b3ebee32976b7958767d7dc652ed561d832fafb8ca5daac3b185f5f7194bb51c8e3b3e9f3f7194bb558767
  | 6, 0, 11 => 0xeaebee32976ab0ece00b8ca5daac2582db5f71a33b5587631bebee36794ab11c767d7dc652ed561e0ecfafb8ca5daac3b175f5f7194c0ddaac3b3ebee32976b9958767d7dc6531f76ab0ece00d7dc652e2471d9801afb8ca5588e25b6bee32976ab0ec0c7d7dc652ac47204ecfafb8d1a52ed561d9f5f7194bb55876003ebee32976ae958767
  | 6, 0, 12 => 0xd7dc652ed561d830fe1d7dc652ed471d9c01afcddc6528e3b36bee34194bb558767d7dc652ed5629cece00e8ebee329471d9801afb8ca5da761b36bee32976ab0ec4e7006be52ed3b0d82edb3d7dc652ed561d9f5f71b8ca5daac3b3ebee32976ab0ec17700722e32976ab0ecdafb8ca5daac3b021f5fa7b8ca5588e3b3ebee32956238ec227
  | 6, 0, 13 => 0xd7dc652ac471d8b6fafb8ca5daac3b059f5f71a34a5da8e3b3f4f5f7194bb558767d7dc652ed4ea38ecfafc05c652ed561d9f5f7194bb5587613b8035f7194bb51c76600612e32976ab0ecc00d7ca5da8e3b05db5f7194bbddaac3b3ebf0f7194bb51c767d7e1ae32976ab0ecf87c25c652ed561d9c01afb8ca62e8e3b36bee32985bb558767
  | 6, 0, 14 => 0xd7dc652ed561d80cfafb8ca5dace561d9f5f71aaca5daac3b3ebee32976a38ec177d7dc6531d76ab0ecfafb8ca5daac3b045f5fa794bb5587633bebee32976ab142767d7dc652ed561d83efcad7dc652ac471d9f5f6794bb5587633bebee32976ba958767006bee32947214ecdafb8ca5588e3b17df5f7194bb5587615bebee34f94ab11c767
  | 6, 0, 15 => 0xec6bee32976ab0ecfafb8cfe52ed561d9f5f7194bb55876083edf5f7194bb558767d7dc652ed561d804fafba5c652ed561d9f5f7194bb55876373ebee3297b3b558767d7dc6531a76ab0ecfafb8d05daac3b19df5f2983bfddaac3b3f86e36794bb558767d7e52e32956238ecfafb8ca5daac3b079f5f7194bb55876333ebf4771b3bb558767
  | 6, 1, 0 => 0xf0f2ae32976ab0ecfafd7dc652ed561d9f5f7194bb5b07633b8035fa7b8ca51c766d7dc652ed6e2b0ece00d7dc6528e3b089b5f71b7ca5daac3b38035f71b3ca51c766d7dc652ed561d8d2fc4d7dc652ed561d9c01d9b8ca5daac3b36bee2ed6db4558767d7dc652ed712b0ece00006bee3294712d401afb8ca51c813b3002e329823b558766
  | 6, 1, 1 => 0x6bee329471d8b6dafb8d1252ed561d9f5f7194bb5587632b8035f7194bb56a766d7dc6c52976ab0ece00d7dc5f0ed561d9b5f7194c39daac3b3f86e32976ab14c767d7dc652ed561d8ecfafb8ca5daac3b1a9f5f7194c5ddaac3b38035f6994bb558766d7e6ee32976ab0ecfafb8ca5daac3b189c01afb8bb5584b1137475f7194bb558767
  | 6, 1, 2 => 0x6bee36394a38ecdafb8da652ed561d9c01cad7dc6528e3b379b5f7194bb558767d7dc652ed762b0ecfafb8ca5daac3b051f5f7194bb558853b3dc6cf298ebb558767d7dc652ed561d8a0fe1eddc652ed561d9f5f71984a5daac3b3ebf477194bb558767d7dc652ed561d89efc8d7dc652ed561d9f5f71b5ca5daac3b38035f71a7ca51c766
  | 6, 1, 3 => 0xd7dc652ed561d838e00d7dc652ed3b0cd801dbd7dc6528e3b37875fa794bb558767006bee329471d858c00d7dc6528e3b161b5f7194c1dda8e3b3800017194a38ec0b5d7dc652ed561d88ef71b3ca5daac3b1b9c01afb8ca54c8e3b30035f71949d86c2c6d7dc652ac56238ecfafb8c75dadd561d9f5f84b8ca5daac3b38035f7194ba558766
  | 6, 1, 4 => 0xd7e9ee32976ab0ecfafb8ca5daac3b08df5f7194bb55876113ebee32976ab0ec377d7dc652ed561d836f7194c75daac531d9f5f71b3ca5daac3b3f6f5fa7b8bb558767005c5daac3b08816c00d7dc682ed561d9801afb8ca5daac25b0035f2976ab096176d7dc652ed561d8e4fafb8ca5daac409d9c01afb8ca51c7631b72ae3298ebb558767
  | 6, 1, 5 => 0xb8ca60f0476ab0ecfdbb8ca5daac3b1b9c01afb8ca51c7633b6bee32976ab0ec497ecebee32976ab0ece00d7dc6528e3b0f1b5f7194bb5587610bebee32976ab0ec4c70067ee32976ab0ecd7194bb558a63b1b9c01afb8ca5ea761b36bee32976ab0ec737eddc6531d76ab0ecfafb8ca5dae3561d9f5f7194bb5c2ac3b3f2ae32976ab0ec6e7
  | 6, 1, 6 => 0x6bee32988a38ecdafb8ca62aed561d9c01cfd7dc6528e3b36bee34594bb558767d7dc65b2976ab0ecfcad7dc652ed561d9f5f9eb8ca5daac3b38035f8eb8ca51c766006bee32947224ecdafb8d1a3aed561d9f5f7194bb5587601bebee32976ab0ec057ecdc6531776ab0ecfafb8d3e52ed561d9f5f7194bb558762db8035f7194a38ec4b6
  | 6, 1, 7 => 0x35f7194bb55876053ebee32976ab0ec637000035f71471d844a00006bee3293b0f175f7194ca5daac3b3f6f5f7194bb558767d7dc652ed561d8b0e00b8ca5daac3b02d8012976ab0ec1705b6bee36694bb558767
  | 7, 0, 0 => 0x35f7194bb558766000035f2976ab0ec176006bf0f7194bb558767007875f7194bb558767006bee32976b6d58767006bee32976ab11c767006bee32976ab0ec0b7006bee32976ab0ec367000035f7176ab0ec226006bee32976b7558767006bee32988bb5587670000001afb8ca51c765006bee32976ab0ec4b7006bee32976ab0ec677006bee32976ba158767006bee35794bb558767
  | 7, 0, 1 => 0x72b5f7194bb558767006bee32976ab0ec5b7006bf4f7194bb558767006bee32976ab0ec227006bee36794bb558767000035f7194bb5584b6006bee3298bbb558767006bf377194bb558767007475f7194bb558767006bee32976b8958767006bee32976ab0ec6e7006bee3298ebb558767000035f7194bb51c766000035f7194bb4ec366006bee32976ab0ec177006bee34694bb558767
  | 7, 0, 2 => 0x6bee32976ab0ec6370076f5f7194bb55876700002e32976ab0ec0b6
  | 8, 0, 0 => 0x35f7194bb558766
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]

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
private theorem z4_192 : span (Z 4) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_216 : span (Z 4) 7 216 = true := by decide +kernel

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

private theorem z4_a9 : span (Z 4) 223 0 = true :=
  span_join (f := Z 4) (a := 216) (o := 0) (b := 7) z4_a8 z4_216

private theorem z4 : span (Z 4) 223 0 = true := z4_a9

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
private theorem z5_576 : span (Z 5) 3 576 = true := by decide +kernel

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

private theorem z5_a24 : span (Z 5) 579 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 3) z5_a23 z5_576

private theorem z5 : span (Z 5) 579 0 = true := z5_a24

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
private theorem z6_360 : span (Z 6) 18 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 378 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 18) z6_a14 z6_360

private theorem z6 : span (Z 6) 378 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12485

theorem PEqualNP.Outside.L_meta_12485 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264000 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12485.mainG PEqualNP.Outside.L_meta_12485.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12485.CG, PEqualNP.Outside.L_meta_12485.CG_mono, by
      have : PEqualNP.Outside.L_meta_12485.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12485.CG_eval⟩
