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
namespace PEqualNP.Outside.L_meta_12605

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 6, 7, 3, 3, 3, 11, 3, 13, 14, 15, 3, 17, 3, 19, 3, 21, 22, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 33, 3, 35, 3, 37, 38, 39, 3, 41, 42, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 6, 6, 6, 3, 6, 6, 6, 7, 6, 6, 6, 11, 6, 13, 14, 15, 6, 17, 6, 19, 6, 21, 22, 23, 6, 25, 26, 27, 6, 29, 30, 31, 6, 33, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 3, 7, 7, 6, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 17, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 6, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 17, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 33, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 13, 6, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 17, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 14, 6, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 17, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 15, 6, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 17, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 17, 17, 17, 3, 17, 17, 6, 7, 17, 17, 17, 11, 17, 13, 14, 15, 17, 17, 17, 19, 17, 21, 22, 23, 17, 25, 26, 27, 17, 29, 30, 31, 17, 33, 17, 35, 17, 37, 38, 39, 17, 41, 42, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 58, 59, 17, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 6, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 17, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 33, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 6, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 17, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 22, 6, 7, 22, 22, 22, 11, 22, 13, 14, 15, 22, 17, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 23, 6, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 17, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 6, 7, 25, 25, 25, 11, 25, 13, 14, 15, 25, 17, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 33, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 26, 6, 7, 26, 26, 26, 11, 26, 13, 14, 15, 26, 17, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 27, 6, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 17, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 6, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 17, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 6, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 17, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 6, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 17, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 33, 33, 33, 3, 33, 33, 6, 7, 33, 33, 33, 11, 33, 13, 14, 15, 33, 17, 33, 19, 33, 21, 22, 23, 33, 25, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 42, 43, 33, 45, 46, 47, 33, 49, 33, 51, 33, 53, 54, 55, 33, 57, 58, 59, 33, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 6, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 17, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 6, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 17, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 6, 7, 38, 38, 38, 11, 38, 13, 14, 15, 38, 17, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 6, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 17, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 6, 7, 41, 41, 41, 11, 41, 13, 14, 15, 41, 17, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 3, 42, 42, 6, 7, 42, 42, 42, 11, 42, 13, 14, 15, 42, 17, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 33, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 3, 43, 43, 6, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 17, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 6, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 17, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 6, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 17, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 6, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 17, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 49, 6, 7, 49, 49, 49, 11, 49, 13, 14, 15, 49, 17, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 6, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 17, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 6, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 17, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 6, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 17, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 6, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 17, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 6, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 17, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 58, 6, 7, 58, 58, 58, 11, 58, 13, 14, 15, 58, 17, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 59, 6, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 17, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 6, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 17, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 6, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 17, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115111511151737111511151115173711151115111517370000000000000000111511151115173711151115111517371115111511151737000000000000000011151115111517371115111511151737111511151115173700000000000000001115111511151737000000000000000011151115111517370000000000000000111511151115173711151115111517371115111511151737000000000000000011151115111517371115111511151737111511151115173700000000000000001115111511151737111511151115173711151115111517370000000000000000111511151115173700000000000000001115111511151737000000000000000011151115111517371115111511151737111511151115173700000000000000001115111511151737111511151115173711151115111517370000000000000000111511151115173711151115111517371115111511151737000000000000000011151115111517370000000000000000111511151115173700000000000000001115111511151737111511151115173711151115111517370000000000000000111511151115173700000000000000000000000000000000000000000000000011151115111517371115111511151737000000000000000000000000000000001115111511151737000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c80000000000000000eeeaeeeaeeeae8c8000000000000000000000000000000000000000000000000eeeaeeeaeeeae8c8eeeaeeeaeeeae8c800000000000000000000000000000000eeeaeeeaeeeae8c8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8eeeaeeeaeeeae8c8

def cMZZ : Nat := 0x1115111511151737000000000000000000000000000000000000000000000000111511151115173700000000000000000000000000000000000000000000000011151115111517370000000000000000111511151115173700000000000000001115111511151737000000000000000000000000000000000000000000000000111511151115173700000000000000000000000000000000000000000000000011151115111517370000000000000000000000000000000000000000000000001115111511151737000000000000000011151115111517370000000000000000111511151115173700000000000000000000000000000000000000000000000011151115111517370000000000000000000000000000000000000000000000001115111511151737000000000000000000000000000000000000000000000000111511151115173700000000000000001115111511151737000000000000000011151115111517370000000000000000000000000000000000000000000000001115111511151737000000000000000011151115111517371115111511151737111511151115173700000000000000000000000000000000111511151115173711151115111517370000000000000000111511151115173711151115111517371115111511151737

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
  | 4 => 234
  | 5 => 623
  | 6 => 393
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xa05544d6
  | 3, 0 => 0xf0b23000e58430e1e0e35e79b230e3a7a4bc442d9c56c12692a233b3903132dd881b92c556f717974e2d4f444252ab650cbd4e3c042b7e00
  | 4, 0 => 0x341743a132a8ae3d31b5e70e303682302f43984e2ea973452e696f932dd805052cc26d1d2c48f7622bb67aec2b14242b2ad610cf292bac152878d9502644736425413b2a231c5f84231c18e722b4fda2217efa2d2107623e20f633bc1f47c0fd1d36f9771c3d842a1bc95af41b8c9a6c19cd497919cb81681821c9d01782650015ff271114e60f2f14d86022133c560710da671210ce54b610cd5cab10196e6e0fc326780f96c5580eccefac0e97d8710d51baa80d01839f0c3d02fe0b85b2630b0528130ada439609f3883508b006f8071d3585071a1a4705d1a9c5052f233304e5f54c04b339fd045e952f036c59a103227c0602452bc001b8d13701b35cf1
  | 4, 1 => 0x789666c6785f65fe78249ca0780faee577a69eea7413ce7172c46d157048ded96f1fa59e6d0a57f46924c71c67b81d106586eaf96528ec5164e9e7a26428e95f62449b8a6204c8a9616ff75a608999675fac65e95f38ceb95ef6ce8d5e62991c595680a75861922557cac0f156f336ef55a3a4bb5561a48f54f0c41452e1064f4e7457ba4e56a75b4df755ad4d9f12354cd9da474bdebb754b86a38d49abf6f4495b7af9487edaaf47929b93471e4440455aa26d45531cb3446aafa343cb8f1c43ab9fc1430702d642e4d3bb426fb7464253d8b3412b53b03feb1f913f7fd77d3eca31ec3c51c33e3b2282eb3a56b1ac37e6150236ffc77835d5102a3426478f
  | 4, 2 => 0xc9880b3dc7be11aac56c9472c51250b4c37b1478c2abfd99c1476390c06fc24bbeee9952bc15ab0abbc5f936bb3fd1d2bb2eab42b9ffa329b70e64c7b6fc7c82b3523d67b26d14f2b1998144af633e16ac34d533ab2c5925aa97ead2aa173dd9a991d284a8396e96a6e23d79a340bc16a2bfa583a0ef24649e87ab879de9235c9d2453249c3ef90f9aaa9e2098421063981bb95395c6d0e99586c28a954c70cc9524551d91f4a92f914061e690565ca88e1cf6468c81f9298c657ca78bb746ce8acf72f68a432af189f3749787023a3f8684f51086520222865071618611abe1855e6bb78524b98a84eadac68424b6988129126c7d2d3de27c92928b7a732d56
  | 4, 3 => 0xfe7c196dfe23c2b0fd8c9208fbc71dc8f9816961f42f4b20f365e801f317f3a3f301e1c9f2b0b523ef630181eaad5be4eaad0542e8a8b6d2e895a081e81b257ee7aee520e5aef754e41dca45e393ccb9e11412b1e111cfc9e07ea193e0144573db397aa5d96b5375d7d59562d74814fbd6d1daedd63f87dbd3a40cefd3135803d148a2d9d105d06ed0240dc8d022f161cd8789f1cd3a2659ccd0ac59cba3077ccab831faca56fc7c
  | 5, 0 => 0x12993718127e260d1259fe7f11473b9c111b574d1111d41411089bd910cd5cab10be930c0fce38f00fc537dd0f9cde380f68680c0f64a8700f4630490f0a57550eee4ad70e8da9260e6fcab50dde40650dd30b290d6306690d42a22a0cc0553c0c1dedd20bf8a5d90ada43960a9444670a3e66690a341a3d09f38835099fabea093d8eef093463d6092a2e0a0899939c083aa098080e342c07fe88500790e5ea06c8ec4606922aa30688121c05d1a9c505c0dde705b5578705aab7ae051811b5048fce23040ee16803a5e0ff03a1a89a034b7c7b02cee38502c3eea8026fb03902487d2e01da66c901c7669b01b0ed9c01906c4d00d0870c00b8da8200511f44
  | 5, 1 => 0x274704622726c8bc26742624265b41e42658ecc725d62ccb2474558a245970dd24090d7623e8f61a23e0b15c23a7aec62393e512238fe231222a985221c419b0218e16ff1ffa16a91f9580b21f76e8f11f47c0fd1e957dc01e7bf3f81e4cf9ae1e1247e81df65a6a1de4cc391dde6ad61d8b12561d8adacf1d5299bc1d0ec6df1cfc85701cc75aab1c6a9d501bf12ed61bd19d591bc95af41b2e53711afd216a1add63c11acdba4e1a6ace581a22d07419c9e2d119c6747b19bc9102196362ee1918443f1907644118d7971018cc50391874c155185f1fc31853e55f182ef78b17d16a5a169e783416142bcd14aea32214a83af914a3d7f6139c83fe12ce2686
  | 5, 2 => 0x39426aca392a7bb7389f912e381a03b636ff26ec36dd567a36720e663655359a35e8fc5e35d5bf273515ebcb34fdcdf5345b7b0f340e52e533bb933833a39d03339754cf33794cba331c59e432c5328432abce0732a4bd5a329c4036328c3971327d2290324a3945321b191b3213c87b3204e56c31ebcda131d0f4e731afd107317c4446317c1233313a0f3131399ed330995e99307fed67306442053027330f2ffe0d5d2fac76672f5298ab2eeef2dc2e2d510e2dd805052d8312382d69b6cd2d5826682d1ad4452cb3ed872c92024b2c41e7712c377a162c1c96892b5e5dd62b46e30e2b0a97cf2afbe3b62ad610cf2a05530b29bff31228464aac27794acb
  | 5, 3 => 0x5228452950588b914fda05fd4fd17aec4fb039474f90e97e4f1ed5ac4f058a0e4e693acf4e43425b4def5f804d0e01204cef5c8e4cca9dc54c46b2674c2d51644c272bd74b6ec8cb4ae76bf54ac6bee54a35ee61499be6a04921132f47f2f66247b077ea478c242e477801354722e69646d21108469784a4464fcaf14625de3e45330bc044b6b86c44b200f944acdc92446008f843cb8f1c43b55334435fb68e433950a34334d43241bec53a41b092e74128055440bd05c2401bd3c9401307273fee1bc63f8662ab3f7fd77d3ea50e503e4ed24b3c5766393b6e360b3b530d193b2282eb3ae607673a7d827c3a6c3a533a69e92c3a1b98af3a11371839ec4996
  | 5, 4 => 0x6740ffbe662ee7f065d5b6fb656858976528ec516524ed3164d96ad864d41f6e644355c46428e95f640174da62fb0e2e62cb53a0626170f8622a3d1961ddfef361658774614cecd36136982e611cc7d960a77085606a96515fc333735fa882e85f53bf2b5f2e611f5ef6ce8d5e7eb8885e0022375de450a85d907b435d42e68c5d2b83c85c9b8ed25c9453205c8a6e7c5b7b10855b6baef05b5bb8c55b29aec45ae967cd59a9dc2a59a6f108596f2ea0588f2f3258892a795861922557c18a2057a580705790e785578db445575b4618568ad44f558c4aeb5561a48f5517250153e50810537a1c7a53288c5752dc79a452aea4c4526da919524e521e5230a63d
  | 5, 5 => 0x7b02530e7a72da98796f91ba78fe0a707882b73b77ec1fe877cebd4e777842be773ed55877113adb76fe6d00768a26137683e8e9765c13ca7646965975da62f8756aaf7f755fc95374f609dc7398152a7383993e72a35bdc725c1c7b7244171a71d6ebc1713aa93070fea8af70f302da70cc951270c5ba29704c11da700bbcf56fd51dbe6f972c2b6f835a646f212f816f16e4906e9e866b6e57f37a6dbed1c86d9f99846d9b01926d4075066cf511c36c86bbd46c597bbb6bfe9c556bee845b6b5407b66ad97bfd6a8d73766a6724e86a3883bc6a2a18fb6a0ce92669fcfb6769e204a969b50bd56992de5a68fb4948689fdb8467bcfe7b678f58e26741fc0b
  | 5, 6 => 0x9565f3029524551d9507ac8a94dcd13d94b66219941afa4a93a5ddd5933568cd932e08a292e7787892824aaf917f5103913e6f4e9130c46990ac1c3c909895a2902797588fcf42ab8f71ab118f3e43438edc96238eb7f7b48e8215fa8d91fd428cdfc6188c657ca78b562b068b1149b08a3f296f89f37497899b688d89922457893f37e688336d2887ff41f187ab4c3d8774dd8f870b36b9868989858650716186484774862ab52985a2e15e859ef471854c347784a06fce847811408448fc3d83b281a483b009f482cea118822c228e80f4c26c803582d27f1ed9467e8abc557e6926277e4f82107e2770337dfffba97dc267677cd19a3e7c92928b7b5f8e30
  | 5, 7 => 0xb163d6a3b0fdfb0ab0b30580b09791ffb08b2a16b04a525daf6383adaed3016aadd27c62ad7c18cdacff16c0ab82cbc7ab456132ab22a432aae67c88aa69887da9ba87d1a8ab505ea85e17d3a7869bc2a76a0eb0a758d866a69a5ca6a66e2696a5da4756a5d26fe6a3da3bd1a3ceb4e6a37270b6a3148b4ba2d3502fa2b360d4a2ae1b71a20ec3e9a1ec94cea1e6edc6a15b99c6a10a9900a0ef2464a0e7fe6ca0506e699f4944a49e8798909da722b09d2453249c9859779c2a14989b5984519b48c33b9b3a14719a2a43fe9a1bbddc99befbea998ceb07995e72bf9912b1ed98d84089988b94fa9842106396eeb2b296edd61596912403968090e995fdcf73
  | 5, 8 => 0xd7aed9bfd790889ad6d1daedd64ca8a5d63f87dbd34a2fa2d3357d68d31b8f84d2dbbd7ad2b052c9d182732ece94f295ce1ebb0fcd89c6a4cd13f543cce1fdb9cc969713cc7af9c7cb39f107c9fb8014c9b2f9e8c8e0c296c85bf2ccc78602aec6f2ab8bc546d7f2c4d0412bc49bcfa4c4601c91c42c5d42c3ba322dc2f2c70ac17903bec14c5c9dc14ad637c078290ac03e3e21bfdd5d22bf6a1fe3bf6718d3be47f1c7bdfe8fa0bd60d8f8bcb1c938bb68925bbae1b527ba8f22e9b9823579b96ab029b8f5ae42b8c4a0a0b8b8f02ab817778bb7618b79b74fb3e6b6c784f9b5faf802b5e3533db3f88527b3523d67b33856f4b31a4d16b2a2ac29b1e8c762
  | 5, 9 => 0xfe678edefd7dc4a2fd12041cfcf95df9fc57a865fc2c1437f9a04437f8c84914f893cad9f749d176f7237a66f621355ef4ce91fcf459d818f42c1630f370e222f365e801efddba8aee88e64eeddb86e1ed89d566ed73be52ecb9c045ec962decebaffa22eb6d3dbae8b8b4f8e82c049be828cb05e7c268cce6fcf778e51a6adce501857ae343136ee3203134e0b99a30e056a8b8e054ee52dece6c59de5540dedd819c32dd66e359dce62989dca12e3ddc6de04edb9a539ed7def0de
  | 6, 0 => 0x1dd80f131d8b12561d4fb2df1d0ec6df1cf026791c689a101b7c8de21b35300d1b10ac741a7644361a7053731a008260199af5801872714117fd6f5a17cc61b816694c9115d843511529bb7d14eb145514e309b8143c58891240180c12220e2e120a9949113b06e5106b97bb103fbdfa100d77911005bc220fc414ea0fbac6980f9f53170f9cde380f92eb2e0e6b44c50dde40650ddac2820dd30b290cb673d80bf112400b91c7e00ada43960a58e4ab0a4d224a0990fbc909721e6f09714995093463d60798c328076a3ba80765d8eb0651858505d53a0e0575e7ae04e2086e04d13f540448fc1901b5dc8900bc5f520092729f0074708000511f4400125a18
  | 6, 1 => 0x3ba8ef553b43c4ad3a7fdfca3a7d827c3a6d538d3a3385f536eef7fd36e6b1f6369849b236720e6635adafd635a79da7359cd3013595e957350a78a834373f3e337f94283251f0ba324a394531afd107313a0f313105200d2fac76672e748d6d2e2d510e2e1053c42d9cb3ad2d1ad4452d0ff03d2c9187bc2c1c96892c1bb65b2be9bed12b9e582b2b18509f2a5e6ab629b0cd2329478af428b48ef527794acb276b817f2763b3e427470462268dc3c62546105e244e990a23f5de1323d8024323a390bc2343f5ab23341e5a22c1f34521fa882221c419b020e12525209b7c512080c4d61ff02a761f9181921f7fea221f76e8f11f3881951e71e0fb1e6ed9eb
  | 6, 2 => 0x61cbafbb6177714c61552e6e5f2e611f5ec255745e372f405d6f4ff65d4cfa505d1aafd25c5d4cb95b772d615b6baef05b5f697d56c0792e5696a8f955c2a9c85528f67653dfacba53619930531565bd52f08c2a51ed07165075f23350588b915033667c4fb8753b4f058a0e4ef55b1f4e1272364c7b7f6a4c757cc54bebe5644bc1815d4b13ee824b0aabcb4a942bb94921132f48c2f01b47c07610478cd51c4733c5b347308c1d464fcaf1464e0b914646b8bc4625de3e4604b8904432221f4409469243abcc47429637574227f24c41bec53a4177cb1a4151dad4412ad45b4070e8d63fee1bc63f5caf6a3f166d223ea50e503e0590863dd62d713d5d01f6
  | 6, 3 => 0x8b748ea08b3f3b298b24579c8a03a4c9893f37e687f65b05870b36b986810bde864ec575857be7378560adda841f8e498310ce8982e8726f8297a34481f2970f80c872657fb36c537eab52527e4f82107d5f5b6b7d1a08fb7ce62be97c92d3697c5a5acf7af8efe979c81979792a918778ce358e77df582377d4114c775ba6727736b89e72a35bdc71ce1fda71a0f82b7185e720701995276ce601786c6ac77c6c4a633d6bc8164f6b0066ec6af7be776ad97bfd6a2a18fb69e204a969679dbb68fb494868455002683c24e96706496366f69b29662ee7f065d0ad596524ed3164d96ad864c89efa64bd189a62fb0e2e62caac3462ada21262533d8e61d6a498
  | 6, 4 => 0xba316fd7b9f128e0b8e5002ab8b19d3db7618b79b6c94b33b6957558b4940bfeb41ee614b2304d6ab1386750b08b2a16aee1c710aeb7fa5aae5e97e1ae0d4b21ad4b036eabd25ed8aa7689dea9ef2d08a85e17d3a84de8e4a693e541a59f45b7a52d9f51a43accd3a2d3502fa2ae1b71a2955f66a26777a1a1698bd9a10a99009f6e19db9ef5dcd99e8798909daccf639d65eb479c2a14989af9b8fc9a75f71e9a2a43fe99edc87a9971aa3f993b00ba9579cf79955cf6ad941dacde94058f0893a5ddd593633c22931613f892ab5e16929f15e29208e86491ccf397917f51039151fa5890b7921a9041d044902797588f87ae7a8f2ef4228c7177e08c229558
  | 6, 5 => 0xf58851fcf46db415f42c1630f40f6d9df3be232cf322bb5df2ad9ee8f0871216f038857cefa056b5ef2f586beed703beee796c24e946ea82e8f90b5ae8a329a0e828cb05e6fcf778e612f7cce532763ce501857ae4aaa271e37fd253e2b7cb07dece6c59dd927d68db9a539eda674f43d97a9babd6f3e0fbd58ba9fcd1ab1cefd0deacd4cf53d2edce9eed3ece8b1b77cd89c6a4cb8e7ce7cb065d68caf6456eca5bc8c9c9e13d10c9b2f9e8c904bc7ac89a9f6dc84ad4c1c7a79c97c78602aec6c4bf8ec546d7f2c42cae44c3a0f832c304235ec2f2c70ac1d314b3c0e5c006c03e5941bf725764bebc23dabe5b803ebe362232bd86799bbc983c56ba82d198
  | 6, 6 => 0xffefbf7ffc2c1437fb31d5abf8c6bcfdf81a7300f7e0019cf793560df5f673c5f598e516
  | 7, 0 => 0xfb31d5abf0871216e612f7ccd1ab1cefc546d7f2c42cae44ae0d4b21a52d9f519ef5dcd99daccf639579cf799151fa5890b7921a8c22955886810bde864ec5757c92d36969e204a9683c24e947308c1d4604b890440946923dd62d71359cd3013595e9572e748d6d2c9187bc21fa8822113b06e50f92eb2e0b91c7e00ada43960765d8eb01b5dc8900125a18
  | 8, 0 => 0x69e204a9
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff00ff0000000000f0f0f0f000000000aaaaaaaa0000000033333333000000000f0f0f0f000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xf000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa00005555000055550000333300003333000000ff000000ff00000000ffffffff
  | 0, 2 => 0xf00ff000f00ff000f000f00ff00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff0000000000ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000f000f0f0f0f0f000f000f000f0f0f0
  | 0, 3 => 0x3333000033330000330033003300330030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff00000fff00000f0fffff0f0fffff0f0fffff000000000f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f00000000
  | 0, 4 => 0x50505050505050504444cccc4444cccc444444444444cccc44444444444444443f3f3f3f3f3f3f3f3f3f3f3f3f3f00003f3f00003f3f00003f003f003f003f0033ff33ff33ff33ff3333ffff3333ffff3333ffff0000000033333333ffffffff333333333333ffff333333333333333333333333333300003333333300000000
  | 0, 5 => 0x55ff55ff55ff55ff5555ffff5555ffff5555ffff0000000055555555ffffffff555555555555ffff55555555555555555555555555550000555555550000000055550000555500005500ff005500ff0055005500ff00ff00550055005500ff0055005500550055005050f0f05050f0f050505050f0f0f0f0505050505050f0f0
  | 0, 6 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a000000000a000a000a000a000888888888888888888888888888800008888888800000000888800008888000088008800880088008080808080808080777777777777777777777777777700007777777700000000770077007700770070707070707070705f5f5f5f5f5f5f5f
  | 0, 7 => 0xaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000a8a8a8a8a8a8a8a8
  | 0, 8 => 0xc0c00000c0c00000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafafafafafafaf0000afafafaf00000000af00af00af00af00aaffaaffaaffaaffaaaaffff00000000aaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0
  | 0, 9 => 0xcccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00ff00cc00ff00cc00cc00cc00ff00cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000cc000000cc000000c8c8c8c8c8c8c8c8c0c0f0f0c0c0f0f0c0c0c0c0f0f0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000
  | 0, 10 => 0xccccffffccccffffccccffff00000000ccccccccffffffffccccccccccccffffcccccccccccccccccccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00cccc8888cccc8888cccc0000cccc0000
  | 0, 11 => 0xececececececececececececececccccececececccccccccececccccececccccecccecccecccecccec00ec00ec00ec00eaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaaaaaaaaaeaeaaaaaeaeaaaaaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0e0c0e0c0e0c0e0c0ddddddddddddddddcfcfcfcfcfcfcfcfccffccffccffccff
  | 0, 12 => 0xeeeeeeeecccccccceeeeeeee00000000eeeecccceeeecccceeeecccccccccccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecccccceecccccceeaaeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaeeaaeeaa0000eeaaeeaaaaaaaaaaeeaa0000eeaa0000ee00ee00ee00ee00ee00ee00ee00aa00
  | 0, 13 => 0xf0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000ffff0000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f050f050f050f050f000f000f000f000f000f000f0000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000
  | 0, 14 => 0xf0f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0e0e0f0f0e0e0
  | 0, 15 => 0xfa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f8f8f0f0f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f500f500f500f500f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f3f3f3f3f0f0f0f0f3f3f0f0f3f3f0f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0faf0faf0faf0faf0f3f0f3f0f3f0f3f0f0fffff0f0ffff
  | 1, 0 => 0xfafafafafafafafafafafafafafaf8f8fafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf8f8fafaf8f8fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafaf0faf0faf0faf0faf0faf0faf0f0f0faf0f0f0faf0f0f0faaafaaafaaafaaa
  | 1, 1 => 0xfefefefe00000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcccccccccfcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcf0f0f0fcccfcccfcccfcccfc00fc00fc00fc00fc00fc00fc00f000
  | 1, 2 => 0xff00ff00ff00aa00ff00ff00ff00a000ff00ff00ff003300ff00ff00ff000000ff00ff00fc00fc00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff0000000000ff00f000ff00f000ff00ee00ff00ee00ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000
  | 1, 3 => 0xff0fff0fff0fff0fff0aff0aff0aff0aff03ff03ff03ff03ff00ffffff00ffffff00ffff00000000ff00ff00ffffffffff00ff00ff00ffffff00ff00ff00ffccff00ff00ff00ff55ff00ff00ff00ff0fff00ff00ff00ff00ff00ff00ff00fc00ff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00
  | 1, 4 => 0xffa0ffa0ff00ff00ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55ff50ff50ff50ff50ff33ff33ff33ff33ff33ff33ff33ff00ff33ff33ff330000ff33ff33ff00ff00ff33ff3300000000ff33ff00ff33ff00ff11ff11ff11ff11
  | 1, 5 => 0xffaaffaaffaaffaaffaaffaaffaaff88ffaaffaaffaaff00ffaaffaaffaaf000ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaff88ff88ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00
  | 1, 6 => 0xffeeffee00000000ffeaffeaffeaf0c0ffccffccffccffccffccffccffccff00ffccffccffccccccffccffccffcc0000ffccffccff00ff00ffccffccccccccccffccffcc00000000ffccff00ffccff00ffccccccffccccccffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ffc0f0c0ffc0ff00ffc0ff00
  | 1, 7 => 0xfff0fff0fff0fff0fff0fff0fff0ffc0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff00000fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0ffc0fff0ffc0fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeeffee0000
  | 1, 8 => 0xffff0000ffaa0000ffff0000ff000000ffff0000f0f00000ffff0000cccc0000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffafffafffafffafffafffafffaff00fffafffafffaf0f0fffafffafffa0000fffafffaff00ff00fffafffaf0f0f0f0fffafffa00000000fffaff00fffaff00fffaf0f0fffaf0f0
  | 1, 9 => 0xffffaa00ffffaa00ffffaa00ffff0000ffffa0a0ffffa0a0ffffa000ffffa000ffff8888ffff8888ffff7777ffff0000ffff5555ffff5555ffff5555ffff0000ffff3333ffff3333ffff3333ffff0000ffff1111ffff1111ffff0f0fffff0f0fffff0f0fffff0000ffff0055ffff0055ffff0000ffffffffffff0000ffff0000
  | 1, 10 => 0xffffccccffffccccffffccccffffc0c0ffffccccffff8888ffffccccffff0000ffffccccccccccccffffcc00ffffcc00ffffc8c8ffffc8c8ffffc0c0ffffc0c0ffffc0c0ffff0000ffffc000ffffc000ffffafafffff0000ffffaaaaffffaaaaffffaaaaffff8888ffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000
  | 1, 11 => 0xffffff00fffff000ffffff00ffff0000ffffff00ff00ff00fffffefeffff0000fffffcfcfffffcfcfffffcfcffff0000fffffafafffffafafffff0f0fffff0f0fffff0f0fffff000fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000ffffeeeeffff0000ffffeeee00000000ffffeeaaffff0000
  | 1, 12 => 0xffffffff88880000ffffffff88008800ffffffff80808080ffffffff50505050ffffffff3f3f0000ffffffff33333333ffffffff0fff0000ffffffff00ff00ffffffffff00ff0000ffffffff00cc00ccffffffff0000ffffffffffff00000000ffffffaaffffffaaffffffaaffff0000ffffff33ffff0000ffffff00ffffff00
  | 1, 13 => 0xfffffffff0c0f0c0fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeeee0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a0a0a0ffffffffa0a00000ffffffff88888888
  | 1, 14 => 0xffffffffffff0000fffffffffffa0000fffffffffff0fff0fffffffffff00000ffffffffffee0000ffffffffffccffccffffffffffcc0000ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafa0000fffffffff0f0f0f0fffffffff0f0c0c0fffffffff0f00000
  | 1, 15 => 0xffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffffa000ffffffffffff8888ffffffffffff8800ffffffffffff8080ffffffffffff5555ffffffffffff5050ffffffffffff3333ffffffffffff1111ffffffffffff0f0fffffffffffff00ffffffffffffff00ccffffffffffff0055
  | 2, 0 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff0c0fffffffffffff000ffffffffffffeeeeffffffffffffccccffffffffffffcc00ffffffffffffc8c8ffffffffffffc0c0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x16e2ac843
  | 3, 0, 0 => 0x4bced3488448197f2ac8447bd112e4ab47bd322e4ab48157c2ac8445f135348844819632ac844829862ac8447bd612ac8446195d2ac8444c8ed348844815352e4ab4570ed2ac844568d92ac844
  | 4, 0, 0 => 0x7bd35368ab2115ef4d4ed2ac8457bd35364ab2115ef4c4ed2ac84564183560ab2116004d4ed2e4ab57bd353f8ab2115eb4d4ed2ac8454d4ed348a62115cb4d4ed2ac845711b34d4b92ad55a3b4d62ac8457bd734d4ab2115ef4d4e12ac845709834d4ab2115ee4d4ed2ac845
  | 4, 0, 1 => 0x7e1353b4ab2116077bd632ac8457bd103b4ab2115ef564ed2ac845795353b4cd2115ac4d4ed33c8457bd323b4ab2115ef4f4ed2ac845801633b4ab2115ef4d4ed2ec845669353b4ab2115ef4d4ab2102157bd353b49e2115ef5f0d62ac84581def4d4b92ad5ef4d4ed31c845
  | 4, 0, 2 => 0x7bd353c8ab2115fb4d4ed2ac8457bd353b4c82115c94d4ed2ac845568ed2ac841cd5444d4ed2ac8454c8ed2ac841f95ef3b4c12ac8457bd353a8ab2115fa534ed2ac845709353b4ab2115ef4d4ed2dcab57bd35434d22115e7554ed2ac8457bced2ac841555ef4d4ed2d4ab5
  | 4, 0, 3 => 0x7bd352ac922115ef4d4ab2105257bd4e3b4ab2115ef4d4f42ac8457bd253b4ab2116054d4ab2448456f1353b4ab2115ef574ed2ac8458157f3b4ab2115f04d4ed2ac8456c1353b4ab2115ef5f0ab2107357bd353b4cf2115ef4f8ed2ac8457bd843b4ab2115ef580ed2ac845
  | 4, 0, 4 => 0x7bced2ac841215ef4d4ed2104e57bd63364ab2115ef4b0d92ac8457bd353c4ab2116035f1352ac84571190444b92ad5ef444ed2ac8457bd353d8ab2115ef524ed2ac8457bd353b4b92ad5ef4d4d72ac8457bd643b4ab2115df6417f2ac8457bcd92ac992115ef4d5012ac845
  | 4, 0, 5 => 0x7bd2b3b4ab2115ef4d4ed2f88457bced2e8ab2115ef4d4ed2a48457bd873b4ab2115ef554ed3348457bd353b484135607574ed2ac8457bd804d4ab2115ef4d5052ac8457bd543b4ab2116054d50f2ac845695353b4ab2115ef4d4ab2508457bd3541cab2115ef58ced2ac845
  | 4, 0, 6 => 0x7bd352ac841855f44d4ed2ac8457bd363b4ab211535340b42ac8457bd35408ab2115ef7997c2ac8457bd7c4d4ab2115db4d4b42ac8457bd353dcab2115ef5d1352ac8454d4ed348d02115ef4d4fc2ac8457995a3b4ab21155a4d4ed2ac8457bced2ac892115ef4d4ed30cab5
  | 4, 0, 7 => 0x6c8ed304ab21155d568ed2ac8457bd864d4ab21160557ced2ac8457bd352ac840815ef58ced2e4ab57bd773b4ab2115ef504ed2ac8455f1352ac841f95ef3b4ab2688457bd2d3b4ab2115ef578ed2ac8457c5353b4ab2115ef4d50a2ac8457bd7c4c8ab2115b24d4ed2ac845
  | 4, 0, 8 => 0x7bd7e3b4ab2115854d4ed2ac8457e9353b4ab2115ef4d50e2ac845711744d4cd2115ef4d4ed2f08457bd763b4ab2115ef3b4c02ac8457bd352ac841415ef4d50a33c8457e9353f8ab2115b24d4ed33c8455c1353b4ab2115c14d4ed2ac8457bd583b4ab2115ef555062ac845
  | 4, 0, 9 => 0x7bd4d3b4ab2115ef4d4ed2ac8154d4ed2ac841915ef4d50d2ac8457bd4d3f8ab2115ef5fcd92ac84580d2f3b4ab2115ef5f16d2ac8457bd352d0ab2115ef3b4ab2102e57bd35380ab2116034d4ed2a08457bd353f4ab2115a25e1352ac8457bd353b4d221156d568ed2ac845
  | 4, 0, 10 => 0x7bd2f3b4ab2115ef3b4ab2102d58295a3b4ab2115ef574ed3488454d4ed310ab2115ef4d4ed3308457bd35358b92ad5353b4ab2103857bcc12d0ab2116074d4ed348845815323b4ab2115ef3e4ed2ac8457bd353ecab2116054d4ed2ac8457bd322ac912115ef52ced2ac845
  | 4, 0, 11 => 0x7bd383b4ab2115f94d4ed2ac8457bd352e4b42ad5ef4d5142ac8454bced2ac841f9586569352ac8457bd353b4b82ad5ef540ed2ac8457bd35474b92ad5ef4d4ed314ab57bd352ccab2115ef5750d2ac845829ef5f0ab2115ef3b4ab26c8457bd623b4ab2115ef4c90f2ac845
  | 4, 0, 12 => 0x7bdb84d4b92ad5353b4ab22c845801353b4ab2115353b4d02ac8457bd3544cab2115ef4d4b92ac6f57bd373b4ab2115354b0ed34884582a075fcab2115ef4d50f2ac8057f9353b4d22115ef444ab244845814ed2ac992115353b4ab2104a57bd1e3b4ab2116014d4ed2ac845
  | 4, 0, 13 => 0x7bd353b4ab20d5ef4b8ed2ac8453b4d0304ab2115ef51ced2ac845819353b4ab2115ef5d4ed2ac84581935364ab2115ef4450f2ac84577d9058cab211535480ed2ac8457bd5f364ab2115ef530ed2ac8457bdb858cab2115ef4d4ec2ac8457fd353b4ab2116054b0ed2ac845
  | 4, 0, 14 => 0x7bd453b4ab2115ef500ed2ac8457bced2ac841895ef4cced2ac8457bd353b4ab0f15ef3b4ab2105457bd7d3b4ab2115f64d4ed2ac84580d323b4ab2115ef4d0ed2ac845
  | 5, 0, 0 => 0x709904d4ed2ac8467bd353b4ab2100467bd353b4ab2103067bd354bced2ac8467bd353b4cb2ac8467bd353b4ab2106767bd353b4e62ac8467bdc03b4ab264846711903e4ed2ac846711904d4ed2f4846711904d4fb2ac846711ba4d4ed2ac846711904d4ab24c846739904d4ed2ac8467bd353b4ab210016759904d4ed2ac846
  | 5, 0, 1 => 0x7bd353b4ab2100e67bd353b4d62ac846711b34d50f2ac84671190304b42ac846711904d5063348467bd903b4c12ac8467bd353b4ab2102267bd353b4ab2100b67bd353b4ab2100a6735904d4ed2ac846711903b4ab2102f6001ef4d4fe2ac8457bd35490ed2ac8467bd353b4c92ac8467bdaa4d4ed2ac846789904d4ed33c846
  | 5, 0, 2 => 0x711a64d4ed2ac8467bdd34d4ed2ac8467bd353b4ab2107267bd353b4ab210096765904d4ed2ac8467bd353b4ab2101d67bd353b4ab2103d67bd353b4ab21000675d904d4ed2ac8467bdea4d4ed2ac846001ef4d4ed2ac8457119b4d4fe2ac8467bde84d4ed2ac846711904d4ed330846001ef4d4d92ac845711904d4d62e4ab6
  | 5, 0, 3 => 0x1ef4d4ab1683257bd353b4ab2102a6711904bced2ac84673d904d4ed2ac8467bd353b4ab2100867bd994d4ed2ac84681def4d50f2ac846001ef4c8ed2ac8457bd794d4ed2ac8467115a4d4ed2ac846825ef4d4ed2ac8467119b4d4ed2ac846785904d4ed2ac8467bd793b4e22ac8467bd353b4ab2a08467bdc04b0ed2ac846
  | 5, 0, 4 => 0x7bd353b4ab2100f6711903b4ab26c8467bdbe4d4ed2ac846001ef4d4841083257e99b4d4ed2ac846711353b4dd2ac8467bd353b4ab2106d67bd35458ed2ac8466413547ced2ac8467bd90574ed2ac846711904d4f52ac846641353b4ab21c8467bd7d3b4e72ac846751904d5062ac8467bd904d4ed33c8467bdc45d1352ac846
  | 5, 0, 5 => 0x641353b4ae2ac846711b74d4ed2ac846641353b4ab2105d67bd353b4ab220846801a84d4ed2ac846001c24d4ed2ac845711a94d4ed2ac846801ef4d4ed2ac8467a5904d4ed2ac846711904d4b32ac8467bd353b4d02ac8467bdc84d4ed2ac846711904d4e52ac8467bddc4d4ed2ac8467bd784d5272ac8467bdc45f1352ac846
  | 5, 0, 6 => 0x71190604ed2ac8467bda04d4ed2ac8467bdc44d50a2ac846711905e4ed2ac846001ef3b4c12ac845711b24d4ed2ac8467bd353b4ab210076775904d4ed2ac8467bd353b4ab210116711904d51d2e4ab67bd353b4ab2848467bd353b4db2ac8467bd35474ed2ac846795353b4ab2107767bd7f5b4ed2ac846711353b4ca2ac846
  | 5, 0, 7 => 0x7bd353b4ab2107367bd35434ed2ac8467bd3534cb42ac8467bd354a8ed2ac8467bd353b4d42ac8467b1904d4ed2ac846711904d4b92d0ab6711905e8ed2ac8467bd353b4b42ac8467bd904d4ed2e4ab67bd353b4cd2ac846711353b4ab210376711903b4ab2105667bd353b4bf2ac846711bf4d4ed2ac846711904d4ed334846
  | 5, 0, 8 => 0x719904d4ed2ac8467bd353b4dc2ac8467bd353b4ab2100367bd9058ced2ac84671190444ab2448467bd353b4ab2188467bd353b4e72ac8467bd35424ed2ac8467f5ef4d4ed2ac8467bd9d4d4ed2ac8467bd353b4ab210196001ef4d4ed33c8457118f4d4ed2ac84671190478ed2ac8467bd90444ed2ac8467bd353b4ab244846
  | 5, 0, 9 => 0x710ed328c12ac846000ed2ac8409009580def4d4ed2ac846779904d4ab244846759904d4ed2e4ab67bdab4d4ed2ac846769905e1352ac8467bd3540ced2ac8467bd353b4ab210316781904d4ed2ac846779905fced2ac8467bd353b4ab210446751904d4ed2ac846001ef574ed2ac845711a44d4ed3348467bd353b4ab274846
  | 5, 0, 10 => 0x7bd353b4ab2107b67bd694d4ed2ac8467bd353b4ab2103667bd353b4ab294846711904d5132ac84671190528ed2ac846799e26417f2ac8467bde657ced2ac8467119053ced2ac8467bd5f4d4ed2ac846711904d4b92ac6f67bd5b4d4ed2ac8467bd353b4ab2107967bd353b4ab2108267bdca4d4ed2ac8467bd353b4ab2106f6
  | 5, 0, 11 => 0x7599058ced2ac84677d904d4d92ac8467f9ef4bced2ac8467bd534d4ed2ac8467bdc4560ed2ac846711b8641352e4ab67bdb84d4ed2ac8467bd674d4ed2ac846711905610a2ac846711b8554ed2ac8467bced358ab2648467bdac4d4ed2ac8467bded4d4ed2ac8467bd353b4ab2107067bd353b4ab2100d67bd353b4ab210156
  | 5, 0, 12 => 0x7bd3543ced2ac846711b8641632ac846001ef444ed2ac845001ef4d4ab2103257bd7b4d4ed2ac846641824d4ed2ac8467bd353b4d82ac8467bd353c0ed2ac846001ef4d4ed2e4ab57bd353b4b22ac8467bd3549ced2ac8467d5ef4d4ed2ac8467bd353b4ab2104b6711b357ced2ac84677d904d4ed2ac846751a44d4ed2ac846
  | 5, 0, 13 => 0x7bd353b4ab210766711904450f2ac8467bd353b4ab21078671d904d4ed2ac8467e9c44d4ed2ac846001ef58ced2ac8457bd7d4d4ed2ac8467bd353b4ab2103e67095f4d4ed2ac846829ef5fced2ac846795904d4ed2ac8467bd2c3b4d62ac8467bd905d1352ac8467bdc45d8ed2ac8467119057cd92ac846711904d4ed2d8ab6
  | 5, 0, 14 => 0x6b1353b4ab2107a67bd353e0ed2ac8467bd3543ced34cab6689353b4ab28c846641353b4cf338846711a34d4ed2ac846711905e1352ac846711ae4d4ed2ac8467119051ced2ac8467bd353fced2ac8467cdef4d4ed2ac846711905d4ed2ac8467bdc44d4ed348846001ef3b4ab168245641353b4ab2101767bd353b4ab210426
  | 5, 0, 15 => 0x711904a4ed2ac846711904d5062ac8467bda84d4ed2ac8467119060d352ac8467bd724d4ed2ac8467bdc44d4b42ac8467bd354c0ed2ac8467bdef4d4ed2ac8467bdc4554ed2ac8467bd35484ed2ac8467bd904d50a2ac84681e034d4ed2ac8466c9904d4ed2ac846001ef3b4841082457bd35430ed2ac8467119e4d4ed2ac846
  | 5, 1, 0 => 0x7bd353b4ab2148467bdc4534ed2ac8467bd353b4ab2102867bd353b4ab2100267bd353b4ab2104067bd353b4ab2101360015a4d4ed2ac8457bd35460ed2ac8467bd564d4ed2ac8467bd353b4ad2ac8467bced2ac992107367bd353b8ed2ac8467bdc44d50d2ac846711905f4ed2ac8466c5904d4ed2ac8467bd1d444ed2ac846
  | 5, 1, 1 => 0x71190500ed2ac8467bd353b4e82ac846711903b4ab210626759a84d4ed2ac8467bd353b4ab2104c67bde64d4ed2ac846815c44d4ed2ac8467bd354d4ed2ac8467bd353e8ed2ac8467bd353b4ab2102c678d904d4ed2ac8467119050ced2ac8467bd553b4ab210776711904d4ed2ac3c6001ef5d1352ac8457bd353b4b92ac916
  | 5, 1, 2 => 0x80def4d4ed34c846711904d4e12ac8467bd353b4ab23c8467bd354c8ed2ac8467bd353b4ab2106a67bd633b4ab2448467bd2c3b4ab210736641353b4ab2104567bd884d4ed2ac8467bd353b4ab2107e6001ef5f1352ac8457bd353b4ab210666711904d4ab2105167bd353b4df2ac8467bd353b4ab210266745904d4ed2ac846
  | 5, 1, 3 => 0x7bd353b4ab2104367bd353b4ab2107a67bd353b4ab2105e676d353b4d32ac846001ef4d50a2ac8457bd353b4ab2105a6711904d4fe2ac846709564d4ed2ac846831ef4d4ed2ac846001b24d4ed2ac845641424d4ed2ac846711b34d4ed2ac846839ef4d4ed2ac8467bdc05fced2ac846711905cd352ac8467bd8e4d4ed2ac846
  | 5, 1, 4 => 0x7bd514d4ed2ac84681def4d4ed2ac846711904d4ed31c8467bd353b4ab29c84664158558ed2ac846711524d4ed2ac846711904d4da2ac8467bd353b4ab210476711904d4ed2ac8467bd394d4ed2ac8467bd353b4ab210716711904d4d92ac8467bd6d57ced2ac8467bd353b4ab2107564d4ed34cd02ac8467e9353b4ab2106b6
  | 5, 1, 5 => 0x711904c8ed2ac8467bd353b4c12ac8467bd353b4c62ac846711904f4ed2ac8467bd905d8ed2ac846711904d4ed2ec846711be5e1352ac8467bdc44bced2ac846711904d4ab2102167bd353b4ab2105967bd353b4ab210146641353b4cf28c8467bd353b4ab238846711904d4ed2788467bd353b4ab2ac8467bd353cced2ac846
  | 5, 1, 6 => 0x7119c4d4ed2ac846711984d4ed2ac846711353b4c22ac8466416f4d4ed2ac846731904d4ed2ac846001ef3b4ab21024580dfe4d4ed2ac84671190564ed2ac8467bd354a0ed2ac8467bd353b4e32ac846751b84d4ed2ac846811ef4d4ed2ac84681def4c8ed2ac8467bdbb4d4ed2ac8467bd35488ed2ac84676d353b4ca2ac846
  | 5, 1, 7 => 0x81d353b4ab2107e67bd4d3b4ab2106b679d904d4ed2ac8467bd784d4ed2ac846711924d4ed2ac8467bd353b4ab2102966413b4d4ed2ac8467bd35468ed2ac8467bd3545ced2ac8467bdc54d4ed2ac846641353b4ab210356711904d4ed2d4ab67bdb54d4ed2ac846769be4d4ed2ac8467bd3c4d4ed2ac84680d354b0ed2ac846
  | 5, 1, 8 => 0x7bd353b4d12ac8467bdb85fd352ac846815b34d4ed2ac8467bd5d3b4ab2107e6809ef4d4ed2ac8467bd35418ed2ac8467bd6c4d4ed2ac8467bdd04d4ed2ac8467bd353b4ab210256711903b4c12ac8467bd5d4d4ed2ac846711934d4ed2ac8467c9ef4d4ed2ac84657d5a4d4ed2ac846001ef560ed2ac8457bd353b4ab230846
  | 5, 1, 9 => 0x7bdaf4d4ed2ac846711904f8ed2ac8467bd353b4ab2106e6711a24d4ed33c846641353b4ab2102767bd353b4ab264846821ef4d4ed2ac846001ef5d8ed2ac8457bd353b4ab2105767bd353b4cf2107a67bd353b4ab2548467bd353b4ce2ac84671190580ed2ac8467bd353b4ab25c8467bd353b4ab2101a6711904d4f22ac846
  | 5, 1, 10 => 0x7f9ef4d4ed2ac8467bd35444ed2ac8467bd353b4ab2101e6711904d4f42ac846711b33b4ab2648467bd353b4ab210686829ef57ced2ac8467bd353b4ab2105b671190574ed2ac846001ef4d4ed3488457bd684d4ed2ac8467bde04d4ed2ac8467bd35448ed2ac846001fa4d4ed2ac8457bd894d4ed2ac8467bdd44d4ed2ac846
  | 5, 1, 11 => 0x7bda14d4ed2ac846001ef4d4b42ac8457bd7f3b4d62ac84671190364ab2648467bd353f8ed2ac8467bd634d4ed2ac8467bd354b0ed2ac846711744d4ab210776711904d5012ac846711ad4d4ed2ac846769ac4d4ed2ac8467bd6d4d4ed2ac846801c44d4ed2ac8467bd353b4ab210846711353b4d02ac8467bd6d4d4d92ac846
  | 5, 1, 12 => 0x7bd3542ced2ac8467bd353b4ab2107f6711904d4ed2e4ab67bdb44d4ed2ac8467bd353b4ed2ac8467bd5a4d4ed2ac846711904d4d72ac8467bd353b4ab2105f67bd353b4d92ac8467bd353b4ab210746001ef4d50d2ac8457bd35358ab24484671190590ed2ac8467bd353b4b02ac8467bd353b4ab2106567bd353b4ab240846
  | 5, 1, 13 => 0x7bdd54d4ed2ac846711904d4ed2104e67119058cd92ac8467119b534ed2ac846711904d4f12ac8467bd8a4d4ed2ac846002054d4ed2ac8457bd353b4ab2101b67f9353b4ab2107e6815353b4d62ac84671190444ed2ac846001353b4ab168095001ef534ed2ac845779b34d4ed2ac8467bd353b4d32ac84671190524ed2ac846
  | 5, 1, 14 => 0x80d353b4ab29884671180549352ac8467bd353b4ab28c846711904d5052ac8467bd353b4ab21041671135328b42ac84671190550ed2ac846001ef2ac840c82457bd464d4ed2ac8467ddef4d4ed2ac846001353b4841080954d52c3b4ab2107e6711904d5072ac846641353b4ab2106367119058ced2ac846711903b4ab210486
  | 5, 1, 15 => 0x7bd35420ed2ac8467bd353b4ab2106c67bd353b4ab2105367bced34cc12ac8467bd353b4ab2101067bd353b4ab2108067bd3543cd62ac8467bd353b4ab2103a67bdc45f4ed2ac846711904aced2ac846711903b4ba2ac8467bd904d4ed3348467bd35474ab244846781905d8ed2ac84671190554ed3348467bdbd4d4ed2ac846
  | 5, 2, 0 => 0x7bdaf4d4ed34c846001ef4d4ed1684257bd8c4d4ed2ac846711353b4ab21049681def5fd352ac846829ef4d4ed2ac84675190554ed2ac846711954d4ed2ac846711904d4fc2ac8467bd35418ab210776711903b4ab224846001ef4bced2ac8457bd353b4ab2104f67bd7f3b4ab210736711a74d4ed2ac846711904d4ed30cab6
  | 5, 2, 1 => 0x7bd353b4b92ac846711904d4ab210616641353b4ab2288467bd353b4ab27c8467bdc44d4fe2ac8467bd353b4eb2ac8467bd352ac912106f67bdb94d4ed2ac8467bd353b4ab210606711905f1352ac8467bd6d3b4ab2648467bd353b4ab2608467bd353b4ab2102b67f1ef4d4ed2ac8467bd353b4e92ac8467bd353b4ab210056
  | 5, 2, 2 => 0x7bd484d4ed2ac8467bd353b4ab2100667bdc44c8ed2ac8467bd6d4b0ed2ac846001353b4ab2100957419b4d4ed2ac8467bd353b4ab2103967bd353b4ab298846711964d4ed2ac8467bdc44d4ed2ac8467bd353b4ab2348467bd353b4ab2888467bdc44d4d92ac8467bdb84d4ab2448467bd354750f2ac8467bd353b4ab210246
  | 5, 2, 3 => 0x4d4ed2aca62107e67bd353b4ab270846002004d4ed2ac8457bd353b4ab2a8846001353b4d02ac8457bd353b4ab2101f682a074d4ed2ac8467119058ced2e4ab67bd353b4ab2102367bd6b4d4ed2ac846835ef4d4ed2ac8467bd944d4ed2ac8467e9ef4d4ed2ac8467bd353b4ab2103267bd3f4d4ed2ac8467bd584d4ed2ac846
  | 5, 2, 4 => 0x815ef4d4ed2ac846001ef4d4ed210425829ef3b4ab2648467bd353f8ab2106b67bd353b4d22107e67113548ced3348467bd5f3b4d62ac846001ef4d4ed2ac5a57bd714d4ed2ac8467bd353b4ab2103364d4ed338ca2ac8466893549ced2ac8467bdb84d50f2ac8467bd353b4ac2ac84671190560ed2ac8467bd3543cab2106f6
  | 5, 2, 5 => 0x801353b4ab244846001ef5f4ed2ac845829ef4b0ed2ac84682def4d4ed2ac8467bd7c4d4ed2ac8467bd353b4d22ac8467bd4d4d4ed2ac8467bdb34d4ed2ac8467bd35434ab2107e67bd6a4d4ed2ac846711904d4ed3488467bd353b4ab2103b67bd35400ed2ac8467bd353b4ab2106b67bd7c4d52c2ac8467bd7f4d4ed2ac846
  | 5, 2, 6 => 0x7bd5f3b4ab210736001352ac840c80957bd353b4d52ac8467bd3546ced2ac8467bd353b4b12ac84671190534ed2ac8467bd35470ed2ac846559524d4ed2ac84681def4d4ab244846711904d50d2ac84671190534fe2ac8467bd353b4ab2101c6711905fcd92ac8467bd35454ed2ac846711904d4b42ac846
  | 6, 0, 0 => 0x1ef4d4ed358ab2119c4641763b4dc2ac847711c3641353b4ab211dc4641353b4ab28c8477bd904d51d3b4ab211dc4641353b4ca2ac847001c4640ab210320919c4641464d4ed2ac8477119f641353b4ab211dc46418b4d4ed2ac847755c4641353b4ab211dc4641353b4ab2101777bdc44d4ed2ac84109dd0641353b4ab2106b7001d6641353b4ab2119c46418a4d4ed2ac847
  | 6, 0, 1 => 0x711903b4d3304ab211c007119b4d4ed2ac846711904d4ed2ac84041dc46413543cd62ac847001ef4d4ed2ac840259c4641353b4ab2103a7001d9641353b4ab2119c47019057ced2ac847711904e9353b4ab211dda711904d4ed2ac847000007bd353b4ab2115d8711904d4ed2ac847711904d51d2ac91211c00711353b4ab1681867bdef711353b4ab211dc46f5904d4ed2ac847
  | 6, 0, 2 => 0x829c4641353b4ab211def799c44d4ed2ac847711904d4ed2ac84031dc464135418ab2107777bd904d4ed39cab211def711353b4e22ac847711904d4ed2ac8413ddc46417f3b4ab210737001353b4ab2101805d9c46413548ced2ac847711904d5083b4ab211def641353b4ab2448477bd904d4ed2ac841cddc4641353b4ab2106c7001c44d4ed210420619c4641353b4ab210537
  | 6, 0, 3 => 0x711904d4ed2ac84059c007bd35474ed2ac846711904d4ed2ac84181c00711353b4ca2ac846759904d4ed2ac91211dc46416d3b4ab264847711904d4ed390ab211de4711904d4ed2ac8477bd9057d353b4ab211def641353b4ab2106f7711904d4ed2ac840ade037bd904d4ed2ac8477bdc44d4ed2ac841f9dc46bd904d4ed34c847001c4641353b45a1099c46418c4d4ed2ac847
  | 6, 0, 4 => 0x711904d4ed2aca2211def6413549ced2ac847711b8641352ac91211dc4641354750f2ac847711904d4ed2ac84091c00711904d4ed334846001353b4ab210180419ef711353b4ab2107a7711904d4ed2e4ab211d9057d564d4ed2ac8477bdc44d4ed2ac84169dc4641353b4ab27c847001c4641793b4ab2119ef6e1904d4ed2ac847711904d4ab244841bddc46e5904d4ed2ac847
  | 6, 0, 5 => 0x71190561353b4ab211dc4641484d4ed2ac847711b86bd353b4ab211dc46d9904d4ed2ac847711904d4ed2ac84049def789904d4ed2ac8477bd904d50f3b4ab211c007bd353b4ab244846001ef641352ac840c99c4641353b4ab210397001ef4d4ed2ac841cd9c4641353b4ab29884781def711353b4ab211dc4711904d4ed2ac847711904d4ed2ac84171dc4641353b4ab234847
  | 6, 0, 6 => 0x711904d4ed2bcab211dc4641353b4ab2101f7001ef57d353b4ab2118007bd353b4ab2106f6002037bd353b4ab2119c4641574d4ed2ac847001e0641353b4ab2119c4641353b4ab210777001d4641353b4ab2119c46418d4d4ed2ac84771194641353b4ab211c007bd353b4dc2ac846001ef710ed2ac840919c4641353b4ab210327001ef4d4ed39cab2119c46413f4d4ed2ac847
  | 6, 0, 7 => 0x711b86413543cab211dc4641353b4ab210467711904d4ed2ac96211c007bd3549ced2ac8466413549ced2ac841e9dc4691353b4ab21077771190560ed2ac841e9dc46413543cab2106f7711904d4ed2ac9c211c007bdb84d4ed2ac846799e2641353b4ab211dc4641764d4ed2ac847001c44d4ed2ac840619c4701904d4ed2ac847711353b4ab2101003ddc4641654d4ed2ac847
  | 6, 0, 8 => 0x1c4641353b4841099ef711af4d4ed2ac8477bd904d4ed388ab211dc4641353f8ab2106b7001e5641353b4ab2119ef711353b4ab26484771190599353b4ab211dc4641353b4de2ac847789904d4ed2ac841e9c007bd3543ced2ac8467119057ced358ab211dc4641353b4ab210347000007bd352ac840c95d2711904d4ed2ac847001c4641353b4ab1699c4641714d4ed2ac847
  | 6, 0, 9 => 0x711b3641353b4ab211dc464135464ed2ac847711904d4ed2ac841a5dfe7bdc44d4ed2ac847001c4641784d4ab2119c46b1353b4ab28c847711904d4ed2ac840eddc465d904d4ed2ac847711904d5003b4ab211dc4641353b4ab2106b7001904d4ed2ac8405d9c4641744d4ed2ac847799c46417f3b4ab211c007bd353b4ab210426711905fd353b4ab211def799904d4ed2ac847
  | 6, 0, 10 => 0x711904d4ed2ac84071dc4641353b4ab290847711904d5153b4ab211dc464135428ed2ac84771190549353b4ab211de0641353b4dc2ac847711a2641353b4ab211c00711904d5062ac846711904d4ed2ac840fddc4641353b4ab2107d7001ef7bd353b4ab2119ef641353b4ab2107a77bdc44d52c3b4ab211dc46414d4d4ed2ac84771191641353b4ab211def7116d4d4ed2ac847
  | 6, 0, 11 => 0x711904d4ed398ab211dc4701903b4ab264847711b34d4ed358ab211c007bd353b4ab2107e6711905d13548cab211dc4641353b4ab2107c77119057ced2ac841cddc4641353bced2ac8477bdd5711353b4ab211dc464135410ed2ac8477bdc4629353b4ab211c007bde64d4ed2ac846711904d4ed2c4ab211dc4641353b4ab2105877bdc44d4ed34cab211dc464135498ed2ac847
  | 6, 0, 12 => 0x1c464135364ab2119c4641353b4ab2100e7711904d4ed358ab211dc4641353b4ab2102277bdda711353b4ab211c007bd353b4ab2107a6711904d4ed2ac84029c007bd353b4ab2105a6001c4641353f8ab2119c464135490ed2ac847711904d4ed324ab211c00711b34d4ed2ac8467bdc44d4ed2aca3211dc4641353b4ab210307711904d4ed32cab211dc4641353b4ab210677
  | 6, 0, 13 => 0x711904d5163b4ab211c00001ef3b4ab210245829ef711353b4ab211c00711904d4ab168326711904d4ed2ac840a9dc4665904d4ed2ac847711904d4ed2ac84025dc4641353b4ab2101d7711904d4ed2ac840f5dc4641353b4ab2100077a9c4641353b4ab211def711353b4ab210107002077bd353b4ab211800711524d4ed2ac846001c4641353b4ab211800711352ac840c8186
  | 6, 0, 14 => 0x769904d5273b4ab211def711c44d4ed2ac8477bdc44d4ed2aca0211c00711903b4c12ac8467bdc44d4ed2ac84091dc4641353b4ab210117711904d4ed36cab211dc464135474ed2ac847711905fd6d3b4ab211dc4641353b4ab2208477bdc44d4ed2ac84061dc8711904d4ed2ac847771c4641353b4ab211dc46f9904d4ed2ac847001c464135210420c99c4641353b4ab2106d7
  | 6, 0, 15 => 0x7bdd5641353b4ab211dc4641353b4ab218847711904d4ed39cab211dc4641353b4ab210197001ef6bd353b4ab2119ef711353b4ab210327001ef4d4ed2ac992119c4641353b4ab244847711904d4ed2ac841cddc46413534cb42ac847711904d4ed350ab211c00711353b4ab210096711904d4ed2d0ab211dc4641353b4cd2ac847711904d4ed2fcab211def711353b4ab298847
  | 6, 1, 0 => 0x1ef4d52c3b4ab2119ed711904d4ed2ac847711904d4ed2ac841c1dc4641353b4ab210157711904d4ed2ac841edc00645904d4ed2ac846711904d4ed2aca5211c007bd6d4d4ed2ac8467119057d353b4ab211dc4641353b4ab2106f780dc4641353b4ab211c007f9ef4d4ed2ac846711ab641353b4ab211dc46413540ced2ac847711904d4ed2ac9d211dc4641353b4dc2ac847
  | 6, 1, 1 => 0x1ef711353b4841099c46413543ced2ac847001c4641113b4ab211800711904d4ab210326001c43b4ab210240618007bd353b4d32ac8467bd904d5233b4ab211dc4641353b4d82ac847001c4641353b4b92ad9c4641353b4b22ac847711904d4ed2ac8412dc007bdc44d4ed2ac5a6711b8641353b4ab211dc4641674d4ed2ac847711903b4d62ac99211dc46b1904d4ed2ac847
  | 6, 1, 2 => 0x711904d5213b4ab211c00711903b484108246711904d4f83b4ab211dc46413543ced34cab7001ef4d4ed2aca32119904d4ed2aca32107a7711904d4ff3b4ab211c00711903b4ab168246711904d4ed2ac84109dc4641353b4ab210767001c4641633b4ab2118007bdd54d4ed2ac8467bdc44d4ed2ac841addc4641353b4ab2103e77bdc45fd353b4ab211c007bd8a4d4ed2ac846
  | 6, 1, 3 => 0x711904d5353b4ab211dc4641353e8ed2ac847711af4d4ed2aca0211dc4641353b4ab2102c70020a7bd353b4ab2119c4641353b4b92ac917711904d4ed2ac840a1dc4641353b4ab210137711904d5183b4ab211dc4640ed2ac9921073771190475113b4ab211c007bd353b4ab210106711a8641353b4ab211dc4641724d4ed2ac847711353b4d3328ab211def711904d4ed2ac847
  | 6, 1, 4 => 0x711904d4ed2ac841d5c007bdc44d4ed2ac846711904d4ed2ac84169def711353b4d62ac847711a24d4ed2ac841e9c007bd353b4ab210246839c4641353b4ab211dc46418e4d4ed2ac847711904d4ed2ac8f211dc4641633b4ab244847711be4d5273b4ab211dc4641884d4ed2ac847711904d4ed2ac841f9dc4641353b4ab210667711904d4ed2ac84099dc4641353b4ab2104c7
  | 6, 1, 5 => 0x711904d5283b4ab211dc464135488ed2ac847711904d4ed304ab211dc4641353b4c62ac847001ef4d4ed2ac840c99c4641353b4ab238847711904d4ed2acab211dc4641353cced2ac84771190545353b4ab211e07711904d4ed2ac847000004d4ed2ac840255c4641353b4ab210477711904d4ed2ac841c5def711353b4ab210097711905b55f3b4ab211c007bd353b4ab298846
  | 6, 1, 6 => 0x1ef4d4ed2ac841ad8007bd7f4d4ed2ac846711904d4ed2ac99211dc4641353b4cf2107a7000007bd353b4841095c4641353b4ab254847711904d4ed2ac84069dc46e1905fd352ac847000007bd353b4ab1695d0711904d4ed2ac847001c4641583b4ab2119c4641353b4ab23084771190534ed2ac841addc4641353b4ab210297711b5641353b4ab211c00711903b4ab210246
  | 6, 1, 7 => 0x711904d4ed2ac84195dc4685904d4ed2ac847001c4641352d0ab2119c46417f3b4d62ac847711904d4fe3b4ab211dc4641634d4ed2ac847711904d52c3b4ab211dc46416d4d4ed2ac847711904d4ed2ac84211dc46416d4d4d92ac8477f9c4641353b4ab211dc464135444ed2ac847711904d4ed2ac84079dc464135448ed2ac847769d5641353b4ab211dc4641894d4ed2ac847
  | 6, 1, 8 => 0x1c4641353b4ab2101b7001c46414d3b4ab2119c4641353b4d32ac847711904d4ed3b4ab211dc4641353b4ab2105f7711904d4ed364ab211dc4641353b4ab210747711904d4d62ac91211dc4641353b4b02ac847
  | 7, 0, 0 => 0x1c4641353b4ab2106b7001c46417f4d4ed2ac84700000711904d4ed21042600000711904d4ed2ac5a600000711353b4ab210186001c4701904d4ed2ac847001c4641353b4ab210777001c4641353b4ab210327001c4641353b4ab210247001c46413548ced2ac847001c4641353b4ab210107001da711904d4ed2ac84700000001ef4d4ed2ac845001c4641353b4ab28c847001d5711904d4ed2ac847001c46418a4d4ed2ac847
  | 7, 0, 1 => 0x711903b4ab210246000007bdc44d4ed2ac846001c4641353b4ab2105a7001ef711904d4ed2ac847001c4641353b4ab210427001c46413543ced2ac84700000711904d4ab210326001c46e1904d4ed2ac847001c46415f4d4ed2ac847001c4641353b4ab2106f7001c4641353b4dc2ac847001c4641353b4ab244847001c4641353b4ab210737001c464135474ed2ac84700000711904d4ed2ac846001c4641353b4d62ac847
  | 7, 0, 2 => 0x1c4641353b4d32ac847001c46416d4d4ed2ac847001c4641353b4ab264847
  | 8, 0, 0 => 0x711904d4ed2ac846
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 2 => 34
  | 3 => 44
  | 4 => 54
  | 5 => 64
  | 6 => 74
  | 7 => 84
  | 8 => 94
  | _ => 0

def idWidth : Nat := 10
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
private theorem z4_192 : span (Z 4) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_216 : span (Z 4) 18 216 = true := by decide +kernel

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

private theorem z4_a9 : span (Z 4) 234 0 = true :=
  span_join (f := Z 4) (a := 216) (o := 0) (b := 18) z4_a8 z4_216

private theorem z4 : span (Z 4) 234 0 = true := z4_a9

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
private theorem z5_576 : span (Z 5) 24 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_600 : span (Z 5) 23 600 = true := by decide +kernel

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

private theorem z5_a24 : span (Z 5) 600 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 24) z5_a23 z5_576

private theorem z5_a25 : span (Z 5) 623 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 23) z5_a24 z5_600

private theorem z5 : span (Z 5) 623 0 = true := z5_a25

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
private theorem z6_360 : span (Z 6) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : span (Z 6) 9 384 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 384 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 24) z6_a14 z6_360

private theorem z6_a16 : span (Z 6) 393 0 = true :=
  span_join (f := Z 6) (a := 384) (o := 0) (b := 9) z6_a15 z6_384

private theorem z6 : span (Z 6) 393 0 = true := z6_a16

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

def CG : Circuit := ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12605

theorem PEqualNP.Outside.L_meta_12605 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373994 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12605.mainG PEqualNP.Outside.L_meta_12605.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12605.CG, PEqualNP.Outside.L_meta_12605.CG_mono, by
      have : PEqualNP.Outside.L_meta_12605.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12605.CG_eval⟩
