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
namespace PEqualNP.Outside.L_meta_12429

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941132928 * 2 ^ 32 + 3934317184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 7, 7, 7, 7, 7, 7, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 7, 7, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 9, 9, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 9, 9, 9, 9, 9, 9, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 9, 9, 9, 9, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 9, 9, 51, 9, 53, 54, 55, 9, 57, 9, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 11, 11, 11, 11, 11, 11, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 11, 11, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 13, 13, 13, 13, 13, 13, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 13, 13, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 14, 14, 14, 14, 14, 14, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 14, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 15, 15, 15, 15, 15, 15, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 23, 23, 23, 23, 23, 23, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 23, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 25, 25, 25, 25, 25, 25, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 27, 27, 27, 27, 27, 27, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 29, 29, 29, 29, 29, 29, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 30, 30, 30, 30, 30, 30, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 31, 31, 31, 31, 31, 31, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 39, 39, 39, 39, 39, 39, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 39, 39, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 41, 41, 41, 41, 41, 41, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 43, 43, 43, 43, 43, 43, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 45, 45, 45, 45, 45, 45, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 46, 46, 46, 46, 46, 46, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 47, 47, 47, 47, 47, 47, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 51, 51, 51, 51, 51, 51, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 53, 53, 53, 53, 53, 53, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 54, 54, 54, 54, 54, 54, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 55, 55, 55, 55, 55, 55, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 57, 57, 57, 57, 57, 57, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 59, 59, 59, 59, 59, 59, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 61, 61, 61, 61, 61, 61, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 62, 62, 62, 62, 62, 62, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1517157f157f157f1517157f157f157f1517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f1517157f157f157f1517157f157f157f00000000000000001517157f157f157f0000000000000000000000000000000000000000000000001517157f157f157f1517157f157f157f1517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001517157f157f157f1517157f157f157f1517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001517157f157f157f1517157f157f157f1517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea800000000000000000eae8ea80ea80ea80000000000000000000000000000000000000000000000000eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000eae8ea80ea80ea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80eae8ea80ea80ea80

def cMZZ : Nat := 0x1517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f0000000000000000000000000000000000000000000000001517157f157f157f00000000000000001517157f157f157f1517157f157f157f1517157f157f157f0000000000000000000000000000000000000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f0000000000000000000000000000000000000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f0000000000000000000000000000000000000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f00000000000000001517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f1517157f157f157f

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
  | 3 => 36
  | 4 => 189
  | 5 => 498
  | 6 => 314
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xbf2fcab19b843b8158c4c5cc31023f5211a30d53036e8dc8
  | 3, 0 => 0xf702084de24aef3cd8e63767d7fc183bad746d72a62af6719fe6b99b9f0d85279caf8ca39b843b8198f7b78b8c17acb6821144b77c00e2ba7b512bc377c0f31e76264a2670435ab46fa3c44b6cc1564f65917d6a5c48867f585c883d572fc8bb4219abd53b5a68cd21937ff61ef938ea1d312d3c18494153137a6f39118531090f1fce030521c81c046d8556021503bf
  | 4, 0 => 0x325ffc17324dcdbb3122399c301f722a2fc2724a2ea23e6a2e6c71752deda0552dd3a0932cb5a6052c4969f72b4f51852b1c8c252b0defd92941d9d72658dd8c24c238e723e5c9d62348f51f224c5815222a62c421e69c17218a53f3203a9b9e1fefb7a41e0d182c1da908fc1d7b47e31c57db011c06dd961bc00b6e1b9125e71a0c82081921bac8178d9055171166881639349f15c9d60a155e1426139dc73312cb16531282671d10f4af8e0f79f1970f5adebf0ececb9e0e33609c0d9f69390d3fc95a0c113f020b9433ff0a7dd0d508f7e49f08499a07082796d207ff656507b8519d079a29d3076ad234073026ab05f267d90402ea60019bd61201882c4c
  | 4, 1 => 0x69c700dd69078cdf675c9167668234a664f97abf6434cfe46334b5e762a336446188bde161817b76611a574e5e229ece5d3f26e55c47cef35b279c0958de17d1582979bc56647e025558658c533120b752f1a09f5281a2e352074def5165fe6d50206b844f70b48d4dbce7844cf3b0214c8e46914be07be84b959e194b9038bf4b609b624b547eb1490755fd483c8388481ecf5146b0441c469fb02e467f3f8f464fce8a45ccff4e4553a8f34462537441fe9ebf40e0df193fd3e6883d8500153d7601593b8e91903b3b218e3b36c3f43ad1a1da39b1338639b1063439487e8338bbade53840642137d72d8037d321e837564f4f3677d28b35f360833380faa1
  | 4, 2 => 0xfc6847a0f92a95d6f3fe0e44f2987846ebc9930fdd5b6c8bd8e63767d7ba7260d5f5624bcedc2453cb219117c979a89cc91d78dfc530028ac217df7ec17f70e7be62f3efbddd0c78bd7d3a52b985ab78b8742a3fb7c9087db6c11908b66a7806b1d068ecb11e92adac1ba105aa235235a440d749a2f379509af4292398fbaf26989665e994e259e5942b4d5d92c1a6389201ffc291fd67389152aaf08ffa624289ec48ef89cc3f0a85eea8d18572414484e6f3ed83bb3ee2824a50f88193f63c7fc474117e98fca27b512bc37a4a7f3b794a7d4f7874f51975476d1f70cf156d6fa3c44b6ed07fca6d83cf8d6c52e2206be49cf8
  | 5, 0 => 0xc4c8d510c4ad78a0c396b9e0bf6b64a0b9b77e00b732eef0ab92a6e0a9ff33d0a3f10100a391b6009e1287109bd1e5d099db0f8095bc6cc09569353093942a308f52fa008d657d608c9c889087bd1c3086e85fe080e087507d70c9d07bec81707408154073745370722722e06fd43ff067f84e1067e9cd3066ca5c906417f3405d4552605d17df705c94d4905c87a8e05c41f6405b9b9f405b372ec057927d10565906605096a0604f614d104e242ad04cf22f104b6b0e604aac2d30491474c04321da10402ea600340c822027a90290260d6f6025abcf802231e5801fe582101d5d9b901a7df49019bd61201157fbf00d52ecf00c184270022f458000babc6
  | 5, 1 => 0x1cc450d51c64f6bf1c5cd78b1c4682fb1bec108d1b9736cd1b6c858b1b01414d1ace10da1ab30ddf1a4ac7c91a2d92e31a0c82081a0610b719eb57ff19d3494a19750ef1197224301962b6b0191f2f9e18cf72ab18400ca11803411b17fb27d117bc5a5d17966ffd178d9055170a1a1c16fb3a671675d43b163c727c1529898e1508940e14770efc144216ee14403a3d1436da3a139f00ee1395f77912dd0eab12cb1653119d18af1196a7d7118424a81160179111306218111a3c5810f4af8e10d33ad010ba7050108c8178101a86990fda41370f1e506b0ecd13f10ecc809a0eb4df220e742de70e3cdf230dd6291c0d3685dd0d2061f20cf233e40cd9e1a6
  | 5, 2 => 0x352f8afb34ff9db634a2f3cd332d95e132fe64d33226b51831e1c11f31a344e5315eafaf30db67b5304f55712f4e225d2f44d1ee2f3c69512f038c3a2e4297112dcea8c02d9155c72d7d14982cfc53ee2c8078e32bc727a72b9b40062aa13d3b2a07756429fd397c28aa89c5286a9eb528647d21281af45927ddfe9e27ac6e80272f9727271baf7c269f97e82560a9542522ab0c252135d32435e20e23d7ef6d23cd1bbe234468bd231b849c231300ae2231db7322132a9521dc704e21bc6683216ea5a72147fd7d20f4b34b20adcf5b204273cd1fb526e31f8194a11f4f0eee1f4daccc1ec9b12c1e7d370a1e1430b71dc2eadb1d9f56af1d2112991d01137c
  | 5, 3 => 0x4b54be3c4af12d0e496725fa4927711748dde43d48aab3b8488f3565483b5f4d483b38dd474a09ce472d15894723670146cb90e8467f3f8f4640dd4f45ebd6c145d999a845ccff4e45ccf9f34553a8f34519254a4503199544b0db1244860da34462537443c6f595438e6a73438ae03b4342646142f4c1c042ee398342c7b699418369c4414e1f25409b9201407ac71a40726aea4039784040287baa40224aed3fd3e6883f53b3a53ea354673e1ef37e3e13b2cc3e0c8eb03de689a73d61a31b3d40c5503d1d811d3ca87f7b3bfc28f53bd4fff43a90976d39728a03387f81bc38022d1937d72d8037d10bec379610ef375369c73725594535f7d99d35864763
  | 5, 4 => 0x644da372633f1a90620002e8616132ac614064d560d335c360d091bb606cd95c5f911b6f5f23df3c5e6f7f4a5dd0bcb55d51b2925d4bad6e5ce422c45c29688c5c0f41ab5bf9017c5bafd59d5b00406f5ae6e4335adfabe159d29dd15991ca0e59916988595c6a16590e42b359067cb7583c2ac257ca465156eb608956e5ac8a56d3d01956cf04b956b5ffef56845ec2561d6d9755b0210c5580a5c15558658c55441b9655062667542ca0855407b98d54056d0f53eaa17a53e5b3d75364610d52074def51a01ae6508212634fb94ca34f70b48d4f42f30d4e4d2d0f4e4851bc4e0dcaf04dfe22514d6c8c484d6a06194d4715b84d2e410e4c26552b4b609b62
  | 5, 5 => 0x8725f45f84e12818844a368d840e77388409567d83b32a4d8383f1b08337bf8e82f71c4982ef85b782ec34e482df5cb98244dc0881b8cebf80f1d95680da302e809978977f283e267e56a7377c810f9d7c6aee597a92247478304c6c777f9fd677526db476bb28cc768cc936745ef3ba744f0a3a743527a773b872b5730a1b377224360f71ba46cd7133547a710e77ab70ece3207087e5f170599c426ffd075b6fa8645b6e9da8eb6e9223d86e41dfca6deb97c16cea22b26c7910e66b1b4cba6ab8b8386ab5c30e6a88bacd6a7eb55869f2052269a23f1a698f912a6909079a66186bf765d08e8565b1aa12655cac4f65289e1365016b0c64b6193664a52de0
  | 5, 6 => 0xb53d4954b4455008b42923b5b2dc82f2b203b222b176ecf4b03ddb81af8918f4ae988759ae07ed20ad2c2f33ad213d9fac5f572aabf1c02eaa45ceb3a92f80d7a882ba76a83aa97ba78c5334a5d73e86a4cd2404a2a13a2ba226dda3a180c79ba1115d069fec0bad9f044e1f9e9c90e49de03a469daad7dc9d25ee179ca464959c0530c69af429239a492cd99a26f27297bb7cd997a716db978fb939966d1d589637684894a7dc0e949edef79462e34293ad2b0b9201ffc291d0424690c036df8f3d44738f2fbe8e8f112aa68e17e25e8dc38f6e8dba99018da84d128c93b3098c847f818c102bae8be891478ab894e18a23b7ee89850a2d882bab3187d8781c
  | 5, 7 => 0xfc2262e5fb9a80d3f98cd3f2f7a61484f6b5a229f5efcc72f3990447f0717ae7ed41438deb941aaee8d851bee8caab1ee89e2e17e580efe5e48ba14fe408311ce2d308ffe231ca57e12d4998df427cc1dd878b3edd5b6c8bdcd85837dbd7da62db838749d8002f71d58070d3d572eaeed567c1fad55fc75fd482b096d36d3bc4d018a52ece79dc7cc98d17b0c92a9fe2c80266dfc7161430c5a01654c530028ac2f16dafc066a0f5bffcbdfebf854e29be44c766be2c27a8bc509ec4bb2d942cb6a05e20b5c373bf
  | 6, 0 => 0x178cc3a116fb3a671695207115c9d53715b244c7158090a4145f1a6f1436da3a1422904413e49b15132900eb12cb165312c4288512a9e4b41295a6e51278d5e011f84d9211427c8d1105f262107e7a520fb7be160fa78aa30efd1e660ea14a7e0e97c1510e7f29610e742de70dbd62880d3685dd0d26c66a0c4f8a850c4ad78a0bf6b64a0b732eef0b2795230ad7c1ea0ad3c5f10ac54dd10aa0c4a60a552ef70a3f10100a1d798809ce8f8609a5d02d08d657d607caa23c078f288a076daa13073891150719d3fb06984f940601dbaf05d4552605c94d490570718a04ca4b6f04321da10400587203e18e43028286f002439f7601a7df4901014be60060ed9e
  | 6, 1 => 0x3c8590183b5f844b3b4963073b031e213a90976d3a31873239e73721365e14843578acfc34f2be8d33d747b933139c5532fe64d332a3be8b3267a93131a47f8f30d1db9b3048f1563011c9282f665a9f2f3810f02e86d9092d7098862d28067f2ce957a62bfe8d1f2bc727a72b7128f62b037c282aa3e78c2a8035fc29f9c16829972ce629672f7b286e05d82769e3d626194d7225714d8724f6e0a524af03332485420e23dfdfba238684d4232c1820218c294621508a3421037e0e20de779620c99fca20800ddb1f4f0eee1f4b4e0a1f2c1e671e6f901d1e6f8b641e2a82ce1dd8de0f1cafc4cd1cab71b61c3027401b4875971ace10da1ab30ddf18605ac9
  | 6, 2 => 0x6b3dcbd86a7eb55869aba1eb69244361680df58567191e2966e8c3cd66a5f50b6598170260f63a3f606cd95c5f911b6f5d7b05925cbeaef45c894c8a5c0462c55bc6eba85b82d9435b4e91505ae6e43359d29dd159a21112596d00065927a1875905672058e7c4e356c1a6b2566e2de7554b920655441b965506266753e5b3d7534157f0522ef4244f42f30d4ef0b29a4e1bb9214e0dcaf04cf6570c4c65b6c44aff1b3f4aec0aa149e335b249d9b92a49cf948e49ae629749979a44486e93044825125747eb0ba947e9729b479d3eb6472d158945ccff4e4480a0d442bb75024262665e42412a0341bdd16740e4c17040287baa3e1fbc033d40c5503d1d811d
  | 6, 3 => 0xa17692baa10c6533a04d781ba00bbe469f1209a59e20f16f9d25ee179ce4b6169c65ffec9c08f8299bf56bc39a61fbf7966d1d58945ee581944636a89251fba3924bb072917e03219142479f905d90918f2fbe8e8eb4ea038e17e25e886b8c5e87400dc58725f45f86e0db8d868ea0a185f488de850d73fb840e77388409567d83fa7977837202bf82ec34e48244dc08820407e081d8059781cfe25d81a0715880f1d9567edb32ac7eb3447b7e63c2d77ca058647b4724f579955dd77828f4cb77087427761283d6755c3bad74a1e86d7353fe467323c4b672f5e5f472f2c1ab71ba46cd71234c7170e226d07067cf756f76418d6e678da26e56c09c6d382766
  | 6, 4 => 0xfcfd6827f96f0c16f6b5a229f6526e34f5efcc72f1dcd97cf0717ae7ee234697edd6a6d2ed210bbaec5b8941e749135ee6f96902e48ba14fe408311ce0267226dbff8742dba2c57edb24f7a4d7ad093ad5e88ec5d58070d3d2e4fa12cd52a290cba79b48cad52af3ca51a398ca3604aec7b88d11c74cfaa7c73505b6c530028ac4a6ef37c4a2940dc491e795c444050fc2f16dafc08653f2c0813337bfb3a378bf854e29bf64119ebd69b610ba78f581ba4d182eb4ce4120b40b177eb1b1a33eb0980fedb03ddb81af4fef95ac3351b3ac1fb83ba7b6c66ca45f6493a36a15fda2e6a5caa1b17dad
  | 7, 0 => 0xf96f0c16cd52a290cad52af3ca51a398c530028abd69b610b4ce4120af4fef95a36a15fd9f1209a5945ee581840e773881cfe25d80f1d9567e63c2d7761283d666a5f50b5c0462c5554b92064cf6570c479d3eb6218c29461422904412c42885107e7a520dbd62880a552ef701a7df49
  | 8, 0 => 0x840e7738
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa0000aaaa00005555555555550000555500005555000033330000333300000f0f0f0f0f0f000000ffffffffff000000ff00ff00ff000000ff000000ff00000000ffffffff00000000ff00ff0000000000aaaaaaaa0000000055555555000000000f0f0f0f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff00000000000000f000f000f000f000aa00aa00aa00aa0055005500550055000f000f000f000f0000ffffffffffff0000ffff00ffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000f0f00000f0f00000cccccccccccc0000aaaaaaaaaaaa
  | 0, 2 => 0x11111111111111110fff0fff0fff0fff0fff00000fff00000fff0000000000000f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f00000f0f00000f00ff00ff00ff000f000f000f000f000505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ffffff0000000000ff00ffffffffff
  | 0, 3 => 0x5555ffffffffffff5555ffff5555ffff555555555555555555550000555500005555000000000000550055005500550050f050f050f050f050505050505050503f3f3f3f3f3f3f3f3333ffffffffffff3333ffff3333ffff33333333333333333333000000000000330033003300330030303030303030302222222222222222
  | 0, 4 => 0xaa00aa0000000000aa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a000000000a0a0000000000000a000a000a000a000888888888888888888880000888800008800880088008800808080808080808077777777777777775f5f5f5f5f5f5f5f55ff55ff55ff55ff55ff55ff0000000055ff000000000000
  | 0, 5 => 0xaaaaaaaa88888888aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaaaaa88aaaaaa88aaaaaa88aa88aa88aaaaaa00aa00aa00aaaa888888888888aaaa0000aaaa0000aaaa0000aa000000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00ff00ff00ff00aa00aa00aa00aa00
  | 0, 6 => 0xc0ccc0ccc0ccc0ccc0c0c0c0c0c0c0c0c0c0c0c000000000c0c0000000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaff000000000000aaaaffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa00aa00
  | 0, 7 => 0xccccc0c0ccccc0c0ccccc0c0c0c0c0c0cccc8888cccc8888cccc888888888888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc0000000000cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c8c8c0c0c0c0c0c0c0f0c0f0c0f0c0f0
  | 0, 8 => 0xcfcccfcccfcccfccccff000000000000cccccfcfcfcfcfcfcccccccccfcfcfcfccccccccccccccccccccccccccccc0c0cccccccccc88cc88ccccccccc0c0c0c0cccccccc00000000ccccccc0ccc0ccc0ccccccc0c0c0c0c0cccccc88cccccc88cccccc88cc88cc88cccccc00cccccc00cccccc00cc00cc00ccccc8c8ccccc8c8
  | 0, 9 => 0xeecccccceecccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ececececececececececccccccccccccecec000000000000eaeaeaeaeaeaeaeaeaeaeaea00000000eaeaaaaaaaaaaaaaeaea000000000000eaaaeaaaeaaaeaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0c0c0c0c0c0c0cfcfcfcfcfcfcfcf
  | 0, 10 => 0xf0f00000f0000000f0f0000000000000f0a0f0a0f0a0f0a0f000f000f000f000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeeee00ee00ee00eeeeee0000000000eeeecccccccccccceeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000aaaa0000eeee000000000000eecceecceecceecc
  | 0, 11 => 0xf0f0f0f0f0f0c0c0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0f0c0f0c0f0c0f0f0f0a0f0f0f0a0f0f0f0a0f0a0f0a0f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0f0f0e0e0f0f0e0e0e0e0e0e0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f00000f0f00000
  | 0, 12 => 0xfaf0f0f0f0f0f0f0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f800000000f8f8000000000000f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0fff0ff00000000f0f0fffffffffffff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0
  | 0, 13 => 0xfcfc000000000000fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafafa00fafafa00fafafa00fa00fa00fafaf0f0f0f0f0f0fafaaaaaaaaaaaaafafa0000fafa0000fafa0000f0f00000fafa000000000000faf0faf0faf0faf0faf0faf0f0f0f0f0
  | 0, 14 => 0xfefefefefefefefefefe0000fefe0000fefe000000000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfc00fc00fcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfc00fc00fc00fcfcfc0000000000fcfcf0f0fcfcf0f0fcfcf0f0f0f0f0f0fcfcf0f000000000fcfcccccfcfcccccfcfccccc00000000fcfc0000fcfc0000
  | 0, 15 => 0xff11ff11ff11ff11ff00ffffffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff000000ff00ff00fa00fa00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00fa00fa00ff00f000ff00f000ff00cc00cc00cc00ff00aa00ff00aa00ff00aa00aa00aa00ff000000ff000000ff00000000000000
  | 1, 0 => 0xffaaffaaffaaffaaffaaffaaff00ff00ffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaaaaaffaaaaaaffaaaaaaaaaaaaaaffaa0000ffaa0000ffaa000000000000ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff88ff00ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff00ff00ff00ff33ff33ff33ff33
  | 1, 1 => 0xfff0ff00ff00ff00fff00000fff00000fff0000000000000ffeeffeeffeeffeeffeeff00ffeeff00ffee0000ff000000ffee000000000000ffecff00ff00ff00ffccffccffccffccffccffccccccccccffccff00ffccff00ffccff00ff00ff00ffccccccccccccccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ff00ff00
  | 1, 2 => 0xffff000003030000ffff000000ff0000ffff000000000000fffcfffcfffcfffcfffcfffcff00ff00fffcff00fffcff00fffcff00ff00ff00fffc0000fffc0000fffc0000ff000000fffc000000000000fffafffa00000000fffaff00ff00ff00fff8ff00ff00ff00fff0fff0fff0fff0fff0fff0ff00ff00fff0fff0f0f0f0f0
  | 1, 3 => 0xffff0000ffff5555ffff0000ffff0f0fffff0000ffff0000ffff0000ffcc0000ffff0000ffaa0000ffff0000ff000000ffff0000f0000000ffff0000cccc0000ffff0000cc000000ffff0000aaaa0000ffff0000aa000000ffff000080800000ffff000055550000ffff000055000000ffff000033000000ffff00000f0f0000
  | 1, 4 => 0xffff888800000000ffff808080808080ffff5555ffff5555ffff555555555555ffff5500ffff5500ffff550055005500ffff333333333333ffff1111ffff1111ffff0f0fffff0f0fffff0f000f000f00ffff050505050505ffff050500000000ffff030303030303ffff00ffffff00ffffff00ff00ff00ffffff0000ffffffff
  | 1, 5 => 0xffffc0c0c0c0c0c0ffffc0c000000000ffffc000ffffc000ffffc000c000c000ffffc00000000000ffffaaaaffffaaaaffffaaaaffaaaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00aa00aa00ffffaa0000000000ffffa0a0ffffa0a0ffffa0a0a0a0a0a0ffffa000a000a000ffffa00000000000
  | 1, 6 => 0xfffff0f000000000fffff000fffff000fffff000ff00f000fffff000f000f000fffff00000000000ffffeeeeeeeeeeeeffffeeee00000000ffffccccffffccccffffccccffff0000ffffccccffccccccffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffcc00cc00cc00ffffcc0000000000ffffc0c0ffffc0c0
  | 1, 7 => 0xffffff00cccccc00ffffff00aaaaaa00ffffff00aa00aa00ffffff000000ff00ffffff0000000000fffffcfcfffffcfcfffffcfcfcfcfcfcfffffcfc00000000fffffc00fffffc00fffffc00fc00fc00fffffc0000000000fffffafafffffafafffffa00fa00fa00fffffa0000000000fffff0f0fffff0f0fffff0f0f0f0f0f0
  | 1, 8 => 0xffffffff000000ffffffffff00000000fffffff0fff0fff0ffffffccffffffccffffffccffccffccffffffaaffffffaaffffffaaffaaffaaffffffaaff00ff00ffffff00ffffffffffffff00ffffff00ffffff00ffffcc00ffffff00ffffaa00ffffff00ffff0000ffffff00ffccff00ffffff00ff00ff00ffffff00ff000000
  | 1, 9 => 0xffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffff88008800ffffffff80808080ffffffff33333333ffffffff33003300ffffffff03030303ffffffff00ff00ffffffffff0000ffffffffffff0000ff00ffffffff0000ccccffffffff0000aaaa
  | 1, 10 => 0xfffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000ffffffffffccffccffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafafafafffffffffa00fa00fffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffcc00cc00ffffffffcc000000
  | 1, 11 => 0xffffffffffffffffffffffffffffff00
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x23e71319ca4dc6336ba2ca678137150f0273299c60dc633
  | 3, 0, 0 => 0x94bf0dc63491b0116634c0b2116634933f0dc63494b80dc6347e39cdc634c0b7116534b9b45166349135d16634d4ca8dc6347e2c5026348a2c5166347e30106594c0b01165447e268dc63496bf126524
  | 3, 0, 1 => 0x96bf0dc54493bf0dc6347e2b8e26348fb5916634c0cb0dc634004a4dc6337e301025a494b00dc634c0c5d266348a2b8dc6347e37cdc6347e398dc634c0b45406347e2e50263494b011663496ca4dc634
  | 3, 0, 2 => 0x94b7cdc63494bacdc634c0b45166349eca4dc634
  | 4, 0, 0 => 0x96bf1708b31adedf8b24598d688fc6022cc6b7b7e3010a6358a30116632aacb5f8c03798d65b016022cc6b3a7e2f5166357e3a1c06e31acb5f8c14598d703066022cc6b3a7e2c91663596bf180aa292cd5f8c04598d6d6fc6022cc6b2d4ea4d16635
  | 4, 0, 1 => 0xc73f1c06e31acb658fc3718d5f8c04598c38b3a7e3011263594b81808b31ad6df8c04598d7033d68a2cc6b818fb0116635c0bf1808b31ae05f8b94598d5f8d26022cc6afc73b011663596bf1808d31abf1628b3d18d65afc6026cc6b3d7e38cdc635
  | 4, 0, 2 => 0xb847d808b31ace9f8c04598565afc60218c6b2d7e2cd16635c0b451663282bf1c0df3718d65af66022cc6b467e30116635c0bf1268b31acc9f8c04598d702fc5ba2cc6b2d7e334dc6358d3f1808b31aea5f8e03718d65afc60228c6b3a6730116635
  | 4, 0, 3 => 0x96bf1d06e31acb5f8c04798d5f8a149a2cc6afc6025916635a8bf1808b31adcd9cc04598d686fc6022cc6b726730116635c0bf5808b31acb5f86e3193165afc48a2cc6b267e3011663596b459c8b31acc5f8c04598d65afc729b8c6b2d7e34116635
  | 4, 0, 4 => 0xb6bf1808b31acbdf8c04598d65afc6022cb8b817e301165a596bf1688b31acb5f8c03918d652fc6022cc6b757e301166357e3014c8b31acb5f8c04596d65afc759b8c6b8188b0116635c4bf1808b2cadf1f8c04598d65afc5d22cc6b507e30116635
  | 4, 0, 5 => 0x96bf1808831acb5808b3189d7538668a2cc6b2d7e33d1663596bf116631cabf1808b318b16751f6022cc6b819130116635c0b011663192ce9f8c04598d65afc601ccc6b2d7e300fc635c0b013a8b31acb652c04598d65b146022cc6b457e30116635
  | 4, 0, 6 => 0xb93f1808b31ac91f8c04598d65afc68a2cc6ac050a75166359d3f1268b31acb644fc3998d6d8fc6022cc6b4a7e301166358a3015c8b31abf1bec04598d65afc721b8c6b8e9ebf0e653596bf1be6e31abf1ccc04598d67afc751b8c6b818130116635
  | 4, 0, 7 => 0x9ebf1986e31acb5808b319456e0fc5aa2cc6b2d7e3291663596bb1808b31ae1a56c04598d65afa6022cc6b8b7e30102635b13011663282e05e6c04598d668fc6022cc6b2d7e24cc64859ecadf86e31acb628c03718d65afc6026490b737e30116635
  | 4, 0, 8 => 0x96bf1808331abf1dac04598d65afc6022ca8afc6b2b916635bebf1808b31a801f8df3718d24efc6022cc6afc571e8dc63596bf18e8b31ae06448b3718d7032c6022cc6a0094b01166347e3014e8b31ad55f8d14598d71d3d7e1b8a8afc6fb00dc635
  | 4, 0, 9 => 0xc0bf1a28b31acb59cc04598d702fc60220c6b8179301166357e3011663202cd5f8d14598d65afc6025516b816022cc6505c0bf1807e31abf1808b3318d700fc6022cc6b81912d51663596bf1807931ae062ec05518d702fc759b8c6b8e943f0dc635
  | 4, 0, 10 => 0x96bf1808b31abf1d6df3718d632fc6022cc6b587e301165957e3011c8b31acb5f8c04ba2d703216022cc6b3a7e3acdc6359ebf1be6e31acb608c04598d652eb6022cc6b816022cc652596bfd808b31acf652c04598d7032d68a2cc6afc65b0116635
  | 4, 0, 11 => 0x15c7e30116635bb3f1808b31acb606c04598d65afc68a80c6b2d8830116635aabf1808b31a80302d14598d302fe6022cc6b3a7e3451663596b01288b31aca5bec04598d702d16022cc6b4e7e30116635
  | 5, 0, 0 => 0xc74f5f8c03998d801357e30116635c74f5f8c03f18da7b2d8fb011663696c5df8c05518da5afc6022cc6116d4e19808b31941a5afc6022cc62667e30116630f071a7b2d7e30116636005adf8c04598d71d867e300e663696bf1808b31931a5afc602d9166369ebf150934598db253d7e30116636
  | 5, 0, 1 => 0xd24b5f8c04598da5afc6022cc6466ad4b5f8c04598d8012d6022c7a1f596bf180994598db0cfc6cb011663696bf1808b31915ae0fc602b91663696b01549d4598da5afc6022cc62f696c79f8c04598db17817e3011663600605f88b318a965afc7ab011663696bf1808b31815b1d1b7e30116636
  | 5, 0, 2 => 0x96bf1808b3193da7afc6cb011663696bf1808b3184db1d3f7e3011663696bf18cc04598db333d7e3011663696bf1808b3618db1d567e30140636003f180631a05d65afc6022cc61d6c7619f8c04418db1d3d7e22cc639696bf1d0c04598dab33a7e3011663696bf1808b318259f8c0459e8c6556
  | 5, 0, 3 => 0x9ebf1c2c04598da5afc6022cc6576d4cf5f8c04418da5afc75b011663696bf180a44598d8012d6022cc61f57e30150a34598db1cfc70300dc636c74f5f8c04418da5b057e3011663696c51f8c04598da8f2d7e30116636bd4b5f8c04598db3d3a7e3011663696c75f8c04598da5afc7130116636
  | 5, 0, 4 => 0xcc4f5f8c04598da5b177e300dc636c0c89f8c04598da5afc6022cc62969d3f1f8c04598da74fc602bd1663696bf1808b318fda7b2d7e24d166369d3f1808b31855a5afc6022cc6506cf5edf8c04598da7afc6022cce63696bf1808b4398d801817e301163d596c59f8c04598dad12d7e2c916636
  | 5, 0, 5 => 0x96bf1e4c04598da5afc6022cee636c74f1f8c04598dadd2d7e30116636c74f5f8d14598da852d7e30116636bdbf1808b31855b573a7e3011663600605f8c04598d65afc6130116636c7611f8c04598db03717e30116636c74f644fc3998db1cfc69b0116636c7619f8d14598d800fc6930116635
  | 5, 0, 6 => 0x96bf1808b3191da932d7e3011663696bf180a34598db233d7e30116636c7619f8c04218da5afc602a51663696bf180a54598dad33d7e30116636c0cb644c04598db0cfc6022cc61e6003f1808b318716752d7e30116636b2cb5f8c04598da5afc6022cc6206d4cf1f8c04598db5f2d7e30116636
  | 5, 0, 7 => 0x96c01f8c04598db1d867e301165d696b01588b31941a5afc6022cc63a6c74f5f8c04218dae92d7e3011663696bf180bc4598db43637e30116636d4cb5f8c04598da7afc6022cc61e696bf1808b31961a5afc601ecdc63600639f8e03718d71d3d7e30132486c7615f8c04598daab3d7e30116636
  | 5, 0, 8 => 0xc761df8c04598da5afc6eb011663696bf1808b31911a5afc6fb01166367e30116630f075a7afc7530116636c74f5f8c045975a5afc7bb0116636c73f1b0c04598dac53d7e30116636d84e9f8c04598db1d3d7e3013e6369d3f180ac4598db352d7e30116636d8cb5f8c04598db1d3d7e24cc6486
  | 5, 0, 9 => 0xc74f5f8c04018da5afc6022cc6036aabf1808b31941b1d3d7e3291663696bf1808b3188da5b0e7e3011663696bf1808b3a18db1d3d7630116636c0bf180aa4598dad92d7e30116636c0bf1808b3187db1d3d7e22ce06369eb01509d4598db1d3d7d3011663696bf1c8c04598da9f3d7e30116636
  | 5, 0, 10 => 0xc0bf1808b31979b43377e3011663696bf192c04598da74fc6022cc66069ec95f8c04598dadf3d7e30116636b3cb5f8c04598da7afc6022cc6216b24f5f8b24598dad8fc602b116636c35bdf8c04598da5afc75b00dc6369d3f1808b318a9a5afc6022cc61967e30116630f871b1d8690b0116636
  | 5, 0, 11 => 0x3f1808b318255f8c055285166369b3f1808b31979a7afc6026116636ac4b5f8c04598db02fc6022cdc63696bf1808b31835b03817e301166369ecadf8c04598da7b2d6027516636c0bf1808b3b18daad547e30116636004b5f8631a0a971d7f7e30116636d04f5f8c04598da5afc6022cc6526
  | 5, 0, 12 => 0x4b5f8c0318d165afc6022cf463696bf1808b318d5b1d3d7e2491663696c21f8c04598db592d7e30116636c75ddf8c04598db113d7e3011663696bf1808b318d98012d7e3acdc635004e9f88b318a94012d7e3007a345c74f5f8c74598db4b3d673011663696c85f8c04598da7afc5da1cdc636
  | 5, 0, 13 => 0xc73f1648b3d98da74fc6022cc6166b0bf1808b3b18da7b357e30116636c74f5f8c045951b1d337e3011663696bf1808b318d18013a7e301163d5004b628c04598d65afc6022cd463696bf1808b3182da5afc7db0116636b5cf5f8c04598db030f7e301166369ebf198c04598db3f2d7e30116636
  | 5, 0, 14 => 0x9ece5f8c04598d8013a7e30116635af4f5f8c04598d8012d7e300e6635c7575f8c04598db512d7e3011663696bf1808b4098dae33a7e30116636004b5f8c03f18d702fc6022cc60769d489f8c04598db02fc6022cc63d6c6cb5f8c04598da5afc6022cc63b6c7521f8c04598db03707e30116636
  | 5, 0, 15 => 0xc0bf1808b3d98db0d577e30116636bddc5f8c04598db53407e30116636aa4f5f8c04598db1d3d7e300f2636c9cb5f8c04598da5afc6022ce6636d4cf5f8bd4598da5afc6022cfc636c7501f8c04598da5afc6f30116636c0bf180b54598d801819130116635c74f5f8bd4598da5afc68b0116636
  | 5, 1, 0 => 0x5b1f8c04598d71d3d7e3012a8b6c74f580a04e98da5afc6022cc8636003f1bec04598d7033d7e3011663696bf180ab4598da5afc6022d10636abcf5f8c04598da5b137e301166369ebf1a4c04598d9f8c05722cf46369abf1808b31941af6fc6022d04636c3605f8c04598d8012d7e30110635
  | 5, 1, 1 => 0xc64b5f8c04598da74fc602a916636c76199cc04598db1d3d7e380dc6369d3f1808b3187daa52d7e3011663696bf1808b318218012d7e3451663596bf1b8c04598da5afc783011663696bf9f8c04598db02fc6022cc60969ebf1808b31871a5afc6ab011663696bf1808b31921b035a7e30116636
  | 5, 1, 2 => 0xc0bf1808b31941b1d3d7e2fd1663696bf1808b31929b1d827e30116636d14f5f8c04598dacd3a7e30116636c74f59cc04598db02fc75b011663696bf1807a3718db1d307e3011663600605808b3187d71d287e3011663696bf1808b31965b45867e3011663696bf1808b318f1b1d3d7e30118636
  | 5, 1, 3 => 0x96bf1808b318b9b032d6022cc650696bf180aa31921b4b3d7e301166369d3f1808b31959b1cfc75b80dc6369d3f1808b31979a5afc6022cc617696bf1808b31955ad52d7e3011663696bf188c04598d800c04598c3e1c5d54b5f8c04598da74fc6022cc6026c74f5f8dc4594db1d3d7e3a4dc636
  | 5, 1, 4 => 0x96bf1809e4598da7afc62b011663696bf1808b31989b1d567e30116636c55edf8c04598daf32d7e3011663696bf1808b318c5a5afc6022cc633696bf1dec04598da5afc602f916636bdbf1808b31979a5afc7a301166369d3f1808b3718da5afc6730116636b23f1808b3d98db033a7e30116636
  | 5, 1, 5 => 0x96bf1808b31841a7afc743011663696bf180904598da750f7e30116636c75f9f8c04598da5afc6022cc65f696bf1806e31921b1d3d7fb011663696c3d808b31941b0cfc743011663696bf1808b3186daf13d7e30116636c74f9f8c04598db02fc7bb0116636d4d59f8c04598da712d7e30116636
  | 5, 1, 6 => 0xc0d61f8c04598db0d3a7e301166369d3f1808b3d98da5afc6022cc638696bf1f0c04598db2d3d7e301166367e30146a14598db392d7e30116636c73f1808b318b5b1cfc60289166369d3f1808b318f5ae12d7e300fc6369ecb5f8eb3718da5afc6022cd66369ebf1808b31905a5b0b7e30116636
  | 5, 1, 7 => 0xbdcf5f8c04598db1d3d8fb011663696bf1808b31935b1d3d7e30116636c35edf8c04598db533b7e30116636004b580631a07d6f6fc6022cf6636c0cf644c04598d800fe7e30116635d4e19f8c04598da5b1c7e301166369ece9f8c04598db1d3b7e30116636c7619f8c04598da7b2d7e300fc636
  | 5, 1, 8 => 0x96bf1f8c04598d800fc6022cc61759d3f1808b31941a5afc6022cc6156c0bf1808b318d1b1d3d6025116636a64b5f8c04598da74fc75b0116636003f1808b318294013a6022cc61f59ebf1bec04598db02fc6022cf4636c73f1dcc04598d800fc6022c7a175d6605f8c04598da7b2d7e30110636
  | 5, 1, 9 => 0xa0cb5f8c04598d8012d673011663596bf1808b31851a5b0a7e30116636c7cf5f8c04598da753a7e3011663696bf1808b3c18da5b2d7e301166367e3adbec04598da5b097e30116636c7e19f8c04598da5afc6022cc61a6c74f5f8c84598d801816022cc65059ecb5f8d14598d9f8e86fb0116636
  | 5, 1, 10 => 0xcacf5f8c04598da5afc6022cda63696c7d80ae4598db02fc6022cc6596bdbf1eec04598db02fc7830116636cdcf5f8c04598db02fc6022cc6486d4cf5fac04598da74fc7bb0116636c74b5f8c04418da5afc68a2cc6506d84b5f8c04598da5afc6022cc642696bf180ac4598da5afc6022cc6066
  | 5, 1, 11 => 0xc752df8c04598da5b117e30116636c84f5f8c04598db1d3d81b011663696bf1808b31849b1d3d7e34540636d44f5f8c04598da5afc6022cc6376aacb5f8c04598db02fc6022cc6176c0bf1808b31955b51867e3011663696bf1808b31981b132d7e3011663696bf5f8c04598da5afc6022cc63e6
  | 5, 1, 12 => 0x96bf1808b31861b39567e3011663696c09f8c04598da5afc6022cc6006d44e9f8c04598d8012d7e3011663596c89f8c04598db1d3d4ea4d16636cecb5f8c04598d8012d7e301163d596c1df8c04598db1d3d7e270dc636afcb5f8c04598db593a7e30116636d4e1a44c04598da5afc6030116636
  | 5, 1, 13 => 0x96bf1808b318c1b5b2d7e3011663696bf1808b3418d801557e30116635c0bf1f8c04598d9f8e8703011663696bf1808b31891b1d3d963f0dc63696bf1808b3187d800c04598c3e17596bf1b8c03998db1d2e7e301166369d3f1808b31921a5afc602711663696bf1808b3e18db033d6022cc6506
  | 5, 1, 14 => 0xc4e05f8c04598da5afc6022cc60e6c74f5f8eb3718da5afc6022cc63d6c7619f8eb3718da5b0f7e3011663696cb1f8c04598db1d3d7e1b8c64c6a6cb5f8c04598da5afc6022cc61c696bf1808b3298da5afc6022cc601696bf1808b3718db032d7e30116636abcb5f8c04598da5afc6930116636
  | 5, 1, 15 => 0xac3f1808b31955a5afc6022cc6636
  | 6, 0, 0 => 0xc761ad0fc6022cc6f8e9ebf1808b3998df1d3d7e36d808b31be3a7afc6f30116637006925afc6022cc6c00ad4b5f8c04598db1d3d7e351808b31be3a7afc68b01166370063a7afc601ccc6d3d7e30154a84598df518e9ebf1808b31b8031cfc4598c54156d24f5f8c05da2cc6e009ecb5f8c04598db533d7e30116631a3dc67b2d7e30116637
  | 6, 0, 1 => 0x4b5f8eb6022cc6c00004b5808b3187d71d3d7e30d808b31b8031d2d7e22cc62a600639f8c0458f42ada19ebf1808b3b18df1d867e301608b31be3ad13d7e301166370063a7afc60220c6d8e9ec49f8c04598df1d3d7e301166321bcf5f8c05da2d0e637004f5f8d96022cc6d8e9ec55f8c04598df4d8e9ebf1808b31be4f1d3d7e30116637
  | 6, 0, 2 => 0x9ecb5f8c04598c3ef8ec33f1808b31821f1d867e371808b31b8031cfc6022cc6156d4cf5f8c05822cc6f8ec33f1808b31921f3d3d7e30116632f3e3a7afc6022cfa637c74f5f8c045990c6f8e9ec31f8c04598dc012d7e301166328363a7afc602c116637004b5f8c045a1cc6d8e9ebf1808b4418df53689ebf1808b31b8025afc6022cc6576
  | 6, 0, 3 => 0xc75c65afc6022cc6e00b2cb5f8c04598db1d2d913f1808b31be3a7afc6022cc63c7c76327afc6022cc6e009ebf5f8c04598db1d3d7e30116630438031d3d7e34516636c74f5f8dc6022cc6f8e9ebf1e0c04598dc018e96bf1808b1eb00001817e30116635c74f5f8c04598c90f3d96bf180aa4598df1d8cc33f1808b31b80352fc6022cc6156
  | 6, 0, 4 => 0xc74f5808b3b18ca0f819ecb5f8c04598dc012d7e3dd808b31b63a7afc6022cc61779ecb5f8c0459d8c6f8e9ebf1808b31955f1d867e3c5808b31beab533d7e30116637c74f5f8c0459a4c6e00c73f1808b31851a7b2d7e30116632f3eab1d3d7e30116637cbe3a7afc6022cc6e00d4cb5f8c04598d8013d7e30116630f3639f8c05822cc6577
  | 6, 0, 5 => 0xc74f5f8c04f22cc6f8e9ebf1808b31989f1d3d7e301166318be3a7afc6022cc6257c75c67afc601fcc6f8e9ebf180ad4598df1d3d7e3bd808b31be3a7afc602f91663700501f8c04598c0ed8e9ebf19cc04598df533d7e3c5808b31be3a7afc6022cc62e7c74f5f8f16022cc6f8e9ec89f8dc4598de7b2d7e301166e31be3a7afc602a8c6487
  | 6, 0, 6 => 0xcf63a6cfc6022cc6f8e9ebf1d2c04598df1d3d7e301208b31be3a7afc6022cc65f7c74f5f8c03718c90f8e9ec3d808b31941f1d3d7e30116630dbe3b06fc7bb01166379ecb61efc6022cc6f9c9ebf1808b31941c016f9ebf1808b31b63a7afc7cb01166379ebf1808b3187c3cf8e9ebf1c0c04598dee36f9ebf1808b31be3a7b387e30116637
  | 6, 0, 7 => 0xc74f5f8b0459b8c6f8e9ebf1808b318e1f1d3d7e3e1808b31be1a7b2d7e30116637006b25afc6022cc6d3d96bf1808b3d98df478e9ebf1808b31be731d3d7e30116637c74f5f8c04598c92f8e7e3adc0c04598df1d2d7e30116632f3e3a7afc6022cd6637005625afc6022cc6d3d96bf1808b3181de7b2d7e30116631ebdc27b2d7e30116637
  | 6, 0, 8 => 0xc74f5f8c0459d4c6e009ecb5808b3187d8013d7e301166301367b1d3d7e301166370063a80fc6022cc6c00004e9f8c04598d73d8ec33f1808b31be3a7b067e301166370063a7ac0318d03ed5a9ecb5f8c04598df1d3d8e3f1808b31be871d3d7e30116637004b5f8c04598c68d3d9ecb5f8c04598dc000096bf180631a28025afc6022cf4636
  | 6, 0, 9 => 0xc74f5f8c04598c34f8ec34b5f8c04598dc01819ebf1808b31b6a67afc6022cc6157c74f5f8fc6022cc6e00abcf5f8c04598db1d3d7e30116630abe3a7afc6022cc6287c7619f8fc6022cc6f3d96bf1808b31941f1d3d7e301166325be3b0cfc6022cc6157c74b5f8c04598c0ef3d96bf1808b4398df539e9ebf1808b31bcf65afc75b0116637
  | 6, 0, 10 => 0x9ecb5f8f76022cc6f8e9ebf1808b31819f1d3d7e3011663273803453d7e301166360063a7ace6022cc6db0c7619f8c04598df1d5a96bf1808b31be3a7afc6022cc6147c74f614fc6022cc6f8ec33f180ac4598dc018e6022cc61f0ab63a7afc6022cf0637c74f65afc6022cc6e0096bf1b8c04598d8012d7e3c1808b31b0025afc6022cc6486
  | 6, 0, 11 => 0xc74f5f8c04598cc0e00c7559f8c04598db1d3d7e301166307be3a7afd7e30116637c74f5f8c04598c7cf8e9ebf1808b3698df1d3d903f1808b31be3a7afc6022cc62a7c74f5f8c05722cc6e009eb0116630f8798012d7e30116630bb0025afc6022cc6556c74f5f8d14598ca0fb0c74f5f8c04598df1d3d7e3011663213e3a7afc602b116637
  | 6, 0, 12 => 0xd64f65afc6022cc6e00c74f5f88b318a9b1d3d86bf1808b31be3a7afc6030116637c74f5f8c04598c18f8e9ec45f8c04598dc018ec33f1166315363a5afc7bb0116637004f5f8e86022cc6d8ea9cf5f8c04598df1d3d7e30116630938031d3d7e22c7a2a6ac4f65afc6022cc6f8e9ebf1808b318ddf1d3d7e30116630f3ea67afc6022cc6607
  | 6, 0, 13 => 0xc75827afc6022cc6f8ec33f1808b4118dc01a9c33f1808b31b0027b3a7e30116636c74f5f8c04598c44f8e9ebf1808b318adf1d3d913f1808b31be3a7afc6022cc63270063b0cfc6022cc6d9dc74f5f8c04598df1d86913f1808b31b8031d3d7e301163d69ecb5f8c04598c68e00c7619f8c0458f5a7b2d7e301167a31be3a80fc6022cc6077
  | 6, 0, 14 => 0xc74f5f8c04e22cc6f3d96bf1e0c04598df1d867e30116630fbcf65afc6022cc648700001f8c04598c2eb8e9ebf1808b31811c012d7e30116630ab63a7afc6022cc6187d763a7afc6022cc6e00bdcf5f8c04598db1d3d813f1808b31be3a7afc6022d04637c74f5f8c04598c00f94c74f5f8c04598dc018e9ebf1808b31b0030d7b7e30116636
  | 6, 0, 15 => 0xd3e3a7afc6022cc6fa99ebf1808b31979f1d867e301166e31be3a7afc6022cc6307c74f5f8c04598cbcfadc74f5f8c04598dc012d7e301588b31b4f65afc6022cc6177c74f5f8c0459a0c6f3d96bf1808b31955f1d867e30116632f3e3a7afc6022cc6247004b65afc6022cc6d8e9ebf1808b3187df1d3d7e371807331be3a7afc6d30116637
  | 6, 1, 0 => 0xc761a7afc6022cc6f8e9ebf1808b3198df1d86c33f1808b31be3a7afc6022cc63d7c75c27afc6022cc6f8ec33f1808b318f5f1d3d913f1166e31b803513d7e30116636c74f61efc6022cc6f8ec343df8c04598df1d3d963f1808b31be3a9b3d7e30116637c74f5f8c04598c02f8e9ebf1808b3718df1d819ebf1808b31be3aaf3d7e30116637
  | 6, 1, 1 => 0x63a7ac04598c3ed8ec33f1808b31941f1d867e3ad808b31be3a7afc63301166370063b0cc04598c3ec00004b5f8c04598d4018e9eb01163d0fb63a7afc6026516637c74f5f8c04598c8af8e9eb01549d4598dc012d913f1808b31b63a7b3d7e30116637c35ee7afc6022cc6f8e9ebf1808b31931c000096bf1808b1eaea70d3d7e30116637
  | 6, 1, 2 => 0xc74f5f8c96022cc6f8e9ebf1d6c03718df1d3d7e30116630cb8025afc6022cdc636006065afc6022cc6d8e9ebf1bac04598df638e9ebf1808b31be3a7b007e30116637c74f5f8c04598c74f8ec35edf8c04598df1d3d9d3f1808b31b8025afc6022cc61f69ecb65afc6022cc6f8e9ebf1808b31941c013d7e30116630bb63a7afc75b0116637
  | 6, 1, 3 => 0x31d3d7e3ed808b31beb31d3d7e301166370063a7afc759b8c6dacc7619f8c04598dc012d7e30116631eb63ab13d7e30116637004b61efc6022cc6c00c74f5f8631a0a9800fc6022cc61503b63a7afc6022cc6527
  | 7, 0, 0 => 0x63a7b227e30116637000031d867e30116636000031d3d7e301163d6000031d3d7e22cc62a60063a7afc6022cc62a70063a7afc602b1166370063a7b2d7e301166370063a7afc6022cc61570067b1d3d7e301166370063a7afc78b01166370063a7afc6e301166370063a7afc6022cc6487000031cfc6022cc61560063a7afc602c1166370063ad13d7e30116637000027b2d7e30116636
  | 7, 0, 1 => 0x6b31d3d7e301166370063a7afc6022cc65070063a7afc75b0116637000031d3d6022cc61f600000012d7e301166350063b0d3d7e301166370063a7afc6022cc63d70063a7b0f7e301166370063a7afc6022cdc6370063a7afc6022cc65e70063a7afc6022cc61f7000031d3d7e30116636
  | 8, 0, 0 => 0x31d3d7e30116636
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
private theorem z3_24 : span (Z 3) 12 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 36 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 12) z3_0 z3_24

private theorem z3 : span (Z 3) 36 0 = true := z3_a1

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
private theorem z4_168 : span (Z 4) 21 168 = true := by decide +kernel

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

private theorem z4_a7 : span (Z 4) 189 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 21) z4_a6 z4_168

private theorem z4 : span (Z 4) 189 0 = true := z4_a7

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
private theorem z5_480 : span (Z 5) 18 480 = true := by decide +kernel

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

private theorem z5_a20 : span (Z 5) 498 0 = true :=
  span_join (f := Z 5) (a := 480) (o := 0) (b := 18) z5_a19 z5_480

private theorem z5 : span (Z 5) 498 0 = true := z5_a20

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

def CG : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [9, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12429

theorem PEqualNP.Outside.L_meta_12429 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132928 * 2 ^ 32 + 3934317184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132928 * 2 ^ 32 + 3934317184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12429.mainG PEqualNP.Outside.L_meta_12429.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12429.CG, PEqualNP.Outside.L_meta_12429.CG_mono, by
      have : PEqualNP.Outside.L_meta_12429.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12429.CG_eval⟩
