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
namespace PEqualNP.Outside.L_meta_12601

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 6, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 3, 11, 3, 13, 14, 15, 3, 17, 3, 19, 3, 21, 22, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 33, 3, 35, 3, 37, 38, 39, 3, 41, 42, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 3, 5, 5, 5, 7, 5, 5, 5, 11, 5, 13, 14, 15, 5, 17, 5, 19, 5, 21, 22, 23, 5, 25, 26, 27, 5, 29, 30, 31, 5, 33, 5, 35, 5, 37, 38, 39, 5, 41, 42, 43, 5, 45, 46, 47, 5, 49, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 5, 7, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 17, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 5, 11, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 17, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 33, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 5, 13, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 17, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 5, 14, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 17, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 5, 15, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 17, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 17, 17, 17, 3, 17, 5, 17, 7, 17, 17, 17, 11, 17, 13, 14, 15, 17, 17, 17, 19, 17, 21, 22, 23, 17, 25, 26, 27, 17, 29, 30, 31, 17, 33, 17, 35, 17, 37, 38, 39, 17, 41, 42, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 58, 59, 17, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 5, 19, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 17, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 33, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 5, 21, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 17, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 5, 22, 7, 22, 22, 22, 11, 22, 13, 14, 15, 22, 17, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 5, 23, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 17, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 5, 25, 7, 25, 25, 25, 11, 25, 13, 14, 15, 25, 17, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 33, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 5, 26, 7, 26, 26, 26, 11, 26, 13, 14, 15, 26, 17, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 5, 27, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 17, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 5, 29, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 17, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 5, 30, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 17, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 5, 31, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 17, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 33, 33, 33, 3, 33, 5, 33, 7, 33, 33, 33, 11, 33, 13, 14, 15, 33, 17, 33, 19, 33, 21, 22, 23, 33, 25, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 42, 43, 33, 45, 46, 47, 33, 49, 33, 51, 33, 53, 54, 55, 33, 57, 58, 59, 33, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 5, 35, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 17, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 5, 37, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 17, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 5, 38, 7, 38, 38, 38, 11, 38, 13, 14, 15, 38, 17, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 5, 39, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 17, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 5, 41, 7, 41, 41, 41, 11, 41, 13, 14, 15, 41, 17, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 3, 42, 5, 42, 7, 42, 42, 42, 11, 42, 13, 14, 15, 42, 17, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 33, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 3, 43, 5, 43, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 17, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 5, 45, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 17, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 5, 46, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 17, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 5, 47, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 17, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 5, 49, 7, 49, 49, 49, 11, 49, 13, 14, 15, 49, 17, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 5, 51, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 17, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 5, 53, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 17, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 5, 54, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 17, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 5, 55, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 17, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 5, 57, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 17, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 5, 58, 7, 58, 58, 58, 11, 58, 13, 14, 15, 58, 17, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 5, 59, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 17, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 5, 61, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 17, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 5, 62, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 17, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 5, 63, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115111511151757111511151115175711151115111517570000000000000000111511151115175711151115111517571115111511151757000000000000000011151115111517571115111511151757111511151115175700000000000000001115111511151757000000000000000011151115111517570000000000000000111511151115175711151115111517571115111511151757000000000000000011151115111517571115111511151757111511151115175700000000000000001115111511151757111511151115175711151115111517570000000000000000111511151115175700000000000000001115111511151757000000000000000011151115111517571115111511151757111511151115175700000000000000001115111511151757111511151115175711151115111517570000000000000000111511151115175711151115111517571115111511151757000000000000000011151115111517570000000000000000111511151115175700000000000000001115111511151757111511151115175711151115111517570000000000000000111511151115175700000000000000000000000000000000000000000000000011151115111517570000000000000000111511151115175700000000000000001115111511151757000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8000000000000000000000000000000000000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a80000000000000000eeeaeeeaeeeae8a8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8eeeaeeeaeeeae8a8

def cMZZ : Nat := 0x1115111511151757000000000000000000000000000000000000000000000000111511151115175700000000000000000000000000000000000000000000000011151115111517570000000000000000111511151115175700000000000000001115111511151757000000000000000000000000000000000000000000000000111511151115175700000000000000000000000000000000000000000000000011151115111517570000000000000000000000000000000000000000000000001115111511151757000000000000000011151115111517570000000000000000111511151115175700000000000000000000000000000000000000000000000011151115111517570000000000000000000000000000000000000000000000001115111511151757000000000000000000000000000000000000000000000000111511151115175700000000000000001115111511151757000000000000000011151115111517570000000000000000000000000000000000000000000000001115111511151757000000000000000011151115111517571115111511151757111511151115175700000000000000001115111511151757000000000000000011151115111517570000000000000000111511151115175711151115111517571115111511151757

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
  | 2 => 4
  | 3 => 36
  | 4 => 326
  | 5 => 788
  | 6 => 474
  | 7 => 37
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xd0e19b31d0e0d5cfd03a932566562a83
  | 3, 0 => 0xeb294cd5e5cba99fe4f9fba4e2eff338d53e7215cd9969c4b1dee2bca3641dea96a45e528c2a5af987610777856a698b817bc6c38092d5677d874f4870c730d96e18ecd069bc59926679f1e866629c085b82b44f4ae5e85d475aaf1e3b48bee4393741e1365d64ce31544750285364b7277a8f212499c1281e2093870ff3f88f0f63fa9e04a0d0f901f2073b00c75714
  | 4, 0 => 0x2bcc67ac2b9801d82b8e22742b63c5bc2b1c92062a3e4ee029abd77727a531ac269575fc2686774f264d2fbe25a69d44249d2b252452e22d23f41632216d8a0720eeedcb2015b69520103ff22007106e1fd8d1f11f8f8aa91f5dfb7b1d3182031b8527281b7a253b1a6a78fc1a5d9a0119dc45d719d37a66180fef4317f7336e17ac6124177b49551617d0c6136118b712fadfd912c2f4a1121346c11107fd650ff944d60e5c957a0e000f9e0d9a32440d40ee850c8865c20b7152b20a2c25b40a04d25209ce223609779f3408ea4a2708dd68e908aad3ce08513c1c079c0ba40767744d054d04a504c6f12603e1a058039baca901ef78a800ad6f5b0078e1ae
  | 4, 1 => 0x53d762d553d347f753b16f1952e5546f5267e9be51d83acf5136c20a4e58b8da4d8faabb4d1338a44ca41eb64c73a2af4c6f31ab4b5fa26e4b5854eb49f3a6ef48e88df24731c0994642ebe845437ba5447f00ab441db49843ca386d4380eda640e61feb3fd9b46d3f8799e13f6330683f06331f3eff241d3e66993c3e03dc803d1c0f3e3d02d9e43c59c4f13bc6879939fba9f639e4767839d338c639a86cc1392fd6d4387a5c03382be012381c1b63379d32c7371e1e92365c06f83658450a360e1393352c7af03529fbfc338600ac330172c6327edd2431d7275e31c5ec41310151da30628263305ce22d2ed41e572dff4d882d7987ee2d5a32182cca6fcb
  | 4, 2 => 0x86789b688593465284a8f1d280c83f6080b99dc6809c04648012d71b801140367ff957d27f31ef5e7d81cfae7c9332cb7b7652437b3797aa7aaf7a207a0c0db079e9497f78d0120378cf422977400a0276e0378c76a17cf3769c97e0760c9e4875532ec87494900870f652c570d5c1f170c730d96f425f836d9d7fb06d2d97936c42c3486bd2466069b324a068977cdc67ab917766cc409f65ffed4965c9cc0165a455c5642568ca64036aee631576c062ba6f63624f3c88622bcf7c6174c42a614e3cb1611a5f435f7c025e5ef9d2145eec01715ea262725c83635759e25a8b592d4f7b58fffef757d0403c575240a25653844f55978564549734c454478268
  | 4, 3 => 0xad488573ad296f6babbea23baba59a46a9fe7e92a862e825a84fc6dfa7f54e20a6d41685a59b3861a56750d5a52d6ea8a4e18b3ba4be8157a37740e6a25f8b38a227782ea129c7fca04ddc8d9fd513a09f85d39a9e2297619df70e8e9d0ea0919d0c633a9cf48f1a9cdb27b59c4f81419b9e12179af0b9ef9adea68e9ac8d9d79a2a74bf98aa5b6396c34aa896abda6d96488bd795945a08956c4cba9562392194c3c0ac9463daff93dc0102939d46699358f37c924ef83e907f731c905bf9e1902da5f58fa5b8c18e724d078dca2d458d963b7d8d754fb28d47ff518d08db198d08709389bf799389b4eca9883ebdb487e42ae0879035b4872024db86d24810
  | 4, 4 => 0xf184ef40f111f070ef5e2120ee3b29a1ee1f07d6ec7bd5b9ea0d8787e8ca1612e3a01483e39406a0e1542109de553647ddb15960dcb37b9bdbd21aeddbccbc55d91a1c48d907d729d8486e4dd6d4ff87d5afe786d56fdfb8d43b0c14d2dfe072d2dba40ad0d9c501d0218402cd29e59bc82fb2d4c695832dc566472bc3dbb96cc3951cc5c28ebf50c272c2cfc1950953c19362b8c17c814dc15baa3cc0f00b3ec0a2286ac02a250ebe7f5452bd042e35bcfd4801bc0c0db3bbfba807ba38e080b9a601f9b8f82f74b8cd3843b5898df5b5502569b4c436dcb4b53000b344554db307369ab290237eb2349918b17f32c1b12ee6d4af9b6893aed664edae63987b
  | 4, 5 => 0xfc213cd7fb1af720f891c0ccf65a9cb4f415c9b8f3fefc30
  | 5, 0 => 0xec897e40eb240840e15305b0e000f9e0db8eba50db0fd910daf394f0d5d40a80d40ee850d39a4eb0d21ed0f0cd8d3c20cbc15b00c4418af0bb47cc80b69181a0b5b2e190b45a6170b3bfebf0b16e6990b051dcd0b04bf230acce3050ac9bbfe0ac2fc3409fbf19009f3289209b11c880980f98f097ba20d0966436f08a149e80874c8880842b90b07f9f5ac07e09378074b7b3e0706732106c5136206af8b6006a41fa006661b4906054a2405a2c9c505998d080566b03e0540f6180509121b04d1eacc0456700e04479c3803e1a0580347b77f02c4a98002b56087024e5bf702053e33015ba36c014e824701284d5100aadb61008f612e00336fdb0023e16c
  | 5, 1 => 0x1da042371d8a07b71d66206b1d5c0b0e1d4f615a1d3dffa91d30a0231d268f6e1d1cf3971d0f66921cf698331c536c7e1c2d05b31ba41eba1b9c64fa1b93f6a41b835f3c1b788b7f1af3a4551ae8332b1a9d43941a28976c1a1fb7ed19f9139319e3e8a519d4e9f8199ba2671932536c190bb6e418e949fb18da5c1918d09e7418ccfc4b18879bed1833eafc17f7336e17eb9dce17a154d6177eae20174aafe916fe22a416e2999216b1f2b7160728dd155fe0ca154791f3153bf7c614bbfcb014b37697149cc8f314532f44136419eb135eb29b1355831712d09e0c12bb741b11e4efa91163dd871142e78f0fc288e20f9ad9da0f5150960f14f8110eeef36e
  | 5, 2 => 0x2de9f6d92de677a22daa63d22d32e9212d21ab6f2d112c2d2c7e497d2c209d6b2bed697c2b9a259b2b8e22742aeba5702ace14102a86725e2a47db372a3948542975276a296f3446287aed9927cb6731279ae8f62709b95a2709b4e325dc277f25cc5c7c25c2ef672591b41d25798f81254daae1253e828125259a0724e6056d249d2b252460c1b32421cd9223f4163223c0dcd823ab54d62371e4f12369c1892330a02922739ea3223e567322229100221667df2206b1d221e57c11218cb2ea213641c520c3206a20a8a4c1205ed9282018e2741fd3c16a1f995a0b1f37152c1ee674811edc951d1edbca3a1ed7dc3e1e8dda461e6b04af1e082fc71da6a4d7
  | 5, 3 => 0x4304c32342c2d349427f522f41999a3e40752d584061ab4d3ff2915f3fc215583fbda4543eae15173ea8e4ff3ea6c7943e20ff033dbd39883d96456f3d7651183d75f8993c8b0b043bd793b03adc67633ac504913a528d4839b95cf739a1528d39949b9e397685bb3928cf293911d7de39003e4c3891ee4e38740b2f37e704a237bfd96036cf604f3606270335b490ce35aac1be3563257235234240350b37d634b1832a34349294335b9fd933282716331f94263314168c32b1a31132a25b20327c9259325ec2523259254d3254a5c831b50be531a746e431524f2931513985314ef8ba3091225a3088f4b8306a81e730514c8d2f1c8d152f14fa422e41c388
  | 5, 4 => 0x53567498531845dd52ca750752aff1bb529f2f1152538068524844bd523a741a520f10fb5207014c51e865c951cfa06751218a2b50e277ee4ff02e1e4fdffd624f6deac44f2d01884f0c81264ecc6f454ea335694dde26594dcf0d844dc05f444dbd65b14d3985b04c4768dd4c28b5f84b5fa26e4b5854eb4b4535ac4b1eb2e54ae2411849a1f6f8499136ce49897acd4984f6fb495cb63849561e9a4938f2cd49366ca4492a448d4915a5c94901360848bc07ce48a8a5874867e56c4842378547f9be9247e168d04795f51147823bd44729e5974725d57e47027b8346ffe1c246db34dd46d3e75a4633c718460d7b4b44a051ed441db4984416053c439440cf
  | 5, 5 => 0x65806c506568fc156540ca9364d5ede4649f36ec64917bf56444c56e6430861a642ae7ce641b14c3635948f6632723e6631576c06290d22c62637b63624fa22c6217e8ba61bdea59619806d861711e0d61324c2261222622607fe76060518053601302a0600cc58c5fef88d65fd1d7ef5f45471f5ebcb4145eb2850c5e91092f5e378d0b5d5909fc5c8c0b6b5bcbb5785bbe9a7a5bbb659c5b6a71e25b477a525b468d195afa04205af7cf7e5a1c6a555a1ab34859faee7859183eaa590b0c0658f2c86e5858aa0b57f95f405751dd975663e96956629ce45623bd9b55b7a4e255a0310c557d3ba354e1fdc1548648d55468d1ec5419ea4553da0f9f53b16f19
  | 5, 6 => 0x795e4e5678e5961f78cb1a0e780ec53a77f7647b77cf75e77789213e771833cb76f6b7ee76b99e5a74c8339f7490ea46746b41fe735fb2df7347ca7b73395b307311df6b729975c0728c19d17284bff872806207723e8b3f71cfaedc71b4ef2970004efc6ffacf8f6fe1a5746f5236bc6f50e0c36ec643546e860a536e1d53a16d77766d6d5a80596d37bc286d2d97936cf0a0d26cebf7946cd2e7526c7f99046c78c5156c3e6ab76c1db4d26bdcb54f6b992d0e6ab92f276a8e7cab6a354f2669efef9c6991a31d68c6a0d168a1a171686f2ad36813a5c767e302b167ab917767a850006792b04767321e04670da63e67031257666e82dc66260e036621f0cf
  | 5, 7 => 0x8d78e7688cfc85b88cf699058cb75ad38bd08e428bb87e718ba10e368b70b9708aab443f8aa7c3c78a6aea0c8996fe808904889688e2ccb188b0abca886160fc87e42ae087b24da8875ee67087512f3d870ce4d886ebb91286a7e2578683c2688609927085f5bba5859d6ae784ef784884a8f1d284a41976844e83af8448be7284287a3283f8e4b683aa6c8a835fbd4f82f42b6a828d7b2f8135792480c3c25b801140367fff92977f925f7b7e7c22bf7d0dec3c7cea48817c9332cb7c235a197b8d305d7b8cd2a57b7652437b3797aa7b329d897adea85d7a8917a17a84eb2f7a64d09d7a2399187a20bab979e9497f79c70e11798876917987d4e179677f8e
  | 5, 8 => 0xa2b42685a2ab3cbda277061ca2409482a224d796a1b20b24a17704f4a0a90117a096f81ca08c84daa03681709f95d48f9e6f412f9e1e0bce9de0eb659dccb0ea9d1e3bc19c8e28f19ba29a0c9b1131d89adea68e9ab604c39a2a74bf9917f21098b4f1d5988fbbc0988ba699988ba1f59888210a987be151982391b9980cf40097a9cdad9720ad3296c5b38f96a753219623091d94c3c0ac93f5873e93f2816493a1096a933f190e932386499309908592ead90292767f68916ea056914581379107b50e90cc7bf0904301c3903524a690299a5e9018b0d88f3048ed8f0638d28eec84c08eb7db238ea755118e7a2b2f8e6a228f8e666b718e2d19378de064b1
  | 5, 9 => 0xbb19d544badcb4dbbad21ea4ba4a89fdb9e3f5d6b9c86ff9b8cd3843b8b4b9d4b7f31a41b7c0fae8b72a2c15b68f1296b60c68b3b5dd31f9b5cd6c23b5c13578b5ac5e55b58c980ab583ea80b4e1d561b4caf3f6b4bc5a5ab448cab2b43e7de7b376e097b08a6297b04bbaaaafdc9012afb14c06af935542af8238e5aef9bc90ae6edd04adffc85cad94fbddad875329ad58db05ad09baf4ac1baaecabf447e0ab6dea78ab46755baadc2e27aad65321aac959fdaabb5908a988fadaa8d8009ea89e9812a80d0814a7d77f12a75e20bca751de5ba6fb73ada6cc1a30a692c7f6a5de9627a5c152eea52d6ea8a51682cfa4ec1279a4cda56aa376ed5da341645b
  | 5, 10 => 0xd34a2a84d32dfb0ed317fe15d2d90e82d2c5579ad22f3f88d1603da5d148cd6ad148c19ad0ffcc09d0a01206cfc1e921cf54ad96cf208d96ce81e35ecdaa4b94cd6c3375ccdbd382ccb2a6e3cc4d0ff5cb46a8d6caf543caca6c4c62ca237230c9238710c8f01156c8d618bec8be5d79c8be5261c8423ed1c7d39f1cc7289a2bc7142404c6b08e1fc695832dc62a16b3c5f062b0c5d631abc53501aac4d38aaec4552363c42837aac3eeec63c3dbb96cc33eaf5ac3390ce9c3350a4dc2edbf03c2328fc1c211159cc1fc794cc19fd235c1897acec0a2286ac072b6d3c03d6ff7c03d2dd1c01019f7bf9ca181bf574bdbbd7afae5bd09b77ebc8f48bebb50debd
  | 5, 11 => 0xf609dc4bf4b7ff68f3fbe1fff3de69ebf3c75452f2d1461ef2ce02e1f2b137d5f1c49f34f1a6a8bef146d3b5f111f070ef484f34ef3a0f02ee5c071bee4496e0ee3b29a1ee320972ee1b1d1eed9bdb7ced5e6d43ed3d1b01ec36ffe2ebe03375ebac633ceb7dacd4ea6eebade9b6bc10e9ae7059e9a90f5de8c232f0e8a7004ae8694fdee74d6ed9e5d1e234e4f4e5dae4606319e3ac5795e3a01483e2e2298be2d1fb21e2ac93c9e20408bbe1b31934e1899c4ae042a806df1ba6f2dda691a4dd5bfa30dd39396ddc5dfc51dbd21aeddba45e19db97a7f1db68a8bfdab832d9da017630d95ef075d94c1dffd74dad5cd6ee872cd5f6585cd5dee821d5362cbd
  | 5, 12 => 0xff66dfcaff633ed2ff5d32c2fe4c43f3fe15e42afdebc285fd5a9499fce1e32ffc623a4dfc3410aafbf55611fbafac6afaea7e48f9dda217f9b6293cf84bc878f7e8dd71f73012fcf6ea1f4df63cc375
  | 6, 0 => 0x1bd8fd0d1ae95b9f1a582c03192a9a281922374618e949fb189c1d8a1834781617eb9dce17af345c170f4f8116c0579a16b8343215f63bde15c2114c1564da881555247b1533eeba1411931314076d86128587d5122a3ce312264ee711dc4cef10d87a6010b49314109dd403108c7252105dd93b0fa1df270f7b785c0eead7a30ee2694d0e36a5d40debb63d0d6e2a960d47863c0cd8d3c20c37bca40c28cec20b825da50b5b2e190b45a6170a9922920a4c954d0a310c3b0a00656009d3cf5809559b8606b28c940540f61804b250300423ee2b03951fbd0310fb8b029fc33f023d6617018fed240163a304014e824700fdabf800aadb6100881794000a8859
  | 6, 1 => 0x3cd369a43cab28e13c84df4d3c78b7363c6418723c4fa8b13c22a2fa3bf718303bb61aee3b48313b3b20286e3ab3a0623a50ee2c3a29a7863a225a0339b95cf739a1528d395bedf43899222d37eec4963779088f36e2b37835cdc4d834e80ce732e2edd8327c925931f757a8317d5d71310bac3130e4b818300be4092fd97dad2f2606592f1c8d152e2ada0c2e13773a2d07cfa02cefc5362c7741d22c604a872c4eb0f5295499ac2903037728f9346728b1981b2871b4e92859aa7f266e06cf25f0cdc925ad34fb24f5b98d2371e4f122c0595f21e57c1121bdded321386982212e12f220c3206a205f9ed61f3bdc251e1c86b91da6a4d71d0382021cc39a13
  | 6, 2 => 0x577ef8c35675968f5663e96955b7a4e255665b6354ea8e0c548648d55480becb53ce5a09539ff2fc53617549533dfb7f53204a985261e6c452538068520b26bd51df7bd851cfa0674f1a28214f09d8454e1fc7384dcf0d844dc05f444dbb159f4d71f4b34d4961214b47d1e94b46351249dd416749366ca44906178b48cbae4c4830706a47d4bb7e4728824846ffe1c246a4e741466f5e3f4666b88645fe646445eda1ba45a1f311456d7e5f456ce3b3455573f5451e13104490d84e433ea0c742bc5d6d427b7431425af3cf4256164f421ae1ee41f1a81241539bc3412c9902410ed1ed4087f85940498b26400c6abd3f95db863eae15173ea6c7943ce06f55
  | 6, 3 => 0x77f28c1f77cf75e7779cf6587776ecdb7747575f75dbedd87490ea46738bbcfd73744cc2735fb2df72e0d22472cb915e720c7a8671ca956870ad62b67038bb2a6fe1a5746ede263b6edb454e6e860a536d37bc286cd6e93a6c3e6ab76c3408c86c198cb76b992d0e6b5d37e36b0198166ad793e76a452a9768dc0d7768becccf6801b10367ab917765d332a163512f1d634ec1a5631576c06268ef4f61222622603f137b603a6a3d6037b1625fc737be5f9857565f8cdd605f3536d65f2b27f85eb2850c5e91092f5d83c1cf5ce015c65c15137a5bbd9d7c5b6218705afa04205af6c2a95ae122f05a8090ad5a7ada05597480ac58cedef95824608d57eda995
  | 6, 4 => 0x9be1a8949b25f1bb9aac93659a7747d09a49e6569a1a8cd999beb3a0990fc5979864f578983a8522968fd7049602992e95c578c5958f072b9384f41992767f6891bdb3d89173ce8c916c7e7791374e36912f5e0e906cae6a90469c769034d3aa8fe34cf18fdc9b9a8ef10cb58ee0d2658e2d19378d78e7688c03647e8bda149e8bd693b38b7a76d98ad27fa289717bc68743f9e78740f40d868d8bb78658032e86394bab85c4f21184bd12ff845627b784287a328399d0dc8368a83583672381827ebb9681c89dd881b4de1a812ed75a801140367df9b6e87df636707db95cb57c77261b7b8cd2a57a99ed4b7a5b578179f6550079d235117958051979442e4e
  | 6, 5 => 0xc02a462bbf9b829ebe951b7fbe588506be43b673bdbabf0bbc3e83ffbc248b67bc0cd022bb2211c5ba6296adb9ff00c8b9e3f5d6b924a454b821fd57b72a2c15b6a81c0db68d2203b6877f92b67eae97b63c31acb55f8845b4ee44deb38be2a0b38ba07ab35e8ca0b2eb142ab2a5be84b0c96d8eb08a6297b0582a27afdc9012ae6847edae2b2784ac1baaecab418ceaaa6e385ea91bdecca8fad0fea8f092b5a8d25d29a80d0814a7d77f12a7973d5ba6fb73ada3d8d540a32b02bba2ffbeafa2e1c7eba2d65ab4a2d0ab8ea2b42685a277061ca1bd4fada14e3b05a0582d9d9f42ba899ebc5d219e2aa0d09e17cca69d7ce0529d1e3bc19cd76d839c7a65c6
  | 6, 6 => 0xed3d1b01ed049be5eb507a3be9584ef4e72cdc94e61fb8c7e61c758ae5ffaa7ee51311dde28881abe1aa79c4e1899c4ae1807c1be1698fc7e0ea4e25e08b8daadefad5e5decc1f7ddd052eb9dc10a599dbb7c287da0f9189d92054ddd89386e7d736b729d6faca3ed6ee872cd6206dcad5f6585cd5dee821d5527b64d5362cbdd3911aafd317fe15d26a199bd148c19ad0f5044dd090504bd087ac16cfac6efacf208d96cef2d0c2ceb71b68cd6c3375ccad631ecc3d2052cb46a8d6ca9c2005ca6c4c62c944cb05c92d5acac8849f66c66670bec613ca43c4d38aaec4aeb04ec4973443c3ee84afc3105bcac2a3203fc1d05607c19fd235c107498dc0baa61e
  | 6, 7 => 0xfea9a0bdfe8a7163fe65593dfe4c43f3fe1b55a9fce1e32ffc266dcbfbc33b2cfa99ede2fa138606f9b48dedf88f68bcf603d32bf4aa1610f3de69ebf34d097ef2b55273f2b137d5f19ab69cf16456d3f13a352ef03055d8efe8e504ef650503ef43c8baeefe1f13
  | 7, 0 => 0xfea9a0bdf19ab69ce5ffaa7ec944cb05c8849f66c66670bec0baa61ebe951b7fbdbabf0bb821fd57b4ee44dea3d8d5409b25f1bb9a49e6569602992e95c578c5906cae6a85c4f2117776ecdb735fb2df6edb454e67ab91775f8cdd605afa04205663e96951df7bd847d4bb7e451e1310410ed1ed3c84df4d3779088f2d07cfa02cefc53616c0579a1533eeba141193130540f618
  | 8, 0 => 0x5afa0420
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffff000000000000cccccccc00000000555555550000000033333333000000000f0f0f0f000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xf000f0f0f0f0f000f000f000f0f0f000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff000000f0f00000f0f00000aaaa0000aaaa00000f0f00000f0f000000ff000000ff
  | 0, 2 => 0xf0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f00ff000f00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff0000
  | 0, 3 => 0x333333333333ffff33333333333333333333333333330000333333330000000033330000ffff000033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff0fff000000000f0fffff0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
  | 0, 4 => 0x555555550000000055550000ffff00005500ff005500ff00550055005500ff0055005500550055005050f0f05050f0f0505050505050f0f050505050505050504c4c4c4c4c4c4c4c4444cccc4444cccc444444444444cccc444444444444444444004400440044003f3f3f3f3f3f3f3f33ff33ff33ff33ff33333333ffffffff
  | 0, 5 => 0x88008800880088008080808080808080777777777777777777777777777700007777000077770000770077007700770070707070707070705f5f5f5f5f5f5f5f5f5f5f5f5f5f00005f5f00005f5f00005f005f005f005f0055ff55ff55ff55ff5555ffff5555ffff555555555555ffff55555555555555555555555555550000
  | 0, 6 => 0xaaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a000000000a000a000a000a000888888888888888888888888888800008888888800000000
  | 0, 7 => 0xc000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaa0a0a0a0aaaaaaaa00000000aaaaaa00aaaaaa00aaaa8888aaaa8888
  | 0, 8 => 0xcc88cc88cc88cc88cc88cc88cc88cc00cc88cc00cc88cc00cc80cc80cc80cc80cc00ff00cc00ff00cc00cc00cc00ff00cc00cc00cc00cc00cc00cc00cc00c000cc00cc00cc000000cc000000cc000000c8c8c8c8c8c8c8c8c0c0c0c0f0f0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000
  | 0, 9 => 0xccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000ccccccccc0c0c0c0cccccccc00000000cccccc00cccccc00cccc8888cccc8888cccc0000ffff0000cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc8ccc8ccc8cc88ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc00ccc0ccc0cc00cc00
  | 0, 10 => 0xeaeaeaeaeaeaaaaaeaeaeaeaaaaaaaaaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0dddddddddddddddddd00dd00dd00dd00cfcfcfcfcfcfcfcfcfcfcfcfcfcf0000cfcfcfcf00000000cf00cf00cf00cf00ccffccffccffccffccccccccffffffffccccccccccccffffcccccccccccccccccccccccccccccc88cccccccccccccc00
  | 0, 11 => 0xeeaaeeaaeeaaaaaaeeaaeeaacc00cc00eeaaeeaaaaaaaaaaeeaacc00eeaacc00ee00ee00ee00ee00ee00ee00ee00cc00ee00ee00cc00cc00ee00cc00ee00cc00ececececececececececececececccccececececccccccccececccccececcccceccceccceccceccceca0eca0eca0eca0ec00ec00ec00ec00eaeaeaeaeaeaeaea
  | 0, 12 => 0xeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccceeeeeeee00000000eeeeececeeeeececeeeecccceeeecccceeeecccccccccccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecccccccccceeaaeeaaeeaaeeaaeeaaeeaaeeaaeaaaeeaaeeaaeeaacc00
  | 0, 13 => 0xf0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0a0a0f0f0a0a0f0f00000ffff0000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeecec
  | 0, 14 => 0xf5f5f5f5f5f5f5f5f500f500f500f500f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f3f3f0f0f3f3f0f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000
  | 0, 15 => 0xfafafafafafa0000fafafafaf0f0f0f0fafafafa00000000fafaf8f8fafaf8f8fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafaf0faf0faf0faf0faf0faf0faf0f0f0faf0f0f0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0
  | 1, 0 => 0xfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0fcf0fcf0f0f0fcf0fcf0fcf0cc00fcf0f0f0fcf0f0f0fcf0cc00fcf0cc00fcccfcccfcccfcccfca8fca8fca8fca8fc00fc00fc00fc00fc00fc00fc00f000fc00fc00fc00cc00fc00fc00cc00cc00fafafafafafafafafafafafafafaf8f8fafafafafafaf0f0fafafafafafaaaaa
  | 1, 1 => 0xff00cc00cc00cc00ff005500ff005500ff000000ffff0000ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000fefe0000fefe0000feaafeaafeaafeaafe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcf0f0fcfcf0f0fcfcccccfcfccccc
  | 1, 2 => 0xff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00c000ff00ff00ff00aa00ff00ff00ff005500ff00ff00ff000000ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0055005500ff00ff0000000000ff00fc00ff00fc00ff00cc00ff00cc00
  | 1, 3 => 0xff33ff00ff33ff00ff30ff30ff30ff30ff22ff22ff22ff22ff11ff11ff11ff11ff0fff0fff0fff0fff0aff0aff0aff0aff03ff03ff03ff03ff00ff00ffffffffff00ff00ffaaffaaff00ff00ff33ff33ff00ff00ff00ffffff00ff00ff00ffaaff00ff00ff00ff33ff00ff00ff00ff0fff00ff00ff00ff00ff00ff00ff00fc00
  | 1, 4 => 0xffaaffaa00000000ffaaffa0ffaaffa0ffaaff00ffaaff00ffaaff00ff00ff00ffaaaaaaffaaaaaaffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff33ff33ff33ff33ff33ff33ff33ff00
  | 1, 5 => 0xffc0ff00ffc0ff00ffbbffbbffbbffbbffaaffaaffaaffaaffaaffaaffaaffa0ffaaffaaffaaff88ffaaffaaffaaff00ffaaffaaffaafaaaffaaffaaffaaf0a0ffaaffaaffaaeeaaffaaffaaffaacc88ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaff88ff88ffaaffaaff00ff00ffaaffaaeeaaeeaaffaaffaacc88cc88
  | 1, 6 => 0xfff0ff00ff00ff00fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeeffee0000ffeeffee00000000ffccffccffccffccffccffccffccff00ffccffccffccccccffccffccffcc0000ffccffccccccccccffccff00ffccff00ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00
  | 1, 7 => 0xfffafffafffaf0a0fffafffafffa0000fffafffaffaaffaafffafffaff00ff00fffafffaf0f0f0f0fffa0000fffa0000fff0fff0fff0fff0fff0fff0fff0ffa0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff0f000fff0fff0fff00000fff0fff0ff00ff00fff0fff0f0f0f0f0fff0ffa0fff0ffa0fff0ff00fff0ff00
  | 1, 8 => 0xffff7777ffff0000ffff5f5fffff0000ffff5555ffff5555ffff3333ffff0000ffff1111ffff1111ffff0f0fffff0f0fffff0f0fffff0000ffff00ffffff00ffffff0000ffff0000ffff0000ff000000ffff000000000000fffcfffcfffcfffcfffafffafffafffafffafffafffaffaafffafffafffaff00fffafffafffaf0f0
  | 1, 9 => 0xffffccccffffccccffffccccffff8888ffffccccffff0000ffffccccccccccccffffcccc00000000ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaaaffffa0a0ffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa000ffffa000ffff8888ffff8888ffff8888ffff0000
  | 1, 10 => 0xffffffaaffffffaaffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00fffffefeffff0000fffffcfcfffffcfcfffffafafffffafafffff0f0fffff0f0fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff0a0fffff0a0fffff000fffff000ffffeeee00000000ffffcfcfffff0000
  | 1, 11 => 0xffffffffaa000000ffffffffa8a8a8a8ffffffffa0a0a0a0ffffffff88888888ffffffff88008800ffffffff80808080ffffffff55550000ffffffff33333333ffffffff30303030ffffffff0fff0000ffffffff00ff0000ffffffff0000ffffffffffff00000000fffffffaffff0000ffffffccffffffccffffffccffff0000
  | 1, 12 => 0xfffffffff0f00000fffffffff0a0f0a0fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeeee0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c00000ffffffffc000c000ffffffffaaaaaaaaffffffffaaaa8888ffffffffaaaa0000ffffffffaa00aa00
  | 1, 13 => 0xffffffffffff1111ffffffffffff0f0fffffffffffff00ffffffffffffff0000fffffffffffa0000fffffffffff0fff0fffffffffff00000ffffffffffee0000ffffffffffaa0000ffffffffff00ff00ffffffffff00f000ffffffffff000000fffffffffcfc0000fffffffffafa0000fffffffff0f0f0f0fffffffff0f0f000
  | 1, 14 => 0xffffffffffffeeeeffffffffffffccccffffffffffffcc00ffffffffffffc0c0ffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa8a8ffffffffffffa0a0ffffffffffffa000ffffffffffff8888ffffffffffff8800ffffffffffff8080ffffffffffff5555ffffffffffff3333ffffffffffff3030
  | 1, 15 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff0a0fffffffffffff000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0xf8a50f277f511e4fe4933c9e0142793
  | 3, 0, 0 => 0xf5c3944794e761d28794f843944794f6dd944794f960544794ee2b11e794f2b9984a24733351e794f2d75ccd14f960944794fb60144794f8e0d44794f943144794ee39926794f94c55ea24ee35528794
  | 3, 0, 1 => 0xaa39942794ee399849d4f85d944794f6c3544794ac38144794ee39982a24ee3cd84a24f8de544794f95d544794f6b997ea24ee575e6d14f95dd44794aa39544794f95e144794bf35544794f958144794
  | 3, 0, 2 => 0xf928922794ee39984854ee4395aa24fae0144794
  | 4, 0, 0 => 0xee39998b93caf728ae6511e57b976aea88f2bca732ed44795ee4c5ccb43caf71cccf449e57b95273330f2bdc98b9990795d9575cca23caf71ccbe511e5662e6511e4b8bdc9739944795ee39912790e2f7262e65b1e57b93151210f2bdca4b996e795
  | 4, 0, 1 => 0xf94b9c0a23caf726ee6511e57b90e6a288f2bdcb728912795d9e8a1ca23cacc5cccf669e57b9d6bb288f2bdc98b98f2465ee4f9cca23cafcb0f77511e57b92073288f2bdc82b9944795ee4c5cccf3caf7262f7511e57b93181288f2bdc91b9944795
  | 4, 0, 2 => 0xee3994479262fb650e6511e57b93185a88f2bdc7333112795ee501cca23caf71cca2489e57e0e651224f2be398b9944795efcc5cca23caf7216a2449e57b9317b288f2ba098b9944795ee4c1cca23caf7262e6619e57b95873288f2bdcb74c544795
  | 4, 0, 3 => 0xf239944893caf724ce6511e57b92c73288f2bdc73288f22b5ee4c5ccbd512f726301679e5767875623cf2bdc98a88f24a5ee429cca23caf71ccbd512257b95173288f2bdcaeb999e795ee4c5cccc3caf7262a23c87d7e13173288f2bdc98b9928795
  | 4, 0, 4 => 0x98b9950a23caf72bae6689897b93172a88f2beb7328912795e261e1ca23caecf4783511e57b93673288f2bdc732fd4489598b9944791aaf9262e6511e57b96eaea88f2bdc98bad44795f54c5cccf3caf72b4e6679e57b95d7331d44bdc732c944795
  | 4, 0, 5 => 0xee421cca23caf72bae6661e57e15d73288f2bdca6bed44795ee4c5ccd03caf72bee6511e57b95d73250f2bdcab39944795ee54dcca23caf7266e6511e57b8e651238f2beb98b9944795ee51dcca23caf71ccba511e57b931732fd44bdc98b995ea25
  | 4, 0, 6 => 0xec4c5cca23caf9e92e6511e57b95973288f2bdc90b9944795d9e46bae668af9662e6511e57b90c73288f2bdca739944795ee50dcca23caf7306d5511e57cae651224f2bdc98b9994795ee39984a2312f72aee6511e57b97c73288f2bdc87288fe795
  | 4, 0, 7 => 0xee531cca23caf7262a2419e57b8e65123cf2bdc98b7144795cecc5fca23cafd6a8e6511e57b93273288f2bb3c8b9984a25ee575caa23caf71ccb9511e57b8e655288f2bdcaeb9960a25ee399447921af72a4e6511e57b97373288f2b317333d38795
  | 4, 0, 8 => 0xec575cca23caf71cca2481e57b93175288f2bdc7329944795ee3994479162e3e62e6511e57cb5d73288f2bdcd45dd44795ee4c61aa23caf7304e6511e57b9317f330f2bf5f95e544795ee4c56e823caf7262e3511e57b90d51224f2bdc73288f24d5
  | 4, 0, 9 => 0xf95de62a23caf71cca2441e57b73173288f2ae666a8912795ee4c5cca23caf72f731511e57b931731e48abdc9d39944795ee5bdcca23cafca62ff511e57b8ee73288f2bdc7328912795f94c600a23caf2262e6649e57953173324f2bdc7328914795
  | 4, 0, 10 => 0xee4c5ccb73caf7262a23c9257b931732b944bdc98b5d44795f938144893caf7158a2449e57cb3179a88f2bdcc04c544795ee3996e893caf71ccb1511e57b95e73288f2bb3c3d75e6d15007caeea23ca77262a23c9657b98173288f2b317333544795
  | 4, 0, 11 => 0xee4c5f8a23cad75cccd511e57b93180a88f2be598b99a279598b3558a23caf72ecd4511e57b90151224f2bdcaeb9944795ee3991e823caf72f75d511e57c13173288f2bdc73288f24b5f94c5c0a23caf7262ac511e57678779b0944bdc8aa2504795
  | 4, 0, 12 => 0xe539944893caf72bad7511e57b980aea88f2bdc98bb144795f94c5c8a23caf7262b7561e57b97697288f2bf6aa39944795d5cc5cca23caf7262f1511e57b93173288eebdcbeb9944795ee569cca23caf72a0e6511e56fd3173288f2bdc732dd62795
  | 4, 0, 13 => 0xee4c5e6a23caf7262e64f9e57e17973288f2bf09439944795ee3f944893caf71e6a2449e57b92d73288f2bdc8b39944795e54c5cca23caf71cca23c9697e55d70288f2bdcaeab144795f8cc5cca23caf72bae65b9e56631973288f2bdc733451e795
  | 4, 0, 14 => 0xee4bdcca23caf7268e6511e57cb4673288f2bdca539944795bf575cca23caf72f0e6511e57b91773288f2bdcaec0544795f3cc544823caf71cca23c9557b93181adcf2bdc98b9942795ee5b662a23cae3a62e6511e57b9317f288f2bdcb039944795
  | 4, 0, 15 => 0xee411cca23caf2abae6511e57e35d73288f2be698b9944795ee4adcca23caf71cc9c479e57953156288f2bb3d1de544795faf72eca23cafcae931511e57d53180a88f2bdcbbb9944795ee56a02a23caf7278e6511e57b93f73288f2bdc8339944795
  | 4, 1, 0 => 0xf9772eea23cafcaeee0511e57b94173288f2bdc7328916795ee5e5aaa23cadaa62e6511e57b95d73284f2bdcaebf944795ee571cca23caf72baf3511e57b93173310f2bdcaeb99447c5ee4c544790f2ecf5177511e57b9c37330944bdca239944795
  | 4, 1, 1 => 0xf6b9944873caf71cca2461e57b91f73288f2bb698b9944795ee4c5ccad512f7272e6511e56630151270f2bdc98b98f2475f3cc5cca23cafc25ce6511e57d5dc7330944bdca439944795ee3995aa244af9dcca2449e57d13173288f2bdc732891a795
  | 4, 1, 2 => 0xd9e1dccc242af9ebae6511e576787872b544bdc98bcda2795ee56dcca23caf7262f0511e57e53170a88f2be798b996e795ee4c5ccb33caf71e0a2449e57b95d7333944b6aaeb994479598b9944792baf71ccc2511e57b97173288f2bdca339944795
  | 4, 1, 3 => 0xf95ddcca23caf72ed31511e57b8bb56288f2bdca4b9944795ee39980a23caf72eca2449e57b9317d288f2bdc94b9944795ee41dcca23caf9e6303511e55cccd5da88f2bf298a8902795ee4f5cca23caf71cccf5d1e57b8e65da88f2bdc7327512795
  | 4, 1, 4 => 0x3b93179288f2bee7327112795ee40dccc2512f728cf3511e5767876aa50f2bdc732250a795
  | 5, 0, 0 => 0xee5ba631c511e5b678798b98f2466c3cc5cccc4d1e5801dc9739944795d9e1e7ce6511e5ba78798b9944796ee439cca2449e5b95317334544796ee4c5cca23c829bb93173288f22a6d9e1e40e6511e5b6794aeb9944796ee61dcca2449e5b678798b999e796e6e8a62e6511e5bdfdc98b9944796
  | 5, 0, 1 => 0x77262791f0c5400e651224f2095d9e8abae6511e5b673173288f23b6ee4c61ce6511e5ba58798b9944796ee40dcca2449e5b6787b728912796ee4c5cca23c8bdbb93173288f23a6d9e2e62e6511e5bb95d7328938796ee549cca23c9c9bb93180b9944796ee61e62e6511e5b67317336944796
  | 5, 0, 2 => 0xee4c606e6511e5b6787b74c544796ee50a62e6511e5bb95d7335144796ee575cca24d1e5b89877328912796ee4c5cca23e1e5b67879bb9944796c3cc5cccd511e5bb9317332d44796d9cc5cca23c939bb95d7336544796f3f7262e6511e5bb9319039944796d9e1e1cd4511e5bb9317338544796
  | 5, 0, 3 => 0xd9e1e16a2449e5b0f317329d44796ee666bae6511e5801dc9039944795d9e1e62f6511e5b678c98b9944796ee4c5cca23c835b9d8798b99447960077262e6679e57b9318d39944796d9e1e62e6619e58013173288f209500771cc791f0897dddcaeb9944796d9e526303511e5bb99198b9944796
  | 5, 0, 4 => 0xe2e1e62e6511e5bddea98b9944796faf71cca2449e5bb93173288f2536d9e1e630b511e5b67877333112796d9e5ea4e6511e5bb9317328902796dfe1e62e6511e5bb9a998b9944796ee4c5cca24e9e5bb9318ab99a2796e261e62e6511e5801dc73288f8795eb7470f79511e5bb98a98b9944796
  | 5, 0, 5 => 0xee61e62ac511e5bb93173288f2786ee70662e6511e5801dcb74c544795d9e1e62e6661e5b678798a88f21f6ee61e62e65b9e5bb95d73288f26e6ee4c5cca23c841bb9cd98b9944796ee575cca23c8f9bb8e651224fe796ee4c5cca3511e5be5dcaeb9944796ee4c5cca23c9a5b678798b9928796
  | 5, 0, 6 => 0xd9cc5cca24b9e5b2f317328934796d9e1e62a23c929bb93179b9944796ee4c5cca23f9e5bb98773288f24b6ee4c5eae6511e5bb94f98b9944796d9e1e14e6511e5b6787732f544896d9e1ea2e6511e5b679e98b9944796f961e62e0511e5bebdc98b9944796ee4c5cca23c8ddb679998b9992796
  | 5, 0, 7 => 0xf97aa62e6511e5bb93173288f2486ee5cdccde511e5ba3a698b9944796ee39944893c9c9bb9aebcb9944796de61e8ce6511e5bb9ae9439944796d9cc630e6511e5bb9317337544796e361dcca2449e5bb9b498b994479600771cca24494570f317333196796ee4c5fce6511e5bb9b198b9944796
  | 5, 0, 8 => 0xdde1dcca2449e5801dc98b9944515d9e1ebae663a89bb93173288f2216d9e1dccb2511e5be5dc98c0d44796e7e1ee0e6511e5bb96498b9944796d9e1e4ce6511e5b67879639944796ee39944893c8c5bb93173288f20e60077282e63c8f97678798b997aa26ee59662e6511e5bb987aeb9944796
  | 5, 0, 9 => 0x77262e6661e57b9ac98b9944796ee59a62e6511e5801f098b9944795ee57606e6511e5b6787b757544796ee4c5cca23c8c5bb93173288f2206ee4c5cca23c8c9bb8e6512250c796ee61e6301511e5b678798bad44796ee69a62e6511e5bb93184b9944796ee4c5cca23c9c9b8d8798b9944796
  | 5, 0, 10 => 0xee4c5cca2429e5bb9317333944796d9e1ebae668989b0f3173288f2246ee4c5fae6511e5bb931732890c796ee4c658e6511e5bb9c992b9944796dde1e62e6511e5b9d87aeb9944796ee4c5cca23c815bb987ad39944796ee4c5dee6511e58015d73288f2095d9e1e6ce6511e5bb98d98b9944796
  | 5, 0, 11 => 0xee4c5f0e6511e5b91877328912796fbf7262e6511e5b6787afb9944796d9e1ebae64a1e5bb9c77328912796d9e1ea6e6511e5b913173288f26e6ee4c5cca23c981bb38798b99447960077258e6511e576787a3b9944796ee4c5cca23c849b67977328912796dbe1e62e6511e5b7b8798a8904796
  | 5, 0, 12 => 0xe461e62e6511e5bb95da7b9944796e561e62e6511e5b67877330944626d9e1ef8e6511e5bb9c798b9944796d9e1e1ca23f9e5bb93173288f2616faf72bae6511e5bdd317328938796f777262e6689e5b67878439944796d9e1ebae6661e5b679798b9944796d9e1e9afb511e5bcb3173288f2626
  | 5, 0, 13 => 0xee61e62f3511e5b6787a739944796ee70262e6511e5bb931923994479600771cca22892d7b93173288f2736ee399bca2449e5bb8e651224f26a6dae1e62e6511e5b6787a1b9944796e56ce62e6511e5b6787c1b5544796ee61262e6511e5bb93173288f2236d9e1e62e6651e5bb93173288f2146
  | 5, 0, 14 => 0xdf61e62e6511e5bb93173288f20b6ee575cca23c8c5bb93173288f2136ee4c5cca23c8d9b838798b9992796ee4c5ccde511e5bb93173288f26a6f94c5cca24e1e5bb9b398bf94479600772bae6511457b93173288f21c6ee4c5cca23c911b678790b9944796ee61e62fe511e5b679098b9944796
  | 5, 0, 15 => 0xd9dea62e6511e5bb987bbb9944796ee4c64ee6511e5bb9317da88f26e6ee4c5ccd3511e5b6787732e544796d9e1dccaa511e5b6787aeb9960a26d9e1dcca23c90db6787a939944796ee4c5f2e6511e5b6787b9b9944796ee4c5cccf511e5bb931732892a79600771cca23c871767a8b839944796
  | 5, 1, 0 => 0xee4c5cca23c8cd80131511e462095d9e1dcca23c935b6797aeb9944796e861e62e6511e5b6787a639944796ee4c5cca23c831b6787732891e796ee54a62e6511e5bb97398b9944796d9e1e62dc511e5bb99598b9944796ee3994496449e5801e598b9944795ee4c5cca23c9d5bb9a598b9944796
  | 5, 1, 1 => 0xe461ebae6511e5b678798add04796d9ec262e6511e5b878798bf944796ee4c5cca23c9a1bb8e668aed44796d9cc5cca23c959b7b877328912796ee4c5cca24b1e5bb99f7328912796ee4c5ccd6511e5bb9317328932796f2ef262e6511e5bb93151208f2666ee4c5cca23c805bb9318939944796
  | 5, 1, 2 => 0xee505cca23c8f9bb931732891e796ee4560ee6511e5bb9af98b9944796ee4c5cca5511e5bb93173288f2716dee1e62e6511e5bb99f98b9944796ee39944893c9d1bb8e651224f2626ee4c5cca23c89d800e6511e44409500772a4e6511e5401dcb9b9944795fc77262e6511e5b678798bf998796
  | 5, 1, 3 => 0xee75262e6511e5bb96398b9944796d9e1e62ea511e5bb9317328900796ee4c5cca23c991bb93173288f2746d9e1dcca6511e5b678773288f22c6f3ef662e6511e5bb95d73288f26a6ee4d662e6511e5bb93173288f2626ee39944893c825bb9b3b839944796ee471cca2449e5bb987b839944796
  | 5, 1, 4 => 0xd9e1edee6511e5ba987b74c544796ee4c5cca23c975b67877739944796d9e1dcca2449e5bb987a0b9944796f868a62e6511e5bb93173288f2096f9f7262e6511e5bb9317333144796ee4c5cca24c1e5bb9318e39944796d9e1dcca2481e5beddc98b9944796ee4c5cca23c8a5801dc732891e795
  | 5, 1, 5 => 0xf3e1e62e6511e5b839998b9944796d9e45cca2449e5801dc98a88a2315ee55662e6511e5bb8e651224f2416d9deabae6511e5b939d98b9944796ee59e62e6511e5b678798b9944796e54c5ccc6511e5b0ee665a8912796d9e1ef731511e5bb8e65122512796d9e1e74e6511e5bab8798b9944796
  | 5, 1, 6 => 0xee4c620e6511e5b0f6998b9944796d9cc63ae6511e5bb987a339944796ee76a62e6511e5b679198b9944796ee60e62e6511e5bb93173288f241600771cca22888977b8798b996e796ee4c5ccdb511e5bb93173288f2636ee5da6328511e5bb94b98b9944796c3cc5cccb511e5bb9317328912796
  | 5, 1, 7 => 0xee5e5ccd4511e5bb9287335144796fafca62e6511e5801dc73288f2415ee4c5cca23c8f1bb9a898b8144796d9e1ebce6511e5bb8e651224f25f6ee61dccc2511e5bd3dc98b9944796e8e7662e6511e5bb93198b994479600771cca2449e57678798a88f2596d9e8af2e6511e5b679798bf944796
  | 5, 1, 8 => 0xd9e1d58a2449e5bb93173288f2006ee4c5cca23c97db6787732dd12796ee4c5cca23c901bb99d98b9944796d9e1dccb1511e5801dc98b9944795ee39944893c999bb95d732891e796ee6bebae6511e5bb93173288f2026e6e1dcca2449e5bb93173288f4796ee67ebae6511e5bb93173288f2076
  | 5, 1, 9 => 0xee4c5cca23c9d9b67878aa2504796d9e1e62e65b9e5801317333544795ee4c5cca23c961bb95d8e39944796f877262e6511e5beddcaeb9944796ee72e62e6511e5bb93173288f2666d9e1e62e657289bb99b98b9944796e6e1e62e6511e5bb95d73288f2746d9e1e62d7511e5bb95d73288f2626
  | 5, 1, 10 => 0xf54c5cca23c9d180131731e47c095ee569cca23c9d1bb96c98b9944796d9e1ef75d511e5b0f3165ab144796ee5da62e6511e5bb93173288f2506ee4c5cca23c861b66e651224f20e6d9e1dcca23c92db6794a4b9944796ee4c602a23c9d1b738798b9944796d9e1e62ac511e5bb95d73288f2096
  | 5, 1, 11 => 0xee4c5cca2439e5bb983aeb9944796ee4c622e6511e5bb93173288f24b6d9e1e6301511e5b67a698b9944796ee4c5cca23c8e1b0f5d7332d44796ee575cca2449e5b678798b996a796ee3994489439e5b673173288f20e6d9e1e3ce6511e5b6787aeb9944796d9e1dcc8f411e5b67a67328912796
  | 5, 1, 12 => 0xd9e1efae6511e5bb95d98b9944796007ca62e0511e5401dc98ab144795d9e1eb4e6511e5b6787a839944796c3cc5fca24d1e5bb93173288f23f6d9e2662e6511e5b0f69aeb9944796d9e1dccb7589e5801dc98b996e795d9e1e62fc511e5bb9a898a8904796d9e46bae6511e5bb987732ed44796
  | 5, 1, 13 => 0xee75a62e6511e5bb9317328924796d9e1dccd1479e5bb95a98b9944796d9e1ebad7511e5bb93173288f2196ee61e0ee6511e5b678798add5879600772bae6511e57679898b9944796ee759cca2449e5bb931732dcf2666d9e1e62f1511e5bb93173288f225600771cca23c92d7e9dc98b9944796
  | 5, 1, 14 => 0x772b4e6511e57678773288f25a6ee61e4ae6511e5a62e665b1944796ee6aa62e6511e5b6787aeab144796ee4c5ccc7511e5801dc98b98a23e5ee5ae62e6511e5bb93173288f2546d9e1ebae65b9e5bc5dc98b9944796007726301511e57b95d73288f2666ee4c5e6a23c989b0f3173288f2346
  | 5, 1, 15 => 0xd9e1e62f3511e5bcbdc98b9944796d9d75cca23c839b438798b9944796ee61e92e6511e5bebdcbcb9944796faf7250e6511e5b758798b9944796ee6a2f331511e5bb93173288f26d6ee67e62e6689e5b67877f28912796ee4c5cca23c821b678779a8912796d9e1e2ce6511e5bb9b392b9944796
  | 5, 2, 0 => 0xee4c5cca23c93dbb93173288f23d6d9e1dcca23c955b67a6aeb9944796d9e1e63035b9e5bb93173288f6796ee4c606a23c999a62e651270f2746d9e1edb31511e5b6787732f144796ee61eed31511e5bb93173344f2626d9cc5cca23c9bdbb93173288f21a6d9e1e62fe511e5bb8e651224f2516
  | 5, 2, 1 => 0xee6ce9ae6511e5bb9318039944796d9e1e7ee6511e5bb987a6b9944796ee4c5cca23f1e5801ca98b9944795ee39944a2449e5bb95daeb9944796d9e4662f3511e5bb96298b9944796d9e1e94e6511e5bb99498b994479600771cca23c8697b93173288f2516ee4c5dae6511e5b67878bb9944796
  | 5, 2, 2 => 0xee6a262e6511e5bb9d6aeb9944796ee6e262e6511e5baf8798b99447960077262fe511e57678773325707960077262f3511e57e5dc9739944796ee5ba62e6511e5bb93173288f2656ee4c5fee6511e5bb9317328944796ee6a1cca2449e5b6787bbb9944796e161e62e6511e5b67879e39944796
  | 5, 2, 3 => 0x77262a23c8c57b9318a39944796ee4c5cca23c889bb9318db9944796e1ecf0ee661289b6787a239944796ee61e5ce6511e5bb97798b9944796d9e1e08e6511e5bb931732893c796ee4c5ccd2511e5bb93173b9944796ee5aebae6511e5801dc51224f2315ee39944893c889b679198b99a2796
  | 5, 2, 4 => 0xd9e1ef2d5511e5ba98798b9944796ee4c5cca23c859bb8e6511e4a24b6f677262e6511e5801dc73288f2225ee575cca23c869b6787aebf944796d9e1ebaf3511e5bb931732c14479600772eee6511e57b9317328936796ee62262e6511e5b6787aeb99447c6ea61dcca2449e5bb8e651224f2166
  | 5, 2, 5 => 0xee4c5ccdf511e5bb94673288f2626e661e62e6511e5b6787732891a796d9cc5cca23c96dbb93173288f21d6d9e1e82e6511e5bb9dc7328912796ee4c5e8e6511e5bb8e67028912796ee575cca23c945bb98798b999e796ee4c5ccb7511e5b67a798b9944796ee4c5cca23c909b67877328916796
  | 5, 2, 6 => 0xee4c5ccc5511e5bb987b74c544796ee6a2bae6511e5b678798b995aa26d9e1e72e6511e5bc3dc98b9944796ee50662e6511e5b678798b98f2476ebe1ebae6511e5bb9dc98b9944796d9e1dccad51225bb9317338144796ee69262e6511e5bb931732ad44796ee4c62aa2411e5be1317335144796
  | 5, 2, 7 => 0x772baa23c8c57b95d73288f2226d9cc5cca23c8b9b67a898b8144796d9e1dccc2511e5b6787a6b99927960077282e6511e576787b8b9944796ee65a62e6511e5bdddc9639944796d9e1e8ce6511e5bb9b3b74c544796ee4c5cccd511e5b67877328918796ee4c5d0e6511e5b67878fb9944796
  | 5, 2, 8 => 0xee61e62e6661e5bb9317330944796ee4c5cce4511e5bb9c398b9944796f861e62e6511e5801e798b9944795ea61ebae6511e5bb8e65122504796ee575cca23c859bb9a898c0d44796fcf7262e6511e5bb94698b9944796ee39984a2449e5bb9c37328912796ee4c626e6511e5b679398b9944796
  | 5, 2, 9 => 0xee66a62e6511e5bb968732891279600771ccc2511e57678798b9966796004c5cca2288257b9857328912796f3cc5cca23c999bb9317328904796f977262e0511e5b67877828912796ee4c5cca23c949801dca339944795ee4c5ccd5511e5bb93174b9944796ee6ce62e6661e5bb99c98b9944796
  | 5, 2, 10 => 0x77262e63c8f97b93898b9944796f5771cca2449e5bb93173324f26e6ee5a262e6511e5bb98698b9944796ee61662e6511e5b678798bcda2796ee61e58e6511e5bb9dcaeb994479600771cc893c8f97b93173288f2676d9e1e62f0511e5bb95d7338144796ee4ee62e6511e5b799198b9944796
  | 5, 2, 11 => 0xeef7262e6511e5bbddc98b9944796ee4c62ae6511e5b0ee665aed44796ee4c5cca23c979bb93173288f2036ee5e5cca2449e5bb9287328912796f577262e6511e5b67879eb9944796ee399a2a2449e5bb93173288f2706ee4c5cca23c86db6787732ed44796ee455cca2449e5bb9317328940796
  | 5, 2, 12 => 0xd9e1e62fa511e5bb95d7328904796ee58662e6511e5801dc732ed44795ee575ccd5511e5b7b9498b9944796ee4c5cca9511e5a62e668b3544796ee5d262e6511e5bb93173288f2796f977262a2411e5bb931732ed44796d9e1e0ee6511e5bb97998b9944796ee4c650e6511e5bb9317334544796
  | 5, 2, 13 => 0xee4c5cce6511e5b6787732250a79600772bae63c8f97b95498b9944796d9e1eed31511e5bb968aeb9944796007720ee6511e57b93173288f2306ee616bae6511e5b67875dab144796007714479188897cb8798b9944796d9e1e92e6511e5bb93187b9944796ee4c60ee6511e5bb93173288fa796
  | 5, 2, 14 => 0x77292e6511e57b9317329144796ee399a8a2449e5bb95d7334544796ee5ddcce0511e5bb9317328938796ee4c654e6511e5b678781b9984a26ee4c5cca23c8a1bb95d8ab9944796f9772f331511e5bb94998b9944796f5772bae6511e5b6787a33cd44796ee4c5a2ac511e5bb8e65127112796
  | 5, 2, 15 => 0xee4c62b03511e5b679298b9944796d9e1e62a2421e5bdddc98b9944796d9e1e92e65b9e5bb93173288f26b6ee525cca23c999bb9317335144796ee575cca23c9e5bdbdc7328912796ee61dcca2479e5801dcbb4c544795f7771cca2449e5bb93173288f2266ee5e6bae6511e5bb95d9439944796
  | 5, 3, 0 => 0xee4c5cca23c9b1bb93173288f2176ee576a8e6511e5be5dc98b9944796ee4c5cca23c819be5317338144796ee4c5ccac511e5bb93173288f2396d9e1e62e6641e5bb93173288f2046ee39944893c8f9be5dc7328912796ee4c5cccf3c9d1b67879739944796d9e1dcc893c871bdbdc98b9944796
  | 5, 3, 1 => 0xee4c5ccd8511e5bb9317338944796ee4c65ce6511e5bb93173288f23e6
  | 6, 0, 0 => 0xd9e1dcca2449fcf2fb3c3cc5cca23c94dc01dcc3cc5cca23cb6cf538798b9944797e0e1e62e6511e4dcfb3d6cc644e6511e5f678798c55ccd13cb803678773288f8796d9e2b0f3173288f2f8798b99449a3c9c9f6799c3d75cca23cb80367879039944796d9e1e62e6511e41ae00ee61dcca2449e5b678798c69cca23cb8036787731e47c226
  | 6, 0, 1 => 0xd9ec70f3173288f2fb3c3cc5e6e6511e5f678798b99447f3cbecf0f317ab9944797d9e1e9f3173288f2e00004c5cca23c8257ebb3c3cc5cca23cbecf0f3173288f2377e0ecf0f3173288f2e00ee4c606e6511e5801b3c3dba62a23cb6cf0f5d73288f26e7d9e1e62e6511e420fcdd9e1e62e6511e5f6787aeb9944791f3f730f3173288f2667
  | 6, 0, 2 => 0xd9e1e630973288f2fb3c3cc5cca23c9c9c01b3c3cc5cca228b7230f31732892c797d9e1ec93173288f2fb3c3b9944893c8c5f678798b9944790738036787a0b98f23e6d9e1e62e6511e490fb3c3dcdccde511e5f6787732891279393ecf5d87bcb9944797d9e1e62e66ea88f2fb4d9e1e62e6511e5c01b3c3b99448928b6cf0f317f39944797
  | 6, 0, 3 => 0xd9e1e62e6511e422fb3c3cc5fae6511e5f678798b9944863cbf27678792b9944797ee61ebb3173288f2e00faf7262e6511e5b678798bbdcca23cbecf1b8798b9944797006cf0f3173330f2db3d661e62e6511e5f6787aec0dcca23cbecf0f3173288f2317d9e1e62e6511e440e00d9d75cca23c859b67877328912863cbecf4d8798b9944797
  | 6, 0, 4 => 0xd9e1e62e6511e428fb3c3d769ee6511e5f8fb3c3cc5cca23cb803b93173288f2316ee75b673173288f2e00ee4c5cca23c9c9bb9d6c3cc5cca23cbecf0f317c39944797d9e1e62e663288f2e000077262e65114578fb3c3b9944893cbecf0f3173288f2607d9e1e62e6511e424e00ee61ebae6511e5badd1c3cc5cca23cbecf0f31732890a797
  | 6, 0, 5 => 0xd9e1ebae6511e462e00d9e5e62e6511e5b678798b99447909becf0f3173288f2367d9e1e62e66f288f2fb3c3cc5cca23c9a9c01b3c3d75cca228b6cf0f3173288f21c7d9e1e62e6511e488fc0d9e1e62e6511e5f678798c91cca23cb803678773288a24b6d9e1e62e6511e4e6fb3c3b99bca2449e5f6787732891279353ecf0f8498b9944797
  | 6, 0, 6 => 0x77262e6511e4d4db3cae1e62e6511e5c01b398a88f2310b36cf0ee651259127970061e62e6511e41edb3d2e1e62e6511e5f678798c9dcca23cbecf0f317da88f26e70061dcca2449e41ec00e461e62e6511e5b678798be5cca23cbecf3f9998b9944797d9e1e62e651254f2e00d9e1dcca23c871bb98798b99447928becf0f3173288f20b7
  | 6, 0, 7 => 0xd9e1e62e6511e4d0fb3c3b99a2bb511e5f678798b9944963cbecf3f877328912797d9e1e62e66b288f2fb3c3cc5cca24c9e5fb9b398c89cca23cbecf0f3151208f2667ee6cf513173288f2fb3c3cc5cca23c8cdfb98798c89cca23cbf73518798b9944797d9e1e62e6511e418fb3c3d4a62e6511e5f6787b9cc5cca23cb803b9317337944796
  | 6, 0, 8 => 0xd9e1e82e6511e47cfb3c3cc5cca2479e5f67878ac1dcca23cbf7393b398b9944797d9ebf0f3173288f2fb3c3cc5cca5511e5fb9c9c3cc5cca23cbecf0f3173288f2717d9e7f0f3173288f2fb3c3b9944893c989c01dcc3cc5447918b7730f3173288f2227d9e1e62e6511e44ee00d9e1ea4e6511e5801b3c3dcdcca23cb00366e6511e444166
  | 6, 0, 9 => 0xd9e1e62e651260f2fb3c3cc638e6511e5f678798b99447914b8036787732891e796ea6cf0f3173288f2fdcd9cc5cca23c859f6787b1cc5cca23cbecf0f317328900797d9e1e62e6511e4c8fb3c3cc5cca23c9d1f6787aeb99bca23cbf730f3173288f2167d9e1ebae6511e4d4fb3c3cc5cca23c989c01dcc3b9944791136cf0f1c7328912797
  | 6, 0, 10 => 0xd9e1e62e651224f2e00ee4c5cca23c989801b3c3cc5445118b6cf0ee651224f2417ee7730f3173288f2e00dee1e62e6511e5801dccfcc5cca23cb00262e6511e42c156ee61e62e670288f2fb3c3b994489449e5f678798b9944792ebecf233173288f2627d9e9a62e66f288f2e00ee4c5cca24b1e5b678798b99447904becf0f317333144797
  | 6, 0, 11 => 0xd9e1dcca2449e4befb3c3cc662e6511e5c01b3c3b9944893cb003b93173288f2096d9e1e631073288f2fb3c3d75cca24b1e5c01dc98c71cca23cb76b678798b9944797d9e1f073173288f2fb3c3cc5cca23c905c01b3c3b9944511136cf0f317336d44797d9e1e62e6511e4c6fbdc3cc5cca23c999c01dc98b9944793a36cf0f4b98b9944797
  | 6, 0, 12 => 0x61e62e665a88f2c00ee4c5cca2449e5b6787aeb994479313ecf0f3173288f2007d9e1e62e6511e4befb3c3cc5cca23c901f679dc3cc5cca23cb803678798b9944796d9e1dcca2449e4ccfb3c3d75cca2479e5f67afc3d75cca23cbf47878798b9944797d9e7f0f5d73288f2fb3c3de5ccd4511e5c01b3c3b99447920b6cf0f3173288f23c7
  | 6, 0, 13 => 0xee61f0b3173288f2e000077262e6511e576787b64c5cca23cb8036731731e47c166d9e1e62e6511e430e0000771cca2449e57b98798b9944823cb803679198b9944796d9e1e62e6511e4b0fb3c3d7638e6511e5fb9c3d9cc5cca23cbf2f678798b9944797de6cf0f3173288f2fb3c3cc5cca23c999fb9c3c3cc5cca23cbecf378798b9944797
  | 6, 0, 14 => 0x6cf0ee6511e496deaee61e62e6511e5f6787aecc5cca23cb803678798ab144796006cf0f31732dcf2db3d461e62a2411e5c01dc98b9944793336cf0f83aeb9944797d9e1e631173288f2e00e6e1e62e6511e5b678798b99447925b803b98798b98f23e6d9e1e62e6511e470fb3c3d75cca2449e5fb987b44c5cca23cbecf0f7298c8944797
  | 6, 0, 15 => 0xd9e1ebae6511e4cce00d9e9a62e6511e5b678798bcd4479313f5b678798b9944797d9e1e62e651248f2fb3c3cc5cca23c865c01b398b9944790737730f7998b9944797ee61e632873288f2e00d9e1ebae6511e5badb3c3b9944893cbf730f317334544797006d3673173288f2db3c3cc5ccb73c999fb98798c55cca23cbecf0f3173288f2257
  | 6, 1, 0 => 0xd9e1e6303511e4ccfb3c3cc5ccd13c989f678798b9944790d3ecf0ee651224f251700003b95d73288f2bb3d461ef331511e5f678798b99447936becf3f8798b99a2797d9ea262e66ca88f2e00ee57662e6511e5b67a298b99a8a23cbecf558798b9944797d9e1e62e663a88f2e00d9e1e62e6288f9b6787b5cc5cca23cbecf0f3173288f2547
  | 6, 1, 1 => 0xd9ea30ee651224f2fd1c3cc5cca24d1e5fb98798b99449c3cbecf0f3173288fc797d9e1dcca251224f2fb3c3d76bae6511e5f6787b14c5cca23cbecf298798b9944797006cf0ee6511e434db3c3cc5cca23c945f678798bb5cca23cbecf0f3173288f24f700773ad3173288f2db3c3d35cca23c9b9f938798b99449a3cbecf0f3173288f6797
  | 6, 1, 2 => 0xd9e1ed75d73288f2feeee61e62e6511e5c01b3c3a89127918b77367317328934797d9e1dcca2449e444fb3d461e62e6511e5fb98798b99a8a23cbf730f317328934797ee6ce62e66ca88f2fd6d9e1ebae6511e5f71b3c3cc5cca23cbf730f317336544797006cf0f317f288f2c00d9e1e62f3511e5b6787b74c5cca23cbecf0f317328944797
  | 6, 1, 3 => 0xee61e62e6511e47cfb3c3cc5cca23c859f678773288f25125bfcbb98798b9944797006cf0ee6511e444db3c3d75cca23c869f678798b99447916becf0f31732c144797d9e1e62e65126cf2fb3c461e62e6511e5f67877328912790b3803678798a88f2316d9e1e62e6511e444fb3c3cc636e6511e5f678798b99a4a23cb803b93173288f2516
  | 6, 1, 4 => 0xd9e1e62e655a88f2fdcc3e1e62e6511e5f678798c5544823cb80001dc98a88f23150077262e6511e444db3c3cc5ccdf511e5f6787a33994479313ecf0f3173288f21d7ee6cf0ee651224f2fb3c3cc5e8e6511e5f6787aeb99447928becf0f31732dd44797ee6ce62e6511e4dce00ee6a262e6511e5b678798b994479213f730f3173288f26e7
  | 6, 1, 5 => 0x6cf0f5d511e462db3c3d75cca23c889c01b3c3d05cca23cb6cf2d8798b99447970061e62e6511e412db3c3cc5d0e6511e5f678798b998aa23cbf730f3181b9944797d9ea30f5d73288f2e00ea61e62e6511e5801dc98b9944790b36cf0f4198b994479700003b8e6511e444bdcd9e1e62e6511e5f678798b99c0a23cbecf498798b9944797
  | 6, 1, 6 => 0x6ce62e6511442cdb3c3cc5ccd5511e5f678798ba5cca23cbfd7b98798b9944797d9e730f3173288f2fb3c3cc5ccc2511e5f87b3c3cc5cca23cbecf0ee65122504797d9e1ebae6511e42cfb3d461e6303511e5ff3b3c3cc5cca23cbecf0f4698b9944797d9e1dccc251224f2e00ee77262e6511e5b87b3c3b9944893cb803b9317338144796
  | 6, 1, 7 => 0xd9e1e713173288f2fb3c3cc5ccc93c9b9f6787b44c5cca23cb803b98798b9944516d9e1f0d3173288f2fb3c3e1662e6511e5fb9b3c3d75cca23cb803678773224f23e6d9e1e62e6511e4cefb3c3cee62e6511e5f679ac3cc5cca23cbecf0f687328912797006cf0ee661288f2db3c3e15cca2449e5f678798b9944823cb8036787a339944796
  | 6, 1, 8 => 0x7730b3173288f2db3c3de662e6511e5f678798ca1cca23cbecf0f317334544797d9e1e631573288f2fb3c3cc5cca23c979c01dc98b9944823cb6cf0f797328912797f56cf0f3173288f2fb3c3b99a2a2449e5f678798b994479383ecf0f3173288f21b7d9e1e2ae651224f2e00ee70e62e6511e5bb98798b99447918b803678798b98f23e6
  | 6, 1, 9 => 0xd9e1e630f73288f2e00ee4c62ae6511e5b678798c1dcca23cb803d5dc98b9944796d9e1e62e6511f4f2fc3c3cc5cca23c9c9f6787aeb9944823cbecf0f6198b9944797006cf0ee65da88f2db3c3d75ccd5511e5f678798b9952a23cb80001dc98b98f23e5d9e1e62e6511e4f2f8798b99a2cb511e5c01dcb44c5cca23cb6cf0f31732ed44797
  | 6, 1, 10 => 0xd9e1e62e6511e450fb3c3d762ae6511e5f6787a4cc5cca23cbecf0f3168ab144797d9e1e62e673288f2e0098b9944790b03d801b3c3d75cc791f36cf0f3192b9944797ee61e62e6511e4d4fb3c3da2bae6511e5c01b3c3c1dcca23cb6cf0f85aeb994479700772f33173288f2c00ee4c650e6511e5801b3c3a88f231113003b9317334544796
  | 6, 1, 11 => 0x77262e651270f2db3c3b9944893c8f9f0f3173288f2160abecf0f318ac0d44797f76cf0f3173288f2fb3c3cc5cca23c9adf6787a4b994479333ecf0f317335144797d9e1ebae6511e4f2fb3c3cc5cca23c899f6787bcd75cca23cb8036787a4b9944796d9e1e62e652288f2fb3c3b99a8a2449e5f6787aeb99a2a23cbecf0f317328938797
  | 6, 1, 12 => 0xd9e1e62e6511e474fb3c3e1e62e6511e5f67878739944893cbecf0f3173288f22a7007bbb93173288f2ddcc3cc5cca23c825f678798b99b0a23cb803b9317335144796d9e1e62e6511e47cfb3c3cc5cca23c9b1f678798b9944790bbfcb678798b9944797ee61e62e6511e4e8fdcc3cc5cca23c989f678798b9958a23cbecf0f3173288f2397
  | 6, 1, 13 => 0x3678798c0dcca23cbecf0f4298b9944797d9e1ebae66a288f2e00ee4c5cca23c8f9b678798b99447c3cb803e5dc98b9944796ee61e62e651224f2e00d9e1e62791f0c5b678798c39cca23cbecf0f037328912797
  | 7, 0, 0 => 0x1dc98b9944795006cf0f3173288f266700003678798b99447960000367877328912796006cf0f317328912797006cf0f318e39944797006cf0f3173288f2627006cf3f8798b9944797006cf0f31732892c797000030f3173288f20f6006cf0f317337944797006cf0f3173288f26a7006cf0f3173288f2317006cf0f3173288f272700003678798b994451600003b98798b9944796
  | 7, 0, 1 => 0x6cf0f318ab994479700003678798b98f23e6006cf0f6898b9944797006cf0f8598b9944797006cf0f3173289047970070f678798b994479700773678798b9944797006cf0f3173288f216700003678773288f222600003678798a88f2316006cf0f3173288f2227006cf518798b9944797006cf0f3173288f25170075b678798b9944797000036787aeb9944796006cf0f5d98b9944797
  | 7, 0, 2 => 0x6cf0f3181b9944797006cf0f3173288f23e7006cf0f317335144797006cf0f7998b9944797006cf0f317334544797
  | 8, 0, 0 => 0x3678798b9944796
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
private theorem z2_0 : span (Z 2) 4 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 4 0 = true := z2_0

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
private theorem z4_168 : span (Z 4) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_192 : span (Z 4) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_216 : span (Z 4) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_240 : span (Z 4) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_264 : span (Z 4) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_288 : span (Z 4) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_312 : span (Z 4) 14 312 = true := by decide +kernel

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

private theorem z4_a10 : span (Z 4) 264 0 = true :=
  span_join (f := Z 4) (a := 240) (o := 0) (b := 24) z4_a9 z4_240

private theorem z4_a11 : span (Z 4) 288 0 = true :=
  span_join (f := Z 4) (a := 264) (o := 0) (b := 24) z4_a10 z4_264

private theorem z4_a12 : span (Z 4) 312 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 24) z4_a11 z4_288

private theorem z4_a13 : span (Z 4) 326 0 = true :=
  span_join (f := Z 4) (a := 312) (o := 0) (b := 14) z4_a12 z4_312

private theorem z4 : span (Z 4) 326 0 = true := z4_a13

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
private theorem z5_600 : span (Z 5) 24 600 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_624 : span (Z 5) 24 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_648 : span (Z 5) 24 648 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_672 : span (Z 5) 24 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_696 : span (Z 5) 24 696 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_720 : span (Z 5) 24 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_744 : span (Z 5) 24 744 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_768 : span (Z 5) 20 768 = true := by decide +kernel

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

private theorem z5_a25 : span (Z 5) 624 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 24) z5_a24 z5_600

private theorem z5_a26 : span (Z 5) 648 0 = true :=
  span_join (f := Z 5) (a := 624) (o := 0) (b := 24) z5_a25 z5_624

private theorem z5_a27 : span (Z 5) 672 0 = true :=
  span_join (f := Z 5) (a := 648) (o := 0) (b := 24) z5_a26 z5_648

private theorem z5_a28 : span (Z 5) 696 0 = true :=
  span_join (f := Z 5) (a := 672) (o := 0) (b := 24) z5_a27 z5_672

private theorem z5_a29 : span (Z 5) 720 0 = true :=
  span_join (f := Z 5) (a := 696) (o := 0) (b := 24) z5_a28 z5_696

private theorem z5_a30 : span (Z 5) 744 0 = true :=
  span_join (f := Z 5) (a := 720) (o := 0) (b := 24) z5_a29 z5_720

private theorem z5_a31 : span (Z 5) 768 0 = true :=
  span_join (f := Z 5) (a := 744) (o := 0) (b := 24) z5_a30 z5_744

private theorem z5_a32 : span (Z 5) 788 0 = true :=
  span_join (f := Z 5) (a := 768) (o := 0) (b := 20) z5_a31 z5_768

private theorem z5 : span (Z 5) 788 0 = true := z5_a32

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
private theorem z6_384 : span (Z 6) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_408 : span (Z 6) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : span (Z 6) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_456 : span (Z 6) 18 456 = true := by decide +kernel

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

private theorem z6_a16 : span (Z 6) 408 0 = true :=
  span_join (f := Z 6) (a := 384) (o := 0) (b := 24) z6_a15 z6_384

private theorem z6_a17 : span (Z 6) 432 0 = true :=
  span_join (f := Z 6) (a := 408) (o := 0) (b := 24) z6_a16 z6_408

private theorem z6_a18 : span (Z 6) 456 0 = true :=
  span_join (f := Z 6) (a := 432) (o := 0) (b := 24) z6_a17 z6_432

private theorem z6_a19 : span (Z 6) 474 0 = true :=
  span_join (f := Z 6) (a := 456) (o := 0) (b := 18) z6_a18 z6_456

private theorem z6 : span (Z 6) 474 0 = true := z6_a19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 13 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 37 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 13) z7_0 z7_24

private theorem z7 : span (Z 7) 37 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12601

theorem PEqualNP.Outside.L_meta_12601 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373994 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12601.mainG PEqualNP.Outside.L_meta_12601.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12601.CG, PEqualNP.Outside.L_meta_12601.CG_mono, by
      have : PEqualNP.Outside.L_meta_12601.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12601.CG_eval⟩
