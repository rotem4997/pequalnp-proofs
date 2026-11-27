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
namespace PEqualNP.Outside.L_meta_12489

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3938500736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 14, 15, 7, 7, 7, 7, 7, 7, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 7, 7, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 14, 14, 14, 14, 14, 14, 15, 14, 14, 14, 14, 14, 14, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 14, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 15, 15, 15, 15, 15, 14, 15, 15, 15, 15, 15, 15, 15, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 7, 22, 22, 22, 22, 22, 22, 14, 15, 22, 22, 22, 22, 22, 22, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 22, 22, 22, 22, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 23, 23, 23, 23, 23, 14, 15, 23, 23, 23, 23, 23, 23, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 23, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 25, 25, 25, 25, 25, 14, 15, 25, 25, 25, 25, 25, 25, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 27, 27, 27, 27, 27, 14, 15, 27, 27, 27, 27, 27, 27, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 29, 29, 29, 29, 29, 14, 15, 29, 29, 29, 29, 29, 29, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 30, 30, 30, 30, 30, 14, 15, 30, 30, 30, 30, 30, 30, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 31, 31, 31, 31, 31, 14, 15, 31, 31, 31, 31, 31, 31, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 39, 39, 39, 39, 39, 14, 15, 39, 39, 39, 39, 39, 39, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 39, 39, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 41, 41, 41, 41, 41, 14, 15, 41, 41, 41, 41, 41, 41, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 43, 43, 43, 43, 43, 14, 15, 43, 43, 43, 43, 43, 43, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 45, 45, 45, 45, 45, 14, 15, 45, 45, 45, 45, 45, 45, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 46, 46, 46, 46, 46, 14, 15, 46, 46, 46, 46, 46, 46, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 47, 47, 47, 47, 47, 14, 15, 47, 47, 47, 47, 47, 47, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 7, 49, 49, 49, 49, 49, 49, 14, 15, 49, 49, 49, 49, 49, 49, 22, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 49, 49, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 51, 51, 51, 51, 51, 14, 15, 51, 51, 51, 51, 51, 51, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 53, 53, 53, 53, 53, 14, 15, 53, 53, 53, 53, 53, 53, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 54, 54, 54, 54, 54, 14, 15, 54, 54, 54, 54, 54, 54, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 55, 55, 55, 55, 55, 14, 15, 55, 55, 55, 55, 55, 55, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 57, 57, 57, 57, 57, 14, 15, 57, 57, 57, 57, 57, 57, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 59, 59, 59, 59, 59, 14, 15, 59, 59, 59, 59, 59, 59, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 61, 61, 61, 61, 61, 14, 15, 61, 61, 61, 61, 61, 61, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 62, 62, 62, 62, 62, 14, 15, 62, 62, 62, 62, 62, 62, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f1515157f153f3f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f153f3f7f1515157f153f3f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f153f3f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c0800000000000000000eaeaea80eac0c080eaeaea80eac0c080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eac0c080eaeaea80eac0c080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eac0c0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080eaeaea80eac0c080

def cMZZ : Nat := 0x1515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f0000000000000000000000000000000000000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f0000000000000000000000000000000000000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f0000000000000000000000000000000000000000000000001515157f153f3f7f00000000000000001515157f153f3f7f00000000000000001515157f153f3f7f000000000000000000000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f000000000000000000000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f00000000000000001515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f1515157f153f3f7f

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
  | 3 => 23
  | 4 => 175
  | 5 => 459
  | 6 => 296
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xd0952afbae156d47650f1003
  | 3, 0 => 0xd9f1d625d4b712a0c8d0dd63c0018692ba345d369e990a1b9d7daaa5862881e37f4e5a657e5697947c19ca497646ebac6bc0d4cc5fe2093c5d7b6c745c72b6133f88751d3beb0cee39a1249938b6299438b431d22d9d994325e9ae54
  | 4, 0 => 0x324db18131837c5230739e7f2f24d6f52f07ff112ec64f782d8ffa022d2d4f262c3752862b4fd2eb2b0546b72a989b4b28f451d328767a8727b67114265711e6261d70d5255a33ce204ae06e20180b081eaa4b691e96a90c1dfcb0ef1db867791d9352e51d1d72191d0ea8e61c4535d71a9e55901a84339d17564ba2174ba28516ccc3e1158459091507193f144dcf05130ec35c129ce1d61277cd4211e19bc711bc837910ae07ad10588a381003a35a0cea79e00cb378610bd084b80bce7cd80b4cba510b03c8c60accaa200a90ccac0a2096be09d4c8da09cd3ec2076f7299069e47c40495aa700295429f025436b9020b43df01fda839014f20290081c108
  | 4, 1 => 0x885826a58695f504857d87b28445a45b8343bfb68297be4182805bef807e2bff7d96b71b7d8c71b37c1564c178da604e770acb16731626d8722fc13b71dffbd471a0e3517179dace710336776cf78a026b2bd08069b8114d684ec70c67b90e5966d8179e65f7994865eb1b11656d1e916565bab863e5fd33624496a2609392a65ea344375b6ad1095b29cf4f5af5cab45972f1d457e1b309554c88535351fdc350d2a8bf4ce7c80b4c3f618a4b520eff4acbf81049a551b0491e1b33489a277f4776465b439611904211d5513e60acd53d048e6a3cc19a9c3ac6babf3abb05c93a4f798639a567383980e8b238b6299437de9e6135035d1c345d565f339a1489
  | 4, 2 => 0xff494e88fd645e42f1f62db6ef55a2a8e9bd447ae958f787e8e2d2d7de624294dbc3b1c8d9f3c786d737ea3bcd2d376ecc8a8018c59c6b08bd4cfbe4bcffd828bc2a982bba83dab7b70e0dd3b4a6bb05b46658c1b37b5dbcaeb2f436adc15af1aa3afe30a862cd6ba62e0e1aa6072185a3ea6065a3d5bf01a340caaea1657e6ba0a9a9849d2099789b6cf7a29aa81c6f9750cf3892a89379924ab0e091c62e578fd7e5708e68c7958db343e48c774ea18c28f3098b880bac8a7af322
  | 5, 0 => 0x129ce1d61277e0cb1277cd421261a85f1246a4d2121db83c11eb79ef1159eebc1144053e110eaef3102a012f0fe9bb4a0fa8af440f669d680f4ffe000ef004830eef07100ed344260e7ef7620e7638530e35b38f0dc413220d342a950cfba25c0c9fa4d00c7f95150c6e6fc10c3224e80be7a0f30b80c9a70b42f4500a9d199d0a8702c009cd3ec20983f4f80930c3af0905f878090318e108af57660763e146074183f807402c56073c82ce06ee273606ea7d6106e68cd506ab07a7064d3fd905fc8bfa05e423440550ea1e054b8b3b0540274f0489baac047494f004708a5a03806a0e02ef285e01f4760600d2f92e00c8042600715e53005adb9700150577
  | 5, 1 => 0x2b2587c52b0cc8e92b0298ce2a4a8d80297828632917fe54290d6d1028efd8bb289a2e0a28515fc526dabbfc26a5d42f268e842a265147ef26309828260822da25dfd04d25c600b825a3205d242c1d1523e91952237987872346029622f51c5f22d007cb21ac18fa20cc55b220180b081fae3ea81eaf94921eac6fd01e9ebc431e96a90c1e8be0071e088fd21e05fedb1d913dc71d3238e51bedeec81b6eddb11b4570751ad02f3a1aa3a4fd19ae96f0199a94cd1999b24e19706abc1920d739189d97d6179961f51761349b16af00bf16322bcf1578f87e156d509c1564b5c915266f1214f0b061146c49261444dd4713e4a20c1387ff8f1383a924131758ce
  | 5, 2 => 0x442fc01a4412ae3e43c7c78e43c530904210fb7141464cf9410ebc9840619f353fd039593fc3505b3fadfac83f2ed04b3eb7b31e3df0f9413d84f69d3d3feee03cd053113c7972753c746fa43b8f51263ad7dd163ad3bd8c3aa79c6a39b8c9e53917a13f38e9a6043889d182381230113754e8d0371d1f9837152137370a8c53365352a33651bf15360410ac35490ee43519266f34ae4008346e150a3460895633988e973370bf57337068fe335b33213236cf8331d342003171e441310ec0e330f9234e30d6d53f30b49aab30270c272f6bef322ef2f86c2ecaa9252e6915c12e262e2b2cfe111f2c2ca93d2c1f2ac42bb8b8e92bb7727f2b907b282b69d5cf
  | 5, 3 => 0x64850b656442fc64641e2bb463bb5d6a63a8070462b8ab896221b92a61c7104d602c950a5f4aee615f22ad285e0032155dcd813c5d7e839f5d36c98e5d1213485d0563645c03d3b95b6ad1095ac1dca25a040b33592776c1591160d258fc2c4958fac0465835bc4057c96b4457a128e7575c12da5747ef64568acf8c5688e5f55615938555ad9afe553dc7fe5150174f50fb4ecc4fbbd2884f9d98d24f7f53c64ed4b2194dbd7e004db660a64db52bfd4c287a334c130e664bc4c6814b768a9a4ae97e614a333d5d499ffb6c490c84ab480586e047f26b9b47d36ea247c50ff947b3494d474fb44546d9a49545e5053e4575d1494509413144cf1e024442836b
  | 5, 4 => 0x8297be4181fb1c7b7fe5a9637fb39da57f689fac7f5c8baf7ef5901d7eec44707ead64847d521ec07cd078077c1564c17c07f0667bc1c9167b1ed91d7a34a6987829926f77fed0ab77b4167e7713b46c770acb1676b80926766b16c97597c42875651920756436a1756274f4753fdead753a13ba751e58bc74e2a67b74950f937484245273d22870731626d872f996ad72b984577236991d722835717203cc6971fcb0227196bb10715ad010712f3a1c70fc152d6e7e846c6df517e46de83c8f6c47a0906bcc9a9c6a9dc8796a1ad6d569ee2e9069cb7ea46994b421693544ef684ec70c6838f41466937640668463fc667b84ea65eb1b1165d30ed8656d1e91
  | 5, 5 => 0xaa142c5da8f70aa6a7f2834ea73c2be6a6072185a5f8672ba5782de4a54ef42ba340caaea2f0e77ba1ed5ab3a0e2a4fda0a9a9849fa83e689f990ea99e765a1a9e03792b9c9f444e9c4f25429b6574ac9b643b059b1014969add3f309a5b4e5e99ddf68e99c9f0dc9843f6c897bb84fa956a155f94dd44c293a289d79386ca7a92eff8ca926104c4924f2e199203cd7f91db8fbe91ce94ff90e3aac290908dff907704fd9056f5f4902fdeab8fd7e5708fcc4d678fc7da858fc3e34d8fb360bf8f6cbb538d3d016a8d16a21e8c7bacbe8b8c514388009a0687833d3c875aff7b864053ae85d1fdc4855b00f2855841378532d07c84e4ac70844c1c9c830631e5
  | 5, 6 => 0xf1eaa7a5eeba7d1decf4f563eb8e67a0eb373fa6eb1fc54fe8e2d2d7e81fdb04e313fb34e2ea4f61e0bccd70e048543ae03252b9deab315bde624294dc9f5c4fdbc3b1c8db2fda02dae02429da75cea5da657b92d958f878d944ab43d8c43b02d8734a07d7a5e4a6d6300531d5ef0377d45c87cfd224babbd117d56fd05f93e6ced86835cec41b00cdf2b9c4cd255463cc258a34c9d89c05c7acfc33c6c8389bc6166269c59c6b08c23b7a83c1e99e90c1986138bfb31846ba7b44f6b925e0fdb7bd7b37b786cec4b610a724b5f474a2b3dc9524b37b5dbcb2dc5d2eb2a3d289b1caa8d9b018e293affab4b3afc89144ae477194ae373322ab220e16aad9981e
  | 5, 7 => 0xfe598049fe08f3defd5cf269fb6392fcf93b0d60f851a5dbf77e46e4f60ef7e3f4a1c27ff42e609df3d8f006
  | 6, 0 => 0x1b4570751a6d72951a5e42d61906bf5a18fdf30718fd108818c8ad5817c8e8501764787b1677ad46162aa8d915674035152f549115266f121520828b14f0b06114d6357614c4223d14a32abb148f2509147f8b79146c49261387ff8f13092af512c1951312ae70b81280b92710a76378102f498c0fa278ef0e4bfea70dde7b870d707da60d2638f10d1462460c9c6dc90c93c92c0bf8e32e0bd1cdfb0ba8deef0b1c2a210a8d0eb20a89177a095137250930c3af090318e1067dbdf60604984c055fea3404bac9df04a334190484c4bf038ab65d0373533e0302670402e3c84802c5ce3302487169022033a8015f8322010f7a9e009731f100565085001d7564
  | 6, 1 => 0x3d7ff6133caed2bd3c5d95653ba385f33b7dffa53b736ee93b6595873a4b15ea39c7620b3703f44735ae978335676ee63566ed1334ae4008348fea95347c84a9340e3c1f33cb5b07337068fe327964ae320dab4f310ec0e330d6d53f30b9a8cf302fc25530270c272ef722ab2ea1c9512e6915c12da1915b2ca54c052c8fdd062b1c17232af3d9622ade16c0296ad7ab2917fe5428fc674f287aabbc286162f02814420827fdc8b6274d53192630982825e742432593f6622586b1ea24c11297244d368023bc3ed322c0606422b1fe992201601321dd75ef21b0be2121ac18fa203d62111e4301cd1e05fedb1d913dc71d25fd701cb28ee01c1e74511b5c8ca3
  | 6, 2 => 0x70d42c1070be2e4a7059a95c6fd1cc426ef394ca6e7a039b6d9b2f006b204d876a9dc879697fb14a693fc0906838f4146807348066bf972b66539bcd63a8070462e50f3162b8ab8961c7104d5f4aee615c7fa6725c14380d5b0d8867592776c1581fbdf357a128e756cbe7375688e5f55617cf6d5585489d54319bb953a8efdd53896f2f52518196516708e3500970b84f21bbfc4e9afd834e8e892b4db52bfd4d63c5964cfacf494b24c8134b18c8b74a0e81b949cd05ac499d9c6249894f2d48c4ba6648b7edf147ea88904707213946eabe61449dd0324484e65d443ae3d7430d3e2141a9179a418d6cc841464cf940a6c8cf40619f353e692b233d84f69d
  | 6, 3 => 0xb1da555fb11886cbb0c944d4afde5a97ae359d26ae206749ab79ced3aaec404fa9b82c94a952b022a67ded11a3de610fa3b50ce3a1167c17a06854859efc6ce39ef1513d972ed8659638972a95956362957d98ed927ca594925357049243596a922668c391ce94ff90e3aac2903e2ca68f933ce58f2741878e4d33b78ce2ec648c7bacbe8bd3e31b8aef35578aaeef728889474a87d64cf287833d3c8764d8f8875aff7b85d1fdc48297be418229156e8206b82081fb1c7b81703bcf80c1c0227e68862c7e459e367bd60409788bf43b77622ee5769bd8bc7628c72975bd96fb75982c9675651920756436a173f86dcd725cf4e772437b11718b93ab70fe933b
  | 6, 4 => 0xffa9e098fd5cf269fb6392fcf1d8e894f02a4d48f027a91cef5a43bbeeba7d1dee975c98edbecad5eced6999ecc90091ec200438eb8e67a0e8e2d2d7e691cec4e313fb34de624294dc8c4475da102289d9e7e150d9214ad3d3d694fad2665d0fd20d238cd05f93e6cec41b00cdf2b9c4cd255463c87b94cec87a6025c63bbec2c4f87185c3d1b8d3c298a2cab8052308b73ea69db720d971b598f1b4b3dcd567
  | 7, 0 => 0xfd5cf269de624294dc8c4475da102289d2665d0faaec404f81fb1c7b7628c7297059a95c66539bcd592776c1525181964e8e892b4b24c81349894f2d48b7edf147ea8890443ae3d73a4b15ea348fea95340e3c1f2ca54c051e4301cd0c93c92c0ba8deef02487169022033a8009731f1
  | 8, 0 => 0x592776c1
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f000f0000ffffffffffff0000ffff0000ffff0000ff000000ff000000555500005555000000ff000000ff00000000ffffffff00000000ffff000000000000cccccccc00000000c0c0c0c000000000aaaaaaaa0000000055555555000000003f3f3f3f00000000333333330000000000ff00ff0000000000000000
  | 0, 1 => 0x505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff0000ffff000000ff000000ff000000f000f000f000f000cc00cc00cc00cc00c000c000c000c000aa00aa00aa00aa0055005500550055003f003f003f003f0033003300330033
  | 0, 2 => 0x33333333ffffffff3333333333333333333333330000000033330000333300002a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a2a000000002222222222222222151515151515151511111111111111110fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f00000f0f00000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a
  | 0, 3 => 0x5555ffff5555ffff55555555ffffffff5555555555555555555555550000000055550000555500005500550055005500444444444444444440404040404040403fff3fff3fff3fff3fff3fff000000003f3f3f3fffffffff3f3f3f3f3f3f3f3f3f3f3f3f000000003f3f00003f3f00003f00ff003f00ff0033ff33ff33ff33ff
  | 0, 4 => 0xa8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a000888888888888888888888888000000008080808080808080808080800000000080800000808000007f7f7f7f7f7f7f7f7f7f7f7f000000007f007f007f007f0077777777777777775f5f5f5f5f5f5f5f55ff55ff55ff55ff
  | 0, 5 => 0xaaaaaaaa80800000aaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa00aaaaaa00aaaaaa0000000000aaaa8080aaaa8080aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa80aa80aa80aa80aa00ff00aa00ff00aa00aa00aa00aa00aa00aa0000000000aa000000aa000000
  | 0, 6 => 0xaaffaaffaaffaaffaaffaaff00000000aaff0000aaff0000aaaaffff00000000aaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa8080aaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa80aa80aaaaaaaaaa808080aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaa88888888aaaaaaaa80808080
  | 0, 7 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000c0c0c080c0c0c080c0c0c000c0c0c000c0c08080c0c08080c0c00000c0c00000c000c000c000c000c000c00000000000c0000000c0000000bfbfbfbfbfbfbfbfbfbfbfbf00000000bbbbbbbbbbbbbbbbafafafafafafafafafafafaf00000000
  | 0, 8 => 0xccccc0c0ccccc0c0cccc0000cccc0000cccc000000000000ccc0ccc0ccc0ccc0ccc0ccc0c0c0c0c0cc00cc00cc00cc00cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c8c0c8c0c8c0c8c0c8c0c8c0c0c0c0c0c4c4c4c4c4c4c4c4c0c0ffffc0c0ffffc0c0f0f0c0c0f0f0c0c0c0c0ffffffffc0c0c0c0cccccccc
  | 0, 9 => 0xd5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfcfcfcfcfcccccccccececececececececdcdcdcdcdcdcdcdccffccffccffccffcccfcccfcccfcccfcccccccccfcfcfcfcccccccccccccccccccccccccccc0000ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc88cccccc88cccccc00cccccc00
  | 0, 10 => 0xeaeaeaaaeaeaeaaaeaeac0c0c0c0c0c0eaeaaaaaeaeaaaaaeaeaaaaac0c00000eaeaaaaaaaaaaaaaeaea0000eaea0000eac0eac0eac0eac0eac0eac0c0c0c0c0eac0c0c0eac0c0c0eaaaeaaaeaaaeaaaeaaaeaaa00000000eaaaaaaaeaaaaaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0c0e0c0c0c0c0c0e0c0c0c0e0c0c0c0
  | 0, 11 => 0xf0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeee0000eeee0000eecceecccccccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ececececececececeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeaeaaaaaaaaaeaeaeaea00000000eaeaeac0c0c0c0c0
  | 0, 12 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f000f000f000f000
  | 0, 13 => 0xfafafafac0c0c0c0fafafafaaaaaaaaafafafafa00000000fafaf0f0f0f0f0f0fafaaaaafafaaaaafafaaaaa00000000fafa0000fafa0000faf0faf0faf0faf0faf0f0f0faf0f0f0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f0f0f3f3f0f0f0f0fffff0f0fffff0f0f0f0ffffffff
  | 0, 14 => 0xff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0
  | 0, 15 => 0xff0fff0fff0fff0fff05ff05ff05ff05ff00ffffff00ffffff00ff00ff00ff00ff00ff00ff00f000ff00ff00ff00c000ff00ff00ff000000ff00ff00fa00fa00ff00ff00f000f000ff00ff00ea00ea00ff00ff00c000c000ff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00cc00ff00cc00ff00c000ff00c000
  | 1, 0 => 0xffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaff0000000000ffaaaaaaffaaaaaaffaaaaaaff000000ffaaaaaa00000000ffa0ffa0ffa0ffa0ff80ff80ff80ff80ff80ff80ff00ff00ff80ff00ff80ff00ff55ff55ff55ff55ff33ff33ff33ff33
  | 1, 1 => 0xffeeffeeffeeffeeffeeffee00000000ffee0000ffee0000ffeaffeaffeaffeaffeaffeac0c0c0c0ffeaffea00000000ffea0000ffea0000ffccffccffccffccffccffccff00ff00ffccff00ffccff00ffccccccffccccccffc0ffc0ffc0ffc0ffc0ffc000000000ffc0ff80ffc0ff80ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0
  | 1, 2 => 0xffff3f3fffff3f3fffff3f3f00000000ffff1515ffff1515ffff0505ffff0505ffff0000ffffffffffff0000ffff0000ffff0000f0f00000ffff0000eeee0000ffff0000c0c00000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfff0fff0fff0fff0fff0fff000000000fff0ff00ff00ff00fff0f0f0fff0f0f0
  | 1, 3 => 0xffffc0c0c0c0c0c0ffffc000ffffc000ffffc000ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaac0c08080ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffaa0000000000ffffa0a0ffffa0a0ffff8080ffff8080ffff8080ffff0000ffff5555ffff5555ffff5500ffff5500
  | 1, 4 => 0xffffff00ffc0c000ffffff00ff00ff00ffffff00ff000000ffffff00c0c0c000ffffff0000000000fffffafafffffafafffffafa00000000fffff0f0fffff0f0fffff0f0f0f0f0f0fffff000fffff000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcc00ffff0000ffffc0c0ffffc0c0ffffc0c0ffff0000
  | 1, 5 => 0xffffffff00550055ffffffff00005555ffffffff000000ffffffffff00000000fffffff000000000ffffffccffffffccffffffcc00000000ffffffc0ffffffc0ffffffc0c0c0c0c0ffffffc000000000ffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffffc000ffffff00ffff0000ffffff00ffc0ff00
  | 1, 6 => 0xffffffffaa000000ffffffffa0a0a0a0ffffffff88888888ffffffff80808080ffffffff80800000ffffffff55555555ffffffff55005500ffffffff44444444ffffffff40404040ffffffff3f3f3f3fffffffff33333333ffffffff15151515ffffffff0f0f0f0fffffffff05050505ffffffff00ff00ffffffffff00c000c0
  | 1, 7 => 0xfffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeaeaeaeaffffffffd5d5d5d5ffffffffccccccccffffffffcc000000ffffffffc0c0c0c0ffffffffc0c0c000ffffffffc0c08080ffffffffc0c00000ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaa00aa00
  | 1, 8 => 0xffffffffffffffffffffffffffffff00ffffffffffffccccffffffffffff0000fffffffffff0fff0ffffffffffc0ffc0ffffffffffc0c0c0ffffffffffc00000ffffffffffaaffaaffffffffff00ff00ffffffffff00c000ffffffffff000000fffffffffcfcfcfcfffffffffafafafa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1533f990e9e7f351d48fe653
  | 3, 0, 0 => 0xae54d4e6a4c5540fe6a4a8c38fe6a4953f1606a4c4548fe6a49b438fe6a47e2a8fe604953f0fe644b7d4cfe6a493be8fe6a4953f166544a9d34fe6a4c154cfe6a4a63b8fe6a4a99fcd4624c354cfe6a4
  | 3, 0, 1 => 0xc3d4cfe6a4bbccdf8b44a8d38fe6a4a9c1cfe6a493bf0fe68499bf1666a495439506a4
  | 4, 0, 0 => 0xae4a8fe6a21ad72a12a3f9a96b93e3f9a8a4b2a7e1fcbc565953f14c7f2f2d723afc3f9a96b9517e1fcd4b77953f15a7f5ae509f87f352ca9f885351796b92a851fcd4b75953f0fe6a5ae3f0fe6a0c2d7254a6519fd6d72a7e1fcd4b5c95411687f5
  | 4, 0, 1 => 0x953f1be7f352ddea12a3f9a96b9533f9a8a0b77a8bf0fe6a5ae4a9f8a7352d7255043f9a96d92a7e1fcd4b57953f0fe6a5ae4aa22ad3fad3a76cf4b9a9654fc3f9a86cb5c953e8fe6a5b04a9f87f352e2254f53f9a96b32a7e1fcd4b2a7e2994a7f5
  | 4, 0, 2 => 0x95419f87f352ca9f87f350a55f8b93f9a8bcb5c7e2a8fe6a59528cfe6a2f2ca9f8bb3f9a96551a7e1fcd4b5c99c10fe6a5b64cdf87f352dde55043f9a9705534b9fcd4b5c953f0fe5c5ab4a9f87f352dde54fa3f9a9654fc3f980b0b3e7e1fcd45e5
  | 4, 0, 3 => 0xb3ca9f87f352cea54fc3f9a96bf2a7e1fcd4b5c953d8fe6a5a4ca9f87f352dde54fc549a96e72a7e298feb53a5bb8fe6a5ae3f0fe6d352cee14cf4b9a9654fc3f978a8b777e2a8fe6a5ae4a9f8a8352de254fc3f9a96b92a7e280d4b4c953f0fe6a5
  | 4, 0, 4 => 0xa9bb8fe6a2f2d469ccf4b9a96b8fc751fcd4b2a7e1fce06a5ae4aa067f352d7254fc3f9756a70767a5cd4b739f3f0fe6a5993f0fe6a2f2dde54f63f9a96b9197e1fcd4a00c154cfe6a4ae2e56c7f352e2b09533f9a96b92a7e284d4b2a7e1fce66a5
  | 4, 0, 5 => 0x95451f8b3352ca9f8b13f9a96d32a7e1fcd4b5c951fcd4315ae4a9f8ab3faca9f87f351116ef2a7e1fccab2a7e2d0fe6059aca9f87f352caa0efc3f9a96e52a7e1fcd4b5c953f0fe665ae4a9f87f32acf1f87f2f1616b92a7e2bcfeb5c953f8fe6a5
  | 4, 0, 6 => 0xae4a9f8a43faca9f87f3517d6b9287e1fcd4b3b7e1fcd45757e375b27f352e0e54fc3f9a96972a7e1fcd4b5c953f0fe2b5c3ca9f87f352d8a54fc3f9a96b92a7e298feb2a7e1fcd4605974a9f87f352da254fc3f9a96b8fc569fcb0b8a93bf0fe6a5
  | 4, 0, 7 => 0x953f1587f352dddf8b93f9a96b92a8a298feb2a7e294fe6a5c1572a67f352ca9f87f351796b953881fcd4b2a7e1fcdc6a5bbcf9f87f352caa1cf43f9a96b8fc5c9fcd4b5c95448fe6a595431f87f352d727cfc3f9a9654fc3f9a838b4ea5ca8fe6a5
  | 4, 0, 8 => 0x953f15c6a2f2ca9f8b33f9a95f8b1551fcd4b367e1fcd45e5c2545f87f352d727afc3f9a96b93e8a1fcd4b5c96bf0fe6a5ae54de07f352ca9f87f350cd6f52a7e1fcd4b337e1fcd45e5953f1d67f352d3a547f35179654fc6d1fcd4b82a9bb8fe6a5
  | 4, 0, 9 => 0xae4aa047f352d7154a33f9a9654fc3f9a8c4b54953f0fe6a5a8c95f87f352d4e9acf4b9a97055367a5cd4b5c983f0fe6a5bbd4ddc7f352d7254fc3d9a96a6cf4b9a8c4b2a8dbf0fe6a5b9ca9f87f352d7254fb3f9a9654fc599a890b5ca9bb8fe6a5
  | 4, 0, 10 => 0x59254fc3f9a9654fc3f9a8b4b77953f1026a5953f0fe5e02adda54fc3f9a96df2a7e1fcd4b77953f0fe6a5ae4a9f87f352daa54fc3f9a96ef2a7e2d090b6fa9b3d2e6a5aeca9f87f352e0aa72a3f9a97052a7e1fcd4b5ca9be4fe6a5
  | 5, 0, 0 => 0x953f0fe6a2f035aef2a7e3a0fe6a6ae4a9f87f350ddab92a7e1fcd40c6c154ddccf4b9a9ab92a7e1fcd43a6ae4a9f87f35109ab8fc5525cfe6a6953f1947f35179a54fc5da5cfe6a6bbca9f8c03f9a9ab92c7e33d2e6a6ae4aa227f3c1a9ab92a7c33d2e6a6ae4a9f8e43f9a9aef2a8c3f0fe6a6
  | 5, 0, 1 => 0xae4a9f8ad3f9e18015ca8bf0fe6a5ae4a9f8cf531fdab92a91bf0fe6a6953f19e7f35181ab92a7e3d0fe6a6ae4aa3efc3f9a9ab92a7e1fcd43c6ae4a9f87f3501daf92a7e33d2e6a6953f1d6cf4b9a9a9d2a67a5cd45e6ae4fa54fc3f9a9ab92a82bf0fe6a6ae4a9f87f350e5a54fc6d33d2e6a6
  | 5, 0, 2 => 0x9dca9f87f35179a54fc67a50d45e6a8d2df8cf4b9a9ab92a8a228fe6a6af4a9f8cf4b9a9ab95a953f0fe6a6ae4aa290f3f9a9ab92a7e33d2e696ae4a9f87f3513dab92a7e1fcd40e6004a9f86a2f0d16b92a7e1fcd4326a5ca9f8cf3f9a9ab92a7e33d366a6ae4a9f8d24b9a9a54fc67a5cd4336
  | 5, 0, 3 => 0x57255043f9a96b92a7e2fcfe6a6005b254fc3f9a96b92a7e334fe6a6ae51254fc3f9a9a54fc3f9a8bc516ae4a9f8883f9a98015c953f07a345953f0fe6a2f08dab92a7e374fe6a6c157254fc3f9a9ab92a7e2e4fe6a6004a9f86a1a0256b92a883f0fe6a6ae4a9f87f35095ab92a7e27cfe6a6
  | 5, 0, 4 => 0xadca9f8cf4b9a9ab92a7e33d0c6a6c14a9f8ee3f9a9ab93e7e33cfe6a69b3f19e9735179ab92a7e1fcd42d6c2545f8cf4b9a9a54fc3f9a8bc476ae4a9f8cf479a9ab92a67ad92e6a6ae4a9f8d34b9a9ab92a7e1fcd42c6b2d7254fc3f9a9ab92a7e2d0fe6a6bbca9f8f43f9a9ab8fc5ca892e6a6
  | 5, 0, 5 => 0x4a9f8bb3f9a96b92a903f0fe6a6bbca9f8b43f9a9ab9537733d2e6a69c4a9f8cf4b9a9a54fc67a5cd86a6004a9f87f3500d654fc67acd2e6a6ae4a9f87f3b9a9aa74b953f0fe6a695431f8cf3f9a98012a7e1a868335953f0fe6a2f0d1a54fc5125cd45e6ae4a9f8cf459a9ab92a7e1fcd43f6
  | 5, 0, 6 => 0xae4a9f8f23f9a9aef2a7e1fcee6a6ae4a9f87f351a9ae15c953f0fe6a6953f19e8735179afb5c953f0fe6a6ae4a9f8cf4e1a9ab92a821fcd4486b64a9f87f35121ab92a7e1fcd4526b9ca9f8cf4b9a98015c7e2a8fe6a5ae3f19eb93f9a9ab92a7db3d2e6a6ae4a9f8f03f9a9ab8fc629fcd4586
  | 5, 0, 7 => 0xae51e54fc3f9a9ab92a7e30d2e6a6ae4a9f87f35119ab92a7e1fcd44c6ae4c1f8cf4b9a9ab941953f0fe6a6ae56254fc3f9a9ab95c953f0fe6a6ae54e547f35149ab92a7e234fe6a6953f0fe6a1a0cdab8fc6cb3cfe6a6953f19e972f155ad55c953f0fe6a6953f19e7f35179ab92a7e28cfe6a6
  | 5, 0, 8 => 0xae4be54fc3f9a9ab92a7e238fe6a6ae4a9f87f35185ab92a7e3b8fe6a6a8c95f8cf4b9a98012a7e1fc7a095ae4a9fefc3f9a9aff5c953f0fe6a6ae4a9f87f3507dab92a7e36cfe6a6bbca9f87f35149ab92a7e3392e6a6004a9f87f2f0f56e95c953f0fe6a69e4a9f87f35179ab92a7e2d0fe4a6
  | 5, 0, 9 => 0xc6d7254fc3f9a9a54dd6b33d2e6a6b8ca9f87f35179a54fc67a5cd4626a9ca9f87f35179ab92a7e2f8fe6a6ae545f8f43f9a9a551e7e33d2e6a6bbd0654fc3f9a9a54fc679fcd4336bbd7254fc3f9a9ab92a7e1fcd4136ae4aa1afc3f9a9aa92a7e33d2e6a6ae4a9f8a93f9a9b155c953f0fe6a6
  | 5, 0, 10 => 0xae4a9f8ba3f9a9a54fc3f9a8bc3e6ae4a9f8e63f9a9b1577953f0fe6a6ae4aa287f3b9a9ab92a7e350fe6a6bbca9f8ee3f9a9ab92a79b3d2e6a6b0d7254fc3f9a9aff77953f0fe6a6953f1b89735179ab9537cb3d2e6a6ae4a9f897411a9ab92a7e1fcd44d6ae54e54ee3f9a9ab92a7e1fcd4166
  | 5, 0, 11 => 0xae4a9f8ad3f9a9ab92a8e3f0fe6a6ae4a9f8f73f9a9ab92a7e1fcec6a6ae4a9f8cf4e9a9a54fc6eb3d2e6a6ae4a9f8d53f9a9b052a7e33d2e6a6ae4a9f8b23f9a9a54fc58a5cfe6a6ae4a9f8cf4c9a9aef2a7e2f8fe6a6953f18e9735179aef77953f0fe6a6ae4a9f87f35129ab92a7e34cfe6a6
  | 5, 0, 12 => 0xae4a9f87f3a9a9ab92a7e3e4fe6a6b9ca9f8cf3f9a9ab92a873f0fe6a6bbca9f87f35129abb2a7e33d2e6a6004a9f87f350156b953a0bf0fe6a6bcca9f87f35179b05539533d2e6a6ae54ddccf3f9a9ab92a7e1fcd4676b6d7254fc3f9a9ab92a90b3d2e6a6ae4a9f8d13f9a9a54fc67accfe6a6
  | 5, 0, 13 => 0x953f1c27f35179ab92a7e1fcfc6a6ae3f168aa3f9a9ab8fc3f9e0d4586ae4aa16fc3f9a9b155ca9bf0fe6a6ae4a9f8cf4a9a9ab92a7e2f4fe6a6ae4a9f87f35155a55147e1fcd45e6004a9f87f350f96b92a7e1fcf86a6ae4a9f87f3a1a9ab92a7e1fcd42769e4e254fc3f9a9ab92a843f0fe6a6
  | 5, 0, 14 => 0xb657254fc3f9a9b115c953f0fe6a6004a9f8b13f9a96b92a7e33d006a6ae4a9f8cf5c1a9ab92a7e33d2e6a6ae4a9f87f35079ab92a7e3052e6a6ae50254fc3f9a9aef2a7e1fcf86a600571f86a1a0356b92a7e1fcd42e6ae4c654fc3f9a9b015c953f0fe6a6ae3f1c2d93f9a9ad52a7e33d2e6a6
  | 5, 0, 15 => 0xae4a9f87f35045ab9337e33d2e6a6b7ca9f8cf4b9a9a54fc3f9a8bc4e6bbca9f8cf4b9a9ab94e9533d2e6a6bbca9f87f350b9ab92a7e1fcd40d6ae4a9f87f391a9ab92a7e328fe6a6ae55654fc3f9a9b092a7e1fcd45e6c5d7254fc3f9a9a54fc629fcd45e6954399e9735145a550f67a5cbc526
  | 5, 1, 0 => 0xbbca9f87f35035ab92a7e1fcd4046ae4a9f8cf4a1a9a54fc67a5cbc056ae4a99e973514daef2a7e328fe6a695425f8cf4b9a9b052a7e33cfe6a60052e54fc3f9a94015c953f0d4345ae4a9f8de3f9a9b1177953f0fe6a6ae4a9f87f3500d8015c953f14c7f5ae4a9f8c23f9a98012a7e1fcd4605
  | 5, 1, 1 => 0xae4a9f8cb3f9a9ab92a7e1fcd45b6005727cfc3f9a9654fc3f9a8bc3d6005de54fc350d16b92a953f0fe6a6003f0fe6a2f0356b92a7e3b0fe6a6ae4d9f8cf4b9a9ab92a7e33d226a6953f0fe6a2f179ab92a7e1fcd4476bbca9f87f3500dab92a7e1fcd4286ae4aa22cf4b9a9ab92a7e1fcd4516
  | 5, 1, 2 => 0x953f19e9735169a55257e1fcd45e6ae4a9f8cf56a5d8015c7e1fc7a0d5004aa18fc3f9a96b92a7e33d086a6953f0fe6a2f125ab92a7e240fe6a6ae4a9f87f350d1ab92a7e2892e6a6003f0fe6a068256b93c953f1687f6ae4a9d2cf4b9a9aef2a7e33d286a6953f17cbb3f9a9a54fc3f9a8bc096
  | 5, 1, 3 => 0x4a9f87f351796b92a7e33cfe6a6bbca9f87f350d1ab92a7e33d0e6a6ae4fe54fc3f9a9ad52a7e33cfe6a6953f1c07f35179ab946953f0fe6a6ae4a9f87f35041ab933953f0fe6a6ae3f19e97350618015c7e2e4fe6a5ae4a9f87f35049a54fc3f9a8bc586ae4a9f87f35165acd5c953f0fe6a6
  | 5, 1, 4 => 0x953f1667f35179ad92a7e33d2e6a6ae4cdf8cf3f9a9aef2a7e33cfe6a6ae53a54cf3f9a9ab92a7e1fcd66a60057254fc3f8f56b93c953f0fe6a6ae4aa26fc3f9a98012a7e1fcd4095953f19e9e35179ab92a879fcd4526ae4a9f8f53f9a98016a953f0fe3d5ae4a9f87f35019ab92a7e1fcd4246
  | 5, 1, 5 => 0x953f0fe6a2f121ab92a7e1fcd4056ae4a9f8e23f9a980177953f0fe3d5bbcf254fc3f9a9ae35c953f0fe6a6ae54e54fc3f9a9a54fc5a2c4fe6a6953f1bacf441a9ab92a7e318fe6a6953f0fe78351798012a7e1fcd4335ae54d9e9735141ab92a7e1fcd4196953f0fe7f35179aef2a7e3d4fe6a6
  | 5, 1, 6 => 0xae4a9f8ef3f9a9ab92a7ebf0fe6a6bbdc654fc3f9a9ab92b953f0fe6a6bbd4e54fc3f9a99f8cf5ca5cd45e6ae3f19eaa4b9a9ab92a7e1fcde6a6c24a9f8f43f9a9a55187e1fcd45e6ae4a9f87f350f9ab92a7e394fe6a6ae4aa44fc3f9a9ab92a7e340fe6a6ae4a9f8833f9a9ab94e953f0fe6a6
  | 5, 1, 7 => 0x4a9f8813f9a96ff79953f0fe6a6a9d2ddccf4b9a9ab92a7e1fcd4216005ce54fc3f9a96b92a7e2c4fe6a6ae4a9f8ed3f9a9ab92a7e33d306a600572a6ee3f9a96b92a7e1fcf26a6ae4a9f87f35141a55067e33d2e6a6004a9f8b33f9a97035c953f0fe6a6953f1d07f35179ab92a7e1fcd4386
  | 5, 1, 8 => 0x953f1687f35179ab92a7e33d2e5d6b64a9f8cf3f9a9ab92a7e1fcd402695495f8f43f9a980182a9b3d2e6a5ae52e54fc3f9a9ab8cf5cad92e6a6ae4a9f87f35029b195c953f0fe6a6ae4a9f87f35181b1584a9b3d2e6a6ae4a9f8c94b9a9ab92a923f0fe6a6c2d7254fc3f9a9a54fc6ea5cfe6a6
  | 5, 1, 9 => 0xae4a9f8cc3f9a9ab92a7e1fcd43d600571f87f350356b92a7e1fcd45e6b54a9f87f350f5a54fc3f9a8d45e69541df8cf4b9a98015c3f9a8340d5ae4a9f87f3511580182953f0fe6a5a9bb99e9735179b1584953f0fe6a6ae4aa18fc3f9a9ab92a7e1fcfa6a6bbca9f87f35181a54fc67a5ce06a6
  | 5, 1, 10 => 0x5aa54fc3f9a96b92a7e35d2e6a6bbca9f87f35025ab92a7e1fcf46a6ae4a9f87f350cdaef2a7e330fe6a6bbca9f87f350f5ab92a7e1fcd4016005ddf87f350356ef2a7e1fcd45e6953f19eb14b9a9ad32a7e33d2e6a6953f1dc7f35179ab92a7e1fcd4356ae4a9f87f35051ab92a7e1fcd4096
  | 5, 1, 11 => 0x953f0fe7c35179ab92a7e1fcd4486953f19e9735071ab92a7e1fcfe6a6ae4a9f8b33f9a9ab92a7e1fcd42a6005de54fc3f9a96b92a933f0fe6a6a5ca9f8cf4b9a9ae72a7e1fcee6a6b14a9f8cf4b9a9ab92a7e1fcd4006953f19e9735181ad12a7e33d2e6a60057254fc3f9a96b92a7e2d0fe486
  | 5, 1, 12 => 0x2f777953f0fe6a6c1572a6cf4b9a9a54fc67a5cd45e6ae4a9f8e83f9a9aef2a7e1fcd448695439e8cf4b9a9ab92a7e1fcd41d6bbca9f87f3f9a9ab92a7e204fe6a6ae4a9f87f35021af75c953f0fe6a6
  | 6, 0, 0 => 0xae4a9f8cf3f9a81af5c953f1f8cf4b9a9eb92a7e33d6e97353d7254fc67a5d2c6a7ae52a54fc67a5cd4f5c9545df8cf4b9a9eb92a7e33d7897353d7254fc67b28fe6a7ae4a9f8cf4b9acd4e00ae4a9f8cf4b8f5ab93c953f19e97353d7254cf4ba28d45279543e18fc67a5cd4e00953f19e9735025ab92a7e33d2e6a113d72550f67a5cd4527
  | 6, 0, 1 => 0xae50654fc4b9fcd4f5c953f19e9735015eb92a7e3899e97353caa1efc67a5cd45e7b8d7254fc67a5cd4f5c953f19e9735101c015c953f19e6a1a3572a72a7e33d2e6a7ae4a9f8cf6325cd4f5c953f19e9735065e54fc67a5cfe6a2f3d728b2a7e25cfe6a70057255237e1fcd4c00ae4a9f8f43f9a9add5c953f19e97353d7254fc4b9fcd4527
  | 6, 0, 2 => 0xae50e54fc67a5cd4f2a7e385bacf4b9a9f092a7e3d19e97353caa30fc67a5cd45e7ae4a9f8ee4b9fcd4e00ae4a9f8d34b9a98015c953f1687f35357254fc67a5cd43e7bfd7254fc4b9fcd4f5c953f19e973503deb92a7e3959e97353d7254fc679fcd4237ae4aa44fc67a5cd4f5c953f1a0cf4b9a9eb94e953f19e97353ca9f8cf4ba28d45e7
  | 6, 0, 3 => 0x57254fc3f9dcd4d81ae4a9f8cf4b9a9e54fc7433d2e6a2f3d7254fc5f25cfe6a7ae4a9f8cf3f9a868f5c953f19ea24b9a9eb92a7e3bd9e97353ddeb92a7e25cfe6a7ae4a9fafc67a5cd4f5c953f19e973502deb92b953f19e97353e2ab92a7e25cfe6a7ae4a9f897471fcd4e00ae4a9f8cf479a9ab92a7e33d2e6f353802b92a67ad92e6a6
  | 6, 0, 4 => 0xae4aa28fc67a5cd4f7fbcca9f8cf4b9a9eb937953f19e97353e26b92a7e33d2e6a7ae4a9f8cf4b9a842f5c953f12e7f35129eb92a70b599e97353802b92a7e1fcd4526ae4a9f8ed67a5cd4f79ae4a9f8cf4b9a9c015ca9bb99e97353002712a7e33d2e6a6ae4a9f8cf4b9a860f5c953f19e9735141eb92a7e33d2e71353d7254fc67a48fe6a7
  | 6, 0, 5 => 0x57254fc679fc7ad5c9e4a9f8cf3f9a9f195c953f19e9735380254fc679fcd409600572832a7e1fcd4d5c95491f8cf4b9a9eb92a7e33d2e6a31bd7254fc67a5cd4567ae4a9f8f167a5cd4f2a7e3d19e9735179eb92a7e33d889735380254fc679fcd45e6c2d7254fc67a5cd4f5c953f19ecf3f9a9eb92a94bf19e97353d7254fc67b212e6a7
  | 6, 0, 6 => 0xae4a9f8cf62a5cd4e00ae3f12e6a1183580177ae4a9f87f353572912a7e25cfe6a7ae4a9f8973f9f0d4e00c557254fc3f9a98015c953f11c7f35357254fc67a5cd4027bf57254fc67a5cd4e00ae4a9f8ee3f9a9ab92a80bf19e97353caa4afc7a33d2e6a7005feb92a7e1fcd4d5ca5ca9f8cf4b9a9eb92a7e3859e97353d7254fc67a5cd40a7
  | 6, 0, 7 => 0xae4a9f8cf4ba5cd4f8ac24a9f8cf4b9a9eb92a863f19e97353d7255167e33d2e6a7c2572a72a67a5cd4f5c953f19e97350edeb92a7e33d2e89353d7254fc67a5cd44e7ae4a9f8cf4b9a8aef5c953f19eb54b9a9eb92a7e33d2e93353dc6b92a7e33cfe6a7ae4a9f8cf4ba30d4e00ae4a9f8be3f9a9b095c953f19e97353d72a72a7e33cfe6a7
  | 6, 0, 8 => 0xae4a9f8cf4b9a840e00ae3f19e9735035ab92a7e33d2e6a2f3d7254fc67a5cd4417b54a9f8cf4b9a87af2a7e33d2e6a35179eb92a7e33d2e6a17b802b92a7e25cd4236ae4a9f8d867a5cd4f5c953f19e973512dc015c67a5cd41a06b00254fc6eb3d2e6a6953f19e9735178a4e00c14a9f8cf4b9a9ab92a8abf19e97353802b92a7e1fcd44a6
  | 6, 0, 9 => 0xae4a9f8cf4b9a802f5c953f19e9735161eb92a7e25cfe6a11be2a54fc67a5cd45e7953f1dccf4b9a8bcf5c953f19e9735055eb92a92bf19e97353802b92a7e1fcf86a6bfca9f8cf4b9a8bcf5c953f19e9735125eb92a7e33d2e6a04bd7254fc67a5cd4177ae4aa00fc67a5cd4f5c953f1c6cf4b9a9eb92a7e33d9897353d7254fc67a5cd43d7
  | 6, 0, 10 => 0xae4aa4cfc67a5cd4e00ae53a54cf4b9a98015c953f0fe6a06b002b92a7e328fe6a6953f19e973517894f5c953f19e9735099eb92a7e33d2e6a003802b92a7e33d2e6a6ae53a552567a5cd4e00ae4a9f87f350b9ab939953f19e97353802d52a7e33d2e6a6953f19e97351789af5c953f1c0cf4b9a9eb92a8c3f18497353ca9f8cf5f25cd45e7
  | 6, 0, 11 => 0xbbca9f8cf4b9fcd4f5c953f19e7f35179eb92a8c3f19e97353d7254fc67a78d4237ae4a9f8cf4b9a810f2a7e33d7a9735179eb92a7e39d9e97353de6b92a7e3312e6a70057254fc67a50d4d5c953f19e9735121eb92a7e33d2e6a0db800015c953f0d434595439f8cf4b9a8bcf5c953f19e973c1a9eb92a7e33d2e7f353802ef2a7e33d2e6a6
  | 6, 0, 12 => 0x57254fc4b9a842d2a7e33d949735179eb92a7e3859e88353d7254fc67a692e6a7ae4aa4afc679fcd4f2a7e33d2e6a2f0b9eb92a7e3a19e97353d72692a7e33d2e6a7b1d7254fc67a5cd4e00ae4a9f87f350d18015c953f1449735357254fc679fcd4097ae4a9f8cf3f9a87af5c953f19e9735075c015c7e33cfe6a06b572a6fc67a5cd4587
  | 6, 0, 13 => 0x5de54fc679fcd4d5c953f1bacf4b9a9f055c953f19e97353d7254fc67ae52e6a7ae56a54fc67a5cd4f79ae4a9f8973f9a9c0000ae4a9f87f1ead7254fc67a5cd44f700572792a7e1fcd4c00004a9f87f3502540000953f0fe6a2f2d7254fc67a5cd43c7ae4a9f8cf4b9a80ee00ae4a9f8cf3f9a9ab92a7e33d2e6a1cbca9f8cf4b9a8bc0d7
  | 6, 0, 14 => 0xb857254fc67a5cd4e00ae4a9f8cf1e8b9ab92a7e3852e7f353d4e972a7e33d2e6a7004a9f8cf350b812d5c953f19e8a3f9a9eb92a7e33cfe6a24380254fc679a8bc2e6c14a9f8ee67a5cd4e00b8d7254fc3f9a98015ca9ca9f87f35357254fc67a5cd42d7ae4a9f8cf3f9e0d4f5c953f19e7f3f9a9eb92a7e33d6897353ca9f8cf4b9a8bc517
  | 6, 0, 15 => 0xae54e54ee67a5cd4f8dae4a9f8cf4b9a9ee32a7e33d2e6a2f3d4e54fc67a5cd45e7bbd7254fc67a5cd4f5c953f19e973504deb92a7e33d2e6a30bd7254fc7733d2e6a7004a9f8cf4b8f412c00ae4a9f8d3350b98012a7e33d2e5e1eb57254fc4b9fcd44e7ae57254fc67a5cd4f6aae4a9f8cf4b9a9eb92a7e33d2e6a353d7254fc7433cfe6a7
  | 6, 1, 0 => 0xc057254fc67a5cd4e00ae4a9f87f350258015c953f0fe6a1eb000015c7e1fcd40d50057254fc3f9a8bcc00953f19e97350f9ab92a7e33d2e7c353d7255087e33d2e6a7ae4a9f8f967a5cd4f5c95439f8cf4b9a9c012a7e33d2e6a02b57254fc69b3d2e6a7953f19e97351787cf5c953f19eb43f9a9eb92a7e3519e97353d86b92a7e33d2e6a7
  | 6, 1, 1 => 0xae4a9f8cf4b9a8b6f2a7e33d2e6a2f0f5c00fc67a5cd45e06b57254fc7633d2e6a7953f19e9735178bce00ae4a9f87f3f9a980000bbca9f87f352d7254fc67a5cd40470052e54fc67a5cd4c000057254fc3f9a96b92a7e33d2e6a06bd7254fc67b292e6a7ae55654fc67a5cd4e00ae4a9f86a1708dab92a7e33d2e6a0f3d7254fc67a5cd42e7
  | 6, 1, 2 => 0x5aa54fc67a5c7ac00953f19e97351798015c953f1d07f353002b8fc67a5c7a0d6ae4a9f8cf4b9a868e007e33d2e6a06825a54fc67a5cd45e04b802b92a7e1fcd4486
  | 7, 0, 0 => 0x57255257e33d2e6a70057254fc67a5cd40970057254fc67a5cd43d700002b8fc67a5cd40d60057254fc67a5cd45e700002b92a7e25cd42360057254fc67a5cd44e700612b92a7e33d2e6a70057254fc67b152e6a70057254fc70b3d2e6a7005e6b92a7e33d2e6a7005c6b92a7e33d2e6a700572a72a7e33d2e6a700002b92a7e33d2e3d600572792a7e33d2e6a70000254fc67a5cd4096
  | 7, 0, 1 => 0x254fc67a5cd45e600000015c953f0fe6a50057254fc67a5cd40d70057254fc67b292e6a70057254fc67a5cd42e70057254fc7733d2e6a700002b92a7e33cfe6a60057254fc7433d2e6a70057255187e33d2e6a70057254fc67a5cfe6a700002b92a7e33d2e6a60057254fc67a5cd4587
  | 8, 0, 0 => 0x2b92a7e33d2e6a6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]

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
private theorem z3_0 : span (Z 3) 23 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 23 0 = true := z3_0

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
private theorem z4_168 : span (Z 4) 7 168 = true := by decide +kernel

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

private theorem z4_a7 : span (Z 4) 175 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 7) z4_a6 z4_168

private theorem z4 : span (Z 4) 175 0 = true := z4_a7

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
private theorem z5_456 : span (Z 5) 3 456 = true := by decide +kernel

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

private theorem z5_a19 : span (Z 5) 459 0 = true :=
  span_join (f := Z 5) (a := 456) (o := 0) (b := 3) z5_a18 z5_456

private theorem z5 : span (Z 5) 459 0 = true := z5_a19

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
private theorem z6_288 : span (Z 6) 8 288 = true := by decide +kernel

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

private theorem z6_a12 : span (Z 6) 296 0 = true :=
  span_join (f := Z 6) (a := 288) (o := 0) (b := 8) z6_a11 z6_288

private theorem z6 : span (Z 6) 296 0 = true := z6_a12

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

def CG : Circuit := ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12489

theorem PEqualNP.Outside.L_meta_12489 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3938500736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264000 * 2 ^ 32 + 3938500736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12489.mainG PEqualNP.Outside.L_meta_12489.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12489.CG, PEqualNP.Outside.L_meta_12489.CG_mono, by
      have : PEqualNP.Outside.L_meta_12489.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12489.CG_eval⟩
