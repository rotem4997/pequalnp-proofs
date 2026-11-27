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
namespace PEqualNP.Outside.L_meta_12581

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008225440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 5, 5, 5, 5, 7, 5, 9, 5, 11, 5, 13, 5, 15, 5, 5, 5, 19, 5, 21, 22, 23, 5, 25, 26, 27, 5, 29, 30, 31, 5, 5, 5, 5, 5, 37, 38, 39, 5, 41, 42, 43, 5, 45, 46, 47, 5, 49, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 5, 7, 7, 7, 9, 7, 11, 7, 13, 7, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 5, 9, 7, 9, 9, 9, 11, 9, 13, 9, 15, 9, 9, 9, 19, 9, 21, 22, 23, 9, 25, 26, 27, 9, 29, 30, 31, 9, 9, 9, 9, 9, 37, 38, 39, 9, 41, 42, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 5, 11, 7, 11, 9, 11, 11, 11, 13, 11, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 5, 13, 7, 13, 9, 13, 11, 13, 13, 13, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 15, 15, 15, 15, 15, 5, 15, 7, 15, 9, 15, 11, 15, 13, 15, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 5, 19, 7, 19, 9, 19, 11, 19, 13, 19, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 19, 19, 19, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 5, 21, 7, 21, 9, 21, 11, 21, 13, 21, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 21, 21, 21, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 5, 22, 7, 22, 9, 22, 11, 22, 13, 22, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 22, 22, 22, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 5, 23, 7, 23, 9, 23, 11, 23, 13, 23, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 5, 25, 7, 25, 9, 25, 11, 25, 13, 25, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 26, 26, 5, 26, 7, 26, 9, 26, 11, 26, 13, 26, 15, 26, 26, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 26, 26, 26, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 27, 27, 5, 27, 7, 27, 9, 27, 11, 27, 13, 27, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 5, 29, 7, 29, 9, 29, 11, 29, 13, 29, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 5, 30, 7, 30, 9, 30, 11, 30, 13, 30, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 5, 31, 7, 31, 9, 31, 11, 31, 13, 31, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 5, 37, 7, 37, 9, 37, 11, 37, 13, 37, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 37, 37, 37, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 5, 38, 7, 38, 9, 38, 11, 38, 13, 38, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 38, 38, 38, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 5, 39, 7, 39, 9, 39, 11, 39, 13, 39, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 5, 41, 7, 41, 9, 41, 11, 41, 13, 41, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 42, 42, 5, 42, 7, 42, 9, 42, 11, 42, 13, 42, 15, 42, 42, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 42, 42, 42, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 43, 43, 5, 43, 7, 43, 9, 43, 11, 43, 13, 43, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 5, 45, 7, 45, 9, 45, 11, 45, 13, 45, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 5, 46, 7, 46, 9, 46, 11, 46, 13, 46, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 5, 47, 7, 47, 9, 47, 11, 47, 13, 47, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 5, 49, 7, 49, 9, 49, 11, 49, 13, 49, 15, 49, 49, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 5, 51, 7, 51, 9, 51, 11, 51, 13, 51, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 5, 53, 7, 53, 9, 53, 11, 53, 13, 53, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 5, 54, 7, 54, 9, 54, 11, 54, 13, 54, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 5, 55, 7, 55, 9, 55, 11, 55, 13, 55, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 5, 57, 7, 57, 9, 57, 11, 57, 13, 57, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 58, 58, 5, 58, 7, 58, 9, 58, 11, 58, 13, 58, 15, 58, 58, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 58, 58, 58, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 59, 59, 5, 59, 7, 59, 9, 59, 11, 59, 13, 59, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 5, 61, 7, 61, 9, 61, 11, 61, 13, 61, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 5, 62, 7, 62, 9, 62, 11, 62, 13, 62, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f000000000000000000000000000000000000000000000000000000000000000000000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa000000000000000000000000000000000000000000000000000000000000000000000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa0000000000000000000000000000000000000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa00000000000000000eeeaeee0eee8aaa000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0eeeaeee0eee8aaa0

def cMZZ : Nat := 0x1115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f1115111f1117555f1115111f1117555f1115111f1117555f1115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f0000000000000000000000000000000000000000000000001115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f00000000000000001115111f1117555f1115111f1117555f1115111f1117555f1115111f1117555f1115111f1117555f

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
  | 2, 0 => 0xe1265dae
  | 3, 0 => 0xfea63787cd60eb8fadad5d6ba843d762a5603c286f8df05967a9c1496235563d5d7ee7b3573d4c684579ea152731a2ca0ddf2361006d75e2
  | 4, 0 => 0x3b2c94013a9b9e3c397deefe37522203354d96b43513ff4134b24fa433778ed832faa4c232bf1b82325494c13253335f321cd49931de0f5831a8726331881b0f30fa89d12ffdf9a52eaf633c2b8273262a4503292918318e286f2a5e28389abb26c7003523666f5a22d8b16022a4083a222e8b5721b0dcad20b6add02017fc7a1fd328491f86af8d1e2658951d6ffb521c4ee9341a4864fe18b9546017f7b4a3173047e3171c4bdf167674cd13c01c93131aa40010d4c7d80aa4d8be0a530dbb099c3fc5094057ca08f04fc6085d46c707521f92073d88f806c725f706b89dbe066b56e4053f70650515bc5e04fe3fc103c701be0257ea6f0217f8b300e9daef
  | 4, 1 => 0x873ea57387012b6986ba23387e63dbbf7caa45b4788c2654785442257749ea5876be351975d2f664754c65bd74ef0ce2738c7a977314d5477170b566716c0f1370980fbe708a5f826c311a3b69d16b6f6733b3876699f9e76616391f65198409641fa76563944800633e1e53628b8278615f23e9603378f15f55d6515d80dde45c7abfe35bd69b8457ff88d757f20cbe56f3073f565ac64e558a4c5053f1763d5332a0f4531c7b85522d60a5521b34ef51647f094e91d3fc4d9632c64c8000bd4bceeab34a80df6a49abac3649575c9e48b5e9f8483eb18347349a24455fc2db447186b943ffeb8343e49aec435eb08542bc134d418cd68b3fad69a23f6dc98e
  | 4, 2 => 0xd02bc7aecfc79a6ccfb494d8cf104aaccd0413cbca79cf74ca2285a4c9db9579c9cb0e73c989ca76c93467f8c720034ec687574fc45a7cffc0d6eaeac037d410bda7ed67bd6a4207bd226433ba3896d5b9204d31b91d8565b64e72b5b5679e3fb51c4e57b503d1cbb417cf08b1df372db198db62b1665b62b0fbb1a6ade15217aa9afbecaa82c5b9aa4e491aa7e733f2a7d6c44ba4c974aba1afb4d3a0d2d52da0b585f69d05ff569c2c9da69a55f49899ae9e9f996cea8498cb191898ba087e95e6b910950a1ef394fe5e6192febc0292f3a26691fd69e490a5ead49088534b8c1c92948bab59488a0cb5d689be6efa891db3508907f4c388d376bc8740b66d
  | 4, 3 => 0xffff26f7fdbc7a4cfcf24f1dfc6ef9e1fa18e4cff95647b0f67532e7f5a667bcf43a3120f2e4ccb9efa801d0ef85db21ef34b660ef19556aeeb6d231ebdfe084e9a3e7e1e8747fd1e734db5ce65f6c4de534ac59e456a3b5e3039ca5e0c29960ddb28449dbfd0023d6162d8bd59ada95d2fa8776d2eb77d0d0a26e91
  | 5, 0 => 0x1c0555051b8bd59a1b46cd721a78a6eb1a0f337119a5616d199a6fdc1844b97217fa5b8417f930ba17c9e70a169df55e167bb91f1673ca8a1654f36d153a0061152d331914e5333514b4772d13b49e0813354b5313319f4e131aa4001311991d12df984a12b609a7129083731264e4e6123d198011caa9cf1119c6c310ee7fd71032d1910ff56f570f829daf0ef6eb9c0e2e47150de085af0d3bb21b0cf9b1390c95e4c50bc715a40ba9e2020a6509e209d0473c09a19f8409714a270944ccf1094263d40864dadf083c55bc0827cf2f0827656208142e7b073290bc06be8f1705c4eca105275179040ee69a03129b100257ea6f01870a62015dcff700139edb
  | 5, 1 => 0x2f2f5f762ee2c7812ed66e512e580d682e2297cd2db0259f2d30555c2d2ced8f2c73dfc12b7d6ec02b5f93682a865a192a75a1b229fb9e6b299373132964a89229357efc28cf70892881bb46286a79b5282b1f4027bddaa82746a7d227457ca42719896626f54baf264977e02600445a25d1204b258818f02510b0902494535c24554e7e2447034423b394e42378e3fb2368b4fd22ed017b22bccd562266ab98220be26e21b4989e21b0dcad218aafd02167aabf215d216d213db2a8211eecf02115dfbc20c67af220b6add0208f060f205f04d81f4721451f19ee561f0662611ea9d9321e9267fd1e677cda1e590a9b1e32e8311d3ca2f31ce0b4a51c3793e3
  | 5, 2 => 0x49f7250549527d8c493f130b490a4237488bdada481550ff47fb9d0047a16b55478f23bb4717ee1b470f901746c6c95a46c0cba64648e52b4506fcc743e6dc5143b565a3439680404371f37e42050ab240e96c06403444a1402121a7400a50133fe3791c3fd49deb3f43e9703f3deef23f02fee33ec6ee563dc1e5043da8dea03cc6bf533cc559193c502bf43bf998173bf3cccc3bd9e4fc3afc8c233991db3d38a6749238769a663801568636a72fef3676f3e5364ad28135e6e0c735e079b1358addd735449743352f5c313511abdc338f131d330ac21d32e4c92c3253335f31de0f5831bd0c7c312835c030c39ba5306748be2ffdf9a52fd0aac12fc95a3f
  | 5, 3 => 0x61c2e375617e52bc615f23e9612e52ba603378f15fb7164a5ecf9bed5ea71cb25e6a7e1b5df76c255cbfbf8b5c9052b65c6dd55c5c58298d5c481c6c5bff586559e9fd6459da2a86590adc9c58e59465587bede4584f13be584a99c257a9c720579f4505571544315711345956d67048561244f7558361e055682cfa554e8d465535aada550e3dd9542f0ccf532e2826531f2e4d531d994d5260ee325254c8cc522031a75176b0e950cbd9c65061a23b4fa8803d4f38f8c74ed9cb5b4e2f0aa44e0a542b4e0745e14d9613614d44485e4d01b0ec4ced794a4cba7fda4cb7390a4c2ba3864b58474a4b54a0294b21dfec4aff99c84a76dfb34a755e5c4a0a1ed0
  | 5, 4 => 0x7e59132a7e44e4867e1a6bfd7dd3794e7d9c98987b0f1a2e7a6ac4557a361b2f78da0528786464f37848c0c577ca78fd77b3d45077aa0f6f77a38a4776e5f2ae7679fe9c74c52f2674a62a4d73ed51a473e0fc2972ef3448720ac31471ea11ae71da77f3715bbb197157e9ea7148b9a671273d8d710ed00d70b4a7cd70ada76870980fbe7082e9b9704b67556fced37d6f873e856f84b9aa6f2305b36ec25ad86e0887c26d5b05d16d32114d6b9686c56b522f886b44bbc26aacb6f56a6835f06a1a83b569450bec68f0118a68e22922689189cd6804cd9d675e82f3675a127966fd4fc4659542dd653dcd5264fda85562b84ec662b225ff6236ebb361e520b0
  | 5, 5 => 0x99798f8698caabe998ba087e9805046b97f774b097a99c7395e6b91095c6667c95b428ac9544dd44951a8737950a1ef393badfde92f3a26692e60bb292cd00289230465691d3607b91801d4290efa7ac90d7ac788fd807d98f65a79d8f6538118e3ca6528e1394838c73faa58bcf56488b867a688b353bc88ac799f58a25d4c789e6a7b689d72b9589c53ec689aee78e8970224d895ea2f9893a8558891a2e0488ee70c5886d1e8c8864a4608837be6c87c63c9887900c9a86492419856d1bd0843f0e538414573583570110831173368204eb2a81ffe61a81d7b4bd81cead31815dad358148035d80aa448380635ff77fcaadb07f6389467ee636b07ea2ab11
  | 5, 6 => 0xb4ab4b14b47ce699b40cd2d8b3c548d3b39d0e3eb31a1725b2df820ab2505345b24e483db2198252b1f8203db1df372db17b7a26b0fbb1a6afe04e45ae851a34ae4730dcadecd943ad84cecead1c5f45ad01e146acf63ba3ac0afb45abe14dc3ab838932ab7b0359aac05d67aa6c8d8daa60dee4aa332a9ca9d71787a99fa81ca8f691fea886ac1ca826482ba7c964f2a623e6f1a5c279dea52845bba4a7137ba4168ad6a360fda8a1cc016da140807ba0ec2af4a0d71d34a05dec25a047fced9fcac6c49f6f78ad9f48448f9ec6ad199e3c580d9de02daf9cb85de69c62fc279c2c9da69c2a80369c0399ae9af0c37a9aec40019ae1502c9a889e6999ae9e9f
  | 5, 7 => 0xd5c11b28d59ada95d590ffc5d50d94b8d3cfb44dd2362039d001b18ecfe05766cedbfd4dced8d3cccebab73bce964ba0ce50480ece1c824ccd650959cd0d661bccaa7006cbf92f66cbcaacf4caa6e83cca90056aca4b7bb3ca0cb938c93b762ec902c85bc82a22b3c81c7277c7a40109c69cb69ec659cab6c5aac1bdc4d3497dc49415edc3c499ffc2a4ad1fc037d410bff8be76bfaf0114bec5c67cbe6a7b9abe3ef7afbdbb79a4bdbaad6ebda84c14bda7ed67bd5dba4cbd11caf0bcab96febbf82a44bb265af5bad03148b9984a4fb9930312b8f136deb8af7d8bb8af6ca0b7c58be6b78d975db750e351b6e7e946b6848d0cb65e101bb64e72b5b63ad786
  | 5, 8 => 0xfd0c9155fcc1a6d7fcb88f59fc0ec008fb840575fb1353d9f950b846f8feed43f84798ebf83f533cf7bc1fe6f67532e7f58465aff498124bf466ec54f3beb09bf2529551f140b194f10df6bbf04c1b73ef85db21ef3cd449ef34b660eef55e44eeb3fcadedf8ef3eed7a21afed78cc05ecedf521ebdc78d0ea90cef7e9f9a2cae9ef33b9e9d02da4e98f7cd9e8f5ce03e7fa9a5fe734db5ce6762a04e5cad3a7e534ac59e3bede44e2fc49f0e23c10e5e238bf21e1fa02e7e1685ae9e0b9b927e09a07b8e06589b1dfbf52bfdf8558c0de4c362dddb65410dc9a7d43db5a895adb0d9850d9ebf7b4d99a2cb1d8493305d6c17619d6bc3ad7d6219156d5f5eeb4
  | 5, 9 => 0xffc7a9d8ff68d740ff45189b
  | 6, 0 => 0x1b56acf91a36c0191a0f337117c9e70a178ad1701741140e1701fc2f16d84593169df55e1673ca8a1654f36d1600ae0415fc8e9415d10aa9153a0061150f268315031fab14efcd4614a3ddea132b120c128c7a191125160c10ff6a950f1faa570ee2f64b0e2094050df023150dccea800da66f630d95c9710d71e78c0d3bb21b0d29d1500bc715a40b575bcd0b2f21380ac666f50a9aaefd09ab954c09714a27091a8331082728e708142e7b08003b6807baafa2073b1bfe06ef0cca06ec578d062c7876062300a40516e1c8049d59b404884e9d03129b10030d165302ef8145027a00da02591ce30252706101fea08701f2f1de01c53d960131bb160076d483
  | 6, 1 => 0x37176bba36db5769365b408d3627723d35e6e0c734d8b8f7347e4037342c903d3388178a331ac02f32ec9c54329fab4a32364efb317e0aae3174458d312c3fab30c5403c306be09c2fdb45ff2fada2b32ef744252e4e4dd12e06c6af2d532e222d2312bf2ca178a82c9fa7b22c73dfc12bc212ac2b7047a92abc128128bd15b42793c48826a8ba9025d1204b2510b09024e2d6d1249f79152494535c2450b367243c8300238b42602341984f22ed017b228e43a0227547212222186421dd8ead213db2a820e8414a20cd892820b4975020b109a51ff1d55d1f3614031ea9d9321e43825f1e32e8311e2ec9981e2b244d1debddb01c655c771be048241b9ee496
  | 6, 2 => 0x59191d5759170f4858f637d058efe2ec58d08ebd5868efc757a5b1d05780d394577a995156d72b9556d6704856a8ba38569a7b64561991ac557cda755453b9d15452d010544aa25352a566d35260ee325049a29b4fd166364fa40e424f0a6ddd4e7198c34d1678a94bf9631d4bf8ff4e49f0caad49c9334949bd277448a009b54840df1147fb9d0047c481dd478f23bb470f901746c0cba64687713e46460fa7454b7568450c34a944c3dbda4480081b443fe31c439b3e0c43828cf743123a704303f98041da07b3418bb5c4416316b24087e0fd3f8cad593ec6ee563e3bdf813da8dea03d5ce6a13d3f61f23c8114683b50f13e3adc2ce73a8e5cea375165b9
  | 6, 3 => 0x8a9cd51289c53ec68970224d894f1f7187f95bb387900c9a875b6d348674da768668814685b4aac2841457358405f2b683570110830f81b582186d0e818db16080c791f17ffc8caa7e875ea47ddb8ad57d6333407c2666517bd916397b0af6f07afac7f27a7ff97079be8ef978f9bdb478b0ffe578a7f2b17848c0c5777c6f38763bec2775c4fb26739767fa72ef3448720ac31471a146667148b9a6712c82d16e0dcc146e05dd7f6cbf460e6b9686c56b46b0fd6b44bbc26aacb6f56a8c6acb6a22966868abd9b8689189cd688092cc64fe110364cdc5106359289961625a316133b27960d90d2160d6dfe65ec4a3b15d56ff965cb9646e5c8e880e5b17cbe8
  | 6, 4 => 0xc1fa48e5c0743c17be8f62b9bd2755d2b9930312b91065b1b8f136deb750e351b749293fb5897f1ab3ffe851b3da2f61b1df372dafe126b3ae68833dae4730dcacfa3fefaa60dee4a9f30127a9e6dbc1a826482ba73a9332a59c6720a5282656a4d65b53a47f8c3fa3bdb67ba2ea5a3fa2e6b31ea2b3f2e1a2077151a19c31c5a09c552c9f8daff59f2136b09ea1a30c9e52de9b9de0cf819de02daf9d7231e49cc6092a9c990fbc9c62fc279b4778989aec40019a161c7799971da798caabe997b3349c97758c1196d001e7969511d8953af19593e23ee9938bab0c928e9f189123ee32910b69498e3942e48d78f3bc8d1cf0cc8cc16f268bc1b84e8abb9151
  | 6, 5 => 0xff45189bfd548cd3fcc1a6d7fc392670fb1353d9f95e1462f87e3de9f7efff1af75cd9b9f7018ba2f6da5784f3f50f1cf3bc932bf27e52f6f2736321f10ba27bf04c1b73ef8987a5eb4cf2d3ea5f131de9f9a2cae9657370e9123037e881baa1e869bf6de76a1acee5ceb947e3bede44e2fc49f0e2c74ebde259aceae1693e8ae15751bbe08083badfff3181dfc9d161dfbf52bfdcff2ec5dc9a7d43dba66a2adae91405d996fe1fd991f90fd7f00543d67849a5d634be06d5ac7ef2cff677e8cf5c8bf2ce7805a3ca90056aca81473dc8dacc9bc82a22b3c719517ac716cc9fc32899bac2d6ceb7
  | 7, 0 => 0xf3f50f1cf27e52f6e15751bbdba66a2aca81473dc8dacc9bc32899bac2d6ceb7b1df372dae68833da9f301279f8daff59f2136b09ea1a30c9e52de9b953af1958d78f3bc7d63334075c4fb26720ac3146e05dd7f6359289956d72b955453b9d152a566d3418bb5c43b50f13e3a8e5cea34d8b8f724e2d6d1222218641125160c0ee2f64b09714a2708003b68
  | 8, 0 => 0x9714a27
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000f0f00000f0f0000000f0000000f00000000ffffffff00000000ffff000000000000fff0fff000000000ff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f00000000000f000f000000000000ffff0000000000000000
  | 0, 1 => 0xf000f000f000f000f000f00000000000f0000ffff0000000f0000000f0000000c000c000c000c000a000a000a000a000500050005000500030003000300030000ffffffffffff0000ffff0000ffff0000ffff000000000000fff00000fff00000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa0000555500005555
  | 0, 2 => 0xf000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000f000f000f000f000cc00cc00cc00cc0033003300330033000fffff000fffff000fffff00000000000f000fffffffff
  | 0, 3 => 0x33333333333333333333333300000000333300003333000033303330333033303300330033003300222222222222222211111111111111110fff0fff0fff0fff0f0fffff0f0fffff0f0fffff000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f00ff000f00ff000f000f00ff00ff00
  | 0, 4 => 0x55550000555500005550555055505550550055005500550050505050505050504c4c4c4c4c4c4c4c44cc44cc44cc44cc444c444c444c444c44444444cccccccc44444444444444443f3f3f3f3f3f3f3f3f003f003f003f0033ff33ff33ff33ff333f333f333f333f3333ffff3333ffff3333ffff0000000033333333ffffffff
  | 0, 5 => 0x8080808080808080777777777777777777777777000000005f5f5f5f5f5f5f5f5f5f5f5f000000005f5f00005f5f00005f005f005f005f0055ff55ff55ff55ff55ff55ff00000000555f555f555f555f555f555f00000000555f0000555f00005555ffff5555ffff55555555ffffffff55555555555555555555555500000000
  | 0, 6 => 0xaaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aaa0aaa000000000aaa00000aaa00000aa88aa88aa88aa88aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a000a000a000a00088888888888888888888888800000000888800008888000088808880888088808800880088008800
  | 0, 7 => 0xaaaaaaaaaaaaaaa0aaaaaaaaaaaa0000aaaaaaaaaaa8aaa8aaaaaaaaaaa0aaa0aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaaa8aaaaaaa8aaaaaaa0aaaaaaa0aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000
  | 0, 8 => 0xcc88cc88cc88cc88cc00cc00cc00cc00c0c0c0c0c0c0c0c0c0c0c0c000000000c0c00000c0c00000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaf00af00af00af00aaffaaffaaffaaffaaafaaafaaafaaafaaaaffffaaaaffffaaaaffff00000000aaaaaaafaaaaaaafaaaaaaaaffffffffaaaaaaaaaaaaaaaa
  | 0, 9 => 0xcccccccc00000000ccccccc8ccccccc8ccccccc0ccccccc0ccccccc0cccc0000cccccc00cccccc00ccccc0c0ccccc0c0cccc8888cccc8888cccc4444cccc4444cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc8ccc0ccc8ccc0ccc0ccc0ccccccccccc0ccc0ccc0ccc0ccc0ccc000000000ccc00000ccc00000
  | 0, 10 => 0xcccf0000cccf0000cccdcccdcccdcccdccccffffccccffffcccceeeecccceeeecccccccfcccccccfccccccccffffffffccccccccccccffffccccccccccccccccccccccccccccccc0ccccccccccccc0c0cccccccccccc8888cccccccccccc0000ccccccccccc8ccc8ccccccccccc0ccc0cccccccccc00cc00cccccccc88888888
  | 0, 11 => 0xee00ee00ee00ee00ececececececececececccccececcccceccceccceccceccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaaaaaeaeaaaaae0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcf00000000cf00cf00cf00cf00ccffccffccffccffccff0000ccff0000cccfcccfcccfcccfcccfcccfcccccccccccfcccf00000000
  | 0, 12 => 0xeeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000cccc0000eeeceeeceeeceeeceeeceeeccccccccceeeccccceeeccccceeeaeeeaeeeaeeeaeeeaeeeaaaaaaaaaeeeaeeea00000000eeeaaaaaeeeaaaaaeeea0000eeea0000eee0eee0eee0eee0eecceecceecceecceecceecccccccccceecccccceecccccceeaaeeaaaaaaaaaa
  | 0, 13 => 0xf0f00000f0f00000f0a0f0a0f0a0f0a0f000f000f000f000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeceeeceeeeeeeeeecceecceeeeeeeecccccccceeeeeeeecccc0000eeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeee0cccc0000eeeecccceeeecccceeeecccccccccccceeeecccc00000000
  | 0, 14 => 0xf8f8f8f8f8f8f8f8f5f0f5f0f5f0f5f0f3f3f3f3f3f3f3f3f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000f000f0f0f0f0f000000000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0
  | 0, 15 => 0xfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcf0fcf0f0f0f0f0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaafa00fa00fa00fa00
  | 1, 0 => 0xff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00f000ff00f000ff00ee00ff00ee00ff00aa00ff00aa00ff000f00ff000f00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fef0fef0fef0fef0fe00fe00fe00fe00
  | 1, 1 => 0xffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55ff30ff30ff30ff30ff0fff0fff0fff0fff00ffffff00ffffff00fff0ff00fff0ff00ff00fff0fff0ff00ff00ff00ff00ff00ff00ff000000
  | 1, 2 => 0xffe0ffe0ffe0ffe0ffccffccffccffccffccffccff00ff00ffccffccccccccccffccffcc00000000ffccff00ffccff00ffccccccffccccccffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00
  | 1, 3 => 0xfff0fff0ccc0ccc0fff0fff0aaa0aaa0fff0fff000000000fff0ffe0fff0ffe0fff0ffc0fff0ffc0fff0ffa0fff0ffa0fff0ff00fff0ff00fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff0eee0fff0eee0fff0ccc0fff0ccc0fff0aaa0fff0aaa0fff00000fff00000fff0000000000000ffeeffeeffeeffeeffeeffee00000000
  | 1, 4 => 0xfff3fff3fff3fff3fff3fff300000000fff1fff1fff1fff1fff0fffffff0fffffff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0faf0fff0fff0fff0f0f0fff0fff0fff0aaa0fff0fff0fff00000fff0fff0ffe0ffe0fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff0fcf0fcf0fff0fff0f0f0f0f0fff0fff0eee0eee0
  | 1, 5 => 0xfffcfffc00000000fffcfff0fffcfff0fffcccccfffcccccfffc0000fffc0000fffafffafffafffafffafffafff0fff0fffafffaaaaaaaaafffafffa00000000fffafff0fffafff0fffafff0fff0fff0fffafff000000000fffaaaaafffaaaaafffa0000fffa0000fff8fff8fff8fff8fff8fff0fff8fff0fff5fff5fff5fff5
  | 1, 6 => 0xffff0000ffff0000ffff0000fffc0000ffff0000fffa0000ffff0000fff00000ffff0000ffcc0000ffff0000f0f00000ffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff000000000000fffefffefffefffefffefffe00000000fffe0000fffe0000fffcfffcfffcfffcfffcfffcfff0fff0fffcfffccccccccc
  | 1, 7 => 0xffff8880ffff8880ffff8800ffff8800ffff8080ffff8080ffff5555ffff5555ffff5555ffff0000ffff555500000000ffff3333ffff3333ffff3330ffff3330ffff3300ffff3300ffff3030ffff3030ffff1111ffff1111ffff00ffffff00ffffff000fffff000fffff0005ffff0005ffff0000ffffffffffff0000ffff3333
  | 1, 8 => 0xffffccc0ffff0000ffffccc000000000ffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaaa0ffffaaa0ffffaaa0ffff0000ffffaa00ffffaa00ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa000ffffa000ffff8888ffff8888
  | 1, 9 => 0xffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffff0f0fffff0f0fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0f0f0f0f0fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeeee00000000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffccc0ffffccc0
  | 1, 10 => 0xffffffff0000000fffffffff00000000fffffffcfffffffcfffffffc00000000fffffffafffffffafffffffa00000000fffffff0fffffff0fffffff0ffffaaa0fffffff0ffff0000fffffff0fff0fff0fffffff0cccc0000fffffff000000000ffffffccffffffccffffffcc00000000ffffffaaffffffaaffffff00ffffff00
  | 1, 11 => 0xffffffff80808080ffffffff55555555ffffffff55550000ffffffff33333333ffffffff33303330ffffffff33003300ffffffff30303030ffffffff11111111ffffffff0f0f0f0fffffffff00ff00ffffffffff000f000fffffffff000c000cffffffff00050005ffffffff0000ffffffffffff0000aaaaffffffff00003333
  | 1, 12 => 0xffffffffcc00cc00ffffffffcc000000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaaa8aaa8ffffffffaaa0aaa0ffffffffaaa00000ffffffffaa00aa00ffffffffaa000000ffffffffa8a8a8a8ffffffffa0a0a0a0ffffffffa000a000ffffffff88888888ffffffff88880000ffffffff88808880ffffffff88008800
  | 1, 13 => 0xffffffffffaaffaaffffffffff00ff00ffffffffff00aa00ffffffffff000000fffffffffcfcfcfcfffffffffcfc0000fffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffccccccccffffffffcccc8888ffffffffcccc0000ffffffffccc0ccc0ffffffffccc00000
  | 1, 14 => 0xfffffffffffffffffffffffffffffff0fffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffffcfffcfffffffffffc0000fffffffffffafffafffffffffff0fff0fffffffffff0aaa0fffffffffff00000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x529a6803
  | 3, 0, 0 => 0xd75a188804d252938804b7d29ac804e952950764a53353e804a53519a804d752948764d2d2950804e1dbd88804b352938804d3d29ae804f052950764e95bd88804b452948804
  | 4, 0, 0 => 0xd752950802d2ee6df4a5420179586a52a100be4b7d2950805f068294a8402ebad14a6d2017496fa52a0ecb6fa52a100555ece9e94a8402dbe22e86b20175d6fa536500baea52a100335d55be94a8402e92df4a5420175d6fa52e950baeb7d294c805
  | 4, 0, 1 => 0xd733988a8402ebac74a5420175d6fa6aa100bcbb7d2950805d752966a8402ebb2f4a5420178d6fa52a100baeb7cb988805b4529509f402ebedf4a542017a56fa536900baeb7d2900485ee5be94a8402eeedf4a542016df4a52200f0b6fb352948805
  | 4, 0, 2 => 0xb7b5188a8402ebadf4a5220175d6fa531950baeb7d2982805d75a29492402ebaeb4a5420175d7da52a100baebdd2950805e9dbe94a8402ebadf4a5720179d6fa52a100baece52948805d752950802a2ebadf2f5420175d4a672a100bd2b452950805
  | 4, 0, 3 => 0xd75be5ebe402ebadb4a542017a56fa524900baeb7d2962805d75beaca8402dbe94a84015d75da9a529100bc0b7d2950805d75e294a8402ebb154a541d975d6fa536100baec1d2950805d75be9498402dbe94d45420175d6fa52f100bdab7d2950805
  | 4, 0, 4 => 0xd760e94be402d62a74a5420175d6fa527100b6fa52a100215d75c294a8402f534f4a542017b36fa529100baeb7d4550805e25be94a8402eba94af542017a16fa52a100be6b452950805d75be94cb402dbe95305420174fa4a52a100b6fa52c150805
  | 4, 0, 5 => 0xd75be94a5402ebb0b4a542016d1117429100bc5c1d2950805d75be94d1402ebb054a5420179b6fa535d00b6fa52a1005d5d75be9494402dbe94a8400a575d6fa52ad00baeb7d2550805d75299aa8402eba95025420172b6fa52a100baeb7d2950825
  | 4, 0, 6 => 0xe95be94a8402dbe94d44ba0175d6f9e2a100baebb52950805b7d29aed4402eba94c5542017876fa536900b6fa52d950805d752a66a83b2dbe94d0542017a59ca52a100bc9b7d2950805d75a294a8402dbeb14a542016f56fa52a100b6fb252950805
  | 4, 0, 7 => 0xd763294a8402ebb4f4a4e20175d4a6bb3500bb8b7d2950805f0529508038aebb1f4a542017c5a7a52a100baeb7d2952805d75ae94a8402ebad34a542017a5a9a52a100b6fa54f5ae805f0dbe94a8402dbe94a841a0175d4a67aa0e2baeb7d2946805
  | 4, 0, 8 => 0xd75be949d402ebadf4a61a017836fa52a100b66a527d2e805d766a94a8402ebadf4a5caa175da8a52a100bae97b3950805d75be94a83eaebadf4a642a175d4a5425cecbaeb7cd950805e1dbe9492402f52df4a5220178f6fa52a100bd4d75bd88805
  | 4, 0, 9 => 0xf36ba94a83b2ebadf626220175d6faf24900baeb7d1d50805e15be94a8402dbeb14a4aa016df2f6a2a100bc8b7d2986805a53519ca8402dbe94d74fa0175d53a52a100baeb7d293a765d75be94cc402ebadf4a4012975d6f6631100b91b7d2950805
  | 4, 0, 10 => 0xe45be94a8402f2adf4a6620175d4a52200e2b6fa52a100415d75be80a8402f8adf4a5220175d6fa52a0ecbaeb7d2958805b7d3a94a8402eba94a8401c975d81a52a100baeb7d2950805d75be948024aebadf4a541fd75d6f622a100baebfd2950805
  | 4, 0, 11 => 0xeedbe94a8402ebadf455420179b68a52a100baeb7d2994805d761a94cc402ec2df4a542017456fa52a100ba7a52a100785dedbe94a8402e9ecd4a542017cd6fa535d00b11743519a805b7d298ea8402e3adf4a5420175d4a542003abc3b7d2950805
  | 4, 0, 12 => 0xeb5be94a8402ebb0d4a541d975d72a52a100baeb7d29ae805d25be949d402ebb0d4a5420175d6f62200c8baeb752950805d754e9495402ebadf4a6120175d9ba52a100ba4a52a12e805e55be94a8402ebadf4a4f2017676fa52a100baeb7d294e805
  | 4, 0, 13 => 0x5beab4a542017a54a54200e2b11743353e805d75be94a83baed2df4a5420175d6fa524d00baeb7d292a805d65be94a8402f83534a542017636fa52a100baeb7b112e805f05be94a8402ebb4f4a542016d14a9eaa100bd2b7d2948805
  | 5, 0, 0 => 0xd75be94a840181b5d86a53a150806daebadf4a54201b5d6f742a10e806d75be74e854201b5d9f88ba150806d75be94a840101b5d6f9bc4550806d75be94a840189b5d6fa52a116806d75be94a840171b5d6f742fd5080600692df4a5420175d6fa52a100046d75be94c3401a9bcdaea52a100716
  | 5, 0, 1 => 0xd75be94fe54201b5d6fa524900646ee5be711154201b5d6f88bb150806d75becb4a54201b5d6f88ba150766d75bec54a54201b5d6f88ba158806d7445d0a8401c9b5d6fa52a100716d760622e854201b5d6fa53a1ae806f5ebadf4a54201b5d6fa52a100386d75be22e854201b5d6fa52a1002f6
  | 5, 0, 2 => 0xf3ebadf4a54201b5d6fa144550806d7445d0a4401c5b5d6fa52a150806d75be22e85ea01b5d6fa543d5080600772df4a5420175d6f84ba150806d7683154a54201bc16fa53a150806d75be94a84013db5da7a53a150806d75bdd0a8400c1adf11742a100416e95be94a84ba01b5d6fa535150806
  | 5, 0, 3 => 0xd75be94a84004db5d6fa54a950806d75be949749201b5d6f88ba1004b6f16badf4a54201b5d6fa53a12a806d75d2df4a54201b5d6f89ba150806d75be02bf54201b5d6fa547d50806e1dbe22e854201b5d8488ba150806ecf36df4a54201b5d6fa537d50806d75be3ae854201b916f88ba150806
  | 5, 0, 4 => 0xb7d9a94a84fa01bcd6f88ba1ae806006ba94ce5420175d6fa54b9b4806b7d62951154201b5d6f8cba150806d7672953354201b756f88ba150806d75be953d54201bb1aeb7d2950806d75be1ce854201b5d6f88c0550806d75be94a8401a9adf11742a1005b6d75be22f954201b5d6fa52a1001a6
  | 5, 0, 5 => 0xd75beb74a4aa01b5d6fa543550806d767e831154201b5d8db7d2950806d75be94e154201b5d6f88ba17c806db6badf4a54201b918488ba150806d85be22e854201b456f88ba150806006badf2f5420175d68a544550806b7d29509f401e1b7b6f88ba150806d75be4ee854201b5d6fa52a1003e6
  | 5, 0, 6 => 0xd75be952154201b5d6fa52a100236d75be4ce854201b5d4a6d33950806d75bdd0a840115bbb6f88ba150806e6da222e854201b5d6fa52a100446d75be76e854201b5d6fa52a1002c6d75f2df4a54201b5d6f742d550806d75be94ff54201b496fa53a150806d75be831154201b5d6fa52a1001f6
  | 5, 0, 7 => 0xd75be94a840021b7daeb7d2950806ca646df4a54201b5d6f8c3a150806d75bed14a54201adf1181ba150806d75be94be54201b956f88ba150806d75be953354201b5d6fa52a1003a6d761294a8401a9b5d6fa52a100286d762e22e854201b916fa52a1006a6d75be951454201b5d6f97b6950806
  | 5, 0, 8 => 0xd75be94a84002db5d6f88ba184806d75be94ed54201b5d6fa444550806d766e22e854201b5d71b7d2950806d75be950854201801aec1d2950805005be94d45420175d6fa53c550806d76a6953354201ba56fa544550806d75be94b854201801aeb7d2948805d75be3ae85f201b5d6fa53c950806
  | 5, 0, 9 => 0xd761a22e854201b5d6fa531150806d75be94a8400edb5d6fa52a11e806e2dbe3ae854201b5d6fa23a150806de6badf4a54201adf4a6d35150806d75be94a840089b5d6fa52a1003c6d75be94a8401bdb5d92b7d2950806d75bed94a54201bb96fa53a150806d75be94a840031bb36fa54f550806
  | 5, 0, 10 => 0xe7ebadf4a54201b5d6fa54b924806eb5be22e854201b5d6fa52a100656d75be94b254201b5d6fa537950806d75be94a8401e5b5d6fa53cd50806005be94801f83177f6f88ba150806d75beb14a54201b5d6fa52a100066d759a94a84ba01b5d6f88ba1ae806005bd50800f83175d6fa552950806
  | 5, 0, 11 => 0xd75be94a8401edb5d6f54249006e6b7c45d0a8400d9b5d6fa535d50806e2dbe22e85f201b5d7e88ba150806d7652df4a54201b5d7788ba150806d75be94a8400d5bc16f88ba150806d75be94a840191b5da788ba150806d75be94a84fa01ba56f88ba148806d767294a84ba01b5d4a7433950806
  | 5, 0, 12 => 0xd75becf4a54201b5d6f88ba12a806f35be94a8401e1bcd6fb352950806d75be950c54201b5d6fa52b550806d75be954354201b5d6fa52a100246d75be94bb54201b5d6fa52a100696d75be951754201b5d6fa52a142806d75be950454201b636f88ba150806d75be94a8400b5b5d6fa52a108806
  | 5, 0, 13 => 0xd75be951161a01adf4a7435150806d75be94a848a01b5d6fa53a148806d766a951154201b5d6f83ba150806d75be94a84ba01b5da3b7d2950806d75be94a84010db5d6fa52a1001c6d75be22e754201b5d6fa544150806e96badf4a54201b5d6fa54d550806d75be36e854201b5d6f88ba180a86
  | 5, 0, 14 => 0xd25be22e854201b5d6fa544598806d75be9f4a54201b236fa544550806d75be22e853201ba9cdb7d2950806d75be94a84aa01b5d6fa52a136806d75be94a851201b5da9a52a12e806d75be9534542018016fa52a1000c5d75be95114ea01b5d83a53a150806e1dbe94a840191ba511742a100716
  | 5, 0, 15 => 0xd75be953254201b5da1b7d2950806006bad14a5420175d11742a1005a6005beb14a5420175d9ab7d2950806d75a222e86d201b5d6f8b3a150806d75bd7eb854201bb36fa52a13e806d75bdd0a8400c5b5d11742a100336d75be953954201b5d53a5445508060052950800b03175da7a54f550806
  | 5, 1, 0 => 0xf05be953354201b5d6fad52950806d75bea74a54201b5d9db7d2950806d75be94a846a01ba3aeb7d2950806d76a6df4a4ea01b5d6fa52a10a806d75be94a8401f9bcdaece52950806d75be952454201b5d6fa852950806d75beaf4a54201bb16fa53a150806b7c45d0a4401e1adf6688ba148806
  | 5, 1, 1 => 0x74adf4a542017d5aeb7d2950806e35be22e854201b5d6f893a150806005be94a82883175d6fa52a100156d75cedf4a54201ad111742a13e806e95be22e86d201b5d6f742a100596d75bebd4a54201b5d6fa52a100786d75be22e840121b5d6fb352950806ee5be22e854201b5d6fa52d150806
  | 5, 1, 2 => 0xd75be9511541d9b5d6fa52a100266d75be94a840135b5d6fa54fd50806d7445d0b354201bcdaeb7d2950806d75be951154201b5ce8672fd50806d765e22e854201b5d90b7d2950806d761222f254201b5d9cb7d2950806d75be22c454201b5d6f88b8d50806d7666df4a54201b5d9fa544550806
  | 5, 1, 3 => 0xe9dbe22e854201b5d6f88af970806d75be94a84011db916fa544550806d75be94eb54201b5d6fae52950806e75be22e854201b5d9c88ba148806d75be22ee54201b5d6fa52a100536d7445d0ce54201b5d91b7d2950806ea5be953d54201ba56888ba150806f36bb534a54201bd1aeb7d2950806
  | 5, 1, 4 => 0xd75be952954201b5d6fa52a100166d76a6df4a54201adee86a2fd50806d75bed54a54201b5d6fa541550806006bade801f87d75d6f93aa100676d75be02e854201b5d6fa52a1001b6d75d622e854201b876fa544550806d75ee22e854201b5d6fa52a1000a6d75be94a84018db5d6fb7d2950806
  | 5, 1, 5 => 0xd75be22e86c201b5d6fa549d50806d75be94f654201b5d6f88ba130806b7c45d0d454201b5d6fa52a100616d75be22e85e201bb56f88ba150806d75be94a840141b5d6fa52a100176f1736df4a54201b5d8aa52a100716d76a6df4a541d9b5d6f88ba148806d75be40e854201b5d6fa527d2e806
  | 5, 1, 6 => 0xd75be94cc401b9b5d6fa52a148806d75be94d254201b5daeb7d2950806d96badf4a54201ba9aeb7d29b4806d75be94a843201b5d6fa54b150806d765adf4a54201adf5bac52950806d75be94a840009b5d84b7d2950806d75be95115f201b5d6fa52a100076d75be94a8401c1bcdd9b7d2950806
  | 5, 1, 7 => 0xea6bad14a54201801aeb7aa1001f500646df4a5420175d6f803a150806d75be94a844a01b8b6fa544550806006badf4a4ea017956fa544550806d75be94a8400a9b5d6fa546950806d75be94a840065801aeb7d2986805d75be94a840045801aecd52950805d75be94a8401d1b5d6fa52a100326
  | 5, 1, 8 => 0xea5be94a84fa01b99aeb7d2950806e1ebadf4a54201bb36f88ba148806006b950800f85975d6f88aa100256e46badf4a54201b5d6fa537550806006baa74a5420175d6fa536d50806e25be22e854201bcd6888ba150806006badf4a400fd75d6fa52a1003d6d75be94c954201801aeb7d2998805
  | 5, 1, 9 => 0xd7445d0cd54201b5dabb7d2950806ecebadf4a54201bc56fa54f550806d744604e854201b5d80b7d2950806cadbe22e854201b5d6fa52a100526ec5be94df54201b5d8388ba17c806d75be94aa54201b5d6fa52a100686d75be94d7401e1b5d6fa54ad50806006ba94801f85975d7088ba150806
  | 5, 1, 10 => 0xd75be711154201b5d8288ba150806d75be94a840109b9b6f88ba1ae806d75be994a54201b5d6fa535550806d75bec14a54201b5d6fa551950806b7c45d0a840175b5d6fa52a1005e6edebadf4a54201b5d6fa52a100036d75be94a8401b9b5d6fa52a100106d75be3aa846a01b5d6fa537150806
  | 5, 1, 11 => 0xe56badf4a54201b5d6fafd2950806d75be22e852a01b5d6fa52a100006006badf4a288fd75d6fb1529b4806ea6badf4a49201bc7aeb7d2950806d75be94a840035bd3aeb7d2950806d761adf4a54201801aeb7d2950805006badea82887d401aeb7b1150805d75be974a54201b5d6f88ba1a2806
  | 5, 1, 12 => 0xd769edf4a54201adf117434150806e967222e854201b5d4a99aa100716d75be94da54201b5d6888ba150806d75bdb4c454201b5d6fa952950806b7d6222e854201b5d6fa52a100056006ba94a8400596f56f88ba150806d75be94a8401b1b5d6fa52a100396006badf4a541d975d6fa542950806
  | 5, 1, 13 => 0xd75be94a840081b5d89b7d2950806d75be94a850201801c3b7d2950805d75be94a846201b5d87b7d2950806b7c45d0d76a201b5d6fa52a102806d75be94f754201bcbaeb7d2950806d75be94a8401b5b876f88ba1b480600722df4a5420175d6fa548d50806d75be94a84003dadf11742d950806
  | 5, 1, 14 => 0xd75be94e954201bcdd4b7d2950806d75be38e854201adf11742a106806006badf4a5414575d6fa52a100806d756ea74a54201b5d88b7d2950806d7445d0cf541c5ba56f88ba150806b7c45d0d44ba01bafaeb7d2950806d75be952254201babaeb7d2950806d75be94a848201b5d9aa538950806
  | 5, 1, 15 => 0xd75be952854201801cab7d2950805d75be94f854201b5d6fa52a100666d4e92df4a54201b5d6fa52a100186006ba94a8288597c56fa52a13e806d75be22e854a01b5d6fa52a1001e6d75be94a8401d9bc1aeb7d2950806d75ae22e854201b956fa52a1006e6d75a622e854201b5d6fa52a12c806
  | 5, 2, 0 => 0xea5be22e852201b8f6f88ba150806d75beb74a54201b5d4a5425d00716d7445d0d766a01b5d86a52a1006e6d75be94a849201b5d98b7d2950806d75be94a840039b9b6fa52a100786e6dbecd4a54201b5d6fa52a100016d75bec34a54201b5d6fa52a100736d75bec54a49201b716f88ba150806
  | 5, 2, 1 => 0xd75be94a840139b5d6faed2950806d75be22e85caa1b5d6fa52a100126d764edf4a54201801aeb7d29ae805d76b6df4a54201bbfaeb7d2950806006bb0d4a5420175d6fa538950806d75be94a840145b5d84a53a150806d75be94a840051b5da6b7d2950806d7692df4a54201b5d6fa52a1007c6
  | 5, 2, 2 => 0xd75beb34a54201b5d6f88ba198806f36badf4a52201b236f88ba15080600782df4a5420175d6fa54f950806006bb4f4a5420175d6fa52a132806d75be94b754201b5d6fa52a100566d75be94ce54201b5d6f88ba13a806d75be94da40191b5d6fa52a0e26e6b3445d09f4ba01ba9aeb7d2950806
  | 5, 2, 3 => 0xd75bea94a54201b5d6fa52a1003f6d75be94cf54201bcde2b7d2950806d75be94cc54201b5d8ab7d2950806b7d2a7aa8401e1adf66a54f55080688ba1a8ce54201b5d6fa53692e806d75be94a84ea01801aeb7d292a805d75e6df4a54201adf117435d3e806d75be94a845201b5d5388ba150806
  | 5, 2, 4 => 0x35da9c552950806e15be22e854201b9baeb7d2950806
  | 6, 0, 0 => 0xd75be94e854200a2fb7d75be22e854201f5d6f88ba15080213ebadf117a3a150807d75be22e86aaa100e00d75bdd0bf54201b5d6f88ba150802f3ebadf5ba53a150807d75be22fc742a100faeb7cc622e854201fb7aeb7c45d0a8403ebadf11742a100037d75be22e854200dcfaeb7c45d0a840041f5d6f88ba1b8a8403f7b5d6fa53a150807
  | 6, 0, 1 => 0xea6badf4a742a100e00d75be94a8401c5b5d6f88ba150800038035d6f88ba0a23f6d75bdd0da5faa100faeb7c45d0a8400ddfd3aeb7c45d0a84038035d6f88ba150806d75be22e854200befaeca5be951154201c01aecfc45d0a84030035d6f742a100276d75be9511542006afaeb7d2a22a840191f5d6fa53a1c4a8403ebadf4a88aa13e807
  | 6, 0, 2 => 0x6badeeb742a100daeb7c8e22e854201f5d6f88ba1508007b8035d6f542006a2f6d75be95115425d00faeb7c45d0da54201f5d6f88be9d0a8403ebadf11742a100057006ba22e8542002cdc5d75be22e854201f5d6f88ba150801cbebadf11853a150807d760e22e854200cefaeb7cb622e854201c01ae742a100270b30035d6fb152950806
  | 6, 0, 3 => 0xd7626df11742a100faeb7c45d0a850201c01e2d75be94a8403003876f88ba150806d75be22e85423100faec3dbe22e854201c016fa5445508006379bbd6f88ba150807006bb0911742a100c00d75be94df54201801aeb7c75d0a84036badf437438950807d75be22e85420500faeb7c45eee854201c01c8b7c45d0a84036badf117439550807
  | 6, 0, 4 => 0x6badf27742a100c00b7c4550801a831b5d88b7c45d0a8403ebadf115423500677006badee8541444edaeb7d29d0a8400fdfafaeb7c45d0a84038035d6fa54f550806d762adf4a742a100e00d75be94a8401a9b5d6f91445d0a8403ebadf117439950807eaebadf11742a100faecd445d0e254201f5d6f88ba150803abebadf4a85ba150807
  | 6, 0, 5 => 0x6ba22e8541442cddcb7c460ce854201c01aeb7d29fea84030035d6fa0c4550806d75be22e85423900faeb7c45d0a84b201c01aeb7d2950800fb6badf117aba150807d75be22e9742a100fe6ea5be22e854201f5d6f88bfdd0da4038035d6f88ba17c806d75be22e8542008cfcdd75be94e854201c01aeb7c45d0a828b6badf11742a100807
  | 6, 0, 6 => 0xd75be9511542004efaeb7d8a94e854201f5d6f88ba1508000bebadf11742a1002b7d75be94e854200e2faeb7c45d0a8401cdf5d6fa54460ca8403ebadf2888ba150807d75be22f8742a100faeb7c45d0e854201f5d6f88ba150803338035d6fa54cd50806d75be951154200f0faeb7d9a951154201f5d6f88bc1d0a8403ebadf4a88aa11a807
  | 6, 0, 7 => 0xd7445d0a84ba00e2faeb7c45d0a840025f5d6f742a1003517bebadf117eba150807006badf4a5420018dded75be22e854201f5d6f88ba1c0a8403ebadf11742a124807d75be22fb742a100fe6d75be951154201f5d98b7c45d0a8403ebadf11742a1000e7d75be951188aa100fcdb7c45d0a8401e1f5d9cb7d2a22a8403f36df6688ba150807
  | 6, 0, 8 => 0xd75be22e854200f4faeb7d2a7ae854201fa9aeb7c45d0a8403ebadf4a742a1006a7d75be22e85420024faec9dbe22e854201c01aeb7c45d0d74036badf11742a134807006badf4aa52a100ddfd75be22e854201fc5aeb7d29d0a8403ebadf11742a1002e7d75be22e8712a100faeb7d2a5d1154201f5d6f88ba1508028bebadf5b88ba150807
  | 6, 0, 9 => 0xd75be8311742a100e00d7652df4a54201b5d6fa53a150800fb8035d6fa52a100356006badf4a54200c8c00d75be94a84fa01b5d6f88ba15099403ebadf11742dd50807d76731511742a100faeb7c45d0ce54201f5d6f88ba150801a3ebadf117436900647d75be9511542002cfaeb7c7a22e854201f5da9b7d2a22a8403ebadf1588ba150807
  | 6, 0, 10 => 0xd75be952588aa100faeb7c45d0cf54201f5d8ab7c45d0a84038035d6fa52a12e806d75be22ea742a100faeb7c45d0da4ba01f5d6fa54cdd0a8403ebadf117439150807d75be22e861aa100faebcdbe22e854201f5d6f88ba1508035bebadf11742a114807d75be95117b2a100faecf5be22e854201fb9aeb7c45d0a8403f9b5d6f88ba148807
  | 6, 0, 11 => 0xd75be22e85420008faeb7d29d0a840031c01aeb7c4550800fb6badf117430d006a7d75be94e854200cefaeb7ce5d0df54201fcdae88ba1508038bebadf11742a1004c7d75be22e85422100fcdd75be22e854201c0000b7d295080062ebb076f88ba150807d7682df4a88aa100faeb7c45d0a840161f5d6f88bbdd0a8403ebadf11742a1003f7
  | 6, 0, 12 => 0xd75be22e8542009efd2b7c45d0a84ba01c01aeb7d29508d4036badf117435150807006badf11400fc6adaeb7d8a22e854201f5d6f88ba1508038bfaf5d6f88ba150807d75be22e85420070faeb7d2a94e854201f5d6f88ba1508017bebadf11742a100407d75be22e854200c4faeb7c45d0a845a01f5d6fa5445baa84038035d6fa5445003f6
  | 6, 0, 13 => 0xd75be7b11742a100faeb7c45d0a8401a9f5d6f88ba1508009b803cdaeb7d2950806006badf4a88aa100de2d75be22e854201c01aece5be94a84036bae96f88ba150807ecf36df11742a100faeb7c45d0df54201fcfaeb7c45d0a84038035d6fa52a100786d75be22e8542a100e00d75becd4a54201801dcb7c45d0a84036badf4a88aa1006e7
  | 6, 0, 14 => 0xd75be4311742a100fae88ba1b4ce54201f5d6f88ba15080163ebaf96f88ba150807d75be22ff742a100faeb7c45d0a84007df5d6f88c35d0a8403ebb1b6f88ba150807d75be22e870aa100e00d75bd50801a89db5d6fa5445b4a8403dbe22e85427d00787d75be22e8542007cf6fb3445d0a84fa01c01ae88ba19ca84030035d4a88aa100166
  | 6, 0, 15 => 0xd75c6df11742a100e00d75be94f6542018016f88ba1a8a84036badf1178ba150807d75be22e85c2a100e00d75be22e852201b5d6f88bc9d0a8403efb5d6f88ba150807ca646df11742a100faeb7da222e854201c01aeb7d2950800b36badf3388ba150807006bb536fa52a100daeb7c45d0a8400e9f5d6f88ba15080143f22df11742a1006a7
  | 6, 1, 0 => 0xd75be22e854200f2e00b7c45d0801f831b5d6f88ba15080033ebacd11742a12e807d75be9511742a100faeb7c45d0a8400edf5d6f88ba1508f403ef35d6f88ba150807b7c45d0da6a2a100faeb7d2a0ce854201f5d92b7c45d0a8403ebadf11742a1000c7d75be22e85420016faeb7c45dae854201f5d6fa53a1508d4038035d6fa544550516
  | 6, 1, 1 => 0xd75be22e86baa100faeca5be22e854201f5d6f88ba150801abebadf11742a100647d75be22e85427d00faeb7d2a5ce854201c01aeb7c45508012b77b5d6fa544550807d75be95115424900faece445d0a84ba01c01aeb7d29baa840373f5d6f88ba150807000035d6fa52007ebaeb7c75d0a84019df5d6f88ba1508032b80001aeb7aa1001f5
  | 6, 1, 2 => 0xe1dbe22e854200c8e00d75be94a8401b9b5d6f88ba15097403ebb476f88ba150807007675d6fa52a100dd2d75be22e854201f5d6fb3c45d0a8403f9adf11742a100787f35becd11742a100faeb7c45d0ad54201f5d6f88ba176a8403ebadf11742a100697d75be2f11742a100faeb7c45d0a850a01f5d6f88ba1508016bebadf11742a108807
  | 6, 1, 3 => 0xd75be22e85a2a100faecedbe22e854201f5d6f88ba150803f3f9b5d9c88ba150807006badf4a6d2a100daed0dbe22e854201c01aeb4445d0a840300001aea52a100165d766adf11742a100fd9b7c45d0a84fa01f5d6f9cc45d0a840380222e8542002c0c6000035d6fa52a100bd4e6dbe22e854201c016f88ba150800630035d6f9c44550806
  | 6, 1, 4 => 0xd75be2305742a100faeb7c9dd0a846a01f5d6f88ba1508031bebadf6f88ba150807d75be22e8542008efaeb7c45d0a84014df5d91b7c45d0a8403fa35d6f88ba150807000035d6fa52a0a2be6d75be22e854201f5d9cb7c45d0a8403803a56f88ba150806005be22e85414418daeb7c45d0a840055f5d6f88ba150803c3ebadf6688ba150807
  | 6, 1, 5 => 0xd765adf11742a100e00d75be94e254201801aeb7d29508028b6badf11742a100077d75be22e854200e0faeb7c9e22e854201f5d6f88bd9d0a8403ebadf11742a100507d75be22e8542002efaec5445d0a8401c5c01aeb7d6e94a84036badf117427d2e807006badf4a5424900daeb7c45d0a840059f5da9b7c45d0a8403ebadf6a88ba150807
  | 6, 1, 6 => 0xe1ebadf11742a100faeb7c45d0dd54201f5d6f88ba1b6a84038035d6f88ba1003f6d75be22e8542007afd4d75a222e854201c0191b7c45d0a84036badf11742a112807d75be22e85420022faeb7c45d0a8400c9c01d4d75be94a84036badf11742a148807d75be22e8692a100faed75be22e854201f65aeb7c45d0a8403f535d6f88ba1b4807
  | 6, 1, 7 => 0x1cdd75be94a84036bb016f88ba150807006badf4a542007edaeb7c45d0a840149c01aec55be94a84036badf11742a950807d75be22e86ba00f0e00d7445d0801f859ba96f88ba1509f403f335d6f88ba150807
  | 7, 0, 0 => 0x35d6fa544550806006badf117437d50807006badf11742a100717007375d6f88ba150807006badf11742a1003f7006bb156f88ba150807007535d6f88ba150807006badf117438950807006badf11742a1005170077b5d6f88ba150807006badf11742a11c807000035d6f88ba150516006badf117436950807000035d11742a100166000035d6f88ba150806000035d6f742a100276
  | 7, 0, 1 => 0x6badf11742a1001670079b5d6f88ba150807006bb396f88ba150807006badf11742a100787006badf6688ba1508070000001aeb7d295080500002df11742a1000c6006badf11742a12e807006bb296f88ba150807006badf11742a100357006badf11742a100647006badf11742a13e807006badf4a88ba150807006badf11742a1000c7006badf117fba150807006badf11742a1006a7
  | 7, 0, 2 => 0x6badf117437550807000035d6f88ba1003f6006badf117b3a150807
  | 8, 0, 0 => 0x35d6f88ba150806
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]

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

def CG : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12581

theorem PEqualNP.Outside.L_meta_12581 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008225440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008225440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12581.mainG PEqualNP.Outside.L_meta_12581.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12581.CG, PEqualNP.Outside.L_meta_12581.CG_mono, by
      have : PEqualNP.Outside.L_meta_12581.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12581.CG_eval⟩
