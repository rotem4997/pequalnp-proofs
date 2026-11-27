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
namespace PEqualNP.Outside.L_meta_12435

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941107712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 11, 15, 15, 15, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 11, 19, 19, 19, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 11, 21, 21, 21, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 11, 22, 22, 22, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 11, 23, 23, 23, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 11, 25, 25, 25, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 11, 27, 27, 27, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 11, 29, 29, 29, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 11, 30, 30, 30, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 11, 31, 31, 31, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 11, 35, 35, 35, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 11, 37, 37, 37, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 11, 38, 38, 38, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 11, 39, 39, 39, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 11, 41, 41, 41, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 11, 43, 43, 43, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 11, 45, 45, 45, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 11, 46, 46, 46, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 11, 47, 47, 47, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 11, 51, 51, 51, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 11, 53, 53, 53, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 11, 54, 54, 54, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 11, 55, 55, 55, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 11, 57, 57, 57, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 11, 59, 59, 59, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 11, 61, 61, 61, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 11, 62, 62, 62, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 11, 63, 63, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x15171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae88800000000000000000000000000000000000000000000000000eae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae88800000000000000000000000000000000000000000000000000eae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae888000000000000000000eae8eae8eae88800eae8eae8eae88800eae8eae8eae888000000000000000000eae8eae8eae88800000000000000000000000000000000000000000000000000eae8eae8eae88800000000000000000000000000000000000000000000000000eae8eae8eae8880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800eae8eae8eae88800

def cMZZ : Nat := 0x15171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff00000000000000000000000000000000000000000000000015171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff00000000000000000000000000000000000000000000000015171517151777ff000000000000000015171517151777ff000000000000000015171517151777ff00000000000000000000000000000000000000000000000015171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff000000000000000015171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff15171517151777ff

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
  | 2 => 9
  | 3 => 51
  | 4 => 305
  | 5 => 686
  | 6 => 414
  | 7 => 36
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xf928054ee076a2b9df985abccdcc1637977a9f50844fc2fb30563fc506d1d6e6065640d4
  | 3, 0 => 0xe8988984e2a14bbddeef61acdc7f1192d91c8df4ce725753c6b881b6bcc1ada7ae063b7da4fb84e59f63f1899b8edb279b08929198b8b3e5977a9f50962f19119027b6c78e57fd2482bcb5db7cea88e97b2e089b7ab5e2ab791764df76936fb9730cd0ed71eecae4718429b26b68dafe68e99e2664ccf1a363ce59866254a61261a40008529b8c714c9370c848f66c53400cebe73d9a662d31477eff3137f7fd2fce673c26b3d2b226354a0e21ad92de1f6d4aea17bac81713ab2e2111255fea0885c1c5073c3828070c0e51
  | 4, 0 => 0x287b7a6e284a558c27fd661b26fcb222260f4f1324b0fb9324aab8db241f577a23724d7c226c2715216469c02094e5081e48a8d41e42ad201d04ea661ceeb2af1c5fd9371c5e705b1b74ff3b1b45be051b1fa6c11b12e3c71a782e451a61eff81990bf9e18d5112518c1d623178c12c21649e30216044d7115c7a1a414d0553a14a0f399145a8dae141c93a913946d5812c2b04212ac7ff3129349091265aebd1246aef51245476311fb7dd6112e26e60ffceb270f3239770ec8f2f00d24ed380ca51da90c19722a0adca2480a83cefe0a2d0b2908dc326107d9f7ca073c38280638014d05f0b1e9051e64fc048619660419b94f02e736f202c6826101d3f93a
  | 4, 1 => 0x52f99497528739f351e4a8fe4facad1d4efbfb3a4ef0326d4eb0fa844e6bae394ca8a5a74c55ff464a95c5cc4a704b7549c4877e49a1b47d48e1ab5648de26cc47d46ded46ab203846a1435d44224b3643e1e49f43bd2534435a600543313e9542d6c482428b62f540c2e5c940a7ea114077496d3f941f6d3e33f02b3ddeac153cfe294e3c3a73713c12554d3ba73fba3a6fe72339a61b4539a0539c398cbd2339753ae2382c8de1371214f93659cbfd3555b7413495cac0344b6c8433d63bd4336dd89832d4985c32c87f8e31e4915a3099500c3043405c2f4e54f72f28a4132efc1f9a2d7037872d5a70222d04146c2c5001282c201b662b68d1d02b04ba79
  | 4, 2 => 0x96c0184d9680e064942225409247c87b92403155916f2bb190ae0cac8ebbb7b08c64d6b18be7ed1b8aa6aa6289c39f438892cba98888a2698541b0c78395a633810b210980d9f3d97ff9f8397cad01817bd874ce7b35c7a47ad2918f7ab7242178afc3447899d430760b973075d704c2754dbd8b750b588974dba38a72d9e6a1728843bd726f8f9f7116181f6f3bb1ea6e3bb1fa6e0a19306d4415976c80e1736c7fb04c6c4b85e1698fdf4269344fa067128c9566084f05652854d164af8a1f634f81826248142561dfd60f61d45c1d6180990e60b0a23a603f80dc5f5bf8a25ee140b55c70d9795b0a27c35ada40a65a92962258f91cc455a503965386814e
  | 4, 3 => 0xd7296781d68b9d90d48e8a76d477bed7d3c70040d1f48046d1c9a56bccf3cbffca8449abca634ff8c950b98bc85018b7c84a14bcc578e2c9c4d537c4c47ce761c2db37edc25d2544c181cdf6be1865b4bd78fe91bcd3d5a3bc1627debb7a6bacbb3741febab95383baa9cc81ba140262b8b80526b6cb1835b5dd498db32f91d4b2b0a2dcb1241584b01a0f0daef78574aecf190fadff4440acecc4dcab02ffc7aaad0aeca8e92fb1a88f9a8ea880881aa868ac80a845c043a4d6522ca4ca3906a4b5cd25a3eff17aa30a8c9fa2aa2686a29313a1a1acb2efa138a5e5a10917d2a01d4db6a00160009d54a2bd9cefc44a9b31439b99592db498d8bc659847939f
  | 4, 4 => 0xffe94f9affaee790ff1702adfed15d78fb6bbc25fb1bb727faff77b4fadcea45fab546edf9168d4df891a5eff5386ca9f51d2d77f2ceca5ff2c56051f2a47878f199a100f0077c57ef83fb19eedc3373eec9e26cee7f54b5ed2d22dfecac21bcec2d1f82ebbfd75aeb4d377deb3eedb2ea001a0de97c98cfe8d8fdb2e8994cd9e6a56311e6a4bf72e5d070a7e4468767e22ddface1d68d81e1cf60b7e145c285de6a3385dd30c9cbdcdad2f6dc92ffdadb2a73d1da1effe4da1ddae2d940210ad91c8df4
  | 5, 0 => 0x12c5bf37129349091291e92811c12e851179bf8b113305f410ce889a10cb2c83100b7fb40ffceb270fdee68e0f51537f0f022f630ee718640ebec3cf0e6a80ae0db62d050dadfb480d8f9a270ca51da90c9e63070bd90e660bd908e60b60359d0b59d4ba0b4060800b2cd0270b2ba3aa0af2a8340ac3ca390a7bd91f09d7844409d0450c08facd1908c0216108bfa1a00777bb140768ae3b075643c906f9833a068605580643674c06379c990636cc9e06192c3c05d2831705d1a69c05b02e71056ee16d050cbf1f04eb45ea04b565fb0486196604737ee304063a8903e1fee102bc6b7902b8bf170281cd2b0215124b01b5c8c801a8a0d501333335008259f3
  | 5, 1 => 0x245c958d2421062a22c046a52281d309222c3107215e6dc6213646da2130e4fc210424aa20fbac0320f5c21d20f30bdb20577386203b7a531fcf54281f9b53d41f73bad71f4463ae1ebc668a1ea142fc1e9f7b311dfe36b81df4e5cd1d5f12531d1ea92b1ca7178a1c7324e31bbad7191b2982b21b0d9e2c1ae484c41ae1003a1aa0f2371a7d0d531a25f14c19ca363a19c0203819a5b967197936801953ddf8193d016419198bb218f7ff9018994b72184029e417f77b22178121d5170ebbbf168e0a84162d051715f0f22f15940fd2155c0bbb154d140b150a9e2714f8651114d99df0149e8a451475ab09145a8dae141c15781413d67a13f92a6613de4678
  | 5, 2 => 0x349cc525349c3e63348e57f634175f6233f3ebbb33e6faac3381de03336dd898332a384132d4985c32b37ba831fc46b131f8f4d030e5e07e30dedda0308939c7307ea3a030503362301e9a983011ae792fa17fcf2f84f28e2f4a938d2f2e66f42e95a1072e9562db2e94dc192e6437d52d6aa1162d563e6e2c61e6f72c317ca92bf4e4672bcb00082bba15cf2bab12f82b81afd32b48d1082b08c0532af8dad62ade7e342ab43ab42a7aec5b2a6b65592a67e61429270dfd292704aa28ab9f82282e446127c075e4279334fa26c40b8726646ec0265ed5d02642dc9d260f4f13260a3fa825d60da7256437292559eac324f1788c24ddc0e124738a112464030f
  | 5, 3 => 0x451615b4450316bd44ef7daf44dcc00f44a54fb84465bfff43da95b943bd253443619aaa42ee754142d6c48242a97329425b8f4941e3bbfb418b3e43417130824087a64f40681107401a21213fbe9bff3f941f6d3f737a2a3eab39183e5e5db53e1fc7fa3e039ba23d5f4f833d58f91c3ce712f73ccba5893c71914a3b9312df3b69ce383b69176d3ad336273ac444ac3abbecb63ab770ee3aae55983a54f30b39fe927a39e4cf1e398cbd23397d184d394b13ac389cc12b384136e437eb862a37e35e4037c7370937ac29b4378c3b8a3789545336f024f236612288365604f4364565c436191b7c360bae9d35cf414235cd5aaa358bb09534b48a6c349d0351
  | 5, 4 => 0x5af52b9c5a92962259d526d359377dc759365ad85917015058dd39dd58d499b55865c7dc58281ab057c18d9f57be8c2c5716b2c956b6fe445656b564551b212354a31f8b545c49e35454b2bd540482ea53fcce2c53f63a1253ae525253672958536611d25359b20e533fad9953301b7d52e524c552c6129e52c28e1452bbd9f2523d153e51f3a0d65106e54c50e8de2f50750c30500f6e785005c4cc4fd03d184eafdaef4e2921fb4e134d2c4dfc6e834dd9f0d94cbb2bca4c55ff464b3a232a4b2a80014aacb2024aa74d114a24e54f4a0d0b7049513fa74921bbc148f0be6648de26cc48b2dc4347d1288246a1435d468f08994621836b45ad5f3a4532c0e0
  | 5, 5 => 0x7474582e74330d9b742f01bb73af8c5d73ad55d1732557f772fd8fc071e62785710c06dc70ede26b70eb141070e6c02e706064277013c5a86f74371e6ef29db86ea9fb126da5f3876d9a719e6d61783b6d4b03016d17812f6cab72fd6c80e1736c436ff16b108b096afdb1196a9509826a90a2c26a15e0f669344fa06812b3d267ef72386753ffbc6743a0b766eb0bd366ead39466deba6e66ceef546654d70e66398b2f651f662264756b2b62ce8806625077bd6248142562116c60615c5b0f60be911e6069e9d9602238975f9e4f955f6924255ee49c275e86d8e15e85a0b65e80280f5e6e1ded5e6e08e15d45c5035cde12a85cbe608e5c2f454f5c2ae5c8
  | 5, 6 => 0x8ebae6398eb90cef8e49f9d68e0637908d9b017e8cc2ac6d8c8cbc088baa7b998b3697ad8aa6aa628a649a1f8a5e96248a2ea48e8a2b752989748245895b242389057ad48892cba988269aed879574b18772ec078732eb3987225bd686d0d49e869168c9852f3563845f2a72840e0c4284005f4683a4a2d483964f5e838fc05d836d1ffb8353c1d98339f17c82b0e28c824eef65819c4d8c813fe320811af98c802ce71c7f0c1a507ebfc5087e2ad8a37e06a9f87de9015c7d9d408a7d8eed147d4976b77cce092a7cbe4de97c5e3dd67c2883ca7bbf887d7b41e9407a562e5c7a3a5d3f7812efd177f1caf577d33eec7789c1b975f2cae8753a86f674b15d5c
  | 5, 7 => 0xa29bf172a22e28f0a1fd708ba1f8b357a1abbec0a1859a7ca12d9f91a0b1ea4ca089aacda07eb4ed9ef766149e8d81379e5025d19e2a27439d9d2da49d31e33f9d17313b9c93e6289c4c3bcd9c325c4a9c0f94bf9c006a259b7e38329b7b58c69b31439b9aaa88029901c82b98a01ef897dcdf5197d5aaac97cb0e62972887d1970baeae96da428b96d8113296c8069096c0184d968a246d9679873896163e0b95f907db95db81a895642c2c951ce3ec94c2488392fa65e192f5170f925dfe5f9240315591f2875c91cdb62a91b1dde39128871e9121258790c0a44690ae0cac9082c223907224ee906ed4229054a2089032d7738f6d2fc48f62866d8f248250
  | 5, 8 => 0xbdcef34bbd803d8dbcfe661ebca314a2bc628ca6bc57fb55bc253f41bb7a6bacbb2b0eb5bae8d932baa9cc81baa62757b9702c67b9634d50b8c62d10b8b6a60eb777b395b7737d89b5e7a01cb57a2705b5601383b4d7f1c2b45b0592b410d359b3a256f3b381bed3b356e3f8b2929361b1d861e0b042429cb020ba35afe03dd2ae52dcaeae469492ae41a0eaae09710fadf045b4add458c2ad7597bfacfa1e9dace26437acbfc221acb581e7ac5e210bac149b75aaf1f2c3a9e5c748a999577da8fe1ff9a8b9e479a8ad387ca880881aa79e13b6a76e3575a6d42b92a656bec1a554b8faa53e03caa5301751a4cb6a32a4bba562a3c95f13a3bf60aba2f6980d
  | 5, 9 => 0xe3a6a480e30f921be30e984fe2a9666be297ba6ce2367288e21e32f2e1b8476ae06ae18be069f8fde05e9c05df88e116df1c362bdec97136dd342824dca3a42cdc941d2adad65786da9fd967da23c42ed8878da1d86b946ed7e6efcdd79f9187d7296781d6a1eaa3d68b9d90d66f0f11d561e92fd4d5d75ed3a9e02fd342a849d2a6d36bd2537c31d1e4f944d16d1b7fd12819abd09a8859d00fc698cfc3280ace2df38dcc985061cc39c7a2cb9cdf9ccac20343c8912338c732e65fc731c30dc6a5ecb8c69a9ac9c497be19c47ce761c4309c79c35c9f44c2f3e454c2417f1bc2079e5fc12b8415c07a153cc06e8844c0629e4fbf6f3253bebe0858bdd6a725
  | 5, 10 => 0xff30574afeee6147fdbbc11dfd62dafbfd3330d8fd023dc3fc950d3ffba13e86fad166c7f883251cf86e4d60f84a3b3cf76a38a4f6d56823f61f2182f5f75338f58259fbf4dd00f1f4ca047df45cfd7ef4045231f399e853f34c15b0f162d65af13d2576f110a0fdf0ce05d9efff5016ef6ef185ef38ebafedb10653ed97fe18ed96c56dec5b1fa1ebbfd75aebb1f81eea001a0de9f7edcce97c98cfe70a4d5fe6c5bb22e6781612e633d8dde622def0e4a849a1e46ceed1
  | 6, 0 => 0x1af397d41ae1003a1ace03e21ab5b5b11a7a494419d60f0719d30d9419cd7b0a195d09a1193d0164192b343118cb7fac186b36cc172fa28b16d1a7671644363f15dd6f27156e337615542f0115449ce514f9a62d14d99df01475ab09145e68b7145196a6138e17b1131b66b41291e92812898d9811b907a81179bf8b0ffd443c0fee72410f6228f10d4ea4920d08b4bf0cc1336a0c218cd80b4ded1a0ac3ca3909d7844409af032208facd1908a38a01083604d307d0341807474248072a971c0703ff1706b9d120067a416705d1a69c04eb45ea0385b1ea02b8bf17029c27b7022ea28901f0fd1401d31d6701a8a0d50187fb9200b644d20072df1d0034878e
  | 6, 1 => 0x3b69ce3839e7c054399e432138e2873e383c649d3688d996363dc37835c1d739358bb0953539d95f34b48a6c3327e37f330263d331a129033089b24f3088cdb52fba74ef2faef3062f75f9a32f5f84692ebff4652e95a1072e9562db2e57f1592de477702ca5242a2ade7e342a27353a296881242958221f292704aa2855e4cb2733e78a2689ec932613cdc625b12bc024e3096e24c8a12124738a112464030f245c958d2425edc8227e6b412236b9ff22089e3a209a221e2094a97720829f5520828a4920577386203b7a53202bfb691f90da2f1e5a12511e43c6b71d2d596f1d09ad041ca7178a1be9a83b1bc7b8231b5419151b4bff2f1b4adc401b2b82b8
  | 6, 2 => 0x52d525ae52c6129e52c28e145297438b5286a6565283558a52692370524758db517707d5511af61b50cf67a150a0c2695097d378505e7b3e501ab8f84faf82e64ea13d704e2d8ac24dbefd014d4b19154cd2d2804cbb2bca4c4325f64c3ff6914b8903ad4b732a154b6fa58b4b19fc3c4a3b1c5549876d6f4936dd3e48e5560648d000ba4797f3464743b6cb4642c4e046228daa4614e0ae4581a163456843414532c0e045104ead44a54fb844667f5f446370cd440cff1f43b0cef4437e63f0432f7af442e9999c42d6c48241a4b134419090fc41209bb840e87c5b40d44670403f5a0b401b2b60401a21213fb1c1f23f44da0e3e5e5db53c6aafc43c4edea7
  | 6, 3 => 0x796f287c778ea86d777494eb762554c175b6d85b753a86f6705b15fa701df2776f8a19276ea9fb126da5f3876d3a286c6badd8e56ac1b9e46a7d6e6169b2951e6982b6dd6890c968686b4029674498b96743a0b766fccd2865dde07b65d3e21364e83be26442aa58642f9756642a4d9c6411f1f3639a1be462c66bb4610be77c5f4664a75f2bb2a35ece1bd65e2416275e14eb8d5dc09de25d92b99a5d8fda2e5cbf096a5b16499359f160b959ea2c145920301658eec3f358dd39dd58dc87f8589ea5d5588e08a0580d894357b93b985731655456d6c9eb56b6fe44553dbccb550ee7495509987754727fc7540708c453e2379253c65f4b533d088653301b7d
  | 6, 4 => 0xa4ac3bd4a44af3f0a432b45aa3ccc8d2a36ff4eda292debfa27e7a65a20304caa19d627ea130b793a0b5b8099f8143099ea89e929cc4dcb19cbba25e9c3845969b7e383299fb713597d5aaac97a7ac0897766a9796ea58c695f907db95be619794f6bdc294bb54d39467fd99940a77cd93e6257e936564d692fa65e19121258790c0a44690ae0cac9082c2238cebb2a08baa7b998aa6aa628a2b7529895b242388ba6e20852f356384f8826784560083842854d8828e96a4828309ac8183b3bb811af98c7feb288d7fe374b37f12e7867efcf80b7eb7960a7e52e3147e39c0a97d9d408a7d8eed147cb0d9bc7c8448917bedf9f97bca8ecd7b00f9677acb2776
  | 6, 5 => 0xe318a60de26bf4e9e24ffbb6e1afd537e158e511e0b3fc94e012b81bdd3e0415dc3a72afdbdeb79ddb5182c7daadccd5d9233d22d8a28be7d7a89135d63096dbd4a66a8bd2e309fdd2dfade6cded8fc9cd41518accd84b9ccbec05a7c97d2f9ec89a86bbc84c1dfcc7e7047ac5f68044c4cd407ac144d8b2bea98ea7bce5e82fb9a4370db8b6a60eb70bfa0bb6de85e5b6717ee6b618d399b5609718b54db640b51171bdb359f833b3139de1b2e28741afe03dd2afaf05baafac7f80aea67d9aae96f698ae6fa109ae09710fadd458c2ac10b089aa8a670faa6e6ddcaa4be901a9e5c748a88c977aa76e3575a6d42b92a6bccb09a6817039a656bec1a53959d2
  | 6, 6 => 0xfd7e4f9bfc1313ddfba13e86fb9199b0fa55b847f9f7dfa3f99dd5b6f86a8657f6b184b4f4ca047df40d7633f2f35f03f19973f1f142e857f0ce05d9f0aa226af078b938ed1d41b6ecf2ff97ec7fe6bceb3b860deac020e5e8735733e8575e00e76e6c26e6880b74e6788472e440b26ae372ef29e345665f
  | 7, 0 => 0xfd7e4f9bf0aa226aeb3b860de6788472e26bf4e9e24ffbb6db5182c7d4a66a8bccd84b9cb6de85e58aa6aa62701df2776982b6dd5d92b99a59ea2c14580d894357b93b98550ee74952d525ae52c28e145297438b4dbefd014cbb2bca4c3ff6914b6fa58b4743b6cb432f7af4419090fc2fba74ef2958221f15449ce514d99df00747424806b9d120022ea2890072df1d
  | 8, 0 => 0x4cbb2bca
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc0000000055555555000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xf000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff000000f0f00000f0f00000aaaa0000aaaa0000555500005555000033330000333300000f0f00000f0f000000ff000000ff
  | 0, 2 => 0xf0f00000f0f00000f00ff000f00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff00ff0000000000ff000000ff0000
  | 0, 3 => 0x333333330000000033330000ffff00003300ff003300ff0033003300ff00ff00330033003300ff0033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0f0fffff000000000f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f00000000
  | 0, 4 => 0x5555ffff0000000055555555ffffffff555555555555ffff555555555555555555555555555500005555000055550000550055005500550050f050f050f050f0505050505050505044444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff33333333ffffffff333333333333ffff33333333333333333333333333330000
  | 0, 5 => 0xaa00aa00aa000000aa00aa0000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a000a000a000a00088888888888888888888888888880000888800008888000088008800880088008080808080808080777777777777777770707070707070705f5f5f5f5f5f5f5f55ff55ff55ff55ff
  | 0, 6 => 0xaaaa000000000000aaa8aaa8aaa8aaa8aaa8aaa8aaa8aa00aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa00aaa0aaa0aa00aa00aaa0aa00aaa0aa00aa88aa88aa88aa88aa88aa88aa88aa00aa88aa88aa00aa00aa88aa00aa88aa00aa00ff00aa00ff00aa00aa00ff00ff00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa008800
  | 0, 7 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa8800aaaaaaaaaaaa0000aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000
  | 0, 8 => 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c88888c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c00000c0c00000c000c000c000c000bbbbbbbbbbbbbbbbbb00bb00bb00bb00afafafafafafafafaf00af00af00af00aaffaaffaaffaaffaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaabbbbaaaaaaaaaaaaaaff
  | 0, 9 => 0xccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc00000000cccccc00cccccc00ccccc8c8ccccc8c8ccccc0c0ccccc0c0cccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000cc000000cc000000
  | 0, 10 => 0xcdcdcdcdcdcdcdcdccffccffccffccffccccffff00000000ccccccccffffffffccccccccccccffffccccccccccccddddccccccccccccccffccccccccccccccccccccccccccccccc0cccccccccccccc88cccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc8800cccccccccccc0000
  | 0, 11 => 0xececececececececececececececccccececccccececcccceaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaeaea0000eaeaaaaaeaeaaaaaeaea0000eaea0000ea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0e0e0c0c0e0e0e0e0e0e0a0a0e0e0e0e0e0e00000ddddddddddddddddcfcfcfcfcfcfcfcfcf00cf00cf00cf00
  | 0, 12 => 0xeeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecceeccaa00eecceeccaa00aa00eecccccceecccccceeccaa00eeccaa00eeaaeeaaeeaaeeaaee00ee00ee00ee00ee00ee00ee00cc00ee00ee00ee00aa00ee00ee00aa00aa00ee00aa00ee00aa00
  | 0, 13 => 0xf0f00000ffff0000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccceeeeeeeeaaaaaaaa
  | 0, 14 => 0xf0f0f0f0f0f0c0c0f0f0f0f0f0f0c000f0f0f0f0f0f0a0a0f0f0f0f0f0f0a000f0f0f0f0f0f08080f0f0f0f0f0f05050f0f0f0f0f0f03030f0f0f0f0f0f000f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0e0e0f0f0e0e0f0f0e0e0f0f00000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0
  | 0, 15 => 0xf3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0fff0f0f0f0f0f0f0fcfcf0f0f0f0f0f0fafaf0f0f0f0f0f0f5f5f0f0f0f0f0f0f3f3f0f0f0f0f0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0
  | 1, 0 => 0xfaf0faf0aa00aa00faf0f0f0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00fa00fa00fa00aa00fa00fa00aa00aa00fa00aa00fa00aa00f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f8f8f8f88888f8f8f8f8f8f80000f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3
  | 1, 1 => 0xfafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafa0000fafa0000faf8faf8faf8faf8faf8faf8faf80000faf0faf0faf0faf0faf0faf0faf0fa00faf0faf0faf0f0f0faf0faf0faf0aa00faf0faf0faf00000faf0faf0f0f0f0f0
  | 1, 2 => 0xfefefefefefe0000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafa
  | 1, 3 => 0xff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff008800ff00ff00ff000000ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00ff00fa00ff00aa00ff00aa00ff00aa00aa00aa00ff000000ffff0000ff000000ff000000ff00000000000000fefefefefefefefe
  | 1, 4 => 0xff33ff33ff33ff33ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff05ff05ff05ff05ff00ff55ff00ff55ff00ff00ffffffffff00ff00ff55ff55ff00ff00ff00ffffff00ff00ff00ff55ff00ff00ff00ff33ff00ff00ff00ff00ff00ff00ff00fc00ff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00
  | 1, 5 => 0xffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff88ff00ff88ff00ff55ff55ff55ff55ff55ff55ff55ff00ff55ff00ff55ff00ff50ff50ff50ff50ff44ff44ff44ff44
  | 1, 6 => 0xffccffccffccffccffccffccffccff00ffccffccffccccccffccffccffcc0000ffccffccff00ff00ffccffccccccccccffccff00ffccff00ffccff00ff00ff00ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000
  | 1, 7 => 0xfffafffafffafffafffafffafffa0000fffa0000fffa0000fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff00000fff0fff0ff00ff00fff0fff000000000fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeeffee0000ffee0000ffee0000
  | 1, 8 => 0xffff5555ffff5555ffff3333ffff3333ffff0f0fffff0f0fffff00ffffff00ffffff0000ffffffffffff0000ffff0000ffff0000f0f00000ffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffcfffcfffcff00fffcfffcfffc0000fffcff00fffcff00fffc0000fffc0000
  | 1, 9 => 0xfffff0f000000000ffffeeeeffff0000ffffccccffffccccffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffff8888ffff8888ffff8800ffff8800
  | 1, 10 => 0xffffffccffff0000ffffffaaffffffaaffffffaaffff0000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffefeffff0000fffffcfcfffffcfcfffffcfcffff0000fffffafafffffafafffffafaffff0000fffffafa00000000fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0
  | 1, 11 => 0xffffffffa0a00000ffffffff88888888ffffffff88880000ffffffff55555555ffffffff55550000ffffffff33330000ffffffff11111111ffffffff0f0f0000ffffffff05050505ffffffff00ff00ffffffffff00ff0000ffffffff00000000fffffffaffff0000fffffff0fffffff0ffffffeeffff0000ffffffccffffffcc
  | 1, 12 => 0xfffffffffafa0000fffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeeee0000ffffffffeaea0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a0a0a0
  | 1, 13 => 0xffffffffffff8888ffffffffffff8800ffffffffffff5555ffffffffffff3333ffffffffffff1111ffffffffffff0f0fffffffffffff0505ffffffffffff00ffffffffffffff0000fffffffffffc0000fffffffffff00000ffffffffffccffccffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafafafa
  | 1, 14 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff000ffffffffffffeeeeffffffffffffccccffffffffffffcc00ffffffffffffc0c0ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x455427738eaa0d6711541f0e22a13f9c495077388a94fe7d7471acef68e3b9f5d1e6b3
  | 3, 0, 0 => 0x7a284ee614f0c45507f4eba3cc25c48939d50774ebc4950774ebc81506b4bdc75507f4a2459507f4c544950774ebc554a7f48eaa0c25c49fb9d407f47a2e950614bcbd14a7f4ebc49507f49e39d4a7f4
  | 3, 0, 1 => 0x762a0ee614a23d140784ebc55507c4893d150774ebded1c7f4ef455507f4ebd1254bb4bdc7950774f0c5550774ebc55427f485b9d50774bcbd1507c49e39d507c4a239d4079473aa0ee6b4ebded1e7f4
  | 3, 0, 2 => 0xebbd1506d473aa0ee61488aa0ee614a239d50784a2475506c4a23d174584ef3d1967f4ebc51507f4892a0fe774ebc79506b4f5c45507f40044950773892a0ee614a2449507747a348c2584ebded76a84
  | 3, 0, 3 => 0xebad8c2584ebd111e6c4a239d1c774
  | 4, 0, 0 => 0xd2511e8a83faf5e8920541b17af447baa0febd7a2371507f5ebbd1507f35af5e88fa541fd7af3e76aa0fea00ebc49507f4ebdf1e8a53faf5e24a83f9857aea83f98490bd7bdb9d507f5ebc29e8a83faf5de8a83f9897af449522cfebd7ab3d1507f5
  | 4, 0, 1 => 0xebd69cea83faf5e88ef541fd769907a32cfebd7bdaa1167f5ebd51cea83fae91e8a83f9857af387a2a0febd7a23a5507f5ebcfddea83faf6688f4541fd7af4478a94febd78ac31507f5e4d11e8a83fad11e8ba541fd7af4489aa0febd77a2a0fe655
  | 4, 0, 2 => 0xebd1166a83faf5e16f4541fd7d73c73aa0feb96a239d507f5ebd11e8bd3faf5de8c2541fd7af0c73aa0febd777aa0fe615ebbd1507f34af5e88f4542017af4454234febd773aa0fe2d5f2511e8a03faf25e8a83f9856891d541fcb8bd789aa0fe615
  | 4, 0, 3 => 0xa2475e88f3faf5de8c1541fd7aef4541e8c2bd7a2441507f5ebda5e8a83faf5e88e7479fd7af657a2a0febd77a2a0c25d5ebd11d6a83fadc688f4541fd7af4473a94febd7be5111e7f5ebbd1507f1eac7618f4541fd7af447a27cfebebbcbd1507f5
  | 4, 0, 4 => 0xebd11e2a83faf5ef0f4541fd7af447faa0febd7a22d1507f5cf5116ca83faf5de8a83f99d7af44812a0febd7a23d178585ebd11e8b9542f5eaef4541fd7aef465a4cfebd7882a0fe615ebd11e8a840af5e90f4541fd7af44822a0febd7a1bd1507f5
  | 4, 0, 5 => 0xa23d140772c2f5e88f4541f57aef4642a0febd7a223cfe5c5ebd11e8ca3faf5f2715541fd7ad447a2a0febd7a2455507f5ebbc5507f30af5e8911541fd7af44752a0febd7a5bd1507f5ebc09507f30af5de8a83f98d763447a2a0febebebc55507f5
  | 4, 0, 6 => 0xebd09e8a83faf5e2aa83f9556891d7a2a0febd7863d11e7f5ebcf1e8a83e2f5e88b6541fd7af687a2a0febd7a23d140795ebd11cea83faf5e88f4551fd7af3f73aa0febd7b23d1507f5ebbd1947f30af5e2aa83f9857af11541fcc2bd77a2a0fe605
  | 4, 0, 7 => 0xebd11e8a63faf5e88f4541ed7aef45baa0febd7a238d507f5eed11cea83faf5edce7541fd7af4473a38febd7a9bd1507f58ebd1507f30af5ef6f4541fd5e8d2622a0febd7a239d447f5ebad9507f30ad123ce7541dd7af3573aa0febd773aa0fe615
  | 4, 0, 8 => 0xc539d507730af5e18f4541fd7b7447a2a0febe4a239d507f5ebdf1e8a83e2f5e7ce7541fd7af4477aa0f2bd77a2a0fe2d5ebd49e8a83faf5eb4f4541fd7aef4541843abd7a239d76a85ebd51e8a83faf5de8a83f8b97aef4541fc76bd7b7bd14a7f5
  | 4, 0, 9 => 0xebbd11e7f30adb288e7541fd792f4622a0febd77a294fe615ebce9e8a83faf5de8a8439fd7af4478aa0f8bd7a23d11e7f5e4511e8a83faf5e8af4541fd7af15541dcc2bd7a23d14a7f5ebc8150612e2d12591d541fd7af44782a0febd7babd1507f5
  | 4, 0, 10 => 0xebd11e8a83f2f5de8c73f9857af837a2a0febd7a239d507c5ebd11dca83fad11a4b3541fd7af447a31cfebd7a23d15e7f5ebd122ea83faf5de8cb3f9557af7b902a0febd7acbd1507f5ebdb9e8a53faf5e88f2541fd7af4e7a2a0febd773aa0ee615
  | 4, 0, 11 => 0xebdb9e8a83faf5e88f4471fd7af447aaa0febd77a2f150615ebd11e8a23faf5f1512541fd7aef4541fcc2bd7a239d50795a23d1a47f2c2f5e892c479fd7af447a2a0febd77a2a0f2605ebcfde8a83fad11cea83b9616c14473aa0feb9ea2389507f5
  | 4, 0, 12 => 0xda62a888f362f5dcec4541fd7af447a294f8bd7a23d176a85a23496ca83fad11ced2541fd7aefb541fcc2bd78939d507f57a2a1407730af5eece7541fd7af448423cfebd7b5b9d507f5ebd11f6a83faf5de8c9541fd6f6e7541fceebd77a288fe615
  | 4, 0, 13 => 0xebd11e8a13faf5e88f4539fd7af3e7a288febd7a23d12c7f5ebdbde8a83e2f5e88fe541fd705447a2a0febd7d6455507f5da6296c612c2f5e1ef4541fd7af44832a0febd79f3d1507f5ebd11eca83faf5e88f4541e17aec45b2a0febd79b3d1507f5
  | 4, 0, 14 => 0xef3d1507f30af5dcea83f9ad7af08541fcc2bd77a354c2585d4511e8a83faf7a88f4541fd7af447caa0febd7a2421507f5f0bd1507730abd1cea83b9857aef4541dcc2bd796bd1507f5ebbd1427f30af5de8a8411857af4d7a2a0febd7a239d7c7f5
  | 4, 0, 15 => 0xa239d507f3baf5e88f4541e57af0b73aa0febd79fbd150795ebd45e8a83fad11cea83f8c5688e7541dcc2bd79ebd1507f5ebbd1507c30af5e88f4549fd7698a892a0febd7a23d1506e5ebcd1e8a83faf5e88e8541fd7494473aa0febd7a23d1507c5
  | 4, 1, 0 => 0xebd11d8a83fadfa88f4541fd7490c7a2a0febb4c8455507f5ebd12548c3faf9688e7501fd7af7b8f2a0febd77a2a10a7f573aa0fe7730af5ecae7541fd7aef4541e4c2be1ebc55507f5ebd120aa83faf5f02f4541fd7af447c2a0fea0073aa0ee614
  | 4, 1, 1 => 0xebbb5507f30abd1a4a83f985767447a2a0febd7a241d507f5d2511e88f3faf5e80f4541fd7aeec541fcc2bd7a22a0fe525ebbd188a83faf5e8cf4541fd7af447a290febd7a23b5507f5a23d1a4a83faf5e24f4541fd7af3c7a294febd7a22d8fe585
  | 4, 1, 2 => 0xda6291e612e2f5e88a83f9216891d73aa0febd78aaa1267f5ebd116aa83faf5e88f45f1fd7aef461aa0feb7ca2475507f5ebd41e8a83faf5de8b0541fd7af3f7a280febd7bdbc5507f5a24bde8a83faf5e88f3541fd7af7b54230febd7a23b5447f5
  | 4, 1, 3 => 0x1d7a2449507f5
  | 5, 0, 0 => 0xda62ad0f4541fdbafb4a23c5507f6da62a88e7541fdb718aa23d1507f60075ef6e7541fd7afb4bc3d1507f6ebe7e88f4541fdbaf4498bd1507f6da62ac8f4541fdbaf449e3d1507f6da62a8903541fdb6980a23d1507f6cf62a88f4541fdb698a8aaa0fe616ebd123cf4541fdb697da23d1507f6
  | 5, 0, 1 => 0xebd1250f4541fdbaf97a23d1507f6ebcf1e8a83f985b698a8aaa0fe556ebd11e8cd541fdbafc39c3d1507f6e6e2aecf4541fdbaf447a2a0fe216ebd11e8a83f869baf449539d507f6ebd2688f4541fdb698a863d11e7f6cf511e8d5541fdbaf447a2a1147f6da62a88b6541fdbc5d7a23b5507f6
  | 5, 0, 2 => 0xda629e8a83f8f1bafc5a23d1507f6ebd11e8a83f9d5801a4a23d1507f5c5511e8a83f8d5baf447a2a0fe196da6296ca83f985baf4473aa0fe706ebd126ee7541fdbaf449c3d1507f6ebd1246f4541fdbafb4a2455507f6da629cea83f985baf447a2a0fe326dd62a88f4541fdbaf447a2a1407f6
  | 5, 0, 3 => 0xebe2a7ef4541fd801d79c3d1507f5ebd11e8a8461fdb698aa238d507f6e362a88f4541fdbafb48aaa0fe616ebdade8a84e9fdbaef4541fcc2326da629e8c6541fd801c9a23d1507f5ebbd150a03f985baf447a345507f6ebe5de8a83f985bcbd7a239d507f6ebd11e8a83f89db698abdbd1507f6
  | 5, 0, 4 => 0xebd11e8a83f8d9b69447a2a0fe716ebdb9e8a8501fdbaf447a2a0fe296ebed288b6541fdbaf447a35d507f6ebd11e8f1541fdbaf5fa23d1507f6ebe2a88f4541fdb698a7a2a0fe646ebed288e7541fd801d7a23bd507f5ebd11e8a83f86dbaf9da23d1407f6da629e8b7541fdbafbca23d1507f6
  | 5, 0, 5 => 0xf5f5ef8f4541fdbafb473aa0fe616ebd11e8a83f82dbaf72a23d1507f6ebdde88f4541fdb69447a2e1507f6ebd11e8a83f829baf447a2a0fe026ebd11e8d5541fdbaf94a23d1507f6ebd11e8a83f96dbaef454230fe616da5123af4541fdb4944903d1507f6e3629e8a83f985baf44983d1507f6
  | 5, 0, 6 => 0xebd11cea83f83dbaef46aaa0fe616ebda688f4541fdb15447a2a0fe4f6ebd11e8a83f8e5baf447a2a0fe496ebed2f6f4541fdbaf447a2a0fe246da629e8a830875b698aaa3d1507f6ebe2a88f4511fdb69447a2a0fe3e6ebd122af4541fdb698a7a2a0fe2e6ebe2a6af4541fdbaf8a7a2a0fe616
  | 5, 0, 7 => 0xda62a18f4541fdbaf447a381507f6ebd1232f4541fdb6988a23d1507f6ebd11e8a83f975baf4486bd1507f6da62aaaf4541fdbaf157a2a0fe616ebf1a88f4541fdbaf448c3d1507f6da62aa4f4541fdbaf8ab73d1507f6ebdf288f4541fdbaf447a365507f6ebd8688f4541fd801d7a22a098325
  | 5, 0, 8 => 0xebd11e8a83f821b154467ad9507f6c5511e8ad541fdb698ababd1507f6f5f5e88f1541fdbaf7c7a2a0fe616ebbd1b2a83f985801d7b4bd1507f5ebd11e8a83f9e9baf6fa239d507f6ebe2a88fb541fdbaf447a2d9507f6f0f5e88f4541fdb778aa23d1507f6ebd11e8e7541fdbafd7a23d1507f6
  | 5, 0, 9 => 0xda64288f4541fdb69afa23d1507f6e5e2a88f4541fdb69a6a23d1507f6ebde288f4541fdb698aa23d14a7f6ebd11e8a83f9a1bc3d77a2a0fe616ebd11e8a83f825b69ada23d1507f6ebbd1cea83f985bafd77a2a0fe616ebe6e88f4541fdb698a902a0c25c60075e88a83f8c97af447a2a0fe446
  | 5, 0, 10 => 0xda46218f4541fdb698a9d3d1507f6da629e8a8439fdbaf4493bd1507f600511507f190257af6f7a2a1267f6ebe4688f4541fd801d7541fcc2325ebe1688f4541fdb698aa23d11e7f6da62a890e541fdbaf447a2a0fe456da68688e7541fdb6998a23d1507f6ebd11e8a83f92dbafb4aa3d1507f6
  | 5, 0, 11 => 0xda629e88f3f985b698a872a0fe616ebd11ced8541fdbaf447a2a0fe156e0ed31515541fdbafb4863d1507f6ebd11e8a8459fd801d7a23c5507f5da62a12f4541fd801d7bc3d1507f5ebe2a7cf4541fdb69907a2a0fe616ebd1258a8461fdbaef4541fcc2096ebd9a88f4541fdbbbd7a23d1507f6
  | 5, 0, 12 => 0xebd11e8a83f919bafa7a23d1507f6ebf0e88e7541fdbaf447a2a0fe016ebd1202f4541fdb698aa73d1507f6dce2a88f4541fd801d7541fc64235ebe9688f4541fdbaf4473aa0fe336ebd11e8a83f8bdbafb6a23d1507f6f5f5e88e7541fdba58aa23d1507f6da65a88f4541fdbaf857a2a0fe616
  | 5, 0, 13 => 0xebd11e8a83f971baf447daa0fe096ebed288f4529fdb698aa245d507f6da659e8a83f985b69448c3d11e7f6da629e8cb3f955baf447a2a1207f60075e887f208c97afd4a23d1507f60075e8915541fd7af447a385507f60075e88e7541317af447a2a0fe0d6ebd122aa83f985b698aacbd1507f6
  | 5, 0, 14 => 0xebd11e8a83f979bddd7a23d1507f6ebd11e8a83f961baf5ba23d1507f60075e2aa83f9857af447a2a0fe4e6da62a94f4541fdbaf44993d1507f6ebed288f4479fdb154473aa0fe746ebd11cea83f931bafa1a23d1507f6da62a88f4639fdb698aa23d15e7f6ebd11e8a84f1fdba58a7a2a0fe616
  | 5, 0, 15 => 0xebf4a88f4541fdbaf7ba23d1507f6ebd11e8a83f94dbaf8a7a2a0ee616ebd11e8de541fdbaf327a2a0fe616ebd1258e7541fd801d7a22d9507f5f275e88f4541fdb698a7a31cfe6160075e88e7541fd7478aa23d1507f6ebd8e88e7541fdb698a7a301507f6ebd11cea83f985baef4541fcc25c6
  | 5, 1, 0 => 0xebd11cea84c1fdbaef46f2a0fe616da62a7ef4541fdb7b8aa23d1507f6ebdf28920541fd8014473aa0fe095da67a88f4541fdbafa2a239d507f60075dcea83f9857af4473aa0fe236ebd11e8a83f815801448ebd1507f5ebbd1507f30979baef4541fcc2586ebe2a8908541fdbaf447a2a1267f6
  | 5, 1, 1 => 0xebd7a88f4541fda89208ebd1507f60075ea8f45413176944973d1507f6ebd11e8a83f959b6b8aa23d1507f60075dcea83f88d78d447a2a0fe706ebe2a88f4541f1baf449039d507f6ebd1254f4541fdb698aa24b11e7f6ebe3688f4541fdb698aa23d1507f60075ef6f4541fd7aef45424cfe616
  | 5, 1, 2 => 0xf2f5e7ef4541fdb698a7a2f150616da62a88f4511fdb15447a2a0fe266ebdb288f4541fdb698a7a2a0fe6a60075e88e73f9057bfd7a23d1507f6f075e88f4541fdbaf447a2a1327f6ebd5288f4541fdbaf447a2a0fe706ebd11e8cc541fdb698a9abd1507f6da629e8a83f985b694499bd1507f6
  | 5, 1, 3 => 0xebd1218f4541fd801d7aa3d1507f5ebd3e88f4541fdbaef4541fce0616ebd11e8a8419fdbaf447a2a0fe1d6da51230f4541fdb698ab73d1507f6ebf2a88f4541fdb7f8aa23d1507f6ebd11e8a83f849baf447a2a0fe116ebd11e8b1541fdbcbd7a23d1507f6ebd11e8a83f969baf547a2a0fe4c6
  | 5, 1, 4 => 0xebe2a88f4541e5801d77a2a0fe1d5ebe2e88f4541fdbaf9da239d507f6da62a8908479fdb69187a2a0fe616f175e88e7541fdbaf5da23d1507f6ebeba88f4541fdbafc0a23d1507f6ebd11e8a83f965b698aa23ed507f6ebd11e8d4541fdbcbd77a2a0fe616ebd11e8a83f9bdbd7d7a23d14a7f6
  | 5, 1, 5 => 0xf5f5edef4541fdbafcca23d1507f6ebd11e8a83f83dbb9d7a23d1507f6da62988b6541fdb698a9b3d1507f6ebd8288f4541fdb6999a23d1507f6ebd11cea83f905baf44902a0fe5c6ebbd1507f30965baf447a36d507f6ebed26af4541fd801d7863d1507f5ebeca88f4541fdb154473aa0fe776
  | 5, 1, 6 => 0xc5511e8cf541fdbaf6fa23d1507f6ebc8218f4541fdbaf447a2a0fe346ebbd1507f3083db69acc5455507f6ebd1244f4541fd801d7a23d11e7f5ebd11e8f4541fdb3d447a33d507f6da62a1ef4541fdb698a9f3d1507f6ebdd288f4541fdbaf447a2a0ee5860075e88f4529fd7af447a2a1287f6
  | 5, 1, 7 => 0xebd11e8a83f871baf8aa23b5507f6ebeb278f4541fdb15447a349507f6ebdbde8a83f985baf447a2a0fe106d251234f4541fdbafcda239d507f6da62a88f44b1fdbaf44842a0fe586dbe2a88f4541fdbaf4473aa0fe776f4f5e88f4541fdb698aa23f9507f6da62a88f44d9fdbaf8ab5bd1507f6
  | 5, 1, 8 => 0xebd1e88f4541fdbaf447dbd1507f6da629e8a83b985baf447a361507f6da62a5af4541fdbaf447a2a14a7f6da685e8a83f985baef46ab11507f6ebd11e8a8441fda88f46ab49507f6da62a9af4541fdbaf44903d11e7f6ebf0a88f4541fdbaf8a7a311507f6da68688f4541fdb14f467aa0fe616
  | 5, 1, 9 => 0xebe4e88f4541fdbaf44a23d1507f6ebd11e8d2541fdbb1d7a23d1507f6ebd11e8a83f8fdbaf4ca23d1507f6ebd127ef4541fd801d7a23d1504c5da629e8d530961baf447a2a11e7f6ebd1242f4541fdbaf447a2a0fe436ebd11e8cb541fdbaf447a2a0fe336f5f5e88f4541fdb698aa2421507f6
  | 5, 1, 10 => 0xebd11e8dd541fd801d79fbd1507f5ebd11e8a83f8a1801447a2a098095ebd11e8a83f9cdb6970a23d1507f60075de8a8309317af6aa23d1507f6da62a88f4541f1baf447a2a0fe4c6ed75e88f4541fdbaef465aa0fe616ebd11e8a83f9d9bd7d77a2a0fe616da62a10a83f985bd9d7a23d1507f6
  | 5, 1, 11 => 0xebd11e8a83f9fdbaf8abdb9d507f60075de8a82608d7af7fa23d1507f6ebde1e8e4541fdbcdd7a23d1507f6ebd11e8a83f801baf44963d1507f6ebbd1507f30931801d7a23d1507f5da62a88f4541b9b698a9a3d1507f6ebd11e8b2541fdbaf63a23d1507f6ebe4de8a83f985baf447a2a0fe616
  | 5, 1, 12 => 0x75e88f4511fd401d7a23d098415ebeb2f8f4541fdbaf2c7a2a0fe616ebd11e8a83f8ad801447a2a0fe095ebe8a88f4541fd801d77a2a0fe615ebd11e8a83f88dbaf447a2a0fe556ebd11e8a84e1fdbaf447a2f1507f6ebd8de8a83f985baf6ea23d1507f6ebbd1507f30985b2d447a2a13a7f6
  | 5, 1, 13 => 0xebd1276f4541fdbaf84a23d1507f6d262a88f4541fdbafa27a2a0fe6160075edcf4541fd7aef4541fcc2236ebbd1507f30955baf447a34d507f6ebd1240f4541fdb698aa8bd1507f6ebd1256f4541fdbaf447a369507f6ebbd1507f3f985baf447a2a1307f6ebd1236f4541fdbaf447a2a12e7f6
  | 5, 1, 14 => 0xebd1210f4541fdbd5d7a23d1507f60075e88a83f8cd7698ac0bd1507f6ebd11e8a83f91dbaf207a2a0fe6160075e88f43f9057af447a2fd507f60075e88fb541fd7af447a2a0fe506ebbd150983f985b698aa23d150796ebea688f4541fd801d77a2a0fe235e1511e8de541fd800f4541fcc2095
  | 5, 1, 15 => 0xf2f5e88f4541e5baf447a2a0fe4a60075de8a83f941401447a1fc8209500511f6a83f825401d77a1fcc2415ebd127cf4541fdbaef4541fcc2506e7e2a88f4541fdb698a7a2a10a7f6ebd11f8f4541fdbaf8aa23bd507f6003d1507f11825688f454280fe776ebd11cee4541fdbaf447a2a1507f6
  | 5, 2, 0 => 0xf475e88e7541fdb698aa22d8fe5860075de87f2088d401d79f3d1507f5ebe3a88f4541fdbaf9da23d1507f6da62ad6f4541fdbc5d7a23d1507f6ebd11e8a8491fdbaf4494bd1507f6ebd11e8a83f8ddbaf447a2a1447f6da629e8a83f999baf447a2a0fe1e6ebd11e8a83f8a9bdbd7a23d1507f6
  | 5, 2, 1 => 0xd0d11e8a83f9d1baf447a399507f6da62a88a83f949baf447a2a0fe416f175e88f4511fdb698a7a311507f6ebe75e8a83f985bafaca239d507f6e362ad2f4541fdbaf447a280fe586a23d19ecc541fdbc5d77a2a0fe616da62a88ed541fdbc7d7a23d1507f6da62aecf4541fdbaf447a2a10c7f6
  | 5, 2, 2 => 0xebd1282f4541fdbd7d7a23d1507c6c53d1507f3085dbaf447a230fe586ebd125920541fdbaf447a2a1047f6ebd11e8a83f819baef4541fcc2416ebd11e8a83f851baf447a2a0fe316ebd11e8a83b985b69447a37d507f6ebd11e8a0499fdbaf8ab4bd1507f6ebd11e8a83f889b15447a2a0fe176
  | 5, 2, 3 => 0xebd11c8de541fdb698a8aaa1267f6ebd11e8a83f8e1baf447a2b1507f6ebde688f4541fdbaf448fbd1507f6ebd11e8d53f961801d7a2421507f5da62aa0f4541fdbaf449e39d507f60075de8a83b9857698a7a2c1507f6ebed2ecf4541fdbaf448f39d507f6a23d1cea83f9ddbaf447a2a0fe776
  | 5, 2, 4 => 0xebdf288a8461fdb698abdb9d507f6ebcf1e8a8499fd801d7a23d1507c5f175e7cf4541fdbcbd7a23d1407f6ebd11cea83f8c9baf447a2a1087f6ebd11cea8501fdb698aa22a0fe486ebd11e8a83f8e9baf447a2b9507f6ebd11e8a83f95dbaf449cbd1507f6ebbd1507f3b985baf447a2a0fe0e6
  | 5, 2, 5 => 0xebd124cf4541fdbaf446aad9507f60075e88a83f8c57af4473b55507f6ebd11cea83f96dbaf447a2a0fe5f6ebd11e8a83f935b14f467b11507f6da62a8920541b1b698aa2371507f6ebd8a88f4541fdbaf447a3b5507f6ebd11cea8461fdbaf447a2a0fe7c6da629507f30921bab8aa23d1507f6
  | 5, 2, 6 => 0xebf5e88e7541fdb698aa22a11a7f6ebd11e8a83f9e5baf67a23d1507f6ebdf288e7541fdbaf4473b65507f6ebd11e8c5541fdbaf447a2a0fe04600511cea83f9dd7aef4541fcc25f60075e88f4541e57698aa23bd507f6ebd11e8a83f87dbafa0a23d1507f6ebd6288f4541fdb698a8ac31507f6
  | 5, 2, 7 => 0xebd11e8a83f909bcfd7a23d1507f6ebd11cea83f825b698abe5111e7f6f7f5e88f4541fdbaf7c7a2a1267f6ebd11e8a83f945baf4454230fe5c6f2f5e88ef541fdbafc4a23d1507f6ebd123af4541fdbaf447a2a0fe546ebeb2def4541fdbaf447a2a0fe076da62a88f45e9fdbaf4473b9d507f6
  | 5, 2, 8 => 0xebd11e8a8519fdbaf44803d1507f6a246a30f4541fdbaf95a23d1507f60075de8c4541fd7af4473aa1167f60075e88ed541fd76992a23d1507f600511e8d2541fd7af6da23d1507f6ebe1688e7541fdbaf447a2a0fe6c6da629e8a830975baf7b7a39d507f6ebd11faf4541fdbaf447a311507f6
  | 5, 2, 9 => 0xebdea88f4541fdbaf447a3bd507f6da62a88f1541fdb698aa23fd507f6ebeb288f4541fdbaf447a2a12a7f6ebd11e8a83f8b1baf4473aa0fe5c6ebe7288f4541fdb698aa2409507f6da62a88f45e161b698aa23d172a86f475e88f4541fdb69927a2a0fe616da629e8cb499fdbaf447a2a0fe036
  | 5, 2, 10 => 0xebd11e8a8449fdbaf447a2a0fe406da62a888f3f971baf4473aa1267f6ebdee88e7541fdbd7d79e3d1507f6ebeaa88f4541fdb698aa2455507f6ebeb1e8a83f985baf447a2ad507f6da62a96f4541fdbaf4473aa0fe586da62a04a83f985bd1d77a2a0fe616
  | 6, 0, 0 => 0xda62a88f4541fca6fb4c5511e8de541fdf698a993d1507f30b803698aa22d9507f6006d3154473aa0fedb4c53d1507f30971c01d7a24f1e8a83fb6d315447a2a0fe5e7da62a88f4541fcb0fb4c5511e8a83f859f698aadd11e8a83fb803698a8aaa0fe616da62a88f4541fc9ce00a23d1507f07839b698aa24c9e8a83fbf5f6985a23d1507f7
  | 6, 0, 1 => 0xda63715447a2a0fefd7c5511e8a83f931f698a7a2a1267f30bf5f69447a2a0fe5c7da629e8de541fcc2fb4c55f28920541fdc01d7c5511e8a8263003af447a2a0fe3260075e88f454280fedd7e1e2a88f4541fdc01d7cbd11e8a83fb6d314f4541fcc25e7da629e8a83f984b0febebe2a88f4541fdf698aa23d150933fbf4b698aa23d1507f7
  | 6, 0, 2 => 0xebe2a892c7a2a0fefb4c5511e8a84c9fdf698aaa511e8a83fbed315447a2a0fe707da62a88f4662a0fee00ebe2a88f4541fd801d7da511cea83fb75f1563a23d1507f7da62abd447a2a0fefd7c5511e8a83f985c01b4c5551e8a8263003af447a2a1187f6da62a88f4541fcacfd7da511e8a83f961c01c6c5511e8a83fb75f6944993d1507f7
  | 6, 0, 3 => 0xebe8b15447a2a0fee00ebe29e8a83f985b698aa23d1a0a83fbf5f15447a2a0fe237e56d315447a2a0fefb4c5511e8a83f849f698aa23d1507f08bf1b15447a2a1307f7da511e8d5662a0fee00ebd11e8d5541fdb698aa23d162a83fbf97698aa23d1507f7da62a88f4541fcb4fb4c5551e8a83f931fafb4a23d150933fbf5f69447a379507f7
  | 6, 0, 4 => 0xda62a88f4541fcb2e00ebdf288f4541fd801d7a23d1b2a83fb75f1544903d1507f7ebe2a88f4541fce8fb4da62a88f4541fdf698aa23d1507f37bf5f15447a2a1307f7da62a890c7a2a0fee00da62aa8f4541fdb698aa7d11e8a83fbed315447a2a0fe7270062a88f4541fc12db4c53d1507f38185f698aa23d150833fbed315447a2a0fe1d7
  | 6, 0, 5 => 0xda62a8920541fcb8fb4c53d1507f30965f698aa23d150913fb803af8aa23d0fe416da62a88f46daa0fefd7da5126ef4541fdc01d7a23d1cea83fb003afd7a23d1507f6006d3150c7a2a0fedb4d962a88f4541fdc01b4c53d1507f0eb6d3178aa23d1507f70075f14f4541fc46db4c557688f4541fdf69aec5511e8a83fbf03698aa23d1507f7
  | 6, 0, 6 => 0xda62adf447a2a0fefb4c548218f4541fdf698aa23d1507f1a3ed314f4541fcc20f7da62a89227a2a0fee00ebe1688f4541fd801b4c5511e88f3fb6d315447a3d1507f7ebed369447a2a0fefb4c55d288f4541fdc01d7a23d1507f04b6d315447a2a1287f7e66d315447a2a0fefb4c5511e8a83f83dc0000ebd11507f192f97afb4a23d1507f7
  | 6, 0, 7 => 0x75e88f4541fcb8db4c551240f4479fdf85b4c5511e8a83fbf5f69447a2a0fe0f7ebe2a88f4541fc82fb4c5511e8a83f871f698aa23d1507f09bed3156f7a2a0fe6170074b15447a2a0fedb4c5511e8a83f841c01b4cb511e8a83fb6d31573a23d1507f7da62a8908541fcb0fd7cee2a88f4541fdfc5d7c5511e8a83fbf0b15447a2a0fe707
  | 6, 0, 8 => 0x6d315447a2a098dd7c5511e8a83f9ddc0000ebd11cea83faed3358aa23d1507f7e1ed315447a2a0fefb4c5511e8a8479fdfaf8aa23d1509d3fbed3154490bd1507f7da62a88f4541fc86fb4c5511e8cb541fdc01d7a23d1507f2c37af698aa23d1507f7ebed2df447a2a0fee00ebd1264f4541fdb698a7a35588a83fbed315447a2a1107f7
  | 6, 0, 9 => 0x6d288a83f8c830dc3da629e8a83f985f698aa23d1507f263f47698aa23d1507f7da629e8cb541fcc2fb4c5511e8a83f9d9f6993c5511e8a83fbed31544a23d1507f70075e88f45424cfedb4a23d1bca83f9c1c01d7a23d1bca83fb6d315447a2a0fe307da62a88f4541fc7efd7da511e8a83f861f698aa6511e8a83fbed315447a2a0fe257
  | 6, 0, 10 => 0xda62a88f4541fc00e00c5511e8a82603db698aa24b1e8a83fbed314f4541fcc24c7e86d315447a2a0fee00da62a88f4541fdb698aa23d164a83fbed31563a23d1507f7da64f14f4541fcc2fb4c55126af4541fdf698aa23d1507f30bed315447a375507f7da62a88f4541fc50fb4c5511e8a83f9cdc01b4c53d150612636d3156aa23d1507f7
  | 6, 0, 11 => 0xda68b15447a2a0fee00da62a6af4541fd801b4c53d1507f30b6d315447a2a0fe237da62a88f4541fcaafb4c5511e8a84e1fdf698aa23d178a83fbed315637a2a0fe617da629e8a83f984c2fd7e1ed288f4541fdf698aa23d1507f3fbed31f8aa23d1507f70062f15447a2a0fec00da629e8a82608db698abfd11e8a83fbed315787a391507f7
  | 6, 0, 12 => 0xda629e8a83f98446fb4c53d1507f30955f698aa2481e8a83fb80315447a2a0fe0f6da62a88f46d2a0fefb4c53d1507f3f985c01e5ebd11e8a83fb75f8f8aa23d1507f7da62a88f454260fefb4c551236f4541fdf698aa23d150973fb803698aa23d098416da6b3157c7a2a0fefb4c54b1e8a83f985f698aa23d1507f15b803af447a2a0fe706
  | 6, 0, 13 => 0xda62a88f4542a0fefb4c551210f4541fdfafcec5511e8a83fbed315447a2a0fe477da62a40f4541fcc2e00c53d1507f3083d801b4c5511e87f20b6d315447a2fd507f7da62a88f4541fca0fb4c53d150983f985f69a9c5511e8a83fb803698a7a2a0fe236da62a893b7a2a0fefb4c561288f4541fdc01b4a2461e8a83fb6d3458a7a2a0fe617
  | 6, 0, 14 => 0xda67715447a2a0fee00c5511e87f2083dbc5b4c5511e8a83fbed315447a2a0fe3770075e88f4541fc1edd7da511e8a83f9d1f698aa23d1507f0f3ed315447a2a0fe2a700629e8a83f88c1edb4c5511e8a83f929f694490461e8a83fbf3715447a379507f7006d314f4541fca0c00da629e87f30905b698a7a2a0fe61283ed315447e3d1507f7
  | 6, 0, 15 => 0xda62a89257a2a0fefb4c5511e88c3f961f698aa24b240a83fbed314f4541fcc2417da62a88f4541fc28e00da68688f4541fdb698aa23d1cca83fbed315447a2a0fe417da67714f4541fcc2e00c5511e8cf541fd801d7b7d11e8a83fb6d3618aa23d1507f7da62a88f454218fee00da629e87f2088db698aae511e8a83fbed31d8aa23d1507f7
  | 6, 1, 0 => 0x3af447a2a098bb4c5511e8a83f839f698aa2391bca83fbed315447a2a0fe387ebeb315447a2a0fefb4c5511e8ac541fdf7db4c5511e8a83fbed315447a354fe587007afaf447a2a0fec00da62a8908541fdb69aba24dde8a83fbed3198aa23d1507f7da62a88f454268fefcdda62a88f4541fdfd1d7c5511e8a83fbed315447a2a0fe777
  | 6, 1, 1 => 0x75f45447a2a0fec000075de8a83f985401d7a23d1507f11b75f15449e3d1507f70075e892c7a2a0fec000075e88f4541fd401d7b1d11e8a83fb003af447a2a0fe616da62af94454230fee00ebd11e8a83f931b698ac3d11e8a83fbed315447a2a1087f7ebf4f15447a2a0fefb4c5511e8a83f8e9f698aa23d15ca83fbed315449cbd1507f7
  | 6, 1, 2 => 0x3af447a1fc82bb4c5511e8c5541fdc0000ebbd1507f11ae2a88f4541fc30177da62a88f4541fc3efb4d062a88f4541fdc01d7a2481e8a83fb6d31558a23d1507f7ebe2a88f4541fc64fb4c55124cf4541fdf698aa23556ca83fbf5f15447a2a1407f7da62b13447a2a0fefb4a23d150983f9c1c01d7a23d150983fb00001447a2a0fe095
  | 6, 1, 3 => 0xf7ed315447a2a0fefb4c55f1e8a8499fdf698aa23d1507f28bed3154454230fe5c7ebe2a88f46aaa0fefb4c55da88f4541fdf89b4c5511e8a83fbed31544923d1507f7da62a88f4541fca8fb4d662adef4541fdf698aa23d1507f063ed3156ba23d1507f7ebed3154473aa0fefd7c5511e8a8461fdf698ac3511e8a83fbed31567a23d1507f7
  | 6, 1, 4 => 0xebf5f15447a2a0fefb4cae2a88f4541fdc01d7a23d1507f20b003698a7a311507f6da62a88f4672a0fefd7c55f288f4541fdfaf8aa23d1b2a83fbed315447a359507f7006d315767a2a0fedb4c5511e8a83f9b1c01d7ced11e8a83fb003698ab5bd1507f6da62a88fd7a2a0fefb4c5511e8c4541fdc01e2ebd11e8a83fb6d315447a2a0fe207
  | 6, 1, 5 => 0xda62a891c7a2a0fee00ebd11e8a83f9ddbafb4a23d1c8a83fbed3598aa23d1507f7da62a88f454254fefb4c5511e8a83f8b1f699cc5511e8a83fb80288f4541fc300f6ebe2a88f4541fc12e00ebe2a88a83f8c9b698aa2469e8a83fbfa3698aa23d1507f70062a88f4541fc2edb4c5511e8e5541fdf698aa2401e8a83fbf5f15447a39d507f7
  | 6, 1, 6 => 0xda62a88f454230fefb4c55ade8a84e9fdf698a7a2a0fe61193ed315447a2a0fe197da62a89237a2a0fefb4c5511e8a83f8c9f698aa23d150a03fbf0f698a9c3d1507f7da62a88f4541fc34fb4c552688f4541fdf698aa23d1508a3fbed3154498bd1507f7da62a893c7a2a0fefb4c5511e8a8449fdf69aac5511e8a83fbed3598a7a2a0fe617
  | 6, 1, 7 => 0xe36d315447a2a0fefb4c55f288f4541fdf698aa23d1b2a83fb803698aa22a098326da629e8d5541fcc2fb4c5511e8a83f8e5f698aa23d1507f24bed315448abd1507f7da62a88f4541fc16fb4c55ca88f4541fdf698aa23d1aaa83fbed314f454230fe617da62a89307a2a0fefb4c5511e8a83f8d9f698aa23d1507f14bed315447a2a0fe1b7
  | 6, 1, 8 => 0x7a3af447a2a0fedb4c561688f4541fdf698aa23d1507f22bed315447a2a0fe687da62a88f4541fc12fd7da629e8a83f985c01b4c5511507f1936d315447a2a0fe447da62af8f4541fcc2fb4c53d1b2a83f985f698aa23d16ca83fbed315447a39d507f7ebed315447a2a0fefb4c5511e8a83f975f698aa2435e8a83fbed315157a2a0fe617
  | 6, 1, 9 => 0x3698aa23d1507f2e3803698aa21fc82326006d315448aaa0fedb4c5511e8e1541fdf698aa2455507f30bed315447a2a0fe467da62a89017a2a0fee00da629507f1908db698ac2bd1507f30b803afaca23d1507f6da62a892c54230fefb4c559a88f4541fdf698ab7bd150933fb803698a541fcc2326
  | 7, 0, 0 => 0x6d315447a2a0fe237006d31544963d1507f700003698aa23d1507f6006d31563a23d1507f7006d315447a2a0fe617006d315447a2a0fe4c700003698aa23d1504c60070f698aa23d1507f7006d3156fa23d1507f7006d315447a2a0fe0f7006d315447a2a0fe70700003af8aa23d1507f6006d315447a2a1267f7006d315447a379507f7006d315447a2a0fe587006d31544993d1507f7
  | 7, 0, 1 => 0x6d3157ca23d1507f7006d315447a365507f7006d315447a355507f7006d315447a2a1187f7006d315447a2a0fe327006d3598aa23d1507f70000001d7a23d1507f5006d315447a2a0fe417006d33b8aa23d1507f700003698aa23d0fe41600003698a7a2a0fe236006d31544903d1507f70000315447a2a0fe0f6006d315447a2a1307f7006d3458aa23d1507f700003698a7a2a0fe616
  | 7, 0, 2 => 0x6d315447a2a0fe5c7006d31585a23d1507f700003698aa22a0fe3260075f698aa23d1507f7
  | 8, 0, 0 => 0x3698aa23d1507f6
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
private theorem z2_0 : span (Z 2) 9 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 9 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_48 : span (Z 3) 3 48 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 51 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 3) z3_a1 z3_48

private theorem z3 : span (Z 3) 51 0 = true := z3_a2

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
private theorem z4_288 : span (Z 4) 17 288 = true := by decide +kernel

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

private theorem z4_a12 : span (Z 4) 305 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 17) z4_a11 z4_288

private theorem z4 : span (Z 4) 305 0 = true := z4_a12

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
private theorem z5_672 : span (Z 5) 14 672 = true := by decide +kernel

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

private theorem z5_a28 : span (Z 5) 686 0 = true :=
  span_join (f := Z 5) (a := 672) (o := 0) (b := 14) z5_a27 z5_672

private theorem z5 : span (Z 5) 686 0 = true := z5_a28

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
private theorem z6_408 : span (Z 6) 6 408 = true := by decide +kernel

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

private theorem z6_a17 : span (Z 6) 414 0 = true :=
  span_join (f := Z 6) (a := 408) (o := 0) (b := 6) z6_a16 z6_408

private theorem z6 : span (Z 6) 414 0 = true := z6_a17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 12 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 36 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 12) z7_0 z7_24

private theorem z7 : span (Z 7) 36 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12435

theorem PEqualNP.Outside.L_meta_12435 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941107712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941107712) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12435.mainG PEqualNP.Outside.L_meta_12435.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12435.CG, PEqualNP.Outside.L_meta_12435.CG_mono, by
      have : PEqualNP.Outside.L_meta_12435.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12435.CG_eval⟩
