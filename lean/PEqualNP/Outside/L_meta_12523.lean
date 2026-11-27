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
namespace PEqualNP.Outside.L_meta_12523

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 3907053792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 5, 5, 5, 6, 7, 5, 5, 5, 11, 5, 13, 14, 15, 5, 5, 5, 5, 5, 21, 22, 23, 5, 5, 5, 27, 5, 29, 30, 31, 5, 5, 5, 5, 5, 37, 38, 39, 5, 5, 5, 43, 5, 45, 46, 47, 5, 5, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 6, 6, 6, 6, 6, 5, 6, 7, 6, 6, 6, 11, 6, 13, 14, 15, 6, 6, 6, 6, 6, 21, 22, 23, 6, 6, 6, 27, 6, 29, 30, 31, 6, 6, 6, 6, 6, 37, 38, 39, 6, 6, 6, 43, 6, 45, 46, 47, 6, 6, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 7, 7, 5, 6, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 7, 7, 7, 7, 21, 22, 23, 7, 7, 7, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 37, 38, 39, 7, 7, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 5, 6, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 11, 11, 11, 11, 21, 22, 23, 11, 11, 11, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 37, 38, 39, 11, 11, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 5, 6, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 13, 13, 13, 13, 21, 22, 23, 13, 13, 13, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 37, 38, 39, 13, 13, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 5, 6, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 14, 14, 14, 14, 21, 22, 23, 14, 14, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 37, 38, 39, 14, 14, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 5, 6, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 15, 15, 15, 15, 21, 22, 23, 15, 15, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 37, 38, 39, 15, 15, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 5, 6, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 21, 21, 21, 21, 21, 22, 23, 21, 21, 21, 27, 21, 29, 30, 31, 21, 21, 21, 21, 21, 37, 38, 39, 21, 21, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 5, 6, 7, 22, 22, 22, 11, 22, 13, 14, 15, 22, 22, 22, 22, 22, 21, 22, 23, 22, 22, 22, 27, 22, 29, 30, 31, 22, 22, 22, 22, 22, 37, 38, 39, 22, 22, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 5, 6, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 23, 23, 23, 23, 21, 22, 23, 23, 23, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 37, 38, 39, 23, 23, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 5, 6, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 27, 27, 27, 27, 21, 22, 23, 27, 27, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 37, 38, 39, 27, 27, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 5, 6, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 29, 29, 29, 29, 21, 22, 23, 29, 29, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 37, 38, 39, 29, 29, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 5, 6, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 30, 30, 30, 30, 21, 22, 23, 30, 30, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 37, 38, 39, 30, 30, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 5, 6, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 31, 31, 31, 31, 21, 22, 23, 31, 31, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 37, 38, 39, 31, 31, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 5, 6, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 37, 37, 37, 37, 21, 22, 23, 37, 37, 37, 27, 37, 29, 30, 31, 37, 37, 37, 37, 37, 37, 38, 39, 37, 37, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 5, 6, 7, 38, 38, 38, 11, 38, 13, 14, 15, 38, 38, 38, 38, 38, 21, 22, 23, 38, 38, 38, 27, 38, 29, 30, 31, 38, 38, 38, 38, 38, 37, 38, 39, 38, 38, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 5, 6, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 39, 39, 39, 39, 21, 22, 23, 39, 39, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 37, 38, 39, 39, 39, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 5, 6, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 43, 43, 43, 43, 21, 22, 23, 43, 43, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 37, 38, 39, 43, 43, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 5, 6, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 45, 45, 45, 45, 21, 22, 23, 45, 45, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 37, 38, 39, 45, 45, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 5, 6, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 46, 46, 46, 46, 21, 22, 23, 46, 46, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 37, 38, 39, 46, 46, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 5, 6, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 47, 47, 47, 47, 21, 22, 23, 47, 47, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 37, 38, 39, 47, 47, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 5, 6, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 51, 51, 51, 51, 21, 22, 23, 51, 51, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 37, 38, 39, 51, 51, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 5, 6, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 53, 53, 53, 53, 21, 22, 23, 53, 53, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 37, 38, 39, 53, 53, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 5, 6, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 54, 54, 54, 54, 21, 22, 23, 54, 54, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 37, 38, 39, 54, 54, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 5, 6, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 55, 55, 55, 55, 21, 22, 23, 55, 55, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 37, 38, 39, 55, 55, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 5, 6, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 57, 57, 57, 57, 21, 22, 23, 57, 57, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 37, 38, 39, 57, 57, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 58, 58, 5, 6, 7, 58, 58, 58, 11, 58, 13, 14, 15, 58, 58, 58, 58, 58, 21, 22, 23, 58, 58, 58, 27, 58, 29, 30, 31, 58, 58, 58, 58, 58, 37, 38, 39, 58, 58, 58, 43, 58, 45, 46, 47, 58, 58, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 59, 59, 5, 6, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 59, 59, 59, 59, 21, 22, 23, 59, 59, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 37, 38, 39, 59, 59, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 5, 6, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 61, 61, 61, 61, 21, 22, 23, 61, 61, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 37, 38, 39, 61, 61, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 5, 6, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 62, 62, 62, 62, 21, 22, 23, 62, 62, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 37, 38, 39, 62, 62, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f000000000000000000000000000000000000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f000000000000000000000000000000000000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000001117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f00000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e00000000000000000eee8e8e0e8e0e8e0000000000000000000000000000000000000000000000000eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0eee8e8e0e8e0e8e0

def cMZZ : Nat := 0x1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f00000000000000001117171f171f171f1117171f171f171f1117171f171f171f0000000000000000000000000000000000000000000000001117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f1117171f171f171f

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
  | 2 => 7
  | 3 => 42
  | 4 => 270
  | 5 => 607
  | 6 => 354
  | 7 => 29
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xb559c70e7aa8a0be440c20d6377a27ee2ec26aa60bba4bb600f50cbc
  | 3, 0 => 0xf273db4ed5fa702dd0ae569ec9d76654c99ed03ac571425cc48a0700beeac29aba206132a986add99fd090af9c24880591da8a808dd8fc5b877ef60c7e039a8973840ed0688cc195639fb5695b2cc5b458670b7355981ce1536d8b125258c1805198247748226bb7480674754615b3423cefb2eb373f26bc2f82996e2636412b23e104e9230b76ff2028b34c1e44e8e51b14f26616797e1714e46f2f1379a5bd07419ff30201d6b9
  | 4, 0 => 0x1f28ca571f1ac2571f0d5d971e5b54811e3800351dc44c3e1d2198521c46a1031adfbd421ad4a90e19f7989f19c5e19119c4ab41199bcdd2196bb14c186fb87318342f2e1814add9176cb621174d18b81550b45114d5527813e8dd5e13e14c451392a7c6138dd2c412ad25c91279e197118f4b51116de3a8116340f5111174c710d009e7104e7763100664580fc1d7590f785ae10f5d4c0d0e2d17840e264ab40de177180d4363fc0d0102220c8bdf8d0afca9d50aabc5e00aaacd550a83056d0a5bd2bd0a4609e90a28f971088892f60773cc21070528a706af99e40613fe5f05fc2a5805228a9103fcb10303f35ae002ff943201d05aed00d9ceba004f72c0
  | 4, 1 => 0x4a6a76604a544ecc48ed1ab44732c872462c720645e72b964574abef443ceb7543f1087a4324f474429f0b9241bf71ef4160508140802b813e9159e13d3a33e33bf9506c3be965153ad6f89c3ab528ac3a64e4f039238277382f7c44382cb9e437df8ec536da8127362e4d9735cb20fd35ad2908351bc35934e57e1d349ca76233c001d63202aa6e316ba8b63165fd0c2f0201302ef8fd542eb5474d2e9e2b742e86c5162d13b3e42a2bccc729e5417129ca38df297f12fe28d5fc6b28c26f2b27ba89a526b9eaf7261dcea5261c466125b1d5f325a63b6b2574762c25001461249b31c9237256052371bd552234d8a021956b4c1fdd2e6b1f6aea5e1f31cd29
  | 4, 2 => 0x869b51a6861ea63d854e89da8516710382f3727b80e1d9957c67735f7c2977427b69bd107a91ea687a4119f279a247aa78549dc7780c255c77d40de67630f1c57628747f75fe100d74a3bd5273cf7d1a730e44b1722f3432713727bd705805066f48a2056d5bafae6c0947a56bcdc0066bad261b690bd7ba68eb648a68c71a5c684d4c3967fa7cc86636b62465c23d0964eed52b64ce5b8063babb81628647c061802f9e607271ef5eb3f6025ddedcd25c11ab535b4bdbf559e2cfa75933ae1c591ef0825788b571544c9cd154219cad531518c45305213e5258c1805116e75b50ba330050558d534fc96ac04fc6ca944f4dd7174f1e36694c3357eb4c09d507
  | 4, 3 => 0xde546c31dd3e051bdcd842f9dcd065c7dc78d174d90aa844d342359bd32960fdd3273400d1f8cc3ecebb5a86ccb0e7f9c7a5cd99c744be9ec6b3b4aac55b5be0c4c91c8dc3bc2cb6c2029928bd7b5afdbd0910ddbcd39212bc68f293bbebdc08ba206132b937cab0b8901035b88235c8b881d2b2b52ed536b4f9c656b3ded439b06a970db0699131adf21950add5a990ace1a7a4ab54c7f7aacdbb8ea87c4efda7a64fc7a6e29634a6308e9aa5d80b05a2209062a1512ff0a01350199df077a99ddea9969d99b54d9c6447149a7622e496cd265694e99ab193dfa8bf925935ef9062bf9c8f3591338edc988b8ea40c818b23ed3889d74f0b895f077f891e64c9
  | 4, 4 => 0xff7bd8a3fec398affd443f09f9070a34f77563fff3e3c553f10e24f1f0e6047be8fa7968e8b2d21ee650c927e42bf709e15740dce1012cdd
  | 5, 0 => 0xc9e025b0c70fc620c635c430c44881f0c3f37230c0f7d730bcd5b4d0bc617340bb3aaef0b2bf9080b17afed0ac4e0000aaacd550aa5c1900a63ec170a290dce0a2039080a1ac2680a07d8e90a01a88d09ecd74e09228e8d090c3ed508f1c11708a96ec4087f51d506c8737a06b97c6d069626cf068edf88061e4d5105fc8e2005a1856c05611217051b9c8a051b030f04e4393f04e4068904abf4c204a6d7ab0462cd72043c02e703db18060340c990031161fa02547dfd0249051b0232a158021d3425016c9961016bd80b015cac99012d6457011aaa5700d4cd3f00b4e4b400a90ccd0094c1750078932e00668ec9005d2b74005656f6004ca7d80013aceb
  | 5, 1 => 0x186fb87318590a1f1830be031819555d17e1e95017dc4ef617d256e5178881de16bb641e164b7b53160f8c2616085daf15c6d7e0159d6000155d3204154c336b14d5527814c25b4714b8a41a14b54a1b1489023d147a85931447ce3713eed4d013e14c4513927a48135b0e3b1336c3f81304c95912dd017112d3815012c943e012b69fc612b38d4a12ad25c912859a3f127ca3611245fbb81242bdc511dd704d11ca680f11817f4e1130335610ea3758108dd7fa107c0b55104e77630fcdc8250fb4903c0eee88590eafe8e30eae29260ea033250e854a9c0e6dfa630e56265c0e13e7870dbf20a30d4f2ee10d16961a0d0945f20cc279130cb775680cb0cf88
  | 5, 2 => 0x28372a6f27a149202783e1742767599b274165a0273f0111273c82cd26d5be5d2691fc3926374c79261c466125f032ab25a39b55252bc82f24a3a186242b3f6b23f34f6e23f1fcd423aaa92b232ea51221ec1d9721c5ad5021b2443221b07164217cc50621428e4220db3f67208e2b3220742850206ea9dd1f78756c1f31d5801ec05b511eb4f7a11eaa4fbc1dc86ced1d4c0e6a1d2f4e7c1d042f771ca0b0331c3b48491c0f5cf31bf605cc1be7cec81be684501bc5c67c1b6768591b485ce21af3182e1a5d251f1a580f2119f7989f19e9475519bd3cf9196b70cb196a61491956fa181944aa6f192d1fd6192a05eb18f8956918cd6b6518a87367189619e7
  | 5, 3 => 0x3a74d48939d4942d396fb02d395b99933923827738df7dff3848e2af3721ade636e774a336abf7a73692859f36918b8b367e1243366d0b3a364a53aa3618980e3583991d354db91834f8af5734e57e1d34abc52a34a3abf7349ca76234754c7e33bed24033b3b8b53346ef9d32fe18e232ce65c932c1b4c932bab1cc325436a83207986231d1352a31344377311c6b2f30fcbe08307b59353024ea152fd840a62fa0267a2f990b9c2f2cdda02e7642652e43c83f2ddd41792d5a10652c8c7dba2c7351c52bf47e202b724aca2b5165912a770dc02a5066e729efb56b29ef67502969cc89295afc1628d374ad288c9b55288a32e6287a2a83286b3fad2861dbae
  | 5, 4 => 0x4e866e0a4e3ff1084df10bfd4dcea7f34d7c1e9a4d50594b4d2b47164ceeb34e4c53e0034c4b047e4c45510a4c09d5074b9af5c14b7bc2a94aa6ef8e4a857c784a6b468749b320494972c912491d35ad48c3308848a9c17c47cd04ee4727c6f847141aac46eb55e5465892f8463fe99b4605b5ac45e72b9645942fe745700373452d9d32445c6f8144157cc943654dfb42ec0d4842a0ebe34274825842181bd842169cec41d3175041859de94170709e40e9285e40e7593b40d72c8440d5f3d83fd5946c3fccfd1d3f55de9d3ede72e63eb51cba3e906d083e5376683dca9aff3d3f7a213c6bb1d63c6a13ce3c4dbc5d3ba888fb3af3e64f3ae9d7013ab528ac
  | 5, 5 => 0x6737c064670df20666b0f8bd65891f0c650480e16415c72c637579a0628fe11162215d0161e717ae6178ec8660fdca74603392885fd1bca35f732c765e6b0f3d5e0905fc5cfbb2bc5cf2b3dc5ce1e9aa5bf6c9105b7e17285aca872d5a0a247159df202d59ade8d6598a9ef5586bd8c7582e66f157b21543577c0461576fedfb574e2fe356f8429a561ab55e55584518551f7ca854ecfd9854ac41e454a9fadb5486e85c5463d10b542670a554167b9a540c292353d02e2353b6d92053a78bdc531aef0a5317a93c529b90cf5277e7125258c180523f391651b2222b519b28ff5158abbd50ba3300504eebd24fb5d7474f94e90a4f6065a54ef05d954ed72797
  | 5, 6 => 0x811f1ef480e7fa1180e1d9958071060d8066216080332af97ff84f0b7ff7ebf57f50230a7f434b157e686d007c67735f7c49825a7c2b843c7c1cd0657be629237b7110e07ac947f57ac8e4df7a91f9c479e191eb79a67eb078da86c177ab662e772d80937600522a75936e3d757252257509400e73cf7d1a73248b1972c816c6728e21b07233b63771f47e54717acbf57145608e7121166070a210027092b9cd708264f9704a113a6fe925c06f5e389c6ef99c0b6e604cf06d93d8eb6d4695fa6cc662826c6e871d6bad261b6bab21666b624aab6ad75d876a968db96a76be7c6a0ffa216a0e979b69da2ba269be337269b3c1186870b84d67e7ac0867b22738
  | 5, 7 => 0xa4467f0aa4461bf4a3ff880da39e5309a3269653a2b69cffa272c964a22090629fba96139f4cf6bf9e831e499d99b54d9d4396b59d0e3ae89bfb26cd9b6f49979b33bafe99843db998bcbba097f6a39697471c3496fe088596e729f7965b68c794e99ab194bcda47942ed1e29413b16493ac689b933e47b19303c5c392e77f1892a9e0e59266da749142e6dc91129b508fefd0558e5e2a208e1550038da885de8bff34008bd58af18a6bc592893bd599891e64c987dfb64587a75da7877fd649877858eb86de111086a6042b868ee6ce861d4f1e852fe4c384d4447084a96a8d847f2a208464764482cf78508256fd718180e19a816c2273815adf0d8140e3db
  | 5, 8 => 0xd9942ae0d9777468d7d8e5e8d79183b0d6ef18a2d5724187d342359bd3273400d188a580cfffc99dcd810453cd231891cd1b8a1ecca58a64cbaf3dfacae0a17eca5c952cca1971d2c71fd217c5630ce1c408c612c38ccf07c2a654f9c2029928c1e910bec1a92ec6c10244fdc0e71a4fc0640aa8be969fe5be263378bd53c25abd0910ddbcccc84db9fb170db8c38d35b89fd88fb7ac01ecb64c1554b5294469b4aa807eb46a0826b38ab5e9b32d16a8b023a569b0004bcbaf03dad4ae8a8a9eac13247aaaa7f14caa952063aa7ffb5baa730ecaaa5f0054a96976c8a932d454a8cd5a1fa8072e02a7ad7168a78c0ac9a6e647b4a638a59aa5d80b05a4abf93f
  | 5, 9 => 0xfcd6783afa5c1fb8f9dc8532f7193855f5d544a3f3ceb426f2925d40f1fe8720f10cce22f0f3ba63ec85f30dec114b07e95b28e1e8b2d21ee7a7552ae5323efde4e4780ce4612c17e37954c2e164a448e11af84cdec331f6de526612de3be156dc78b7c0dc185ec5dbfb83c6db813004da3c56e1da33bc34d9b74a67
  | 6, 0 => 0x1a24641318e7d3fe18a873671874016a1819555d180e8c4017e1e9501709e4e71708252a166de38b1588d54414f7fe5f14d552781467b2fd142757511420133812ffbd9412de021312ce936212bde81b128309d2125ba49110ea375810d94dd9104e77630f226f7e0f1378710eafe8e30e8e8e230dfb81700d75988e0d74ff130cefffa30cbcc9760be708e80aa3011f0a8c9d5c0a7730290a6f92df09e4a6ca09b6a89d0974a65b08eebd7908b052fa05ce13ce05a1856c057a83ac051b9c8a04e4068904b09c4604867d79043462b302b61bc102981e0e02657aec0236813b0190a02a016c9961012d64570112bb220110b30d00f3a89700f0a01500841a46
  | 6, 1 => 0x35bd6bc93583991d33ab980d33ab619532d109c432074a5c3121c30630bbd7b2307b59352fd840a62f9b61a42f0a01472eb7e3ba2e91487d2e7642652e5df79a2e4a2eaf2d85c4332cfd9d8a2c4bf8d82b754b002b44deaf2ad4a5582aa8314d2a0c40362a0a6d68299c8a462960fcc6287a2a83282bacfd278bd184266bdb1626374c7924faac37245001d023a258e6232f81ba22ec8e8421b0f61c21871bda2152916d20fcbde620f015eb20b306232073516120694213204aff9e20364afa1f1560221ee86fac1eb6aa6d1db72e081d2f4e7c1d0f461f1c48d0d41c3b48491c0f5cf31bec764c1b9cb9151b90bffc1b233fe41b109bca1adf96431a9cb9c9
  | 6, 2 => 0x54addc0753f4f1c553c169725277e71251b2222b517731b1511d2c8c507e820f502700f24ffcc5bb4f775c524eb28efc4e99e59f4e5fb1b04de5c1634dc9ff774d47d7b94c6f78cd4c53e0034b9af5c14b75eaa64989fac5494324624941553f488e0ff947afdaa14727c6f847141aac45758c2c45700373445c6f8143b173ec43654dfb43389c0642ced08d422e9031418816184184e85341397a033f1e57c43ea44fae3e4969143da7b51c3d9e6f113d3f7a213d05c12e3cfda7fb3c6728b53c18ce443c0db4b93be13fd33ba0eba13b2861cd3b13a7d63af3e64f3a2b312e39d4942d3923827738eb26ec38d684b4387ee61938323caa3786d9a4369dc443
  | 6, 3 => 0x800562327ff7ebf57f877c977f50230a7e686d007ded6a417dcc4e297d633c127c35a6bc7b7e871d7b2212ca7a02772478ecb5d178dc60fd78a40d3e76ba48f475edd4ef75205e867509400e7269f62571167109700c233c6fe925c06f91bc686f0af4c16de31b106d5e7ce56c6e871d6affb3e96ae9dd156a4113b26a0ffa2169b3c1186957c678688d8e8c682bb8a768153298669de3ef66630200654cafe06450c514628fe1116264207560c5d4cb602dbd2f5fc9e9ff5fa82be75e80e63f5d46f99c5cfcefc25cf2b3dc5c70779e5c6625275bf6c9105a0c1e2f59f5250358a8e7d6582e66f157eee50e56a7410a5685d15d55d61a9e55aa554f5585431a
  | 6, 4 => 0xb52e1049b5294469b4aa807eb46d207eb38ab5e9b18cd058b1275623b0c81a6db0612a06b0076d6caeac6e9fad05f543ac598411ab809257a932d454a8cd5a1fa8149217a7ad7168a56836eca5376d64a3c9459ba3342a66a2209062a0d59d6a9fba96139f4125fb9eb564cb9d4396b59d16d64b9c88cde69b9843b59b5dc1c79b417b1c996c97549955845a93b857259339dde29241a0468f45285c8d89e0c78d0366918cd926248bff340089791af8893d8a5b893bd59988a47efc888d26fd8877c57488524b0f8851e7f987aa1f0e879d471986c2690484efa44f84a37e5e847f2a208476cc69844025278319834c8260990a823b8def82007ab4813482c5
  | 6, 5 => 0xff733459fe2f40a7faec5944fa5c1fb8f10cce22f050b7acecbb281bebeee7b2ea505932e71d2dfae4725ac9e28db838df92fd68dec331f6dc185ec5db813004d9e2a184d680395ccd3d6463c9411653c85bb80dc2c4d749c2551311c0f9d493c005fdf0bfa69d63bd83406dbd047c82bbe4b1edbb44cd69b75dd6d8b6bd8f3eb615c653b55c12c5
  | 7, 0 => 0xbd83406dbbe4b1edb18cd058b0076d6c8cd9262486c269047d633c127269f6256ae9dd15654cafe06450c5145a0c1e2f54addc074ffcc5bb4dc9ff774b9af5c1422e903138323caa2e91487d207351611d2f4e7c18a873671709e4e714d552780dfb81700d75988e057a83ac02b61bc1016c9961
  | 8, 0 => 0x1d2f4e7c
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff000000ff000000f0f0f0f0f0f00000f0f00000f0f00000cccccccccccc0000555555555555000055550000555500000f0f0f0f0f0f00000f0f00000f0f000000ff00ff00ff000000ff000000ff00000000ffffffff00000000ffff000000000000cccccccc000000000f0f0f0f000000000000ffff0000000000000000
  | 0, 1 => 0xa0a0a0a0a0a0a0a050505050505050500ffffffffffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000ff00000000000000f0f0f0f0f0f0f000f000f000f000f000aa00aa00aa00aa0055005500550055000f000f000f000f0000ffffffffffff0000ffff0f0fffff0000ffff0000ffff0000ff00ff00ff00
  | 0, 2 => 0x30303030303030302a2a2a2a2a2a2a2a11111111111111110fff0fff0fff0fff0fff0fff000000000fff0000000000000f0fffffffffffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f0f0000000000000f00ff00ff00ff000f00ff000f00ff000f000f000f000f00
  | 0, 3 => 0x77777777777777775f5f5f5f5f5f5f5f5f5f0000000000005f005f005f005f005555ffffffffffff5555ffff5555ffff55555555555555555555555500000000555500000000000055005500550055004c4c4c4c4c4c4c4c44444444444444443f3f3f3f3f3f3f3f3f3f3f3f0000000033ff33ff33ff33ff3333333333333333
  | 0, 4 => 0xaaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa00aa0000000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a000a000a000a00088888888888888888888888800000000888800000000000088008800880088008080808080808080
  | 0, 5 => 0xc0c0000000000000bbbbbbbbbbbbbbbbafafafafafafafafaf00af00af00af00aaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaaaaaaa8a8a8a8aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaaaaa00aa00aa00aaaaa0a0a0a0a0a0aaaaa0a000000000aaaa888888888888
  | 0, 6 => 0xcccccccccccccccccccccccccccc0000ccccccccccc0ccc0cccccccc00000000ccccccc0ccc0ccc0cccccc00cccccc00ccccc8c8c8c8c8c8ccccc0c0ccccc0c0ccccc0c0c0c0c0c0cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc00cc00cc00cc00c0c0c0c0c0c0c0c0c0c0c0c000000000
  | 0, 7 => 0xeeaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaeeaa000000000000ee00ee00ee00ee00ee00cc00ee00cc00ee00cc00cc00cc00ececececececececececececccccccccececcccccccccccceaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0cfcfcfcf00000000cfcf000000000000ccccffffffffffffccccccccffffffff
  | 0, 8 => 0xf000f00000000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeee0e0e0e0eeeeeeee00000000eeeee0e0eeeee0e0eeeee0e0e0e0e0e0eeeee0e000000000eeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeee0000eeee0000eeee0000aaaa0000eeee000000000000eee0eee0eee0eee0eecceecceecceecceecc0000eecc0000
  | 0, 9 => 0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0f0f0e0e0f0f0e0e0e0e0e0e0f0f0c0c0c0c0c0c0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0a0f0a0f0a0f0a0f000f000f000f000
  | 0, 10 => 0xfcccfcccfcccfcccfafafafafafafafafafafafaaaaaaaaafafafafa00000000fafaf0f0f0f0f0f0faf0faf0faf0faf0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f0f0f0f0f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffffffffffff0f0fffff0f0ffff
  | 0, 11 => 0xff000000f0000000ff00000000000000fefefefefefefefefefefefef0f0f0f0fefef0f0f0f0f0f0fefe0000fefe0000fefe0000f0f00000fefe000000000000fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcccccccccccccfcfc000000000000fcf0fcf0fcf0fcf0fcf0f0f0f0f0f0f0
  | 0, 12 => 0xff00ff00aa00aa00ff00ff0000000000ff00fa00ff00fa00ff00fa00fa00fa00ff00f000ff00f000ff00f000f000f000ff00f00000000000ff00ee00ee00ee00ff00cc00ff00cc00ff00cc00fc00cc00ff00cc00cc00cc00ff008800ff008800ff00880088008800ff000f00ff000f00ff000f000f000f00ff000000ff000000
  | 0, 13 => 0xff0fff0f00000000ff0f000000000000ff00ffffffffffffff00fff0fff0fff0ff00ff55ff55ff55ff00ff33ff00ff33ff00ff00ffffffffff00ff00fff0fff0ff00ff00ff33ff33ff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff000000ff00ff00fc00fc00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00
  | 0, 14 => 0xffaaaaaaaaaaaaaaffaa0000ffaa0000ffaa0000ff000000ffaa000000000000ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0ff00ff00ff00ff88ff88ff88ff88ff88ff00ff00ff00ff880000ff880000ff88000000000000ff80ff80ff80ff80ff50ff50ff50ff50ff33ff33ff33ff33ff11ff11ff11ff11ff0fff0fff0fff0f
  | 0, 15 => 0xffe0ffe0ffe0ffe0ffccffccffccffccffccffccccccccccffccffcc00000000ffccff00ff00ff00ffccf0c0f0c0f0c0ffccf0c000000000ffcc0000ffcc0000ffcc0000cccc0000ffcc000000000000ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaf0a0ffaaf0a0
  | 1, 0 => 0xfff0fff0aaa0aaa0fff0ffc0ffc0ffc0fff0ff00fff0ff00fff0ff00ff00ff00fff0fcf0fff0fcf0fff0fcf0fcf0fcf0fff0faf0faf0faf0fff0f8f0f8f0f8f0fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff0aaa0aaa0aaa0fff00000fff00000fff0000000000000ffeeffeeffeeffeeffee0000ffee0000ffee000000000000
  | 1, 1 => 0xffff000000f00000ffff000000000000fffcfffcfffcfffcfffcf0f000000000fffc0000fffc0000fffc000000000000fffafffaf0f0f0f0fffafffa00000000fffaf0f0f0f0f0f0fffa000000000000fff8f0f0f0f0f0f0fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff0f0f0f0f0
  | 1, 2 => 0xffff0000ffff0000ffff0000fff00000ffff0000ffcc0000ffff0000ff000000ffff0000fcfc0000ffff0000f0f00000ffff0000f0000000ffff0000cccc0000ffff0000c0c00000ffff0000a0a00000ffff000088880000ffff000088000000ffff000033330000ffff000030300000ffff000011110000ffff000000ff0000
  | 1, 3 => 0xffff505050505050ffff333333333333ffff111111111111ffff0f0fffff0f0fffff0f0f0f0f0f0fffff0f0f00000000ffff00ffffff00ffffff00ff00ff00ffffff00f0ffff00f0ffff00f000f000f0ffff0033ffff0033ffff003300330033ffff003300000000ffff0000ffffffffffff0000fffff0f0ffff0000ffff0f0f
  | 1, 4 => 0xffffc0c0c0c0c0c0ffffc0c000000000ffffc000c000c000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa00aa00aa00ffffa0a0ffffa0a0ffffa0a0a0a0a0a0ffffa00000000000ffff888888888888ffff880088008800ffff8080ffff8080ffff808080808080ffff808000000000ffff5050ffff5050
  | 1, 5 => 0xfffff000fffff000fffff000f000f000fffff00000000000ffffeeeeffffeeeeffffeeeeeeeeeeeeffffeeee00000000ffffe0e0ffffe0e0ffffe0e0e0e0e0e0ffffe0e000000000ffffccccffffccccffffccccffff0000ffffccccf0f0c0c0ffffccccccccccccffffcccc00000000ffffcc0000000000ffffc0c0ffffc0c0
  | 1, 6 => 0xfffffcfcccccccccfffffcfc00000000fffffafafffffafafffffafafafafafafffff0f0fffff0f0fffff0f0fffff000fffff0f0ffff0000fffff0f0ff00f000fffff0f0f0f0f0f0fffff0f0f0f00000fffff0f0f000f000fffff0f0a0a0a0a0fffff0f00000f0f0fffff0f000000000fffff0c000000000fffff0a0f0a0f0a0
  | 1, 7 => 0xffffffff00000f0fffffffff000000ffffffffff00000000fffffff0fffffff0fffffff0fff0fff0fffffff0ff00ff00fffffff0f0f0f0f0fffffff000000000ffffffaaffffffaaffffffaaffaaffaaffffff00ffffff00ffffff00fff0ff00ffffff00ff00ff00ffffff0000000000fffffcfcfcfcfcfcfffffcfcf0f0f0f0
  | 1, 8 => 0xfffffffff0000000ffffffffe0e0e0e0ffffffffccccccccffffffffcc00cc00ffffffffc0c00000ffffffffaaaaaaaaffffffffa0a0a0a0ffffffffa000a000ffffffff88888888ffffffff88008800ffffffff33333333ffffffff11111111ffffffff0000ffffffffffff0000ff00ffffffff0000aaaaffffffff00005555
  | 1, 9 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffccccffffffffffff0000fffffffffff0fff0ffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafafafafffffffff0f0fffffffffffff0f0f0f0fffffffff0f0a0a0fffffffff0f00000fffffffff0c0f0c0fffffffff000f000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x11434948e0c6b2d1d9d044438a2248870937948e2e6f261d9cc64d3
  | 3, 0, 0 => 0xb3c50c85a481a78de5445f278d65a48d278c65a4833ecde5a4b3c50ec6f48bc50de5a4b3a08de5a4ba418de5a46b27912444b3bfcde5a48a224de5a46b20ce8444b8c50ce5a4b3c24de5a48f27904444
  | 3, 0, 1 => 0xac450de5a46b278d2524831bcb4534b3c50d25a4b3adcde5a4b3c50d65a4a4c18de5a4ac3fcde5a4b3c511a4447b278c65a48ab58de5a4b3c50de554b3c2cde5a4b3c50de5a465278de54462a78ce5a4
  | 3, 0, 2 => 0xb3b59508d48f1f0e8444b3c74c65a48f420de5a48f451508d466278de5248a2ecde5a48f278c64d4b9c18de5a4bdc18de5a4
  | 4, 0, 0 => 0xbecbd3c82222ded949e379696cf143796812b616b278de5a58f2d93c6f2d2db2cf14379696b0d63a1bcb4b1e87a78de5a58f4513c642d2b593c7237969648d64f1bcb4b676b284de5a58f36d3c6f2d2d9e1a9e3796962cd64f1bcb4b1e71a78de5a5
  | 4, 0, 1 => 0x8f278de5c2d2c7a289e37969642d64f1bcb4b7d6b279144458f359466f2d2dce069e379696c5114f1bcb4b5e8a278de5a57cb593c6f2d2c79849e379696ced64f1d8deb678a1bcc45a5953593c8d222c5dac9e3796963cc54f1bcb4b1e6b278c85a5
  | 4, 0, 2 => 0x8f27902622d2c79ac9e37955668d64f1bcb4b066b1bcca5a5b63593c6f292c79ac9e3796969d144f1bcb4b1e68278de5a5b3b593e6f2d2c7a289e379556bcd64f1bcb4b656b278de5a58f3553c6f2d2b593c7d3796963d0b4f1bcb4b1e69a78de5a5
  | 4, 0, 3 => 0xb13353c6f2d2cbe309e3793163cd14f1bcb4b7a64a78de5a58f278f66f2d2d9dacb1379696cef54f1bcb4b678a1bcca5a5b9b293c6f2d2c7a249e3796963ceb4f1bcb4b2a4f1f0de5a5a7b593c7637ad9e286f2d04d63cea4f1bcb4b4e6b278de5a5
  | 4, 0, 4 => 0xb3c51806f2d2c9dac9e3b1bd63d054f1bcb4b1e6b2791a4458f4293c6f2d2d9ead14379696cf4b8a1bcb4b1e6b248de5a5b9c197c6f2d2ca99e9e37969654d64f1bcb2b626b1d0de5a58f4513c8d222c79ac9e3c1696c8d64f1bcb4b75b3c50de5a5
  | 4, 0, 5 => 0xa5b593c6f292d9e286f331695ac9e379687aa00b3c50de394b03593c6f2d2d9d8a9e3796965ef34f1bc98b3f6b278de5a572b593c6f2d2ca9ac9e36969682d64f1bcb4b4f7aa78de5a5b9c7a0c6f2d2c7a1c9e37969644d64f1bcb4b1e7a278de4c5
  | 4, 0, 6 => 0x8f4513c6b2d2be9ac9e37969654c64f1bcb4ad64f1bcb4235b1b593c6f2d2d9dac9e379696ced04f1bcb4b1e4f1bcb4225b3c50de5a222c9dea9e379696289e3796846b495f278de5a599b593c6f2d2d9e289a3796963c9e3e1bcb4b678a278de5a5
  | 4, 0, 7 => 0xb3b593c8d222d8a0cd63796963cda4f1bcb4ad64f218de4e58f2791a7c222d3dac9e3796963cb74f1bcb4b678ec50de5a58f3594c6f2d2d9e286f2d0c16cf14469bcb4b678a1bcb4525a7c513c6f2d2c79ac9e3596963cd64f1bcb2b1e6b25cde5a5
  | 4, 0, 8 => 0x8f3fce86f2d2c7a286f2d03969ad64f1bcb4abe4f1bcb4535abb593c6f2d2c7a0c6f2d129401678a1bcb48d65ca78de5a5b3c51ac6f2d2c79ac9e349696cf14819bcb4b1e8a2acde5a5b3d8a286f2d2c793c7a379696cf148a1bcb4b1e86278de5a5
  | 4, 0, 9 => 0xa33593c6f2d2d9e286f2d131638d64f1bcb4b2a88a78de5a562a78de652d2d9dac9e359696cf14571bcb4b7d6b214e84458f3853c6f2d2d893c6f2d08163c9e3796878b006b278de5a58f3593c772d2d9e28ca3796963cd64b1bcb4b674f1f0de5a5
  | 4, 0, 10 => 0x6b2e13c6f2d2d89ac9e3b1bd6ced64f1a4b4ad64f20cde5a58f3713c6f2d2d9e286f2d0516f9678a1bcb4b6786278de5a58a279066f2d2daecf14379695ac9e441bcb4b7b5f278de5a5ca5ae286f2d2d11ac9e3796963c9e3796842b1e6b1d8e86f5
  | 4, 0, 11 => 0xac3593c6f2d2d89ea9e3796963cc44f1bcb4ad64f23506445b3c51e86f2d2c7a229e379696e6be4f1bcb4b2a63a78de5a576278de5a252d09ac9e3796967ad64f1bcb4b1e66278de5a50059cde5a0a2479ac9e3a9bd63ce74f1bcb4a008a1bcb4094
  | 4, 0, 12 => 0x8f451506f2d2d8a289e379696e7064f1bcb4b678a240de5a58f358de5a0c2c79ac743796953c833e1bcb4b676b1bcb41758f450e86f2d2e6ecf143796963cd64f1f8deb1e8ea78c65a59b3593c6f2d2d9e286f2d09d6ccd64f1bcb4b6797c50de5a5
  | 4, 0, 13 => 0xb3c41ac6f2d2c79aca84f23563d14511bcb4b1e64278de5a5bdd9e286f2d2b59769e37969635144f1bcb4b1e6b2c0de5a58f3593c8d23abc57c9e3796963cd6469d088b5d6b278de5a5b13593c6f2d2d76289e379696cf14379688cb6766278de5a5
  | 4, 0, 14 => 0x8f3913c6f2d2c79869e379696cf1e8a1bcb4b73b3c50de5a58f419ac6f2d2d9e28be3796963cd6539bcb4b678a1bcb4115005ce0c6f2d259dac74379695bcd64f1bcb4b1e8a418de5a5b9c19ac6f2d2d9e29043796963c7c3a1bcb4b1e74a78de5a5
  | 4, 0, 15 => 0xbecbcf874222d9e28933796963cd84f1bcb4b678a418de5a58f3593c6f172c79fe9e379695ecd64f1bcb4b576b1d0de5a58f278de5a102df65f1454235628f64f1bcb4b1e7aa78ec6f58f44d3c6f2d2df65e9e319356ced6541bcb4b1f6b278de5a5
  | 4, 1, 0 => 0x23cc14f1bcb4b7b81a78de5a56b279126f2d2a78de5a118816ce9e3796840ad6419d0de5a5b3c50de5a0dadce5f06379695ac9e3796854b1e6b278ec6f5b3d9e286f2d2c7a289e3b1bd6cf066b1bcb4b1e4f208de5a5
  | 5, 0, 0 => 0xcf479ac9e37969afb6b6b278de5a69f479ac9e37969a3cd64f1bcb4246becbdea9e37969a3d144f1bcb4306becbdae9e37969afb2f6b278b4356becbdd69e3c969a3d144f234de5a6bedada09e37969aced64f1bcb4136a647a289e37969b391e6b278de5a6b5d49ac9e37969b13266b278de5a6
  | 5, 0, 1 => 0x8f3593c6f2d0c1afb266b278de5a68f3593c8d37969a3d026b278de5a6b84bdac9e37969a991e6b278de5a6bedadac9e37955afaf76b278de5a68f365ac9e37969a3cd64f1bcb45268f359649e37969afb678f450de5a6b3b593c6f32969801626b278b4305aac79ac9e37969a3d1d8a278de5a6
  | 5, 0, 2 => 0xc8cbdac9e37969afad64f200de5a697bd9ac9e37969a791e6b278de5a697c793c6f2d081afad64f1bcb42568f3598a9e37969a5ecf4f1bcb4566becbdc69e37969b2f1e6b278de5a6cec79ac9e37969a3d1d6b278de5a6afd75ac9e37969afb6b75a78de5a697b593c7337969aeb676b278de5a6
  | 5, 0, 3 => 0x8f359a49e37969acf566b278de5a6bec51dc9e37969a5f196b278de5a6b3d2dac9e379699f8f66b278de5a68f3593c6f2d0e1a3cd64f1bcb40d6b13593c6f2d045b2d2a6b278de5a6953595c9e37969ac4d64f1bcb44f6004798a9e3796963c9e379684e20600478de5a1386d63d148a278de5a6
  | 5, 0, 4 => 0xa4479ac9e37969aa6d64f1bcca5a68f451ac9e37969a3cd64f1bcb65a6a8cbdac9e37969aced660278de5a6becbe1e9e37969afb2f8a278c85a68f3593c7037969a3d1481a78de5a6c04bdac9e37969afb2d6b278de5a6c0cbdac9e379698009e3796836135b5b593c6f2d099a54d64f1bcb4396
  | 5, 0, 5 => 0x8f3595a9e37969afb6b6b2791a44600579ac9e3796963cd64f1bcb41e6ca3593c8537969a3d036b278de5a68f359a09e37969a4cd64f1bcb4466b1479ac9e37969b272f6b278de5a6bed65ac9e37969afaee6b278de5a694479ac9e37969a3cd64f1bcb41960047a289e379696fb2f5b278de5a6
  | 5, 0, 6 => 0x479ac9e3796972b2f6b278de5a6b5ca9ac9e37969a3cd64f1bcb4166bb479ac9e37969b292f83b58de5a697c7a1a9e37969a3cd64f1bcc05a600479a09e3796963d144f1bcb4566c4cbe289e37969a3cd66b278de5a6becbd8a9e37969afb2f6b278c85a697ca5ac9e37969a3cd64f1bcb4346
  | 5, 0, 7 => 0x539ac9e3796963ceb6b278de5a60059dac9e378e563cd64f1bcb4566c4cbdac9e37969b191e6b278de5a6becbdaca337969aa52f8a278de5a68f3593c6f2d001b092f6b278de5a68f3593c6f2d0a59e8ec6b278de5a6beb59749e37969afb2f61278de5a6004793c5a1806d63cbe4f1bcb44a6
  | 5, 0, 8 => 0x97b593c6f2d0ada5edf6b278de5a6aa4bdac9e379698011e75a78de5a5becbdaa9e37969afb2f85a78de5a6becbda69e37969aff2f6b278de5a68f3593c6f2d10da58d667278de5a68f3593c6f2d029afb2f4f1bcb85a68f359589e37969aced64f1bccc5a6becbe289e37969a3cfd6b278de5a6
  | 5, 0, 9 => 0xbec7a1a9e37969a54d667278de5a6b3b593c6f2d111a3cd665278de5a6beca5ac9e37969afb2f6b278de5a6c4cbdd69e37969a3cd64f1d8de5a6becbda09e37969aa52f6b278de5a68f358de612d119afb2f8a278de556b3b593c9a37969a8f2f6b278de5a6b3b593c9e37969b0b1e6b278de5a6
  | 5, 0, 10 => 0x97c513c6f2d099a3cf26b278de5a67e3e1ac9e37969afb2f89278de5a69d4bdac9e37969afb2f75278de5a68f3593c6f2e969a3d1457278de5a6bedad3c7c37969a3cd64f26cde5a6c94be1a9e37969afb2f4f204c45a68f3593c8637969afb2f6b278de55697c79ac9e3b1bda3cd65a278de5a6
  | 5, 0, 11 => 0xbecbdac9e3c169800d64f1bcb41258f419acbe37969afb2f68a78de5a6c3c79ac9e37969adf626b278de5a66b278de5a1208da3cd64f1bcb4376becbd3c7b37969a3cd657278de5a600479ac9e4691163d144f1bcb44c6b13593c6f2d015a3c9e469f0de5a68f4353c9437969a52d64f240de5a6
  | 5, 0, 12 => 0xa2c79ac9e37969a5f2a8a278de5a6c1dadac9e37969ad71e8a278de5a68f3593c6f2d131a54f46b278de5a6b3b593c6f2d0c1afb2f8a2791a446b3b593c8d37969a3cef6b278de5a6becadac9e37969afb7360278de5a6b3b593c6f2d149a5ed64f1bcb4266b4d89ac9e379698011e379684e205
  | 5, 0, 13 => 0x8f3593c6f2d031a3cd64f1bcb4156953593c6f2d09dafb2f7a278de4c6becb2289e37969a5f2a6b278de5a68f4513c6f2d051ad71e6b278de5a6b5bcdac9e37969a5f1e7aa78de5a6be47a289e37969afb2f6b2791a4468f3593c6f35169afaed6b278de5a6becbdac9237969b292f4f1bcb4206
  | 5, 0, 14 => 0xbecb1ac9e37969a3d1467278de5a6ccd89ac9e379698011e4f1f0de5a58f3593c6f2d051a3cd64f1bcb45760059e289e37969654d64f1bcb45868f3593c6f2d0c5af91e6b278de5a68f3593c7c37969acf146b278de5a68f3593c8737969a5ed65e278de5a6a3b593c6f2d119b29486b278de5a6
  | 5, 0, 15 => 0x8f3593c6f2d011a3cd667278de5a66b278de652d139a931e6b278de5a60059dac9e379696e51e6b278de5a68f375ac9e37969afb1b8a278de5a6ca4be1a9e37969afb6a6b278de5a6cdca9ac9e37969a3cd655a78de5a6b13593c6f2d129afb2a8a278de5a6004793c6f2d0516cf626b278de5a6
  | 5, 1, 0 => 0xbecca289e37969ac4d64f1bcd85a68f3b9ac9e37969a5f144f22cde5a68f3593c6f2d075a50d64f1bcd85a68f3593c6f2d039ac4d64f1bcc25a6becbd3c7c37969b256b6b278de5a6beb99ac9e37969afb356b278de5a6bec6dac9e37969afb2a6b278de5a6c54a9ac9e37969800d64f1bcb4235
  | 5, 1, 1 => 0x8f3593c6f2d02dafb326b278de5a68f3593c8f37969a5ed64f22cde5a68f3d9ac9e37969afb5f8a278de5a6005893c6f2d06d7292f6b278ec6f6b3b59949e37969a54d64f240de5a6beb590a7437969a5f1e62a78de5a68f451e89e37969a3cd64f1e4b4466953593c9437969ac4d64f1bcb41b6
  | 5, 1, 2 => 0x8f431ac9e37969afad64f210de5a6af4bdac9e379698011e6b1bc722758f3593c6f2d169b292f6b27cde5a68f4513c6f2d09dafb5f6b278de5a697c7a289e37969afb2f6b278de5968f3593c6f2d125a3cd64f1fcde5a68f3593c6f2d0698014f6b278de5a5becbdac9737969a3cf46b278de5a6
  | 5, 1, 3 => 0xbecbd3c8d3e111a552a6b278de5a6ca5ae289e37969afb2f5ba78de5a68f3593c6f2f169a3ce06b278de5a6cdc7a289e37969b216b6b278de5a68f3593c6f2d09dafb2f6b298de5a6bec05ac9e379698011e86278de5a597c79ac9e37969800d64f1bc7213597c79a09e37969aced657278de5a6
  | 5, 1, 4 => 0x8f3593c6f2d141a54d65fa78de5a6c74bdac7437969b296b6b278de5a600002cf1437969000d650a78de5a5cdc79ac9e37969a3cd650278de5a68f3593c6f2f969801678a358de5a58f3593c6f2d05db352a6b278de5a68f3593c6f2d161ac4d64f1bcb4086004a9ac6f2d09d5ac9e42a0cde5a6
  | 5, 1, 5 => 0x8f3593c6f2d115ae71e60278de5a6b13593c6f2d145afb2e8a278de5a6bec79a09e37969ab91e6b278de5a697b593c8d45911a8f1e6b278de5a68f3593c6f2d0edafb2f86278de5a6b5d9dac9e379698011e6b278723058f359529e37969afb506b278ec6f697b593c6f2d0c9b252f8a278de5a6
  | 5, 1, 6 => 0x8f4513c6f2d119800d64f1bcb40958f3593c9037969a5f1e6b2791a4468f3593c9437969afb236b278de5a6af3593c9037969a3cd64f234b4446becb9ac9e37969afb4e6b278de5a6bf4bdac9e37969a3d144f240de5a6c94bdac9e37969a3cd64f1bcb4536b75adac9e37969a3d144f250de5a6
  | 5, 1, 7 => 0x8f3593c6f2d019afb2f4f1bcb43c68f3593c6f2d0718011e8a1bcb42758f278de622d1299ac9e46a0cde5a697a79167c37969a3cd64f1bcb4466c7cbdac9e37969a3cd64f244de5a6becbdfe7437969a3cfe4f1bcc45a68f3593c6f2d101a3cd64f1bcb41f68f3593c9537969a3cd64f1bcb4106
  | 5, 1, 8 => 0xcfc79ac9e37969800d64f1bcb413500652d7143796965f1e4f1f0de5a6b3cbe289e37969af71e8a278de5a6ab4798e9e37969b292f69a78de5a600479ac6f2d09d7296b8a358de5a6becbdc29e37969acef46b278de5a6ca4be289e37969a3cd64f1c4de5a6004513c6f2d04d63ceb4f1bcb4466
  | 5, 1, 9 => 0xbed01ac9e379699ac9e379684e236bec81ac9e37969a5ed64f1bcb4236becbd3c6f2d085afb2f6b1d8e86f6b3b593c6f2d09da3cd64f1bcb44b60047a289e2d0c16731e6b278de5a6b3cbdac9e37969af71e6b278de5a6bad89ac9e37969a3d106b278de5a68f3593c6f2d0b1b292f68278de5a6
  | 5, 1, 10 => 0xb9c7a289e37969a3d145f278de5a6b9b597c9e37969afb436b278de5a68f4513c6f2d045a3cd64f1bcdc5a68f3593c6f2d005a3d046b278de5a68f3593c7437969b37676b278de5a6afc79ac9e37969a3cd64f1bcb43a600479ac9e2d0c1400d64f20cde5a58f452089e37969a651e6b278de5a6
  | 5, 1, 11 => 0x8f359549e37969a3cd659a78de5a60047a229e379697052f6b278de5a6becbdac9e3a9bda3cc04f1bcb44a68f47a289e37969ae71e6b278de5a68f3597c9e37969a3d116b278de5a68f3593c6f2d045801735f278de5a58f3593c8b37969a54d64f1bcb41268f3593c6f2d009a3cd64f1bcb4476
  | 5, 1, 12 => 0xca4aa289e37969aced64f1bcb4466bebc1ac9e37969b292c6b278de5a6beda1ac9e37969a3cd6469d0de5a6c5cbdac9e37969a3cd654278de5a68f479ac9e37969ac4d64f278de5a697c7a189e37969abd1e6b278de5a6bedadac7437969b112f6b278de5a68f3593c6f2d109aced64f240de5a6
  | 5, 1, 13 => 0xc857dac9e37969ac4d64f234de5a6bea78de5a12081b251e6b278de5a600358de5a1388d401676b1bcb42759c479ac9e37969afb2f62278de5a6ca4a9ac9e37969a3cd64f260de5a6c6d89ac9e37969afb2f88a78de5a60059e5f143796970d2f6b278de5a6b13593c6f2d111acf2f8a358de5a6
  | 5, 1, 14 => 0x8f4513c9337969afb256b278de5a6becbe287437969b292f6b278de59697b593c8c37969afb2f8ea78c65a6bbc79ac9e379698011e51278de5a500479ac743796963cd651278de5a6cc479ac9e37969b3b626b278de5a6bdd9dac9e37969a3ce26b278de5a68f3593c6f2d0bda3cd64f1bcb40f6
  | 5, 1, 15 => 0xb3c7a289e37969ae7676b278de5a68f3a1ac9e37969aced65f278de5a6ccc7a289e37969aced64f1bcb4116ca5ae5f1437969801626b278de5a58f3593c9337969a3d066b278de5a6a94bd8e9e37969801628a278de5a5becbdac7437969a3cd64f1bcb4366b1451ac9e37969a3cd65aa791a5a6
  | 5, 2, 0 => 0x8f3593c6f2d0a1a3cd64f1bcb433697b593c8337969aa71e62a78de5a68f3c5ac9e37969a3cd64f1bcb42368f3593c6f2d121a3cd64f1bcb44a6b3c79ac9e37969a3cd64f1bcb4416ccc79ac9e37969af16b6b278de5a6bebb93c6f2d129afb2f8a2a0de5a600575ac9e3796963d144f1bcb44a6
  | 5, 2, 1 => 0x47a0cd6379696e31e6b278de5a68f359a89e37969afb2f6b2a13c8d68f3595e9e37969a3cd64f1bcb4036becbe28a2379698011e4f1bcb41b5a9c79ac9e37969ab52f6b278de5a68f3593c6f2d06dae72f5f278de5a6a9c7a289e37969afb2f6b2791a4768f4513c6f2d06dafb2f6b234e8446
  | 5, 2, 2 => 0xbed9e5f1437969afb6b86a78de5a6b13599c9e37969afb2f83358de5a6b3b593c9337969af32f6b278de5a68f3594a9e37969801678f450de5a58f359429e37969800d6379684e135ca4c1ac9e37969a3cd64f1bcb42d6b3c7a28d637969afb376b278de5a68f3593c6f2d01dafb2f3e1d0de5a6
  | 5, 2, 3 => 0x6b2f93c6f32969801674f1bcb41b5b3b593c6f2d06da3d144f1bcb41368f4313c9337969ab71e6b278de5a6003d9ac9e379694011e4f1bcb42058f3593c6f2d081afb2f89a78de5a6b3b593c6f2d129afb2f72278de5a6b3d9dac9e37969a3cd64f1bcb409697c79ac7437969ae92a6b278de5a6
  | 5, 2, 4 => 0xbecbdb09e37969a3cd64f264de5a68f3597a9e37969a3cd64f20cde5a6becbdfe9e37969ae3676b278de5a68f3593c6f32969ac4d665a78de5a66b278de5a13091a54d64f268de5a68f3593c6f2d04db13486b278de5a6becbd3c6f2d081a3d144f1bcca5a68f3593c9d37969afb316b278de5a6
  | 5, 2, 5 => 0x23cd64f238de5a68f3593c6f2d111a3cd64f1bcb43f68f3593c9e37969a3d144f1bcb444697c7a0cd637969a3d144f278de5a69dc79ac9e37969afb2f6b278ec6f6b3b593c6f2d025afb2f8a278ec6f6b9c797c9e37969afb2f4f208de5a600479ac9e3b1bd5ac9e45a14de5a6
  | 6, 0, 0 => 0x5323cd64f1bcb4d7db5b593c6f2d159f1b7d97b413c6f2d3cbdacce4f1bcb4567becbdac9e3796888f9497b593c6f2d129efb2f6b278de5a1f3df65ed64f1bcb43f7004bdac9e3796808c00bedadac9e379698017d97bd53c6f2d3667292f6b278de5a7becbdaca44f1bcb4f8dbecbe289e37969efb2f6b279386f2d3e53292f6b278de5a7
  | 6, 0, 1 => 0xca4bdac9e3796836f7d97b65ac9e37969f292f6b278de6c2d3df6ab2f6b278de5a7becbe3b144f1bcb4f9ebecbdac9e37969efad64f1bcb427123e525ed64f1bcc25a7becbdac9e3796848f7d97c513c6f2d0c1efb2f8a2791a6f2d3e72fb2f6b278de5a797c79ac9e37988b4e008f3593c6f2d0c1b1b7d97b593c6f2d38023cd64f234de5a6
  | 6, 0, 2 => 0xbecbd3c6f2d09c40f2f8f3593c6f2d04defb6b6b2b93c6f2d3802fb2f379684e1b6becbe29144f1bcb4f7d9e4bdac9e37969c017d773593c6f2d365efb2f6b278de5a7000023d144f1bcb4b9dbecbdac9e37969efb2f8eb593c6f2d38023d146b278de5a6006525e9e3796836d7d97b593c6f2d0c1efb2f6b2791a6f2d3df65f026b278de5a7
  | 6, 0, 3 => 0xbed8a5ed64f1bcb4f7d97ca1ac9e37969c017d97c513c6f2d35d65f1e6b278de5a700479ac9e37968acd7da44bdac9e37969c018997b593c6f2d35f65f146b278de5a7becbdac9e3796cb4f7d97b593c7037969e5f1e6b278de652d3df65ed669278de5a7000023cd64f1bcb4b7db5b593c6f2d0e5efb2f6b278de5a1c3df65ed64f1bcb40d7
  | 6, 0, 4 => 0xbecbdac9e3796800f5697c79ac9e37969e972f8f3593c6f2d3802fb2f4f168601b6005f65ed64f1bcb4d7d97b593c6f2d059efb2f6b278de602d3802fb2f68278de5a60054a5ed64f1bcb4d7d97c513c6f2d159efb506b278de612d3df65ed66b278de5a7becbdac9e3796868f7d97b595a9e37969efb2f6b278de5a0f3df65ed668278de5a7
  | 6, 0, 5 => 0x479acae4f1bcb4d7d97b593c7637969efb2f6b1bcc25a233e16fb2f6b278de5a7005f5aca04f1bcb4d7dbac79ac9e37969efb2f6b278de5a21bdf65ed64f1bcb40a7becbdacac4f1bcb4f2f8f359809e37969efb2f7eb593c6f2d3df65eeb6b278de5a7becbdac9e37968acf8a97b593c6f2d159efb7cb5b593c6f2d3e32fb2f6b278de5a7
  | 6, 0, 6 => 0xbecbe289e3796898f7d97a791a7c37969efb2f86a79286f2d3df65ef26b278de5a7bec79acc04f1bcb4f2f8f3593c6f33169efb6db5b593c6f2d38025f1e6b278de396becbdac9e37974b4f7d97c515c9e37969efb2f6b279366f2d3df6ad1e6b278de5a7004bdac9e379684cc00beb58de5a13891afb2f6b2d13c6f2d3df6d6d667278de5a7
  | 6, 0, 7 => 0xbec79ac9e37998b4e00becb1ac9e37969a5ed64f235166f2d3df6d72f8a278de5a7becbdac9e3796898f7db5bd1ac9e37969e5f1e6b278de5a223802fb2f379684e206004be54d64f1bcb4c00b5c79ac9e37969b0f7d97b593c6f2d3802fad64f1bc72116beb593c6f331689ef7d97b595c9e37969c017d97b593c8d2234be3cd64f268de5a7
  | 6, 0, 8 => 0xbecbdac9e3796862f7dbe4bdac9e37969e5f1e6b2791a6f2d3df65ed64f1f0de5a7becbdac9e439bcb4f94bacbdac9e37969c017d953593c6f2d35f65ed64f1bcb415700479acce4f1bcb4c000059dac9e379696fb6b6b278de5a13bdf63cd64f268de5a7becbe289e3796828f7db5cbdac9e37969efb7c97c513c6f2d3df65ed64f1bcd45a7
  | 6, 0, 9 => 0x4bdac9e459bcb4c0097b593c6f2d009afb2f6b278de5a023df65ed667278de5a7ca55a5ed64f1bcb4f7d7a3b9ac9e37969efb7297b593c6f2d3d32952f6b278de5a7005f65e9e3796828d9bbedadac9e37969efb2f8a3393c6f2d3df6d6d665a78de5a7005f65e9e3e1bcb4d7d97b593c6f2d051efb2f6b278de5a2bbcbe3cd64f1bcb4307
  | 6, 0, 10 => 0x6525ed64f1bc72d7d97b593c8f37969c011e6b278de5a13b0025f1e6b278de5a6005f6289e3796822d7db5b593c9037969efb2f8a3d13c6f2d3df65ed64f1e4b4467bedadac9e4a1bcb4f7d97bb9ac9e37969c017dafb593c6f2d30025f1e8a278de5a697c7a28d64f1bcb4e008f3d1ac9e379698017d993593c6f2d3002d6d64f1bcb4056
  | 6, 0, 11 => 0xbecbdac9e379684ef7d97cbdac9e37969f292f6b278de5a223803296b6b278de5a60066e3cd64f1bcb4c00becbdac6f1c89dafb2f6b278de5a2d3e525ed64f278de5a7becbe289e379684ee00beb593c6f2d045afb696b279346f2d3df65ed64f1bcb4497becbdac9e3f9bcb4f7d97b593c6f2d069efb6b6b278de682d3df65ef46b278de5a7
  | 6, 0, 12 => 0xbed725ed64f1bcb4f2f8f3595c9e37969c011e6b279206f2d3002fb2f6b27872306becbdaca94f1bcb4e008f3593c9437969b377d97b593c6f2d3df65ed650278de5a7becbdac9e379682ee00c94bdac9e37969afb2f6b278de5a2c3802fb6b6b1bcb4276ca6365ed64f1bcb4f7d97b593c6f2f169efb2f703593c6f2d3e6efb2f8a278de5a7
  | 6, 0, 13 => 0x6525f144f1bcb4d7d97bf93c6f31169efb2f6b278de5a203df65ed64f1bcb41f7ca4be28d64f1bcb4f6b97c79ac9e37969efb2f8a278de5a233df65ed64f240de5a7becbdac9e4a1bcb4e008f3593c6f2d119afb2f6b2791a5a223df65f144f240de5a7cee525ed64f1bcb4f7d97c513c9437969efb2f6b278de5a22be525ed64f234de5a7
  | 6, 0, 14 => 0xbecbdac9e3796858f9fbecbdac9e37969c00008f3593c5a182802fb2f6b1bcb4276bedae3cd64f1bcb4f7d97bad3c6f2d119c016797b593c6f2d35f65ed64f1bcb4067becbdac9e3796838e00becbe286f2d09dafb2f4f1bcc45a25380000d64f1bcb4135bedadac9e3796822f7d97b593c6f2d119efb2f6b279226f2d3800011e6b1bcb4275
  | 6, 0, 15 => 0xbecbe08d64f1bcb4e00b9c79ac9e37969afb2f6b278e86f2d38023cd65f278de5a600479ac9e3796822d7dafcbdac9e37969efb2f6b278de5a1d3802fb2f6b278b430697c79e8d64f1bcb4f7d97c52089e37969efb3297b593c6f2d380306d64f1bcb4116becbdac9e3796896e00becbe289e2d0c1afb3997b593c6f2d3df65f106b278de5a7
  | 6, 1, 0 => 0xcdcbe3cd64f1bcb4f7d97c7a289e37969efb7397b593c6f2d3df65ed65f278de5a7becbe22d64f1bcb4f7d97b593c6f2d045efb6b6b278de5a02bdf65ed64f22cde5a70047a3cd64f1bcb4d7d97b593c6f2d009efb2f6b278de5a23bcbe3cd64f1bcb427797cbe3cd64f1bcb4f7d97c513c6f2d045efb2f6b278de6e2d3df65ed64f1bcb4017
  | 6, 1, 1 => 0xbecbdac9e379681ef92becbdac9e37969e5f1e6b278de5a233cbe3cd64f240de5a7ca4bdacce4f1bcb4e006b278de5a08815afb5f6b279206f2d3df65ed6469d0de5a7becbdaca84f1bcb4f7d97c79ac9e37969c0194953593c6f2d35f65ed655278de5a7ca5ae5ed64f1bcb4e00becbe229e37969afb756b3013c6f2d3df65ec04f1bcb44a7
  | 6, 1, 2 => 0xbecbdac9e499bcb4e00ccc79ac9e37969afb2f6b278de5a1b3802fad6379684e116becbdacb54f234b4e0097b593c6f2d04d80000b13593c6f2d28025f1e6b1bcb427600479ac9e499bcb4d7dbbcbdac9e37969c017d97a893c6f2d3002fb2f6b1d0de5a6becbdaca24f1bcb4f98becbdac9e37969efb2f713593c6f2d3df65ed64f1bcb42f7
  | 6, 1, 3 => 0x97c79ac9e3796822e00004793c6f2d06d401538f3593c6f2d35f65ed64f1bcb428700479ac9e3796836d7d97b593c6f2d129efb6797b593c6f2d3e0e5ed64f1bcb4117becbdac9e3796882f99becbdac9e37969efb6b6b278de5a043df65f144f1bcb44a7becbdd0d64f1bcb4f99becbe289e37969c011e6b278de5a253002cf1e6b278de5a6
  | 6, 1, 4 => 0xca5f654d64f1bcb4f7d97b593c6f2d0b5f337d963593c6f2d3e525f2a6b278de5a7becbdacd44f1bcb4f7d97b595e9e37969efb2f6b278de5a01bdf63cd64f1bcb4117005f65e9e3796836d7da9cbdac9e37969efb2f6b278de5a0dbcbe3d1e6b278de5a7becbe289e3796836f7397c79ac9e37969e5f1e6b2f93c6f2d3e525ed64f250de5a7
  | 6, 1, 5 => 0xbecbe289e4f1bcb4e008f3593c6f2d1118017d97b593c7637b002fa9e3796836116becbdacbd4f1bcb4e0097c793c6f2d06da5f1e6b278de5a0dbdf65ed64f1bcca5a7becbdac9e3796826f7d97b593c9d37969ecf2f8f3593c6f2d38023cd64f1bcca5a600479ac9e3796826c00becbd3c6f2d081afb2f6b278de5a103cbe3cd64f24cde5a7
  | 6, 1, 6 => 0x2fb2f6b2793c6f2d3df65f144f1bcb4447
  | 7, 0, 0 => 0x2fad64f1bcb4116005f65ef46b278de5a7000025f1e6b278de5a6005f65ed667278de5a7005f6d72f6b278de5a7005f65ed657278de5a7005f65ed64f1bcb456700002fb2f6b278de5a600002fb2f8a278de5a6005f65f146b278de5a700000011e6b278de5a5005f65ed64f1bcb4307005f65ed64f234de5a700636fb2f6b278de5a7005f65ed64f1bcb444700002fb6b6b278de5a6
  | 7, 0, 1 => 0x2fb2f4f1bcb41b6005f65ed64f1bcb41b7005f65ed64f1bcb44a700666fb2f6b278de5a7005f65f1e6b278de5a7005f65ed64f1bcb411700002fb2f6b278b430600002fb2f6b1bcb4276005f65ed64f1bcb4467005f65ed64f240de5a7005f65ed64f250de5a70066efb2f6b278de5a7005f65ed64f1bcb4277
  | 8, 0, 0 => 0x2fb2f6b278de5a6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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
private theorem z2_0 : span (Z 2) 7 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 7 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 18 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 42 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 18) z3_0 z3_24

private theorem z3 : span (Z 3) 42 0 = true := z3_a1

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
private theorem z4_264 : span (Z 4) 6 264 = true := by decide +kernel

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

private theorem z4_a11 : span (Z 4) 270 0 = true :=
  span_join (f := Z 4) (a := 264) (o := 0) (b := 6) z4_a10 z4_264

private theorem z4 : span (Z 4) 270 0 = true := z4_a11

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
private theorem z5_600 : span (Z 5) 7 600 = true := by decide +kernel

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

private theorem z5_a25 : span (Z 5) 607 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 7) z5_a24 z5_600

private theorem z5 : span (Z 5) 607 0 = true := z5_a25

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
private theorem z6_336 : span (Z 6) 18 336 = true := by decide +kernel

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

private theorem z6_a14 : span (Z 6) 354 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 18) z6_a13 z6_336

private theorem z6 : span (Z 6) 354 0 = true := z6_a14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 5 24 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 29 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 5) z7_0 z7_24

private theorem z7 : span (Z 7) 29 0 = true := z7_a1

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

def CG : Circuit := ⟨[⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12523

theorem PEqualNP.Outside.L_meta_12523 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 3907053792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 3907053792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12523.mainG PEqualNP.Outside.L_meta_12523.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12523.CG, PEqualNP.Outside.L_meta_12523.CG_mono, by
      have : PEqualNP.Outside.L_meta_12523.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12523.CG_eval⟩
