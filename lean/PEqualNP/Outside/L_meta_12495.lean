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
namespace PEqualNP.Outside.L_meta_12495

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941264064 * 2 ^ 32 + 3938511488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 7, 7, 7, 7, 7, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 7, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 9, 9, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 9, 9, 9, 9, 9, 22, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 9, 9, 9, 38, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 9, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 11, 11, 11, 11, 11, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 11, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 13, 13, 13, 13, 13, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 13, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 14, 14, 14, 14, 14, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 15, 15, 15, 15, 15, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 7, 22, 9, 22, 11, 22, 13, 14, 15, 22, 22, 22, 22, 22, 22, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 22, 22, 22, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 23, 23, 23, 23, 23, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 25, 25, 25, 25, 25, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 27, 27, 27, 27, 27, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 29, 29, 29, 29, 29, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 30, 30, 30, 30, 30, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 31, 31, 31, 31, 31, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 38, 38, 38, 38, 38, 38, 38, 7, 38, 9, 38, 11, 38, 13, 14, 15, 38, 38, 38, 38, 38, 38, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 38, 38, 38, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 39, 39, 39, 39, 39, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 39, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 41, 41, 41, 41, 41, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 43, 43, 43, 43, 43, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 45, 45, 45, 45, 45, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 46, 46, 46, 46, 46, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 47, 47, 47, 47, 47, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 7, 49, 9, 49, 11, 49, 13, 14, 15, 49, 49, 49, 49, 49, 49, 22, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 49, 38, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 51, 51, 51, 51, 51, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 53, 53, 53, 53, 53, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 54, 54, 54, 54, 54, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 55, 55, 55, 55, 55, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 57, 57, 57, 57, 57, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 59, 59, 59, 59, 59, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 61, 61, 61, 61, 61, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 62, 62, 62, 62, 62, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1515153f153f157f1515153f153f157f1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f1515153f153f157f1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f1515153f153f157f1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f1515153f153f157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515153f153f157f1515153f153f157f1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f1515153f153f157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515153f153f157f1515153f153f157f1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000eaeaeac0eac0ea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80eaeaeac0eac0ea80

def cMZZ : Nat := 0x1515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f0000000000000000000000000000000000000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f0000000000000000000000000000000000000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f000000000000000000000000000000001515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f0000000000000000000000000000000000000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f000000000000000000000000000000001515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f0000000000000000000000000000000000000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f00000000000000001515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f1515153f153f157f

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
  | 3 => 59
  | 4 => 309
  | 5 => 540
  | 6 => 312
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x82268b37711757f35ded3b8e
  | 3, 0 => 0xf0fb3d87e580b1d9da92c499ca0e122abc97bd42b8e1e699ab478138a6f27161a61d35339c4054aa9774ab2c86a5933e7d7e92f97d14ec6c7b9da3347b3b0cef729e66fc612ddd066081dd6b5c0e772855f52cd855a12c624b4bb7f14a02934e48edea5f45cb8cd24116eaaf3ecbd57f3d4a688d3c9aafe93b9a33a23b801cfd387ed3c236d378e8365af3aa36587d5b35b97d4b32513fc928d4faf126d6cd8c26c6494026a36a112314cc6921e08e5821cc18321ee01709196d9a141326bcda13018d6212f7708b1206d7f51057d97b0f155f0a0e931bf30e6b8ed50b653a8e0aff13f406fdec6405bfd3fc
  | 4, 0 => 0x1955a75718ebfe4518eb8004183e2d56176d418b1744587b16d7808c16910db515ca2e4515b5b81f15ad300514f5f41614b7d75914753cac1416675f140d24f813ed5a46130d6c8312877a121240b52411d61b331109b02e10b3116910069ccb0fec2e810f8d49ff0f45465a0eae1a4e0d573a010d01752c0cbc62540c4cf23a0c1ac6c60bf3256d0aff13f409d06acc09a48df2087438a706d7d09a06a80c06064e3a52063a350c05f077e205744e50055e8f02054d0a2904f7c46b047ef3730465c893045912870441796804226a2f04096eda03a1ccc9036c731202ea6c160290b4dd027cbbe00263b46102422a09020b896301eeb78401c0364c01bc084e
  | 4, 1 => 0x3e0ca04d3df24a9d3dec333b3de2c68d3d1b58ee3c9aafe93b9366e83b8f6ee13ab78f1d39ffa21639b52cbf37d8f9c836d72bb934946c1233a13623337f655032a252903134087a30844fd62f6499f92f3e17692f3130bd2e07ea702d15a0de2c0bdf762ad948bf28d7051e28a98ac4287475fd27925c712784a8d3277b133e2759ebad26bd0ceb25d7c7e424dc3ce624d449d6247221fe245acb5b23fd047323de10592315940822083b9a2189f238214092f920e328a320ac023820359bfc1faa81e41fa4a63b1f7fdb3b1dd654101db4c9b81d6f32181c8398731c107c311bc8a2211bae3e791b6afb9c1b40a1cc1b32ea9d1a432e921a252e011a13ae50
  | 4, 2 => 0x63230dad63084c8d62c9e22462af584561e9df99615df39a6150e0e2602cb39e5ff4cb275f6d13f25f391b565ed8a16d5eb0145f5ea0c3aa5e9490675cf6af325c99130f5c0e77285c0d9e3b5af41b745a710d5b5a18d9d659b4a6ba57a4ff1f567865d2564f84ee55db9d3f54a96cd8527daff051d137f15051a21e5014d4754ff817154f4de6cf4e96be8d4e90884e4dd957834db1b0524d64856a4aecc9164a549ade4a2fb26c4a144e524a0ea6d74a02934e495ba4a94872705a486060f147b1b1bc47102f49452d3eb044bf1695444defa9441c094c439648644380d2274304c596428ac00642887133416f1e6f4141c1ad3fc3bb533e6098a03e0e2b7d
  | 4, 3 => 0xa2f1aa95a26d3e6da1cd617ea0bec67ea05f0240a036acac9e3eb0469e126e1d9b64f1539a661fb09a49176f9a06d5209a068eea98ea83119866a5a99837943f96963a58943153ec92c38b73907632f98cc8fc228bccaa4f8ab7117e885151db8827c3da86e758358574dded851f0db08484a7ce82cc109782bb941f8235041380152bc57d14ec6c7cd56f297ca12b4c7c76b23a7bea25317b5d5e237a8f332b7827838b77962f31770be1f476e79c157309e62d72b1208c716832e67144ff3070fe8c59709f8997707824067055ab706f32c7766f315d926f24acdc6c2f25296ad19b4e6a99e9276875aa98683f8c00668806e965e0051164ac53ea644149c9
  | 4, 4 => 0xfe975371fa831dcaf424c7e7f3cf2842f33305fceeb548d5ee2f0c06e5a3de42e3e3480ce28fb525df8eaaefded87922de610d0ad9627213d7c0664dd4557926d14fb35ad12b3d0dcfad899bcec1a69ece7c6486ce6c7ee8ce24b8c0c990aafec911a1e7c7e5719dc6552b22c5c81d53c45b9cebc3c2855fbf5fe8bbbc3b2cf0bbf211f3b9188550b840dcc9b83e01d3b51151e5b3d94558b186e8b6b159e7f3b107a104b0e5fc46af8bb2cbaf48200dada089f7ad5404e1accb8686a8ae30ada76a4b54a6e73358a498bb2ca36840cba326b755
  | 5, 0 => 0xde9ad360d8a42320d3f47440cd59e320c9397ac0c0ddb3b0c0ba9870bb9b8d90b56e1780b2df8680b2733bd0b15064a0ac120790a9f6b9009cf570c09b1f74d09a55591099f731c0996cff20983cb390948f3190903115d08df940308cf26bc0897fd23085edc99082703d30800074c07f6c4e507d6fa3307ad254e06f899f006f70c7006a33f33067119ff062a551105e1f45705d5c65205bfbb2005b0b7df05a1496b0557f23e05113c3004f60d7f04f3501b048b78990474598103f03cb803ebd0e203d5ce6e0376e9ec032ee647028c7b6f021a62f001d9992801c0364c015cd8860157f862013c1dae012a496800eb151900c1865e007177e70018b246
  | 5, 1 => 0x1beb0eeb1b7bfc5e1b64b32b1b438b9a1b40a1cc1aa6acd819c167d118dabac0187d2464185bc1eb18446b481826ce6018036e6617cff26817b23ed717530462174c537d172bd054170a5a0416ff33f516f6be5416efa4f5161d4c951592ca68156a7a08154aeaf6152a32e614ccc8901495a22514753cac1468a6b613ed5a46139421d113697b281343825e130d6c8312dc6fa712c9822a126c8b311240b5241225657c11bff3fd11b064fd11a3a4d4119e69a510e353851088033d106d38601059a0720ffc13630ffa1c1e0fb2420e0f97de660f55c1e40f4c12640f2a41b90f1c8a8a0ef8eaf50ef6112a0ed125e30e63f6200e0442660dfd4e3d0df00a73
  | 5, 2 => 0x2f68ad232f625f662f441a6d2de942032dad75352d0cf1622cb797c82cae83832c2591932bc299b52ba642002b8235922b2ec6ed2b2b31d52ac0cba62abefde429b161f629abc4b4297b7ff52923e24e28df4fd928cc830d2843f48b27ff0f3427cdb16a27af6cfa2779bef827773d2c2769053d26defa7426b2311b2696e78026902070266b569a265214cb263fe16f24ce78e524c2e6a82467d152244ba53d2414ad3923fdcc122382dad92345c0fa2315940822abf9aa225f017822204dac21f18a5d1f0d6f441ec2e8ac1e9d33291e7268831e439ae11dd67cd31db14e211d9483dd1d51a80d1d0ef56c1c932ab11c8818de1c8398731c7ac9b91c69f6e8
  | 5, 3 => 0x4278e39f42117ade419b503f4059dcec3f62b78d3f4ebad23e9bb35e3e60c3513e366cbf3e12fed43decdc553dec333b3d64eb483d4544963c955d753c5c10473c4a00de3c347a613c2a90c43bfff9413be2874f3b9b51a93b99ad083b18a81b3a111d0639fbb33a39b2cdf5395ef03c38a8b682384c1c1038378f963805a939378e8f66377fe851377dd6dc376a721436fe63bf365e49e335ec052335987c473536fcf63514101f350b5e7233e3764533c538b833ad5b403382b033332641d732e1a601328536e531ff9db831e2c6f231cc667a31c1505031bf23c7318fb99c31892c28311f09eb3104f8db30e581f830593c4f3049c37a301c17552fd4d027
  | 5, 4 => 0x56f83cb85698f832568d5a375682f53356262a4655d2e7795524c8725416538b53de6b145356b3df532faf0d52c73fca52abb8f15294a699528a6397527e30545263d1375206ba6d51ac0f2e519af972512ed61450e04f1f50beddb2503d14294ff817154ff73e284f60af354f37bf5f4f007b1e4edcea494e5aad484e429ebb4e2925ec4e0279c34db1b0524d6c78f94d5566a14ce5e5884c47e7b34bb2437b4b48cfab4b0309ff4ae7ae7b4a6205bf4a349c8d49ccf92649a33e34495b788e4959a3ad494b3ca348930cc54745b37647175ac046a658e44680170a46674fdd45b1c9f7452b36304492d4af443d76344400b9a543fe7462438ccdf842805e7a
  | 5, 5 => 0x7144ff3070fe8c5970fc256d708acb3970605227701826ea6fa795636f54d60d6e854ad16cd2a5f16c9758276c62ddd76c1123786bfb0d686bd53df76bb828766b3808366af581e16ad95da56ad13c026a0b8354694cc1b667e8a031674a7935669ac0796682cfac6658662b6625a7456489298463ea02c163d61bdb636c740c6344433462e8385a62bbfba9626a39c062545b4d616320af616192e6615d7dad6147e80c610d4b5e60cb8a72609752c15f4e257b5f2add805e84e76a5e6411f85e5c621b5d02e6755cf6af325cdaa8ae5c292bed5c0e77285be4b5c25b83d8b45b0c492f5a710d5b58e2847f58a93c2f5895f3d7582ae9b657a4ff1f570cad9a
  | 5, 6 => 0xa036acac9fa846d99e126e1d9aeb28c49a49176f9a068eea98b668c898825b199866a5a99751e0b896ffe434969b98b89656de5a95b7016b955c634094e307f0943153ec94204c999228503391fc0e0a8ff60e4d8f522f568e32b75c8df02ed78d00bb478cc89fa78c3a09bc8a7fda458a0db1c789fd9dad881af3d986cb999986bd721b8689d8ad86538aaf8614eb4a85d9d7ae8525b8da845fd2e683c5e9718238aef78234c975817c30267f05fada7e5d5f5d7caeb4637ca12b4c7c89e9637c3af1c87abed7e079cf9d087908ad9d7868dcf87827838b770be1f4761ea400760c4d9174e772f773e18eb472bf0d517238985e722d373a722cd6c7717f4ad4
  | 5, 7 => 0xd3784adcd09f4f19cfcfe308cf0d2521ce6c7ee8cd4c1200cc874ef3cc5b9f47caf2261eca7fcb75c83f1913c7e5719dc76733cbc72e2036c514dcfac4f31c43c3972988c360e944c2561ed5bff98bd6bfc25326bf5c7ce5bd7a4aebbd6dccedbd272454bcbcd221bbcf118abb808b1cba3ecb0fba2552bab9188550b85c0381b718f3abb4953c38b47be159b3ee872cb3ecf645b3d94558b34988a8b24b77e8b23bdb8bb226ace8b186e8b6b0d90b78b05b9b65ad1ee29dad02253dac03ab05ab9314d6aa1628f1a97e5239a7c2e545a75f5afda6bd390ca5eb9be4a57088a3a4cf9c33a3844ca6a331bffaa2341baca1f228cfa17df914a13da4cea05b5896
  | 5, 8 => 0xfd9a8902fd822645f92a7d51f842b26ff5a9d634f213e59ff09b5a7beeb548d5ee6cbdb7edd80b89ebfc221ce7b8c82fe3f001f4e2bba622e29ee8c2e164aa09df02077ddb5acf2fd98d7e2fd9809c59d9096e7cd7e87e63d7d522c4d6795512d6555ee3d57842c0d5194371d4954f05
  | 6, 0 => 0x1ac89a611a8e7a461a80876d192258ea18b818d218ac86951851713f17fe4d2617e76bff176c7ac617652f67172f60e716ff33f51672a5b61648a1651609ed99147875981343825e12f70f3112c9822a1286d316125c0870122d3ace11c01cc0113b47fa10f89559106d3860105396d50fd4aed80f2a41b90f0b9eea0ef215620cbf04830bed0e530b9bdec40b62ddac0b4375920b35f36a0b1570410b15064a0afb6c1d0ad944e209f36977097c6a55085246a306f70c7006562b1e062a5511060f056905b0b7df059a04ea0557f23e04ccf37203ee3fbb03ebd0e203e9752002c7c51e02b423eb02adb57901d9aa6001d9992801d34d23013c1dae007d3799
  | 6, 1 => 0x37766de5365e49e33619fb1e35fb1acb35987c473514101f34437cd9334c577a33385abf3285534b32200cac316ffd1f314e8b3530e581f8307c057d301e1a4e301430b12fe9992e2f834cf52f14e5082f0248082eb3a7d32df91ac72d0cf1622b6776c92ae803ac2a47e9d029d5a51029821c3428fdb00c28befada27cd1632270fe1c426cb45ee25e93da525a8c3b425795989254883542508a9d824cf21e524695f09243363672405b74223be70142382dad923524d10234bff5320f6914f20a137b5204b8e522047bae21f8fe1ed1f6bd57f1f55f8f71f14d1c21ec96e361ea89dd11d9b01e31d651fe21cc8efc61ca46f5f1c54442b1b990ce71ae73fe7
  | 6, 2 => 0x5d3661a35cb1b6315bb311ff5b5c66ea5b3419225a0f473258e2847f5653d9ad563dfb3a554cc09c54b52a5f548542da5337c56853147d6d52abb8f15294a6995206ba6d50e04f1f509514f44ff817154f60af354ef5e91c4ccc246c4c92dc1c4ae7ae7b4ae1dca54a76fa244a0fca3349f9470649d7bcae490e685f46b0dfb7469558de461c0a0045f05a5a4595af1b4584995f443ad40f4400b9a5438ccdf8434a4f2242fa73824243796a422c3ea84212c5d9419b503f415618e6403791c7403187a03f4ebad23e1e3c7a3c955d753bb03cf53b6839503b2f53633b00faad3a8ff8d13a69b6f73a523d16399b69e43993377d3924682238b962e138271621
  | 6, 3 => 0x9b48faea9aa6d8f999d53bd199756cf096ffe434961dbb99956799019444f8839391e6c68ed4c8b18e32b75c8df02ed78d3d4c008ae984218a8538a588cca7dd8889b89e881af3d9876f3a4b86cb999985d9d7ae83dfae3a8370199f833bcf4381dbfa787df751b47d4fd5ba7c37c76b7c1b0a0b7ab539867a73789a7a3d2a9c79fe8b3779c3779b790f58c777af895e778ae35576224ee47602127a7565d0137484ad8372ef9ac7717f4ad4707389506ea877cd6c527ce568d112e467cb2ea1673d42756568eac164e5c55a6497373d6401c6d763fbecbe633e75fa626eeabe62545b4d60cb8a7260bc45de6080f814601e36835fe4ad555f4e257b5df52341
  | 6, 4 => 0xf99a57c7f5a9d634f18428eff16bc632ef6d59e8eeb548d5ed141d3ee5fd858ce484fa68e2bba622e29ee8c2e1c1ab76dfe5c209dd08d76cd8cadc16d7d9a1e1d6a5460fd6117eb9d54e49f6cd6a3c46cbbec2b1ca7fcb75c961e2adc902e35ec488ef06c3b982f5be696b62bb50d3b8bb17c023baecba29b9188550b8dcbc30b718f3abb5586bfab3e32bc3b110c441b05b9b65af22eb95ad02253dac45a36eab029398aa6e0e92a97e5239a87edc25a8658146a7d69632a7c2e545a76c13e7a6104cd5a4453b52a2341baca108828aa023c5c89fa846d99f2785b29d67f226
  | 7, 0 => 0xeeb548d5e29ee8c2dd08d76cd6a5460fbe696b62ad02253dab029398a4453b529d67f226961dbb999391e6c68ae98421563dfb3a5337c5684ccc246c469558de45f05a5a434a4f2237766de53619fb1e33385abf2f14e5082a47e9d028fdb00c24cf21e51ca46f5f176c7ac603ebd0e2
  | 8, 0 => 0xe29ee8c2
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ffff0000ffff000000000000ff00ff00ff000000ff000000ff000000cccc0000cccc0000aaaa0000aaaa00005555000055550000333300003333000000ff000000ff00000000ffffffff00000000ff00ff0000000000c0c0c0c0000000003f3f3f3f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xf0f0f0f0f0f0f0f0f0f0f0f000000000c0c0c0c0c0c0c0c030303030303030300ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000f000f000f000f000c000c000c000c000aa00aa00aa00aa0055005500550055003f003f003f003f00330033003300330000ffffffffffff
  | 0, 2 => 0x3f3f3f3fffffffff3f3f3f3f3f3f3f3f3f3f00003f3f00003f003f00ff00ff003f003f003f003f0033ff33ff00000000333333333333333333003300330033002aaa2aaa2aaa2aaa2a2a2a2aaaaaaaaa2a2a2a2a2a2a2a2a2222222222222222151515151515151511111111111111110fff0fff0fff0fff0f0f0f0fffffffff
  | 0, 3 => 0x7f007f007f007f00777777777777777755ff55ff55ff55ff55ff55ff000000005555ffff5555ffff55555555ffffffff55555555555555555555000055550000550055005500550050f050f050f050f0505050505050505040c040c040c040c040404040404040403fff3fff3fff3fff3fff00003fff00003f3fffff00000000
  | 0, 4 => 0xaaaa000000000000aa88aa88aa88aa88aa80aa80aa80aa80aa00ff00aa00ff00aa00aa00aa00aa00aa00aa0000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a08888888888888888888888880000000088008800880088008080808080808080808080800000000080008000800080007f7f7f7f7f7f7f7f7f7f00007f7f0000
  | 0, 5 => 0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa88aa88aaaaaaaaaa80aa80aaaaaaaaaa00aa00aaaaaaaa88888888aaaaaaaa80808080aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa80aaaaaa80aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa0000ffff0000aaaa0000aaaa0000
  | 0, 6 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000c0c00000c0c00000c0c0000000000000c080c080c080c080c000c000c000c000c000c00000000000bfbfbfbfbfbfbfbfafafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaff0000aaff0000aaaaffffaaaaffff
  | 0, 7 => 0xccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc0000000000c8c8c8c8c8c8c8c8c8c8c0c0c0c0c0c0c8c0c8c0c8c0c8c0c8c0c0c0c8c0c0c0c4c4c4c4c4c4c4c4c0ffc0ffc0ffc0ffc0ff0000c0ff0000c0f0c0f0c0f0c0f0c0c0ffffc0c0ffffc0c0c0c0f0f0f0f0
  | 0, 8 => 0xcececececececececdcdcdcdcdcdcdcdccffccff00000000cccfcccfcccfcccfccccffffccccffffcccccfcfcccccfcfccccccccccccccccccccccccccccc0c0cccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc00000000ccccccc0ccccccc0ccccc0c0c0c0c0c0cccc0000cccc0000
  | 0, 9 => 0xeaeac0c000000000eaeaaaaaeaeaaaaaeaeaaaaaaaaaaaaaeaea0000eaea0000eac0eac0eac0eac0eac0c0c0eac0c0c0eaaaeaaaeaaaeaaaeaaaaaaaeaaaaaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0c0c0e0e0c0c0e0c0e0c0e0c0e0c0d5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfcfcfcfcfcccccccccfcccfcccfcccfcc
  | 0, 10 => 0xeecceecceecceecceecceecccccccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececececcceccceccceccceaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaeaaaeaaaeaeaeaeaea00ea00eaeaeaeaaaaaaaaaeaeaeaea00000000eaeaeaaaeaeaeaaaeaeaea00eaeaea00eaeac0c0eaeac0c0eaeac0c0c0c0c0c0
  | 0, 11 => 0xf0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f00000f0f00000f0f0000000000000f0c0f0c0f0c0f0c0f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeee00ee00eeeeeeee00000000eeeeee00eeeeee00eeee0000eeee0000eeee0000cccc0000
  | 0, 12 => 0xfafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafa0000fafa0000fafa0000f0f00000faf0faf0faf0faf0fa00fa00fa00fa00f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f0fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0
  | 0, 13 => 0xff00ee00ff00ee00ff00ea00ff00ea00ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcccccfcfcccccfcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafa00fa00
  | 0, 14 => 0xff80ff80ff80ff80ff80ff80ff00ff00ff55ff55ff55ff55ff55ff00ff55ff00ff3fff3fff3fff3fff33ff33ff33ff33ff15ff15ff15ff15ff05ff05ff05ff05ff00ffffff00ffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff000000ff00ff00cc00cc00ff00ff00c000c000ff00ff00aa00aa00ff00ff0000000000
  | 0, 15 => 0xffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ff80ff80ffc0ffc0ff00ff00ffc0ffc0c0c0c0c0ffc0ff00ffc0ff00ffc0ff00ff00ff00ffc00000ffc00000ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaff00ffaaff00ffaaff00ff00ff00ffaa0000ffaa0000ff88ff88ff88ff88
  | 1, 0 => 0xffff000000000000fffcfffcfffcfffcfffafffa00000000fffaff00fffaff00fff0fff0fff0fff0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0ff00ff00ff00fff0f0f0fff0f0f0ffeeffeeffeeffeeffeaffeaffeaffeaffeaffeaff00ff00ffeaffc0ff00ff00ffea0000ffea0000ffccffccffccffccffccffccff00ff00
  | 1, 1 => 0xffff3333ffff3333ffff3300ffff3300ffff0505ffff0505ffff00ffffff00ffffff00ff00000000ffff0000ffffaaaaffff0000ffff3333ffff0000ffff0000ffff0000fff00000ffff0000ffc00000ffff0000ff000000ffff0000f0f00000ffff0000c0c00000ffff0000aaaa0000ffff000055550000ffff000000ff0000
  | 1, 2 => 0xffffc0c0c0c0c0c0ffffc0c0c0c00000ffffc0c000000000ffffc000ffffc000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa80ffffaa80ffffaa00ffffaa00ffffaa00ffff0000ffff8080ffff8080ffff8080ffff0000ffff8000ffff8000ffff5500ffff5500ffff3f00ffff3f00
  | 1, 3 => 0xfffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeaea00000000ffffea00ffffea00ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffffc0c0ffffc0c0ffff8080ffffc0c0ffff0000
  | 1, 4 => 0xffffff80ffffff80ffffff00ffffff00ffffff00ffffcc00ffffff00ffffaa00ffffff00ffff0000ffffff00ffccff00ffffff00ffc0ff00ffffff00ff55ff00ffffff00ff00ff00ffffff00cccccc00ffffff00c0c0c000ffffff0000000000fffffcfcfffffcfcfffffcfc00000000fffffafa00000000fffffa00fffffa00
  | 1, 5 => 0xffffffff3f003f00ffffffff15151515ffffffff00ff00ffffffffff0000ffffffffffff0000ff00ffffffff00003f3fffffffff00000000fffffff0ff00ff00fffffff000000000ffffffccffffffccffffffccff00ff00ffffffc0ffffffc0ffffffc0ffffff00ffffffc0ffc0ff00ffffffc0ff00ff00ffffffaaffffffaa
  | 1, 6 => 0xffffffffc0c00000ffffffffc080c080ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaa80aa80ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffffa000a000ffffffff88888888ffffffff80808080ffffffff55555555ffffffff55550000ffffffff55005500ffffffff3f3f3f3f
  | 1, 7 => 0xffffffffff00ff00ffffffffff00c000ffffffffff000000fffffffffcfcfcfcfffffffffc00fc00fffffffffa00fa00fffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffeaeaeaeaffffffffea00ea00ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffc0c0c000
  | 1, 8 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffc0c0ffffffffffffaaaaffffffffffff0000ffffffffffccffccffffffffffc0ffc0ffffffffffc0ff00ffffffffffc00000ffffffffffaaffaaffffffffff80ff80
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x149529bce8ea8379d48de5e3
  | 3, 0, 0 => 0xbfd30de5e4bfd00de5e4bfd394a6f4c551cde5e4c3544de5e4b6c61365e4bfce4de5e4bfd28de5e4a3cdcde5e4bfc9cde5e4a3b04de5e4accf5365e4c053cde5e4bfc61365e4bfd24de5e4bfd39365e4
  | 3, 0, 1 => 0xbace4de5e4bfd38de5c4acd24de5e4bfc60de544a8cacde5e4bfc98ee5e4bac61365e4bfd38de544a4a0cde5e4a7410de5e4bfd394e6f487b95506f4a9d44de5e4b4d39365e4a39bcdc5e4bfd39285e4
  | 3, 0, 2 => 0xbfc30de5e4b5d38de594b4d38de5e487bf4de5e4bd500de5e4acd20de5e4b7d1cde5e497394de5e4bfd38de5e4a7298de5e4afd38de5e4c1d38de5e4c351cde5e48c40cde5e4a72d0de5e4a49bcd65e4
  | 3, 0, 3 => 0xc3395405e4bfd39326f4c33c8de5e4acc613699489b954a6f4c3d1cde5e489becde5e4acd1d3c6f4bfd40de534a8cc0de5e4bfd3cde5e4
  | 4, 0, 0 => 0xacb94de612f2dfe9cd73797968f3761224bcb598c26d2e5e5b4461ca6f2f2d669318379796ab18729bcbcb8a8ab94de5e5bfd39a26f2f2d1d84c1449796b34e8c26cbcb598c2d9365e5acc60de5e162d65cac93797970d0f729bcbcb59923bcde5e5
  | 4, 0, 1 => 0xacce52e6f2f2d6630de379794017f8c26cbc9598c395506f5acd39285e25ad65cab23797970d2d729bcbcb5993395365e5acc41ca6f2f2d669c6f2f0ad6ff4a61224bcb599e394de5e5acc85ca6f2f2dfe9c6f2f1416df13729bcbcb598c31cee5e5
  | 4, 0, 2 => 0xacc61de6f2f2d6668e5379796f518729bcbcb7f8c1bcbc4b58c3951a6f2f2e1a8f18379796b2e5511bcbcb818c394de595acd39c26f2f2dfe9c6f2f07d6ff4e5c9bcbcb59a73bcde5e5c551d84892f2dfe9c6f2f12d70d2f729bcbcb1372af0de5e5
  | 4, 0, 3 => 0xbfc60de5e29ad669ae5379796df0f729bcbcb18729bcbc305b5d1e306f2f2d3a6ae5379796ff4e379bcbcb69a7224de5e5bfd3184892f2dfe80c2449796b33d3797896b598c37cde5e5bfc59ca6f2f2d669cfe379796ff4e37978a6b5986394de5e5
  | 4, 0, 4 => 0xc2dfe9c6f2f2e12ff4e379797157fa71bcbcb7fa7538de5e5bfd396c6f2f2dfe4cc25797966b18729bcbcb598c420de5e5a1461ca6f2f2de21ee5379796b2e5399bcbcb59a5b94de5e5acc75ca6f2f2db6306f2f12d6b347379a8bcb5988b94de5e5
  | 4, 0, 5 => 0xbfc99ca6f2f2d668e80379796b346729bcbcb59a7b94de5e5bfc612e6f2f2dfe9c6f2f0656b318729bcb6b5993395285e5acc8dca6f2f2dfe9d18379796ff18729dcbcb59729bcbc405acd3a006f2f2d66306f2f1316b34e729bcaab7f8c309365e5
  | 4, 0, 6 => 0xbfd3984822f2dfe9cc2449716b34961224bcb59a9b94de5e5b7461ca6f2f2cb656e5379796d34e3797896b598c395345e5acc61ca6f2d2d6630f2379796a3328c1bcbcb5958ab0de5e5bfd392c892f2d662ee5379796b32c72a64deb18729bcbc2a5
  | 4, 0, 7 => 0xaccd1fc6f2f2d4630e53797970d4761224bcb57a7394de5e5acc61b06f2f2802b349379792b318729d8bcb598c3b8de5e5af461ca6f2f2dfe9c6f2f01969cc25a224bca00bfd38de394bfd3a166f2f2d6630e537899630a44b9bcbcb868ab94de5e5
  | 4, 0, 8 => 0xbfd429c6f2f2d6630fc379796ff548c1bcbcb5b8c394de5e5acc61d06f2f2da69d18379796ff4ea21bcbcb72a7394de5e5accc5ca6f2f2dfe30e54c9bd6ff4e5f224bcb7f89b94de5e5acc61caa02f2dfe9c6f2f0096b318729e0bcb59993953c6f5
  | 4, 0, 9 => 0xbfd3984892f2dc230e5379796ff4e431bcbcb5196c60de5e5c1461ca6f2f2c61cab3379796b322729bcbcb6c8c394de5e5acc59ca6f2f2d6664f9379796b34f779bcbcb70a7394de5e50061a8e6f2f2565ca6f2f14569ce5599bcbcb6993394de5e5
  | 4, 0, 10 => 0xacc61fa6f2f2802ff4e379792b340639bcbcb7e8c394de5e5acc612e6f2f2c61ca6f2f06d65ae5379a8bcb598c394ee5e5bfdae9c6f2f2d6660fb379796ff4e64224bcae567328de5e5acd39ea6f2f2d6692c2379796df1872a78deb86bfd38de5e5
  | 4, 0, 11 => 0x729bcbc180bad6630fb529bd6ff1872a6cbcb779eb94de5e59d461ca6f2f2d668ae5379796b31872a60deb418c394de5e58c435ca6f2f2dfe9d473797970d47611bcbcb6f729bcbc505acc3dca9e37adfe306f2f0316ff18561bcbcb5993394de5e5
  | 4, 0, 12 => 0xb4d3984892f2e1e1ee5379796db2c729bcbcb5981394de5e5bfd3984922f2dfe60e5379796f54061224bcb6a8c394de5e5acc3df26f2f2dfe30fb379796ff2c729bcbcb668c394de5e5acd2184892f2dc660e5379796ff478c1bcbcb5995b94de535
  | 4, 0, 13 => 0xacc60de5e1fa802d34e379792b31872a8cdeb6f8c394de5e5acc65ca6f2f2dfe30e5529bd6b3187f3d952b7f86309125e5acc61ca9937ad669ce5519bd6b313729bcbcb86729bcbc4f5bfd38de5e172dfe9d38379796d74e61224b2b7fa7308de5e5
  | 4, 0, 14 => 0xbfc9a306f2f2d6630ac3797963104729bcbcb598d394de5e5bfc61ca9e37ad6640e537979630e552a90deb0f72a1cde5e5c1c61f26f2f2c61f66f2f1596ff18379789ab59a739cde5e5ad461ca6f2f2d6630f64d9796b2e53797862b7f729bcbc175
  | 4, 0, 15 => 0xbfd38de6a2f2dfe9c6f2f11d70d47729bcbcb7f72a70de5e5acce5ca6f2f2d6630fb379796ff4e7b1bcbcb5996394de5e5bfc61fca92f2dfee34e379796b3478c1bcbcb7fa8309125358c394de5e0c2dfe30f9379796b31872a6cbcb1872a94de565
  | 4, 1, 0 => 0xbfd39ca6f2f2d6630e5529bd6ff4e611f8bcb598c394bc345bfd39c06f2f2b95489c379796b34c729bcbcb598c3a4de5e5c351e1e6f2f2e1e8ec2449796c91872aa4deb7fa71bcda5e5bfc91ca6f2f2d6630ec37979630e53797878b598c3f9326f5
  | 4, 1, 1 => 0xb2461ca6f2f2dfe9ca9379796ff18769bcbcb59963f8de5e58c395486f2f2d663ce5379796ff184d9bcbcb598c3953a6f5acd39ca6f2a2dfe9d0f379796c924729bcbcb7f8c26cbc4b5bfc61ca6f2f2802ff4e2f0b9230e54f9bcbcb7f8c3215e5e5
  | 4, 1, 2 => 0xacc61ca6f2f2d6630ef549bd6ff4b729bcbcb598c2652e6f5005fcde5e03a5fe30e1379796ff4e7f1bcbcb0f729bcdc5e5bdc61ca6f2f2d66309b339796c518729bcbcb598c264de4b5c543dca6f2f2dfe9c6f2f0e56b318729bc4eb8679309125e5
  | 4, 1, 3 => 0x1598c3e0de5e5acc60de5e06adfe9c6f2f111630e56c9bcbcb7fa71bcce5e5
  | 5, 0, 0 => 0xacc61cac237979ab34e70b09125e6bfd3984892f07daff4e612e5125e6acc61ca6f2f0cdab318729bcbc3b6acc61cac2491798018687b94de5e5acc61ca6f2f161ab31872b2cde5e6acc61cabc37979acf598c394de5e6bfd3984892f12daff7f8c394de5e6acd39ca6f2f0b9ab34e9c394de5e6
  | 5, 0, 1 => 0xaccd1cac244979ab31889394de5e6bd461cac244979aff1861224bc4b6acc7230e537979ab34e95b94de5e68c395848d44979ab318729bcbc2e6acc61cad437979ab3388c394de5e6accfe30e537979ab34e72b15125e6c351e30c244979ab3438c394de5e6bfc61ca6f36979b031872b0912596
  | 5, 0, 2 => 0xacd3a306f2f12dab2e565308de5e6accf584892f12dab3185b1bcbc4b6acc61ca9e379a9ab31872b0cde5e6acc61bec2449798011873394de5e5acc61ca772f12dab34e7f309125e6acc61ca6f2f979aff4e61224bc536acc31cac244979ab31877b09125e6acc61cac242979aff1872b095e5e6
  | 5, 0, 3 => 0xacc99ca6f2f12dab34e72b08f25e6bfc6184892f14dab34d72b09125e6bfc61ca8037979aff1864224bc4b6acc6212e537979ab318729c4de5e6b5d1e30c244979a9d3572b09125e6acc61ece5549bdab32b8c394de5e6bfd39848937979801183797832185acc61cac837979aff1880b94de5e6
  | 5, 0, 4 => 0xbec61cac237979ab31872a64de5e6acc6210c244979a851872b09125e6bc43dcac244979ab31872aa4de476acc61ca993799dab34b72b09125e6acc75cac244979ab31872b09145e6bfc61cac044979a30e561224c45e6bfc61cac23f179ab34e72b09085e6acc45cac244979aff1872b80de5e6
  | 5, 0, 5 => 0xc2dfe9cc244979b157fa7309125e6acc61cac242179801599a394de5e5acc61ca6f2f135ab31872b08f25e6acc61ca6f2f1198017f8c1bcbc4b5bbd6630e537979aff4ea7309125e6acd5a9ce537979ab31872a65126f6bfd3984b644979aff1872b94de5e6acc4dca8937979a6b1872b09125e6
  | 5, 0, 6 => 0xacc61ca6f2f061ab31872b54de5e68dc61cac244979aff4e8c309125e6c343dcac237979ab3568c394de5e6b7c61ca8937979ab318729bcbc086acc61f26f351798017f8c394bc2e5acd3a00c244979ab31861224bc4c6acd39cac24495580159a73f8de5e5acc61ca6f2f015801598c3bcde5e5
  | 5, 0, 7 => 0xb9461ca7b37979ab31772b09125e68c39584892f0a9aff2672b09125e60056696e5379796b34761225005e6acd19cac244979ab318729bccc5e6acb9594c23c979aff4e61224bc196acc61cac24496dab31472a24de5e6acc621ce537979ab2e5379a8bc506acc61ca6f2f081b11598c394de5e6
  | 5, 0, 8 => 0xb4d3984892f12dab31878b94de5e6acc61e4c244979b03598c394de5e6acc61ca6f2f02dab34e729bcbc0f6acc61cae337979ab34e72ae9125e6accc9cab937979ab31883394de5e6bfc61ca6f2f159ab2c258ab1125e6994b630e537979801358c394de5e5acc61ca6f2f049aff1887b94de5e6
  | 5, 0, 9 => 0xaccc1ca6f35979ab318729bcbc2f6acc61f2e537979ab31872a24e05e6b9d6630e537979ab318729bcbc3e6acb95006f2f141ab31872add6a5e6acc61ca6f2f075ab3268c394de5e6acc61ca6f2f03daff1872ad4de5e6005fe9d18379796b31872b09225e6acc61ca6f2f079ab318729bcbc456
  | 5, 0, 10 => 0x5fe306f2f0656b34e7f308de5e6acc7e30e537979ab31877b08de5e6acc61cabd37979ab3187f395525e6accd1cac237979ad31872b095e5e6b8d669ce537979ab318729f0de5e6acc61ca892f0d9aff18611bcbc4b6c3455cac2449798017f729bcbc0f50056630e51c8b96b31875394de5e6
  | 5, 0, 11 => 0xacc61ca6f2f071ab31879b94de5e6acc61ca9544979aff4e61224bc066acc61588937979ae3598c394de5e6bfc61ca6f2f0e5ab31872a4cde5e6acd3a64e5379798017fa730912395acd39ece537979ab31872b14de5e6bfc61caa93797980118729bc72065bfd3a16c244979ab31872afcde5e6
  | 5, 0, 12 => 0xacc61cab837979ab31872b09185e6c4d6630e537979ab31872a6d125e6abd39cac244979ac31872b09125e6acd39ca6f2f01dab318729e8de5e6b8c61ca6f35979aff59a7394de5e6acc61b0c244979ab3187b394de5e6acd39ca6f35179ab31885394de5e6bfc61ca8337979ab34e729bcbc476
  | 5, 0, 13 => 0xaccb1ca8937979aff4ea2309125e6acc61ca6f32179ae54e72b09125e6acc61ca6f2f01daff598c394de5e6bcd669ce537979ab318729bcd45e6accb1ca6f33979ab318729bcbc476acc618e8937979ab318729bcbc136acd1e308937979aff4e61224bc0268c395126f2f061a71358c394de5e6
  | 5, 0, 14 => 0xb4c99cac244979ab318729bcbc216bfc61cadc37979ab33b8c394de5e6bfc61fce537979aff50a7309125e6acc61caad37979801598c1bc72195acc61ca6f36979a30e554a90de5e6acc61f68937979ab318729bcbc576adc61cac244979aff4e8c308de5e6acc61d0c244979ad34e8c309125e6
  | 5, 0, 15 => 0xacc61cac857979ab31868b1cde5e68c39584b344979ab9598c394de5e6acc61ca6f2f125ab31880b94de5e6acc61cad637979adb598c394de5e6acc3dcab937979ab31889b94de5e6bb56630e53797980186a3b09125e5acc61ca6f2f059ab2e561224bc516acc61cac257979a9ce5612cd125e6
  | 5, 1, 0 => 0xacc61ca9b2f12db154472b09125e672b3994c244979ab318729bcbc096acc61ca6f2f175b17598c394de5e6acc61cae537979ab34e7ab09125e6acc6228e537979ab31872a90de5e6acc61cac044979ab31872ae8de5e6acc61cac23f179b0d7fa7309125e6acc61cae037979aff4e612250c5e6
  | 5, 1, 1 => 0xbfc622ae537979a30e561224bc1b600461cab3379796b34e729bcbc566bfd39ca8937979ab31872b09105e6acc61cadd37979ac9598c394de5e68c395a0c244979ab31872a95126f60056630e52f0b96ff6ba7309125e6acc61cab137979ab31872b08ea5e6acc61cac23f979ab31872a94de5e6
  | 5, 1, 2 => 0xacb9584b044979ab31887b94de5e6acc61ca6f2f069b0f598c394de5e6bfc61ca6f2f111ab32672b09125e69ac61caba44979aff18729bcce5e6005fe9cc2449796b34063b09125e600461ca6f2f0196b31872a51125e6acc61ca6f2f0c9ab318729bcca5e6acc61849744979ab318729bcbc4a6
  | 5, 1, 3 => 0xacc61dae537979aef3d72b09125e6acd39cabb37979a310f729bcd65e6acc61ca6f2f039ab33372b09125e600461ca6f2f0096831872b09125e68c435cac244979aff4ea3b09125e6acc61ca9b37979ac7598c394de5e6acc61ca6f2f159aff1872a24de5e6bfc6184892f031aff18612b1125e6
  | 5, 1, 4 => 0x9f461cac237979ab32f8c394de5e6005664ce5379796b31872b091e5e6b3461cac24497980000bfd38de5e4acc61fcf637979ac1598c394de5e6acc61e0e537979801598c25cde5e5acc61cab537979ab31872b6cde5e6bfd1e30c244979ab32b72b09125360056630e53b9795cac24497830176
  | 5, 1, 5 => 0xacc61ca6f2f0ada30e5612ccde5e6acc620ae537979a30e53797832186acc61ca6f2f0e5aff1872b5cde5e68c395488937979aff598c3f8de5e6acc95cac244979ab31872aa4de446acc61caa937979ab31856259125e600566306f2f0656b318729bcbc386acc61ca6f2f08db0d5999394de5e6
  | 5, 1, 6 => 0xacd39ca6f35979ab31372b09125e6acc61ca6f2f109b0ce561224bc4f6bfc61ca6f2f12dab31872a1cde5e6b2461ca8937979ab318729bcbc0a6bfd3a70c244979ac918729bcbc446acc61cac255179ab32a8c394de5e6c3c3dcac244979ab11872b09125e6acc61ca6f2f011ab318729bcd05e6
  | 5, 1, 7 => 0x5fe9cc23797940169a7309125e5acc61ca6f2f051adf1872b09125e6acc65cac244979ab34b72b80de5e6acc61849737979ab318729bcbc3d6acc61fee537979ab318729bcbc356bfc61ca6f2f07dab318729bcbc036acc61cac24ca25ab3598c394de5e6accc230e537979ab31877b94de5e6
  | 5, 1, 8 => 0x87b95848943979aff1872ad8de5e6acc61ca6f2f10dab34e73b09125e6bed6630e537979801598c395326f50056626e5379796fee561224bc176acc61cae237979ab31872adcde5e6bfc61ca6f37979ab31872b20ee5e6acc6202e54b179ab32672b08de5e6acc61cac247179ab3187f394de5e6
  | 5, 1, 9 => 0xaccca56e537979ab318729bcbc5e6acc61ca6f2f091ab31873394de5e6acc61ca6f33979ab31872aacde5e6acc69cac244979ab3188ab94de5e6acc61e8e537979ab318729bcd85e6bfc61ca6f2f065b0d5987b94de5e6acc61ca6f2f105b097f8c394de5e6005be30e5379797157f8c394de5e6
  | 5, 1, 10 => 0x56630ac379796b3187db09125e6bfd39ecc244979ab32c72b09125e6acc61cae437979ab31872b34de5e6acd1e30c244979a30e561224bc186acc61ca6f2f0b5ab3187d394de5e6acc61cac23e979aff268c309125e6acc61ec6f2f12d8017fa7308bc295acc6184ac44979ab318729bcbc446
  | 5, 1, 11 => 0x56630fb379796b318729bcbc4b60056658e5379796b2e568b28de5e6005668f183797940118729bcbc185acc61caa137979ab31876309125e60056630e54d979630e561224bc3c6acc61cad737979ab31872b18de5e6bfd3984892f11db0d4772b09125e6acc6190c7449798017f8c394de395
  | 5, 1, 12 => 0x461ca5e170196ef1872b08de5e6acc61ca6f37979aff4e72b09125e6accae1ee537979ab318729bcbc536acc61ca6f2f0a1ab31872b094a896bfd39c0c244979ab318729bcbc256acd31cac244979ab318729bcbc1f6acc61cac257179ab34e729bcbc536c351e1ec244979aff59a7460de5e6
  | 5, 1, 13 => 0xacc61ca6f2f065ab31872b10de5e6acc61ca6f2f139aff4e61224bc566acc61ca6f2f0898017fa7394de5e5bfd3a1ec244979b09598c394de5e6acc61ca9737979b15598c394de5e60056630e5529bd6b3187f1bcce5e6acc61cab637979b0d7f8c394de5e6bfc61cac244979ab318779bcbc446
  | 5, 1, 14 => 0xbfd3984892f0e5ad7598c395526f6b2461cac244979801183797832065acc61eee537979ab318729bcdc5e6bfc61dac244979ab31872b31125e600394de5e078196b31872a24e45e68c39584a444979801598c1785c195acc79cac244979aff4e612d5125e6005fe30e5379796b318729e4de5e6
  | 5, 1, 15 => 0xbfc61c2c244979ab318729bcbc116b5c61ca6f2f159ab318729d0de5e60059230e5379796f71872b09125e6acc61529737979ab318729bcbc156acc61cac24a179801598c394de395b1461cac2449798011872a90de5e5acd39ca6f2f019ab318729bcbc4f6c543dcac244979b0d59729bcbc506
  | 5, 2, 0 => 0xacc61cad237979b0d598c394de5e6acc61cac244979ab318729bcbc106acc60de672f12dab3187f2d8de5e6bfd2dcac244979ab318729bcbc016acc61d6e537979ab31872b09025e6acc61cada379798017f61224bc075acc61ca6f34979aff2b8c394de5e6acd429ce537979ab31872b09205e6
  | 5, 2, 1 => 0xacd1e310f37979ab3298c394de5e6acc61ca6f31979aff4e6bb09125e6c343dcac244979ab3478c394de5e6acc61ca6f2f001801598c394de5e5acc6184892f035ab318729bcbc376acc61caac37979a30e56cb09125e6
  | 6, 0, 0 => 0xbbd6630e561224bce00acc61ca6f2f0b9ab356a739584892f3802b3388c394de5e6bfc61cae561224bcf74acc61ca8937979c01598c395846f2f3566310172b096a5e70056630e5449783ad598c395a6c244979eb31883b9584892f3dfe30e570309125e70056630e561248bcd599339584892f12dc01598c395786f2f35fe30e561225005e7
  | 6, 0, 1 => 0xacc61cacf61224bcf598c439cac244979eb31872b09125e103d6630e56122d125e7acc61cadc449bcbcf598c39584892f061eb31872b5584892f3802b32b8c394de5e6acc61fce5449bcbcf59ab461cac244979eb31872a24de6b2f3d6630e561224bc087acc61cac2449780ae00accd1cac244979ab31872b09125e233802ff1861224bc4b6
  | 6, 0, 2 => 0xb2d6630e561224bce00acc61cac242179ab31878b9584892f3802b31872b08f25e6c0d6630e561224bcf598c39584892f02deb34e72b09125e07bd6630e571b09125e7acc620ce561224bcf7f8c39584892f159c01358c39584892f35fe310f72b09125e7b9461cac2449ecbce00acd2dcac2449798015973b9584892f356630c2449ecbc4b7
  | 6, 0, 3 => 0x5fdcac2449781ed599c461cac237979eb3187539584892f3d6630e561308de5e7b9d6630e561224bcf598c39584892f0f9eb2e561225005e283d6630e561224bc1d7acc9a30e561224bcf598c39584892f03dc0159a7395845e14b5fe30e5612d5125e7005fe9d1861224bcd598c39584bc37979eb31872b09125e0f3d6630e561224bc457
  | 6, 0, 4 => 0xbfc61cac24497872f5995c61cac237979eb31872a24de5e223d669cf672b09125e7acc61cac561224bcf598c395126f33979c011872b091239033566310b72b08fc5e7acc61cac25fa24bce00bfc6184892f065ab31f8c39584892f3d6630e5612f5125e70056630e56117852c00acb09125e0c85dab31872b09127c2f3d6630e5611bcbc2e7
  | 6, 0, 5 => 0x9c4d630e561224bcf598c39584b844979f13598c39584892f3d669ce561224bc077acc61cac2449e8bcf598c3956a9644979eff59a739584892f3d6630f672b09125e7acc61ca893797890f598c429cac244979eff1872b0912832f3d669ce561224bc4770056630e5379781ed598c39584892f071eb31879b9584892f3dc6b31872b09125e7
  | 6, 0, 6 => 0xbfc61cadc61224bcf599dc61cac244979eb31872b095a892f3de6b31872b09125e70056630c2448e432d598c395a28937979eb34e80b9584892f3802e3598c394de5e6acc61cac244990bcf598c39584892f01deff598c39584892f3de6b34e72b09125e7acc61cac2449a8bcf598c39584892f11deff748c39584892f3d6630e561224bc137
  | 6, 0, 7 => 0xacc61cae061224bce00bfd6630e537979ab31872b0912802f3d6630d163b09125e70056630e5379a8bcc00acc61ca6f2f11dab9598c39584892f3d6630e561224bc497acc6202e561224bcf598c395acc244979eb30f72b0972892f3d6630e5449bcbc507acc61cac2449782ce00acc61ece537979ab31872b5d126f2f3d6630e561224bc217
  | 6, 0, 8 => 0xacc61cadd61224bce00acc6202e537979ab31872b0962892f3802b31872b095e5e6acc61ca89379783ef598c395728937979eb31872b09125e04bd6630e561224bc5d7c5d6630e561224bcf598c395cac244979ef9598c39584892f3d66311472b09125e7acce230e55d224bcf598c395126f2f12deb31872b08de5e07bd6630e5612e9125e7
  | 6, 0, 9 => 0xacc61cac244978acf598c3d9cac237979eb31887b9584892f3d6630e561224bc1a7c3d6630e561224bce00acc61cac52f0a5801598c395847e2f3002b31872b80de5e600461cac2449780cd598c395126f37979ee3598c395846f2f3d6630e561224bc4a7bfc622ae561224bce008c39584b344979ab34e72b09125e2b3d6630e561224bc527
  | 6, 0, 10 => 0x566310f729bcbcc00acc99cac244979ab31872a24de5e0cb800017fa7309125e50000230e5379780cb598c3c1cac244979eb31872b096a892f3d6630e56db09125e700002b318729785cb598c3b5cac244979eb34e72b0976892f3d6630e561224bc0e7acd3a30e5449bcbcf598c3956c8937979c011872b09125e01358eb31872b09125e7
  | 6, 0, 11 => 0xacc61cac244a1cbce00acc61ca891c87dab31872a24de5e14bd6630e5449ecde5e7acc61cac24497814f5995461cac244979c01598c3956a6f2f3461cac24497832187acc61cac24497872f7f8c395aec244979eb31872b0952892f3d66310172b08de5e70056630c24497832d598c39584892f0e1c01598c394de5e2b3002ff1872a24de5e6
  | 6, 0, 12 => 0xacc621ee5611bcbcf598c3f9cac244979eb31872b09125e0a380230e5611bcbc066acd2dcae061224bce00acc61ca89378e5ab31872b09125e1ebd6630ff72b09125e70056630e53797872c00acc61caa937979ab31872b09125e1abdfe30e561224bc1f70056630e5611785cd59acc61cac244979c0000acc60de5e0cadfe30e561224bc4b7
  | 6, 0, 13 => 0xacc61cce561224bcf598c395848933979eb31872b0956892f3d66311572b09125e7acc61cac23797872f598c3d1cac244979eb31872b09526f2f3dfe30e561224bc1970056630c23797832d86acc3dcac244979c01598c3f9ca6f2f362aff1872b09125e7bfc61cac25b224bcf7dacc61cac244979eb31872b096e892f3dfe30e561224de5e7
  | 6, 0, 14 => 0xacca230e561224bce00acc6184ac44979abb598c39584892f3802b318729bcbc4460056630e53799cbcd598c395c8c244979eff598c309125e25bd6630e566b09125e7acc61cac24497874f598c3d984892f12dc011872b08bc2903361ab31872a24de5e7acc61cac244a24bcf598c39584892f111eb31872b09125e2f3d6630e561224bc247
  | 6, 0, 15 => 0xaccae1ee561224bcf598c39584892f14deb31872b09125e143d6630e564224bc4b70056630e56b9bcbcd598c39584892f07deb34e72b09125e29bdfeb34e8c309125e7acc61cac24497896f5972b4594c244979c0159a3c6184892f300230e561224bc1860056630c22f0a432d598c395aec244979eb31872b1984892f3802ff1872b0912396
  | 6, 1, 0 => 0xacc61cac24497832f598c395a2c237979c01598c394de6f2f356630e562309125e7acc61cac2449789cf598c39584892f089c017fa739584892f35fed71872b09125e7c556630e561224bcf598c39584b644979c01598c394de5e0fb61aff1872b09125e7acc61cac23797890e00acc61ca6f2f12dab34ea739584892f3d6630e561224de5e7
  | 6, 1, 1 => 0xacc61cac24497822f6b8c39584892f159c01598c39584891cb5669ce561224bc067acc61cac2449789ee00acc61ca5e1487d80000bfc61ca6f2f2e1ab2e561224bc5070056630e53797832d598c39584922f07dc011861224bc19033001cac2449781e0660056630e55b1bcbcd599b461cac244979c017f8c39584892f356630e561224f25e7
  | 6, 1, 2 => 0xacc61cac24497800e00c356630e537979801598c39584892f356630e561224bc377acc61cac256224bcf6bacc61cac244979eb31880b95126f2f3d6630e569309125e7c356630e561224bcf598c39584af44979eb31872b09125e083d6630e561224bc017acc61cada61224bce000056630e5378e56ff2b8c39584892f3d66a14e72b09125e7
  | 6, 1, 3 => 0xacc61cac2449785ce00c343dcac244979ab3478c43d84892f3d66531872b09125e7acc61cac244980bce000056630e5379796b31872b0912632f3d668f1872b09125e7
  | 7, 0, 0 => 0x56630e561224bc39700002b31861224bc1960056630e5612d5125e70056630e561224bc56700566310f72b09125e70000230e561224bc0660056630e570309125e70056630e561225005e700566310172b09125e7005e6b31872b09125e7005feb31872b09125e70056630e561224bc4770056630f672b09125e700002b31872b08bc2960056630e561224bc0f700002b31872b08de5e6
  | 7, 0, 1 => 0x1598c394de5e500002b31872b09125e6005aeb31872b09125e70061ab31872b09125e700002b31872b091239600002ff1872b09125e60056630e561224bc1970056630e5612d9125e70056630e561224de5e70056630e561224bc1f70056630e561224bc4b70056630e56bb09125e7
  | 8, 0, 0 => 0x2b31872b09125e6
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
private theorem z3_48 : span (Z 3) 11 48 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 59 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 11) z3_a1 z3_48

private theorem z3 : span (Z 3) 59 0 = true := z3_a2

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
private theorem z4_288 : span (Z 4) 21 288 = true := by decide +kernel

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

private theorem z4_a12 : span (Z 4) 309 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 21) z4_a11 z4_288

private theorem z4 : span (Z 4) 309 0 = true := z4_a12

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
private theorem z5_528 : span (Z 5) 12 528 = true := by decide +kernel

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

private theorem z5_a22 : span (Z 5) 540 0 = true :=
  span_join (f := Z 5) (a := 528) (o := 0) (b := 12) z5_a21 z5_528

private theorem z5 : span (Z 5) 540 0 = true := z5_a22

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

private theorem z6 : span (Z 6) 312 0 = true := z6_a12

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

def CG : Circuit := ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12495

theorem PEqualNP.Outside.L_meta_12495 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264064 * 2 ^ 32 + 3938511488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264064 * 2 ^ 32 + 3938511488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12495.mainG PEqualNP.Outside.L_meta_12495.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12495.CG, PEqualNP.Outside.L_meta_12495.CG_mono, by
      have : PEqualNP.Outside.L_meta_12495.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12495.CG_eval⟩
