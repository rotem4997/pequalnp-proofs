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
namespace PEqualNP.Outside.L_meta_12439

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941116040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 6, 0, 8, 9, 10, 0, 12, 0, 14, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 3, 7, 3, 3, 3, 11, 3, 13, 3, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 25, 3, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 3, 43, 3, 45, 46, 47, 3, 3, 3, 51, 3, 53, 54, 55, 3, 57, 3, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 7, 11, 7, 13, 7, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 11, 11, 7, 11, 11, 11, 11, 11, 13, 11, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 13, 13, 7, 13, 13, 13, 11, 13, 13, 13, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 15, 15, 15, 3, 15, 15, 15, 7, 15, 15, 15, 11, 15, 13, 15, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 19, 7, 19, 19, 19, 11, 19, 13, 19, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 21, 7, 21, 21, 21, 11, 21, 13, 21, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 22, 22, 7, 22, 22, 22, 11, 22, 13, 22, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 23, 23, 7, 23, 23, 23, 11, 23, 13, 23, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 25, 7, 25, 25, 25, 11, 25, 13, 25, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 3, 27, 27, 27, 7, 27, 27, 27, 11, 27, 13, 27, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 29, 7, 29, 29, 29, 11, 29, 13, 29, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 30, 7, 30, 30, 30, 11, 30, 13, 30, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 31, 7, 31, 31, 31, 11, 31, 13, 31, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 35, 7, 35, 35, 35, 11, 35, 13, 35, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 37, 7, 37, 37, 37, 11, 37, 13, 37, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 38, 7, 38, 38, 38, 11, 38, 13, 38, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 39, 7, 39, 39, 39, 11, 39, 13, 39, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 41, 7, 41, 41, 41, 11, 41, 13, 41, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 43, 43, 7, 43, 43, 43, 11, 43, 13, 43, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 45, 7, 45, 45, 45, 11, 45, 13, 45, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 46, 7, 46, 46, 46, 11, 46, 13, 46, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 47, 7, 47, 47, 47, 11, 47, 13, 47, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 51, 7, 51, 51, 51, 11, 51, 13, 51, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 53, 7, 53, 53, 53, 11, 53, 13, 53, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 54, 7, 54, 54, 54, 11, 54, 13, 54, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 55, 7, 55, 55, 55, 11, 55, 13, 55, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 57, 7, 57, 57, 57, 11, 57, 13, 57, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 3, 59, 59, 59, 7, 59, 59, 59, 11, 59, 13, 59, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 61, 7, 61, 61, 61, 11, 61, 13, 61, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 62, 7, 62, 62, 62, 11, 62, 13, 62, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 63, 7, 63, 63, 63, 11, 63, 13, 63, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1517151715175777151715171517577715171517151757770000000000000000151715171517577700000000000000001517151715175777000000000000000015171517151757771517151715175777151715171517577700000000000000001517151715175777000000000000000000000000000000000000000000000000151715171517577715171517151757771517151715175777000000000000000015171517151757770000000000000000151715171517577700000000000000001517151715175777151715171517577715171517151757770000000000000000151715171517577700000000000000000000000000000000000000000000000015171517151757771517151715175777151715171517577700000000000000001517151715175777000000000000000015171517151757770000000000000000151715171517577715171517151757771517151715175777000000000000000015171517151757770000000000000000000000000000000000000000000000001517151715175777000000000000000015171517151757770000000000000000151715171517577700000000000000000000000000000000000000000000000015171517151757770000000000000000000000000000000000000000000000001517151715175777000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a8880000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a8880000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000eae8eae8eae8a888000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888eae8eae8eae8a888

def cMZZ : Nat := 0x1517151715175777000000000000000015171517151757770000000000000000151715171517577700000000000000000000000000000000000000000000000015171517151757770000000000000000151715171517577715171517151757771517151715175777000000000000000000000000000000000000000000000000151715171517577700000000000000001517151715175777000000000000000015171517151757770000000000000000000000000000000000000000000000001517151715175777000000000000000015171517151757771517151715175777151715171517577700000000000000000000000000000000000000000000000015171517151757770000000000000000151715171517577700000000000000001517151715175777000000000000000000000000000000000000000000000000151715171517577700000000000000001517151715175777151715171517577715171517151757770000000000000000151715171517577700000000000000001517151715175777000000000000000015171517151757771517151715175777151715171517577700000000000000001517151715175777151715171517577715171517151757770000000000000000151715171517577715171517151757771517151715175777

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
  | 3 => 35
  | 4 => 302
  | 5 => 741
  | 6 => 464
  | 7 => 37
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xcde9f829cbd75cbbbfb5e52175dbfdd7
  | 3, 0 => 0xf8cfcb74f7517094d5d28868d13db950c6e90e19c413d720ba51dce3a8226a8da646b5549c0af713985663dc98298bcd94df080692aeb43b8b76465e8880f2f686dbc11185d29f05850ad54884d0c45370650134598f9a705747b4ee4f980cc64ecb969448d179fd341865c3305272bd2e4597c825f31b41244f26241ccbef23198c838e152e92b605951467
  | 4, 0 => 0x2b7e63fd2b66c0ee2ad886df29b0a6dc28de975127f6809327dc426c27af78af27261bc02627222025e638b6248643f52406338323fc062323f6634b23cf2e1423b07cc0236a72f6216ab8fa213c7d08213261d71f07738e1e87a1071d0867da1bbaeb6e1b5fb7511a4b872719686289188eae141853007f180d2f09178182cd171331eb15ed0e45153aecc114deaee91370a33e117c28c71178414c10a9627e102ecd8a1004522c0f1f1f000eb228df0e5e1cf10ccc904a0bbee4ee0ac7874c0a6db1a90a34e8cd09fa62b50976a046093a0964081455ec073ef0d706aaeecf04cdc89c04986480047963a303edca8a03eb712f01cfd85b01a90a76016fa09e
  | 4, 1 => 0x5eade8915e2cf5cd5e01075b5c9dfd365bcb393d5ba617385b884a8c5a9cd1dd58ddfc115749523556de3da95670501252b2f437527eda635264c9a65262b3b9521858885209dfc2511676b8509b27ec502535284f5c22b74d5c33984ca515d64b530f174b177f0549c65ee248c4a7bd484fb6004813795347f2f3e446e2a4fe46e0053845e3bda3452aa1784492f09e43cf673d432690434311d1403f9f13d13f8362d83e89dbaf3d14b7f73ca7b8f03c8927983ba113443b7c4a1a3ab0bcac386873ae385695673757c48533879d5d31ec579b31a719983158920b3126da1830733afb2e9c029e2da9c45b2d82033b2d15e1a52cda03712cc983f72c13b43f
  | 4, 2 => 0x9b92d98d9b6fba9198ea38bf9879fd3d98298bcd962e0fa196193d049574136d95650ec591b527c890d9218d8fcfc10b8f6cb76e8ea77e1d8e9789278e477a118e0e9db28df045138cbcf5cc8c71763f8ba6c4688b0fa5bd89f7c7de895e3a64867b947685ae8544859c031a84e247d08483de24844b870182f712db8293bab981865e9180ffba967ec4a1f47bae62387b1ff3b979579c8d7815b1617754445177233de074cb5cc473674faa732f3ccb71e5820d718659917138727a7009c1ab6f27a7e36dcea0c36c8fc5706c551ed96bd24a826b9e4cf86b90b342695164d8694aef4b683c8fef680d33b36739936064f4b9196391c7db633d6e7b610a7c98
  | 4, 3 => 0xe1a89a4bdfef946cddc70de3dd91f78cdcb12c5fdb3daf08db367201daeead53d91f09e6d84d1914d83b74d0d7e1bf2ad7a96807d79983ced5ace54fcf48f715ce5e0c81cc4f5617cb074fd0cab318a4ca52b88ac84d9bbfc8293dcac530cd09c423a1c2c3c70a87c39404dac1461af7c0025234bf302c0dbf00faf7beee9448bec59dc7bec0fb38bd7c8e02bbf53cc7bb6b14b9baffb73bb8e83f6fb4868c38b326ba51aff66a2daff4c866af194751aeec1db5ac562f9dabe05088ab498fb9ab44e557a91848fea67b47dda61be8b2a5dcbb69a5c2aaaca55b7f9ba4f21d1aa425cba8a4232f7ea3e2f544a383162ea1760a06a0d434f8a0195c459d26e42f
  | 4, 4 => 0xff04d2aefeabfeb7fe3417a4fdcfe2dafd3d46e1fc74e92bfad08ea6f9b54d62f9a03813f98fcfeff97102abf94734cbf8c58856f894e346f4881a11f3aaec1bf285dc98f240ae10f217cdc5f1e00032f1afa1f1f18c693bef99cf08ef65b534ef5722f4ef4ba477ee89a683edb22f9fed0c0ff9ec84a9abeb9380beeb529fbfeb3bbb37eacf86c6ea9a7ff8e9521350e8b392efe879c6cae7286f13e7277d8ee6f0d9b8e51308cee382984ce37fb3e0e32da211e2568b41
  | 5, 0 => 0x1058b49b1050756f101bce070fe772f70fd3578c0fd04a3d0fb7bb850fa1223a0eeea9140eece3a60dedbbd10dd5d9c00da548fb0da0b3cd0d4d19150d3f18f10b9eef310b275b470aaa05620a798f4f0a7480920a0b30ae0a0b1aba0a02c74809b564190958e53f095801ee093a096408f6f42208d3914e08572e1a07f738d507b833e407af8995077c13300773e1b3073ef0d70734a4fe0679bd910679b13206752b5b06728b9505f2a63805bb97d60576440005173a6603eb712f03bfc4e4039f82320361ed9a02fef8ad02b916a002a4579d02415fee02351106023002d802088240010a664300ed15e7009d3eb500912e3500896672007033880018f81d
  | 5, 1 => 0x23cf2e14238074272337633623244e3822e7ad8d22952e8f22944ff922611b692206b6e221d3b1e821b2e26a2196639c211e950021182ee4210e7b7a2100785520e9d0ea20469d2f2016c3501f5dc9fc1f35c61e1ee1778c1e97e82a1e5817ec1dc19fd81d938db81c90b0711bd2ab121b76afb61b389d951a8021571a73a6b01a2339aa196c20bc190b2e4318d88dde1884842b182b9c1517362a931714e9af16b4fa0f165408eb1602d66f151be2c614d3cbfa149f7328149725c114689427146146b513c57b1213b48a3e1374625612da97cb12ccd0dc12aa68cf126d392d124ded8712457a94121160c011f7500311aadee51189af731112cb1010a8fd15
  | 5, 2 => 0x345b35fd3433362c33edc7ef33e1c47c338b807433879d5d338725923377f3683341807d32f9d60732add63c31f16d7b31e35d7b31b5f18431917e1c3184f3cf31714732314c9cac313503e93118dfee30ccad1330a23b60309d18482f0587422e87743c2e0820682dcd50d22d6127202d4cd2942cd61d2a2c13b43f2bc5b79f2b787a4f2b66c0ee2b524c762b30d3552b15d08b2af212b62a265b882a23a30f29f11b9829de266b29606fe6293df210290cd15728dd75a828ce10e52833eed927e20a3227d5f43127cf164c2702c2c026c57ad526aa6d6f26905cb2267b675e2658b238264392f72581af8724db6e9324d2cdd124b27d9424982aac241f9f84
  | 5, 3 => 0x46569851464e1dc24644e4fe45eb4e6a45c718c04552f53d45410ba144d70f784492f09e4474ce2d4463fafc43d02974434cd6c7433359a4432690434314852642e69a5a426bb1084245f88c423228de41ef13f341710f0941501f9e4121364c4118e4ee40ae1c4e409240f3408d75d0404d677e3ee1ade43eb63d733ea242d43e5728513df5f9793ce741b03bd580183ba893c83b421b9b3b32728b3b3198433ab27a163ab0bcac3a0c1c4d39dca9c539af7b0338ea22ea38cc7cfe3872ae343851ca523809015b37a837be3791b843378328a537441c8a36b5c43d35eb50de35d2341035b7da3c35a3f8c83561647835528223354667a4352540bf345de321
  | 5, 4 => 0x5a87403e5a74b0be5a6804c959a15dc558fdbe3058c14d00587cbf1c584061415801574f5763d61d573fd057572f6f2f56e3d20056acf217567a0b9755c3687055abc361550699ca54bb447453c44c2d5359b3c7533cfa8852fc807a527feded527eda635264c9a651d512ae5147ae2551412daf50785f96506ba7ea502535284f4491a14eff3dcb4e3a047a4e2a0f844df001ad4dae22574d9a7bed4d0e36514cf8e72a4ca576824c9730ca4c7048c24c63e8ef4c5be8754c501ab94c4f7c294c0b88ee4c03fc9c4ba35a804b3c371b4b255fb24acd669d4a93600e4a760fb24a6a81314a583fbb499b00d448fd789f48fb363048f0c0c146c04bb746658457
  | 5, 5 => 0x6ef48e086eb8145b6eabcdae6e7ea4126e1362326deb845c6d8742a06d2455d86cf9757b6cc042326b72d6e56a72cab568fdee6d68f356c168e6c3c768cf423568352dbe6820e1f566c9a090667d0357662d805c660dce3a65e0bad4657120536555310964eba9036466836063ff1c3763fca07b63b5b5db63a822416399893f638a6783637a7d0163159c8b62ff034062f2a87762d2814f62ab9302622f6dd461bd448361600d906154252260ef726f60aafa1b60a84ccc5f60c9e95f01b9745ed9a0525ec404905e2219c65e0e31cf5d13451f5cfd5c215cf67bae5c6391965c3982d35bf9d40b5bd6e7525baf0c355b6156525b19cc8f5b12a93e5ad9f436
  | 5, 6 => 0x82ef7c99824eeb4881a93f5381865e918152ad4f812e2dfd811ab20e80d472aa8089b0a180813e9b804f23457f40d4077ec4a1f47eacc4ba7e8fd4e07e5381957d5544387cbe7ac57c949ebd7c7a6c797c5511477b88cfab7b7e22007b68372b7b44c13f7adb022a7a2e0ed97a2b352b796d2e1579579c8d78dee81d78c55e6a788e810d787e7dba784b49797813a19177b89852771b0e3575c2a008758384a97544211d744daa647444787573ea798c73cf2fb473bb2c7873a90791737a1563736f5f0873699a99731c047172ce115a72967bff7227e73d71db035071cb6b177186c680712f6a56710e8ef370ea111d70bff5887091c380708d3e916f84daf8
  | 5, 7 => 0x972c0a2b95c711db957adec794cf16ae94aaa346936e1e7c931f04a092f42b9d92a2dc74925922ce91edde2e91ce38e391b527c891214592904522b69013b9268fef42548f666ebd8f3bddc98eeb5dac8edc692d8edb7d728ea77e1d8e11830e8e0fee448e0b37e08dffe3ed8da251d18ce9ebc18cbc536f8be1dc748bd08f3a8bb4492f8b7fcdae8b6a37638b2969ee8acc9b898ab768c08aa1fd908a459f018989b2b88971002f88b1d20188a448aa888321c587e0221c87bbc4278799f2fb874223d0873fa582862fb75a85dc1e0584ecd71284e247d084c3536684ba920e84901b748483de24844b87018427a0a483b6281f8357d0f883268b3782fc77fe
  | 5, 8 => 0xaed96e25ae9185a9ade52144adac8538ad8f34dcacb7250eac9e9656ac87fd0bac6bb414abe7ea12abb748e8ab26071baa8d5035aa33f3e6a9aa4be5a9672b2ca926f6f4a8e499ada8e114e7a76470f9a7123708a6ba03eba69c3eeaa55f1db6a4f1e146a462ee01a3b64a51a3b2d14ba39f98aea34f7b82a33814d2a3123a3da1ba32d0a1a2efeaa13b20a8a0f85cf3a0e08f03a0865d03a03cac69a020bfb09fcc46199fbcc03e9e8f389f9e16ac3d9da0ae369d60bae19d0e11339cc5f4539cc354f29cbea61d9c90d9e09c482f619c43b2bc9b62efbb9b207c409b055ebe9ab2e7799a9c4dcf9a89ec1c9a0901d29942220198ea38bf97cdfb2d97c1dc02
  | 5, 9 => 0xcbffe8f1cb3a071fcb26bceacb167958ca5fabe1ca354602ca003801c98ce90dc8cc8fbcc84d9bbfc81eea78c7184161c715c5a5c6ff7a9ac6c77b9fc6b16fa4c63d7527c4604ef4c423a1c2c215f561c1f31edac1e5e5b8c13b90cec10226f6c08236dec016814bbf7cb6c0bf77f365bef00c7cbe161888bdc69e01bd626937bc736591bc076f88bb7ea99dbab6906dba631503b9ca0683b922564cb894c7dcb8395f07b82769a3b81f4e4ab70a147bb6d85e07b5dfb9ccb53d55a4b45a52d9b44d5375b3fbc480b3e22c03b2e01a7eb221e596b21862f5b1f0fbdab1d3346db16c12d5b0ec86d5b0275b7baf8b2912af2c5565af24ae18af194751aede2ad4
  | 5, 10 => 0xe82cf7b4e808844ce7d3b738e7b186aae6b8a218e5b9a878e4839e53e433d738e39a63c5e398b9dbe361b46ce34d235ae32a1f8be203836de14ad5cddfcd752bdde01df3dd7c624edd6ecc08dd550773dd085053dcb12c5fdc234a88dba7a637db585b91daf23da9daedf888da4fd295d9de0d7fd9ce1c81d8fae8e1d8edbbdad84ab818d83b74d0d821346cd7fbf6b3d7f46b6bd7acf216d7749af3d6933a8dd5f175b9d5aef04cd5702fdad43415e8d42af75bd3a995bbd32a5477d326dc0cd2574710d24da916d22d4275d20c1b90d1edb5e6d03be8d6cff27fc3cfeb34dccfc153e2ceb1a558ce44af37cd8befdfcd72c7d7cccb0f1bcc5f16a2cc477c61
  | 5, 11 => 0xffdf197dff9253f5ff15e930fed4df0dfeabfeb7fdcfe2dafca73e4ffc74e92bfbaadf61faf50ca0f94734cbf8aaf8d8f8519ccbf81b84ddf780e564f76e1b0ff739964ff340e7adf31a23b5f2bbcbf7f290ba80f285dc98f1f51432f1e9ad79f1b1d808f0f2da24f0b96070f09d321def61b3c7ee1ff3c0ec5c0a4feb10ea55eaf94746ea8156beea77703fe967e527e8711da9
  | 6, 0 => 0x1a14d7821a07371b190b2e431793ddac1714e9af17093bf916da57e216c1515f1676585d156a0f42136709e11356d28a134e2ef51349b98512aa68cf1259dcaf1212744a11f7500310d7dd5810d3b40c0fb7bb850fa1223a0f3fef8c0f0173670d4d19150d40a8b40ca0bcae0c37fcdf0c29b7270bf66f4c0bc51a3b0b9e0f4b0b7bd73b0b35e0dd0b232f710b0f477a0acebd780ab7e60f0a874df40a5fecfa0a25e66b0a08960f09fd078e09eac61809b56419088dbc8d0855a13b078855e9077c133005f80ab405e91eae04e57b9a046995d503f681590362afd102fef8ad02df5d2402c5e00102b916a002a70b8301d87ee900e2a5fb00b3bca90056d278
  | 6, 1 => 0x307c977a301fc4ee2faa3b642f8117d42f66b5ba2f1761552e4a9ab82e0820682da5e88f2d7e0ab92d19c8fd2cd04a4e2cb6dc352c77b08c2c52c88f2bc5b79f2b90ea8b2b66c0ee2a05511228a368e2289074ca2885dd1e27b368522778866427382662266e43c0265c26ed260f89b425d105f425373b692503a6b024b9adfd24aa91252428e55823e6531121d1603e20f293ed20e6ab7f206ab044204a5f6f203d8078203ad3291ef350461ec94fbc1e6c26af1e568aed1e3762ee1db4a0231da0b82c1ca5cb7c1c8fe27e1c89020b1bf617f31bb92a061b8864d41b696daf1b5397c01b4192921b1b1d991aac52ec1aa52f9b1a6c7a931a256b831a19c69b
  | 6, 2 => 0x4474ce2d4463fafc4422a1d143ba270142fedefe42ea5755428efe5b41e171a541d02c5941abb8f141622ae041501f9e413bc5b04118e4ee40c0b45a40ad386b401c36fe4019d6764013c4f83e5728513e3f4b173e225b3d3cf057ff3ce741b03c5101223c4dbf363c27251a3b421b9b3b3d52b53b1b56083afabd883ad7479c3a6d888739d711a039c0953638ffb47238e28ac43872ae3438716e7a3821076a3811041737ddcfd6374b1eaf37441c8a3742d14836ad9492358595f235552665354667a4352540bf34d6a77a348a1bb534862abe334db2d533467488333b8dee330c9bc032fc20f632ae8ace3200f82531edecbd31ba6d9a31194cdd30f48bc8
  | 6, 3 => 0x64f1a41363f5745e6348d0ae63321f0b62e201df62ca9b2f629a28c2625d43575fcf32c65fb3460d5f5ecc765f4f469b5ec404905e2219c65e0e31cf5d169fe35c55db4f5bdab5be5ab3029d5a97e51b5a87403e5a2ed42c5a1c7279599b882f5821891057d3502655599838550d652454619d0b5440870153da78695286b1fa523562d151eba92b5180648b50b3cbef4fd7a9134fa63f834f81c8b14ece64264e99ddf14e6eef8a4e3a047a4e3282fe4da274a14d9a7bed4d926a4a4d8e3be14c501ab94c4ed9cc4b55a0ee4b46cf8c4b12540b4afcbdc04abbf04b4a49ef1d49ee5be14903868c4844585e4836cf074815a82248147dda45c23db7447f5d6f
  | 6, 4 => 0x8d1e763c8acc8d7c8ab943478aa8ffb589c7cc5f87e0221c86a84c02869200f7865a01fc8643f6018568ec3f853ecadd84ecd712835fd9d681a87bbe81786c158014bd3b7fa907a87f0f3d1d7f0a79c27ec4a1f47e8fd4e07e8292d97da89ee57ccf6e537c05ebee7b44c13f7a720a49796d2e15795c8ce077b89852769c9ad8755ba6de752b997473ecd936738e4add73699a9973079db972d2db9c724b59d271c83a11712f6f9170fe99326fb9e1d86f6fe8bd6f1daf6f6eb8145b6eb734756eabcdae6e1025df6d77a7a16d3f0b956d3697d46d2455d86d21bb396ca4d8da6bd32f276b4d8b216b2ce41369c67a43693cd2426790f071662ec54765999e26
  | 6, 5 => 0xbd626937bc076f88bafda512ba8792fdb7e42328b7ae0b3ab7031b1ab700a16cb45a52d9b2d36e0ab24e5254b22340ddb21862f5b1879a8fb17c33d6b16eeccab138855bb02fb87aadb27a1dadac8538ad8f34dcad8cb532aa1e7fa0a8fa6b84a7663d95a3c65d95a32cea22a2bca5e8a2a1c654a2a0ad3fa19609caa18c1d319eb590929d0152659cfea12e9cd68e449c9ad6b09c69b5c39c43b2bc9b3a2c949b00ec489aeae1ee9a9c4dcf9960a2de9786f1c89625c0ea951a1d4f9502b63794cf16ae94aaa346933c1c1892bcdad491e9cd6d91e02f7391bfc8d2919ea1ed91803c43912145928fef42548fdd5fae8fb519798f8506208e3528a28e0b37e0
  | 6, 6 => 0xee1ff3c0ed5fd72aecdf58eceb0b00a7eaf94746eae4d2cee983a1f0e8d07868e860973de7d3b738e622e30ae433d738e27a33e5e0b11b58e0aab53ce0a101d2e07c5742dfd92387dec84c76de2a6e82dd542630dba7a637db09360ed9b5c002d6a77007d6933a8dd431f980d306e8aed26d1e23d2003a45d1e073dfd0a55168cfe2fbc7cd8befdfcd686018cd333a25ccdf9f6dcbffe8f1cb3a071fcb317589ca0c15a7c99db706c947ea71c8cc8fbcc84d9bbfc7f95e85c74aba3cc7420fedc715c5a5c70e9988c706680bc6c72b56c5852c90c1d3e646c19b0898c09cec9bc07f9c3fc016814bbf7cb6c0bf719fdabf24da52bef00c7cbe8c6fa0bd731b99
  | 6, 7 => 0xffdf197dfe74343cfc79c808f85f0356f7e450aaf7243e9bf4f3ead0f4d8edfcf3804e47f31e06ccf31a23b5f30a79c0f183f3d3f103cd8af05f336bee980d9a
  | 7, 0 => 0xfc79c808f4d8edfceaf94746d6a77007ccdf9f6dc947ea71c70e9988adb27a1da3c65d959b3a2c949625c0ea951a1d4f912145928d1e763c8acc8d7c87e0221c7fa907a87f0f3d1d7e8292d9752b997473ecd9366d3f0b956d21bb395a2ed42c3e5728513e225b3d3ad7479c374b1eaf32fc20f62e4a9ab82cb6dc352b66c0ee21d1603e1db4a0231da0b82c1a19c69b00e2a5fb
  | 8, 0 => 0xeaf94746
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffff000000000000aaaaaaaa0000000033333333000000000f0f0f0f0000000000ff00ff000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xff00ff0000000000ff0000ffff000000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc000055550000555500000f0f00000f0f
  | 0, 2 => 0xf0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f000000000f0f0000ffff00000f00ff000f00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff0000
  | 0, 3 => 0x333333333333ffff33333333333333333333333333330000333333330000000033330000ffff0000333300003333000033003300ff00ff00330033003300ff00330033003300330030303030303030302222222222222222220022002200220011111111111111110fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff
  | 0, 4 => 0x70707070707070705f5f5f5f5f5f5f5f55ff55ff55ff55ff5555ffff5555ffff555555555555ffff5555555555555555555555555555000055550000ffff000055550000555500005500550055005500505050505050505044444444444444443f3f3f3f3f3f3f3f3f003f003f003f0033ff33ff33ff33ff33333333ffffffff
  | 0, 5 => 0xaa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a000a000a000a0008888888888888888888888888888000088888888000000008888000088880000880088008800880080808080808080807777777777777777777777777777000077770000777700007700770077007700
  | 0, 6 => 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aa88aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa00aaa0aaa0aa00aa00aaa0aa00aaa0aa00aa88aa88aa88aa88aa88aa88aa88aa00aa88aa88aa00aa00aa80aa80aa80aa80aa00ff00aa00ff00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa00a000aa00aa00aa000000aa00aa0000000000
  | 0, 7 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000
  | 0, 8 => 0xcc00cc00cc000000cc00cc0000000000c8c8c8c8c8c8c8c8c8c8c8c8c8c88888c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000c0c00000c0c00000c000c000c000c000bbbbbbbbbbbbbbbbbb00bb00bb00bb00afafafafafafafafaf00af00af00af00aaffaaffaaffaaffaaaaffffaaaaffffaaaaaaaaaaaaffff
  | 0, 9 => 0xccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8cccccccc88888888cccccccc00000000ccccc0c0ccccc0c0cccc0000ffff0000cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00
  | 0, 10 => 0xeaeaeaeaaaaaaaaaeaea0000eaea0000eac0eac0eac0eac0ea00ea00ea00ea00e0e0e0e0e0e0e0e0e0e0e0e0e0e0a0a0ddddddddddddddddcfcfcfcfcfcfcfcfcdcdcdcdcdcdcdcdccffccffccffccffccccccccffffffffccccccccccccffffccccccccccccddddcccccccccccccccccccccccccccccc88cccccccccccccc00
  | 0, 11 => 0xeecceecceeccaa00eecceecccccccccceecceeccaa00aa00eecccccceecccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ee00ee00ee00aa00ee00aa00ee00aa00ececececececececececececececccccececececccccccccececccccececcccceccceccceccceccceaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaeaea0000
  | 0, 12 => 0xf000f000f0000000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecceccceecceecceecccccc
  | 0, 13 => 0xf0f0f0f0f0f0a000f0f0f0f0f0f03030f0f0f0f0f0f00000f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f00000ffff0000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000
  | 0, 14 => 0xf3f30000f3f30000f300f300f300f300f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0fcfcf0f0f0f0f0f0f5f5f0f0f0f0f0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0
  | 0, 15 => 0xfaf0aa00faf0aa00faf00000faf00000fac8fac8fac8fac8faaafaaafaaafaaafa00fa00fa00fa00fa00fa00fa00f000fa00fa00fa00aa00fa00aa00fa00aa00f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f3f3f30000
  | 1, 0 => 0xfafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faf0faf0faf0f0f0faf0faf0faf0aa00faf0faf0faf0a000faf0faf0faf00000faf0faf0f0f0f0f0faf0faf0aa00aa00faf0faf000000000faf0f0f0faf0f0f0
  | 1, 1 => 0xfefefefefefe0000fefefefe00000000feccfeccfeccfeccfe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafa
  | 1, 2 => 0xff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0033003300ff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00cc00ff00cc00ff00aa00ff00aa00ff00aa00aa00aa00ff003300ff003300ff000000ff000000ff00000000000000fefefefefefefefe
  | 1, 3 => 0xff00ffccff00ffccff00ff00ff55ff55ff00ff00ff00ffffff00ff00ff00ffccff00ff00ff00ff55ff00ff00ff00ff0fff00ff00ff00ff00ff00ff00ff00fc00ff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff00a000ff00ff00ff003300ff00ff00ff000000
  | 1, 4 => 0xff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff55ff55ff00ff55ff55ff00ff00ff50ff50ff50ff50ff44ff44ff44ff44ff33ff33ff33ff33ff11ff11ff11ff11ff0fff0fff0fff0fff0cff0cff0cff0cff05ff05ff05ff05ff00ffffff00ffffff00ffff00000000
  | 1, 5 => 0xffccccccffccccccffcc0000ffcc0000ffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ff00ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaaaaaaaaaffaaff00ffaaff00ffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ffa0ffa0ff00ff00
  | 1, 6 => 0xffccffccffccff00ffccffccffccfcccffccffccffccf0c0ffccffccffcceeccffccffccffccccccffccffccffccaa88ffccffccffcc0000ffccffccff00ff00ffccffcceecceeccffccffccccccccccffccffccaa88aa88ffccffc0ffccffc0ffccff88ffccff88ffccff00ffccff00ffccff00ff00ff00ffcceeccffcceecc
  | 1, 7 => 0xfff0fff0fff00000fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff000000000fff0ffc0fff0ffc0fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeeffee0000ffeeffee00000000ffddffddffddffddffccffccffccffccffccffccffccffc0ffccffccffccff88
  | 1, 8 => 0xfffcfffcfffcffccfffcfffcfffcff00fffcfffcfffc0000fffcfffcffccffccfffcfffc00000000fffcffccfffcffccfffcff00fffcff00fffc0000fffc0000fffafffafffafffafffafffafffa0000fffafffa00000000fff0fff0fff0fff0fff0fff0fff0ffc0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff0f000
  | 1, 9 => 0xffff8888ffff8888ffff8080ffff8080ffff7777ffff0000ffff0f0fffff0f0fffff0c0cffff0c0cffff000fffff000fffff0000ffffffffffff0000ffff0000ffff0000fff00000ffff0000ff000000ffff0000f0f00000ffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffc
  | 1, 10 => 0xffffeeeeffffeeeeffffeeeeffff0000ffffeaeaffff0000ffffccccffffccccffffccccffff8888ffffccccffff0000ffffccccccccccccffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaffff8888ffffaaaaffff0000ffffaaaaaaaaaaaaffffaa00ffffaa00ffffa0a0ffffa0a0
  | 1, 11 => 0xfffffffcffff0000fffffff0ffff0000ffffffccffffffccffffffaaffff0000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00fffffcfcfffffcfcfffffafaffff0000fffffafa00000000fffffaf0ffff0000fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000
  | 1, 12 => 0xffffffffa000a000ffffffff88888888ffffffff88880000ffffffff88008800ffffffff55555555ffffffff55550000ffffffff33333333ffffffff33330000ffffffff11111111ffffffff0f0f0f0fffffffff0f0f0000ffffffff05050505ffffffff00ff00ffffffffff00ff0000ffffffff0000ffffffffffff00000000
  | 1, 13 => 0xfffffffff3f30000fffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeee0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffffa0a00000
  | 1, 14 => 0xffffffffffff000fffffffffffff0000fffffffffffc0000fffffffffffa0000fffffffffff0fff0fffffffffff00000ffffffffffee0000ffffffffffccffccffffffffffcc0000ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffefe0000fffffffffcfc0000fffffffffafafafafffffffffafa0000
  | 1, 15 => 0xffffffffffffcc00ffffffffffffc0c0ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffffa000ffffffffffff8888ffffffffffff8800ffffffffffff8080ffffffffffff5555ffffffffffff3333ffffffffffff1111ffffffffffff0f0fffffffffffff0c0cffffffffffff0505ffffffffffff00ff
  | 2, 0 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff000ffffffffffffeeeeffffffffffffcccc
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x374c11fcd052887f337cc01fcd042cc7f3
  | 3, 0, 0 => 0x5a4e62887e47f1072887f47b8e63047f44c0df2887f44e0dd2887f47b9082cc7f4398c92886947b8ab2886947b8e632c694398c918c59437ca21fc6144c8dd2887f480d062887f47b8ab18c5943e8dd2887f47f0e63007f4
  | 3, 0, 1 => 0x634d22887f47b8f73087f45a4e52887f45fcd22887f47e9082887f45b4dd2887f45fce32887f4374a21fc6244d8dd2887f4410d02887f4410a21fc5a45a4e32887f47b8d22886f4600dd2887f44e4dd2887c47b8e62886e4
  | 3, 0, 2 => 0x7e4e63087f45b8dd2887f47b8e62dc694
  | 4, 0, 0 => 0x7b947398a21fd6065fce62887f57b8e62b4a21fd5e95c8e62887f57b8e62887f0dd5ed4e4e62887f54e4e6324a21fd5ee398bd2887f57b979398a21fd5ea5e8e62887f57bd39398a21fd6005c8e62707f57a939398a21fd5ae4e4ab2887f57b8e6288691755ee3ece62347f5
  | 4, 0, 1 => 0x7b9392a8a21fd5ee4e4e62f87f560539374a21fd5ee4e5002887f57b939398b51fd5da5c8e62887f57b939398a21f15ee4e48d1fc5d57b8e62887f1415ee398a21fc2957b8f8398a21fd5ee490e62887f570198420b31fd5ee398cc2886956b8e62e8a21fd5ee4e4f42887f5
  | 4, 0, 2 => 0x7b935398a21fd539434e62347f55fd72398a21fd5ee610e32887f57e572398a21fd5ee5f8e62887f57e939398a21fd5f94e4e62747f57b8e62887a18d5ee514e62887f57b8e6288831fd5ee640d22887f57b8e62cc7f18d6004e4e02887f57ed39374a21fd5ee3989d1fc635
  | 4, 0, 3 => 0x7b97234ca21fd5ee4e4e62887f57b8e62887f1ad5ee398bf2887f57b8e63087f1655ee5c8e62887e57b96a398a21fd5b7398a21fc6357b93946c8d1fd5ee4e4a21fc4f57b92f398a21fd5ee4a8e62887f57b95d398a21fd5ee398a21fc6256d539398a21fd5ee4d8e62887f5
  | 4, 0, 4 => 0x7b96c398a21fd58d5c8e62887f57b94e398a21fd5ee398a21fc6957b96d398a21fd5ee4cce62747f56097f398a21fd5ee5c8e62dc7f56f972398a21fd5ee5c8e32887f57b98c398a21fd5ee4e4d82887f57b951398a21fd5ee59ce62887f57b963398a21fd5ee5e8e62887f5
  | 4, 0, 5 => 0x7b8fd398a21fd5ee2aca21fc63566136374a21fd5e04e4e62887f57b92d398a21fd5ee570e62887f57b949398a21fd5f44e4e62887f57b984348a21fd5ee608e32887f57b8e62887f1096085a4e62887f57dd39398a21fd5ee408e62887f57b95b398a21fd5ae4e4e62887f5
  | 4, 0, 6 => 0x7b989398a21fd50d398a21fc6357b8e62887f19d5ee398c01fc6357b9393988d1fd5ee398a21fc6554e4e02887f1e5603374a21fc6354e4e62c0a21fd5ee46ce63087f57b965398a21fd5ee574e62347f57b939390a21fd5c0660d22886f578d39398a21fd5ee540e62887f5
  | 4, 0, 7 => 0x7b8f9398a21fd5755c8e62887f57b964398a21fd5ee4e4e82887f57b970398a21fd5ee4e4ed2887f56fd72398a21fd4e6324a21fc63581539374a21fd5ea398a21fc63573998398c21fd5ee508e62887f57b939398a21bd5ee4e4e02887f57b9393dca21fd504398a21fc635
  | 4, 0, 8 => 0x7b9393a4a21fd5ee420d02887f57a539398a21fd536398dd2887f57f0e62887f1855ee420a21fc5a57e139398a21fd5e04e4e62347f57b8e62f87f18d5ee400a21fc6357b93941ca21fd5ee5c8e52887f57b139398a21fd5ee398a21fc3957b931398a21fd5ee5c8e62747f5
  | 4, 0, 9 => 0x7b92b398a21fd5ee568e62887f57b8e62887f18d5864e4e62887f57b939398af2895ee5bce62887f57b91d398a21fd5b5398a21fc6357b9393dc8d1fd5ee4e4f32887f57b8e62b0a21fd530374d02887f57e8e62887f18d5ee534e62887f56dd72398a21fd5ad4e4e62887f5
  | 4, 0, 10 => 0x6b8e62887f18d5f14e4e62887f57b9392ac7f1655ee5c8e63147f57b972398cb1fd5ee4e4e62887e5801393989d1fd5ee3b8e62887f5701983dcc21fd5ee4e4e624c7f56dcfb398a21fd5ee53ce62887f55fd39398a21fd5f94e4e62887f57b96e398a21fd5ee4e4e72887f5
  | 4, 0, 11 => 0x5c90d398a21fd58d4e4e62887f57b933398a21fd53943cdd2887f500136374a21fd2035c8dd2887f57b943398a21fd5ee398b82887f570198398b71a55ee4e4e32887f57b939398a71fd5ee4e4df2887f57b9722aca21fd5ee398c22887f57b93934ca21fd5ee528e62887f5
  | 4, 0, 12 => 0x7b98f398a21fd5ee4e4e62c4a257b948398a21fd603608dd2887f57b8e02887f18d5ee3dca21fc6354e4e62887f1495e55fce62887f55c8e6324a21fd5ee4fce62887f567539398a21fd5ee3988d1fc6354e4e63247f1655ee3e8e62887f57b9393989f1fd5fc4c0e62887f5
  | 4, 0, 13 => 0x7b93b398a21fd5ee398a218c1b573d98420a21fd5ee4e4e62307f57b9072887f18d5ee398a21e4695801ee398c21fd5ee4e4de2887f57c939398a21fd50d3ece62887f57b932398a21fd5ee5a0e62887f57b8e62887f0a95ee4c0e32887f57b94f3dca21fd5f94e4f72887f5
  | 4, 0, 14 => 0x4e4c92aca21fd5ee530e62887f580939374a21fd5ee398a21fc6657b939394a21fd5ee5c8e62887f57b8f32887f18d5ee4e4e62cc7f57b9393989d1fd5ee5c4e62887f57b8ba2aca21fd5754e4e62887f57b933380a21fd539434a21fc5d54e4e62747f1e55f8398a21fc635
  | 4, 0, 15 => 0x7b9d9398c21fd5ee398a21fc6457e54f398a21fd5ee4e8e62887f57b8fb398a21fd5ee4e0e62887f57b8e62887f1b15ee4e4f62887f5701982ac631654e6324ba2887f57b982398a21fd57f398a21fc6357e4e62887f18d5ee398a22147f54e51b434a21fd5ee5c8e62987f5
  | 4, 1, 0 => 0x7b93e398a21fd5ee4d8dd2887f57b9393809d1fd5ee398b92887f57b906398a21fd5ee584e62887f57b8e62887f1a15ee4e4e62d87f54e4dd2887f1ed5ee470e62887f54e536374a21fd5ee38ca21fc6354e4f0398a21fd5ee4e4e62687f57b8df2887f18d5ee4e4e628c7f5
  | 4, 1, 1 => 0x7b9703989d1fd5c0660ab2886957b9392aca21fd5ee398cc18c5957b983398a21fd5ee4f0e62887f580d36374a21fd5df4e4e62887f57b972398a21bd5ee5c8e02887f57b98e398a21fd5ee5c8f72887f55fce6340a21fd5ee4e4e62847f57b9723988d1fd53947ce62887f5
  | 4, 1, 2 => 0x4e504398a21fd539434e62887f57b8e62887f0d15ee52ce62887f57b939398c01fd5ee398ba2887f57b973398a21fd5ee398a21fc38581969398a21fd5ee398a218c5e57b937398a21fd6034e4dd2887f57b939388a21fd5ee5c91b22c7f5
  | 5, 0, 0 => 0x661744e4e62887f6701984b4e62887f6701985f4e62887f670198570e62887f670198524e62887f6001ee4e4e61283e57b939398a21fc746701bc4e4e62887f67b9464e4e62887f67b8e62887f18c3e67b910398a21fc6367b9bd4e4e62887f6661854e4e62887f67b93d4e4e62887f67b8e62887f18c5f67b99f4e4e62887f6
  | 5, 0, 1 => 0x7b8e62887f18c5967b94b398a21fc4a6001ee4e4a21fc2e57b939398a21fc0a600139398c92887f57b9534e4e62887f67b9aa4e4e62887f67b93949ce62887f670198540e62887f6701983f4e62887f67b939398a21fc53670109398a21fc636701982aca21fc636789984e4e62887f6001ea4e4e62887f570139398a21fc486
  | 5, 0, 2 => 0x1ee5c8e62884a57b939398a21fc0867019846ce63087f67b939480e62887f6701944e4e62887f67b9d95c8e62887f67399f4e4e62887f6721984e4e62887f67b9844e4e62887f670198594e62887f6739984e4f72887f6001ee398a21fc3757b8e62887f18c1667b9de4e4dd2887f670198574e62347f67b939398cd2887f6
  | 5, 0, 3 => 0x7019a4e4e62887f67b972398a222c7f670139398a22587f67b939398a21fc566729984e4e62887f679d984e4e62887f6701984e4e62347f6791984e4e62887f670198398a21fc6567b939398a21fc0367b9a5398a21fc6367b94f398a21fc596701b35f4e62887f67b9393988b1fc5967b939398a21fc7567e539398a21fc596
  | 5, 0, 4 => 0x701ab4e4e62887f677539488e62887f64e50c424e62887f67b8e62887f18c5d67b959398a21fc636701974e4e62887f67019f4e4e62887f67b9624e4e62887f6001ee3987f18c3e5701984e4e62886f6701984e4e02887f6701984e4f72887f670198624e62887f67b9b4398a21fc6367b939398a21fc4e670198398a21fc676
  | 5, 0, 5 => 0x7b939398a22887f6751a54e4e62887f6701aa4e4e62887f67b9a84e4e62887f67b939398a21fc0b67b9d55c8e62887f66e939398da2887f67b9724e4e62887f67b9394d0e62887f67b972398a21fc79670198508e62887f67b9bb398a21fc6367b9c05a0e62887f67b972398a22607f67b9e85c8e62887f676939398cc2887f6
  | 5, 0, 6 => 0x7b8e62887f18c6367b939398a22507f67b9994e4e62887f6660e6318a21fc6367b972398a21fc69668d39398da2887f67b8e6330a21fc6367019e4e4e62887f67b9444e4e62887f670198590e62887f67b9d34e4e62887f67b95f4e4e62887f67b9ee5c8e62887f6701984e4ed2887f6819ee4c0e62887f67b8e6374a21fc636
  | 5, 0, 7 => 0x1ee4d8e62887f57b9a1398a21fc6367b9394b0e62887f670198398a21fc3967b939398a21fc1d67b939398a21fc606701775c8e62887f67b939454e62887f6701a64e4e62887f680dee5c8e62887f67b96b4e4e62887f6769984e4e62887f67b939398a62887f67b939398a21fc4467b972398d22887f67b939398a22287f6
  | 5, 0, 8 => 0x7b939398a21fc3d67b939398a21fc3c670198400a21fc6367b9824e4e62887f6701885c8e62887f67b939398e02887f67b9393dce62887f67b962398a22547f67b9985bce62887f676d984e4e62887f676939398c32887f67b939398a22207f67b939398c42887f67b939398cf2887f6801fd4e4e62887f67b93943ce62887f6
  | 5, 0, 9 => 0x7b9393ece62887f6001ee4e4e62887f57b908398a21fc63670198420a21fc5a67b9b04e4e62887f6775985c8e62887f67b9393989c1fc5967b9e5610e62887f67b91b398a21fc6367b9c04e4e62747f67b9c0588e62887f67b939398a21fc2467f1ee398a21fc63670198398be1fc6367b8e62887f18c556001393987f0f8095
  | 5, 0, 10 => 0x1ee398a21282157e5984e4e62887f67b939398a21fc76670198534e62887f67b8e6308a21fc63676198398a21fc6367b9b14e4e62887f67b8e62887f18c2e67b9984ace62887f67b9c05c8e62887f6001ee398a21fc4d570198420d02887f67b939398a21fc0067b972398a22707f6001ee5e8e62887f57b998398a21fc636
  | 5, 0, 11 => 0x68d39398a22607f67b9dd4e4e62887f67b9392888b1fc5d673d984e4e62887f67b939398a82887f6001ee398a21fc6957b9ba4e4e62887f67b9393f0e62887f67b9d14e4e62887f670198398ac2887f67b939398a21fc3167b939398a21fc1b67b99853ce62887f67b9724c0e62887f600172398a21fc0956617f4e4e62887f6
  | 5, 0, 12 => 0x7b939398a21fc366775ac4e4e62887f670198474e62887f67b8e6340a21fc6367b9e55c8e62887f6751984e4e62887f6701984e4f72347f6701393bce62887f67b97a398d52887f673998398a21fc63666139478e62887f67b8e62887f18c5a6701985ece62887f67b939398a21fc4a67b939398d52887f6701984e4f32887f6
  | 5, 0, 13 => 0x70198398a21fc6367b9c0608e62887f67b939398a21fc2167399853ce62887f67b998398c22887f67b939398a21fc0f67b9a34e4e62887f67b8e62887f18c096701984e4e62bca26001ae4e4e62887f5701b74e4e62887f67b9c64e4e62887f670139398a21fc726701985bce62887f67b939398b22887f66617c4e4e62887f6
  | 5, 0, 14 => 0x821ee4e4e62887f67b9c03ece62887f67b9765c8e62887f6811ee4e4e62887f6715984e4e62887f67b939398e12887f67b9de4e4e62887f6001ee52ce62884a5701984ace62887f676139398a21fc71670198568e62887f66f9984e4e62887f67b939464e62887f67b939398a22347f67b9984e4e32887f671d984e4e62887f6
  | 5, 0, 15 => 0x7b939398a21fc116701984e5032887f666101398a21fc6367b9984cce62887f6701984e4e62d07f67b8e62887f1fc636701984e4e624c7f67b9784e4e62887f6001e04e4e62887f57019853ce62887f6801ee4e4e62887f67b9934e4e62887f67b939398a21fc2c67b929398a21fc636001ee570e62887f57b939398a21fc356
  | 5, 1, 0 => 0x7b972578e62887f6701985c8e63147f67b939398a21fc0e67b939398ba2887f67b93942ce62887f6001ee4e4a21282e57b972398a21fc3e67b972440e62887f67b93946ca222c7f67b93945ce62887f6701984a0e62887f6701b3398a21fc6367b939458e62887f6701983b8e62887f66f97c4e4e62887f67b939398a21fc6d6
  | 5, 1, 1 => 0x70172424e62887f6701985c8ab2887f670198398c22887f6701984e4d32887f670139398a21fc3b67b939494e62887f666139398a21fc1567b972398a21fc1967b9564e4e62887f67b939398a21fc4167b94b4e4e62887f680dee4e4dd2887f67b939398c82887f67b939398ca2887f666139430e62887f6701984e4ab1fc596
  | 5, 1, 2 => 0x7019850ce62887f670198398b82887f670198398a21fc6a67b939428e62887f66d9984e4e62887f6819ee398a21fc636661404e4e62887f67b972398a21fc166001ee4e4e02887f5001ee4e4f72887f57b939434e62887f6701984e4e32887f67b972398a21fc5966617d5f0e62887f6701984e4e629c7f6001ee4e4e62347f5
  | 5, 1, 3 => 0x7b939398a22407f67b9b24e4e62887f67b939398c92887f67f539398a21fc7967e59f4e4e62887f6701984e4e62f07f6701984cce62887f67b9c04e4ab2887f67b939398a21fc376000e62887f08409570139398ae2887f6731984e4e62887f67b9874e4e62887f6809ee4e4e62887f66dd39440e62887f680139398a22707f6
  | 5, 1, 4 => 0x7b9103ece62887f67f5ee4e4e62887f67b939488e62887f67b9914e4e62887f67b984398a21fc6367b972398a21fc5d67b939398a21fc1f67b972564e62887f6701983fce62887f6735984e4e62887f6001ee5c8e61fc3e57b939398a21fc4567b939398a21fc0767b9393c4e62887f67b9b45c8e62887f6001ee2887f18c2e5
  | 5, 1, 5 => 0x7b9c052ce62887f67b939398a21fc616701983988d1fc63679198398a21fc6367b939398a22007f66117f4e4e62887f6779984e4dd2887f67b9c0398ba2887f66618b4e4e62887f6001ee398a21fc1957b939398a21fc236749984e4e62887f67b8e62887f1d46367b939398a21fc4067b939398a21fc14680dc04e4dd2887f6
  | 5, 1, 6 => 0x7d5ee4e4e62887f67b972398cc2887f67b939398a221c7f67b9e64e4e62887f6819ee4e4e32887f670198520e62887f67b939398e32887f67b939398cc1fc596701983dca21fc63670198628e62887f670139434e62887f67b9725a4e62887f67b972398dd2887f6701984fce62887f6701093ece62887f6711984e4e62887f6
  | 5, 1, 7 => 0x7b9c0398a21fc376001ee4e4e62884a5701985a0e62887f670198398a21fc2a67b939440a21fc5d67b939448e62887f67b9c34e4e62887f67b9d94e4e62887f670139398c92887f67b939398a21fc5e67019853cf72887f67b972398a21fc6367b9a94e4e62887f67b939398a21fc54666172398c62887f67b939398a21fc586
  | 5, 1, 8 => 0x7b939398a22787f67b939398a222c7f67b9774e4e62887f67b939398a21fc7b67b9394d8e62887f67b939398c62887f66f9844e4e62887f66cd39398a21fc7567b939398a22087f6805ee4e4e62887f666139430e62347f67b939398a22107f6001392887f0b80957cdee4e4e62887f67b939398a21fc5b67b9eb4e4e62887f6
  | 5, 1, 9 => 0x7b972398a21fc2e67b9414e4e62887f67b939398db2887f6701a74e4e62887f67b939398a22607f67b939398bb2887f67b939398a21fc1a676198588e62887f67b939398a21fc4367b939398a223c7f67b9393a8e62887f67b982398dd2887f6775b44e4e62887f67b984398d02887f67b9924e4e62887f67b97246ce62887f6
  | 5, 1, 10 => 0x80dee4d8e62887f67b939398a22187f67b939398a21fc4d6701984e4dc2887f67019b4e4e62887f67b939398a21fc1867b939398a21fc7d67b939398a21fc1c67b9d54e4e62887f67b97a4e4e62887f67b9394e4e62887f6761985c8e62887f67b939398a21fc796001ee5bce62887f57b9964e4e62887f6701a44e4e62887f6
  | 5, 1, 11 => 0x701984e4f52887f67b939398a21fc696001ee3987f0f8215001ee4ace62887f56dd984e4e62887f67b939398d72887f67b972398d02887f64e510434e62887f67b939398a225c7f67b9905c8e62887f670139398a21fc2b6739985c8e62887f6001ee398a21fc6357b939398a21fc4767b9ee4e4e62887f670198398a218c1b6
  | 5, 1, 12 => 0x761ac4e4e62887f673d98398a21fc6367b9554e4e62887f67f5ee4e4e02887f680dee4e4e62887f6001ee53ce62887f5701984e4e62cc7f67b972398a21fc0967b93946d102887f60017f4e4e62887f5001f94e4e62887f57b939398d22887f6701984e4e62747f6829ee4e4e62887f6701982e8ab2887f67b939398b72887f6
  | 5, 1, 13 => 0x7b9af4e4e62887f67b8e62887f0f83767b939398a21fc7067b95c398a222c7f64e4e62889c1fc7967b939398a21fc25675198398a21fc63670198398a21fc6667b9c04d8e62887f67b9393ace62887f67b939398a21fc4c67b8e62887f18c4a67b8e6354a21fc636701985c8e62887f6701983cca21fc6367b939374a21fc5d6
  | 5, 1, 14 => 0x7b939398a22707f6819ee610e62887f67b939398a22387f67b939398a21fc7a67b939398a21fc176701985c8e62987f6001ee398c22887f57b939398a22807f67b9a5494e62887f6775984e4e62887f67b9c94e4e62887f67019848ce62887f680139398dd2887f67b9724a4e62887f670198530e62887f66617c398a21fc636
  | 5, 1, 15 => 0x70198398a22147f67b9544e4e62887f67b9b84e4e62887f67b9394c0e62887f600139398a21fc095709984e4e62887f666139318ab2887f67b939398a21fc7767b939398a21fc1367b939330ab2887f67b95c4e4e62887f67b9c05e8e62887f6001ee4e4e32887f57b9c04e4e62887f67b8e62887f18c2167b939398a21fc326
  | 5, 2, 0 => 0x1ee3987f0f8375701393f8e62887f6741984e4e62887f67b8e6330ba2887f6701983ece62887f66dd39430e62887f67b9e14e4e62887f6001ee4e47f0f82e57b939468e62887f67b9e54e4e62887f67b939398d92887f67b939398a22047f67b9c0398a21fc696001ee4cce62887f570198608e62887f6801ee398a21fc636
  | 5, 2, 1 => 0x7b939398a21fc0667b9574e4e62887f6765c0660e63087f6660e62887f18c1567b9814e4e62887f6661745c8e62887f67b939398a21fc0c67b939398d12887f67b939424e62887f67b9524e4e62887f67c1ee4e4e62887f67b93946cdd2887f67d9ee4e4e62887f670198580e62887f6660e6318ba2887f6819ee5c8e62887f6
  | 5, 2, 2 => 0x7b9c05f4e62887f670198584e62887f67b9c0570e62887f67b939398a21fc2064e4e6330c92887f670198470e62887f67b9845c8e62887f67b9764e4e62887f670139398a21fc1e6001ee5c8a21fc2e57b939398a21fc0d67edee4e4e62887f67b939398a22647f67b9cb4e4e62887f67b939398a21fc336701984e4e62687f6
  | 5, 2, 3 => 0x7b939398a21fc3f67b939460e62887f67b8e6288901fc6367b939398a21fc3e67b939440e62887f679d985c8e62887f6701985c8e62347f6791985c8e62887f67b939398a21fc2267b998494e62887f67b939374d02887f6701984f8e62887f673198398a21fc6367b972398a21fc7567b939398a226c7f67b9584e4e62887f6
  | 5, 2, 4 => 0x74998398a21fc6367b9725c8e62887f67b939398a21fc0567b939398a22747f67f5ee398a21fc636701984e4ab2887f67b939398a21fc01670198398cc18c5967b991398a21fc6367a9984e4e62887f67b939398a21fc1967b939398a22487f6701985c8e62886f67b95e4e4e62887f6001ee5a0e62887f5701985c8f72887f6
  | 5, 2, 5 => 0x7b939398d42887f670198398ba2887f67b939438e62887f67b939398a21fc496701985cce62887f67b939398a21fc12670198398a218c5e67b939398a21fc5c67b9c04e4e02887f6701985c91b22c7f67b9c04e4f72887f67b972398a22887f67b8e62887f18c6167b9c04e4e62347f67b9e54c0e62887f67b939398a21fc596
  | 5, 2, 6 => 0x70198398bd2887f6701985e4e62887f6001ee4e4e62747f5001ee398a218c4a54e4e6374a21fc7967b939398a21fc27670198398a21a45d6701983ece62347f67b9d9398a21fc6367b939398a21fc5d67b9594e4e62887f67b9b94e4e62887f6001ee4e4e61fc3e57b939444e62887f670198398a21fc3467019852ce62887f6
  | 5, 2, 7 => 0x66139398c62887f67b939398cc2887f67b9a24e4e62887f67b8e6288981fc63670139398d62887f6001ee2887f0b82157019851ce62887f670198398ad2887f670198398a21fc376001ee5c8e62887f57b96f4e4e62887f67b9694e4e62887f67b939398dd2887f67b939398a22447f67b8e62888b1fc6367b939398ab2887f6
  | 5, 2, 8 => 0x1ee398a62887f57b939440e62347f67b972398a21fc4a67b972398d52887f67b9ee398a21fc636701984e48d1fc5d67b8e62887f18c4d64e4e6318c32887f670198398a21fc506701983e0e62887f670198490e62887f67b939398a21fc63680d39398dd2887f67b8e62887f1e463670198398cc2886967f5ee4cce62887f6
  | 5, 2, 9 => 0x80dee398a21fc636001ee608e62887f570198398b31fc63600139398a21280957b939420e62887f67b97f4e4e62887f67e5ee4e4e62887f67b93946ce62887f670139398a21fc5167f1ee4e4e62887f67b939398a21fc5567f9ee4e4e62887f6751985c8e62887f67b94f4e4e62887f67b939398a92887f65f1774e4e62887f6
  | 5, 2, 10 => 0x7b96f398a22707f67b939398cb2887f67b939398c22887f64e530398dd2887f67b9393b0e62887f6001ee3ece62887f57b939398a21fc2f67b939398a21fc2e67b9393dca21fc59670198514e62887f681dee4e4e62887f6769c04e4e62887f670198398a220c7f67b972398a21fc21670198640d22887f67fdee4e4e62887f6
  | 5, 2, 11 => 0x7b930398a21fc636000e62887f18c0957b939398a21fc0967b9394cce62887f6701984e51b2347f6701984e4a21fc4f6815ee4e4e62887f67b939398d02887f67b9904e4e62887f670198574e62887f6701984d8e62887f67b8e62889c1fc636001ee398a21fc1b57b939398a21fc5a6801ee5c8e62887f6821ee5c8e62887f6
  | 5, 2, 12 => 0x1ee4e4ab2887f57b939398a21fc7f67b9393c8e62887f67b939398a21fc0267b939398a21fc2d6701985c8e62dc7f67b939398a52887f67b939398a21fc046001ee398a21fc2157019858ce62887f6701985c8d32887f6701984e4e62887f666172398a21fc1567b939398a21fc4b67b939484e62887f670198398c21fc596
  | 5, 2, 13 => 0x1ee52ce62887f570198398a21fc426001ee398ba2887f57f5ee5c8e62887f67b9915c8e62887f6002034e4dd2887f5825ee4e4e62887f67b939398a21fc4667b939398a21fc2667f5ee4e4e62747f67b972398a22407f67b939398a42887f67b939398a21fc28670198398a21fc6967b93944ce62887f67b9d64e4e62887f6
  | 5, 2, 14 => 0x819ee4e4e62887f67b939398e62887f670198610d22887f67b930398d02887f600139434e62887f5
  | 6, 0, 0 => 0x7b9392887f0b95c066139398a21fc6d7701984e4e62887f045dc0660e62887f1fc637701985e139398a21fde00701984e4e62887f77019864d39398a21fdc00701985f4e62887f6701984e4e62887f0b1dc066129398a21fc637001c06615c398a21fd9c066139398a21fc357701985d972398a21fddde701984e4e62887f7001c06614b398a21299ee795c04e4e62887f7
  | 6, 0, 1 => 0x1c04e4e62884a0599c066139398a21fc0e77b9984e522398a21fddee661914e4e62887f7701984e4e62e8a21fddc06613942ce62887f7701ba4e529398a21fdc00701984e4a21282e6701985c8e62887f0f9dc066172440e62887f7701984e51b2888b1fddc06613945ce62887f7001ee61139398a21fd9c066139458e62887f700139398a21fc0f0399ee66139398a22407f7
  | 6, 0, 2 => 0x701985c8e62887f059c00701984e4f72887f6701bb66184398a21fddc066172398a21fc597001c0661393988d1fd800791984e4e62887f67b9984e4e6368a21fddc066139498e62887f7001ee4e4e62887f1d59c066139494e62887f7701985c8e62887f065dc066139398a21fc4177019852d39398a21fddc066139398c82887f77f5ee66139398a21fddc066172578e62887f7
  | 6, 0, 3 => 0x7b9c04e4e62887f165dc06c9984e4e62887f7001c06a939398a21fd9c066139398a21fc377001ee5c939398a21fd9c0695985c8e62887f7765d566139398a21fdd986117c4e4e62887f77019861d39398a21fddc066139398a21fc1077b9c04e4e62887f0f9dc066139428e62887f7765984e4e6288981fddee70139440e62887f7001c067d39398a21fd9c0661954e4e62887f7
  | 6, 0, 4 => 0x7019864539398a21fddc066184398a21fc637701985c8e62887f175dc066139398a21fc1f7701985c959398a21fdc007b9984e4e62884a6001c0398a21fc63059800701985c8e61fc3e67b9c04e4e62887f059dc066139398a21fc457701984e4e62887f0e9dc0661393c4e62887f7701b466172398a21fdc00701982887f18c2e67b9d966139398a21fddc066139398a22407f7
  | 6, 0, 5 => 0x1ee701393987f0f99c066139398a21fc7877b9c06d139398a21fddc066139398da2887f7001c0660e62887f0659c066139398a21fc2377b9984e4e62888b1fddee701a54e4e62887f770198398a21fc7518ddc066139398a21fc407701984e4e62887f051dc1701984e4e62887f770198440fb398a21fddfd701984e4e62887f7701bb66172398a21fddc066139488e62887f7
  | 6, 0, 6 => 0x7b9ee66139398a21fdc00001ee4e4e62887f5701985c8e62887f18dc00661393987f0f80f6701a966139398a21fddc066139398a21fc547701985c8e6330a21fddee701bb4e4e62887f7701984e4e62887f15ddee66139398a21fc797701984e4e6288871fdde6701984e4e62887f77b9c04e4e62887f175dee701594e4e62887f7701984e4e63307f165dee66139398a22607f7
  | 6, 0, 7 => 0x701984e4e6288841fddc066139398a21fc5b7701a34e4e62887f1d5dd370198398a21fc6377b9ac66139398a21fddeb701984e4e62887f7001c066139398a21298007b9c05c8e62887f6701984e5102887f175dc066139448e62887f770dc066139398a21fddee70139398dd2887f7765c066139398a21fddc06cd39398da2887f7701984e4e62887f179c007b998398a21fc636
  | 6, 0, 8 => 0x1ee4e4e62887f1298007b939398d52887f6701984e4e62887f10ddc066139398ce2887f77013944109398a21fddc066184398d02887f77b9c04e4e62887f18ddc0661924e4e62887f7701985c91b398a21fddc066139398a222c7f7701985dd39398a21fdc0066172398a21fc0f680dee66139398a21fddc066139398c62887f7701984e4e6288821fddee70139398cc2887f7
  | 6, 0, 9 => 0x701985e939398a21fddc06617d398da2887f7701984e539398a21fddc066139398a21fc797701984e4e6288891fdc006617c4e4e62887f67019865939398a21fddc066172398a21fc2e77019850539398a21fddc066139398db2887f7701984e4e6288981fdc00751984e4e62887f67a1c066139398a21fddc066139398bb2887f770198398a21fc63181dc066139398a21fc1a7
  | 6, 0, 10 => 0x701984e4e6288971fddd866139398a22547f77019864172398a21fdc0070198398a21fc636701984e4e62887f11ddee701984e4e62887f77b9984e4e62889c1fdc007b939398a21fc216701984e4e6288861fddee7013946ce62887f7701984e4e62887f135c007b939398a21fc0f67b9984e4e6288951fddc066139398a21fc187701984e4e62887f071dd5701984e4e62887f7
  | 6, 0, 11 => 0x1c06614f398a21fd800801ee4e4e62887f6701984e51b440a21fddc066139398d22887f7761c066139398a21fde0a701984e4e62887f7701984e4e62dca21fddc066139398a21fc6977b9984e530398a21fdc0066139398a21fc0967b9c04e4e62887f0b9c007b9de4e4e62887f6001c0660e61fc3e085800701984ace62887f6701984e4e635ca21fddc066172398d02887f7
  | 6, 0, 12 => 0x1984e50c398a21fd9c0661724a4e62887f7701984e52e398a21fddc06bd984e4e62887f770198398a21fc3e0dddc066139398a21fc70770198570e62888b1fddc066139398a21fc2577b9c04e4e6340a21fddc0661393ace62887f7701984e4e62887f131dc0660e62887f18c4a770198398d52887f18ddce701984e4e62887f77019855539398a21fde03701984e4e62887f7
  | 6, 0, 13 => 0x701984e4e62887f04ddc066139330ab2887f77019857139398a21fddc0701984e4e62887f770198398a21fc63085dc066139398a21fc327701984e4e62889c1fddc066139398a22387f7701a066139398a21fddc066139398a21fc177001c0660e6308a21fd9c0660e62887f18c0f7701a566125398a21fdc0066139398a21fc156725c066139398a21fddee70139398a21fc097
  | 6, 0, 14 => 0x1c0660e61fc3e0dd9c0660e6330ba2887f7785c066139398a21fdc00701984e47f0f82e6001ee4e4e6288901fd9e5701984e4e62887f7701984e4e6364a21fddc066139398a22047f770139398d52887f1c5c00660e62887f0840f67019855139398a21fddc06e1984e4e62887f7701984e530398a21fddde70198398a21fc637001ee700e62887f0859c066139398a21fc777
  | 6, 0, 15 => 0x701985d939398a21fdc00701985c8a21fc2e6701984e4e62887f035dc066139398a22647f772dc066139398a21fddc066139398a21fc3377b9984e4e62887f059dc066139450e62887f7701984e4e62887f031dc066139398d12887f7701984e509398a21fddc0661524e4e62887f7001fd7b939398a21fd8007b939488e62887f6001ee64539398a21fd9c06f5985c8e62887f7
  | 6, 1, 0 => 0x1c066168398a21fd9c04e4e62887f03c0e770198398a22407f18ddc066139398a21fc3e7001ee701392887f0b98007b9d94e4e62887f6701984e510398a21fddc066139398a21fc5f766139398cc318a21fddce66139398a21fc5977b9b466139398a21fddc066172398a21fc757701984e4e62889b1fddee695984e4e62887f77019861172398a21fde067b9c04e4e62887f7
  | 6, 1, 1 => 0x791c066139398a21fddc066139398a21fc167701984e4e62887f165dc0661725c8e62887f7001ee4e4e62888b1fd9ee70139398a21fc7577019859939398a21fdc004e4e62887f0580f6001c170139398a21fd800661392887f0b80f670198644e62887f18ddc066139398a21fc1977b9c061139398a21fddc066139398a22487f7000007b939398a21295c06615e4e4e62887f7
  | 6, 1, 2 => 0x765c0660e62887f18ddc066139398a21fc5d77019856539398a21fddc06e5984e4e62887f7000007b8e62887f18d4007b9ee4e4e62887f6001c0661393987f0f99c066139444e62887f77b9c05c939398a21fddc066139398d42887f7001ee75539398a21fd9c04e522398d52887f7001ee4e4e62887f1e59c066139398a21fc127001ee4e4e6288981fd9c066172398a22887f7
  | 6, 1, 3 => 0x701984e4e62887f18ddc066139398cc2887f7701a266139398a21fddc0660e6288981fc637001c0660a21fc2e085800701985c8e62887f6701984e4e6374a21fddc066139398a22447f770198398a222c7f18ddc066139398ab2887f77b99866139398a21fddc066139398c72887f7002037b939398a21fd9c066139398a21fc307001c0660e6288631299c066139398a21fc277
  | 6, 1, 4 => 0x1ee4e530398a21fd80000139398a21fc0957019853d39398a21fddc066139398a92887f7001c0660e6298a21fd9c066139440e62347f7701985c8e62887f129dc066172398d52887f77b9c0660e62887f18dc007b9c04e4e62887f6001ee4e4e62889c1fd9c0671984e4e62887f7701a166139398a21fddc0660e62887f18c4d7755c0660e62887f18dc00775984e4e62887f6
  | 6, 1, 5 => 0x701ac4e4e6354a21fddc066139398c22887f7751c066139398a21fddee661394a4e62887f7701984e4ec398a21fddd7701984e4e62887f7001c0660fb398a21fd9c066139398a21fc2e77b9c04e4e62887f129dc0661393dca21fc597001ee79539398a21fd9c066172398a21fc217701984e508398a21fddc06613946ce62887f7001984e4e62887f03d9c066139398a21fc557
  | 6, 1, 6 => 0x70139398a22547f1c5dc066139398a52887f7001c0660e62887f0858007b939398a21fc3e6001ee4e510398a21fd9e570198398a21fc637801ee70139398a21fddc066139484e62887f7701984e4e62887f025dc066139398d02887f77019864139398a21fdc0070198398a21fc1b67b9c04e4e62887f085dc06cd984e4e62887f7701984e4e62887f169dee70139398a21fc717
  | 6, 1, 7 => 0x1c06614b398a21fd80070198398ba2887f6701985a0e6288981fddc0661915c8e62887f7701984e4e62887f119dc066139398a21fc267755984e4e62887f1d5dc066172398a22407f7001ee4e4e62887f1659c066139398a21fc287701984e513398a21fddd6701984e4e62887f7001c0661392aca21fd9c066139398a21fc7f7701984e4f2398a21fdddc701984e4e62887f7
  | 6, 1, 8 => 0x1ee4e4e6374a21fd800701984e4a21fc2e6701984e4e62887f029dc0661534e4e62887f7701984e4e62887f14dc00701984e4e61283e67019851939398a21fddc0660e62887f18c3e770198440e62887f18dc007b939398a21fc5d6001ee56539398a21fda06701984e4e62887f7701984e4e6398a21fdc00001ee4e4e61fc3e5701984e4e62887f1cddc0661684e4e62887f7
  | 6, 1, 9 => 0x701985c8e62888b1fdc007b939398a21fc6367019853ce62887f165dc0661393988b1fc597701984e4e62887f1d5c0066139398c62887f6001ee4e4e6330a21fd800701985c8e62884a6701984e520398a21fddd9701985c8e62887f77019861139398a21fdc0070198398a21fc376000007b972398a21fd5ee70139398da2887f770198398a21fc63165dc06614b398a21fc4a7
  | 6, 1, 10 => 0x70198398a21fc6318ddc066139398a22507f7701985c8e62887f1a5dc0660e6330a21fc6377019851139398a21fdc007b939398a21fc2e67b9c066172398a21fddc066139398a22887f7701985c939398a21fdc007b93946ce62887f6701985c8e6288981fddc0660e62887f18c5d770198564e62887f18ddde66139398da2887f7001c0660e61fc630f99c066139398a21fc4e7
  | 6, 1, 11 => 0x7b8e62887f08540070198398a21fc4d6701984e4e62887f001dc0661393ece62887f7001c066139398a21fd9c066108398a21fc6377019846ce62887f18ddc066139398a21fc24770198398a21fc63155c007b939398a21fc096701984e4f7398a21fdc007b939398d02887f6701984e4e62887f075dc066139398a62887f7701984e4e62887f111dc066172398d22887f7
  | 6, 1, 12 => 0x2067b939398a21fd9c066139398a22347f7701984e4e62887f085dc066139398b22887f7701984e4e62887f0d9dc0660e6340a21fc63770198398a21fc63169dc066139398a21fc4a7701984e4a222c7f175dc066139398a82887f7001c0660e62887f1a59c0661393f0e62887f7701984e4e62887f06dc0070198398a212821670198398c22887f18ddc0660e62887f18c2e7
  | 7, 0, 0 => 0x1c066139398a21fc3e7001c066139440e62887f7001e5701984e4e62887f70000070198398a21fc636001ee701984e4e62887f7001d5701984e4e62887f7001c066139398a22607f7001c066139398a222c7f700000701984e4e62884a6001d9701984e4e62887f700000001ee4e4e62887f5001c066139398da2887f7001c066139488e62887f7001c0661914e4e62887f7001c066139398a22407f7001de701984e4e62887f7
  | 7, 0, 1 => 0x1c0661844e4e62887f700000701984e4a21fc2e60000070198398a21fc216001c066139398d02887f7001c066139398a21fc2e7001c06613946ce62887f70000066139398a21fc0f6000007b9c04e4e62887f6001c066139398a21fc637001c066139398cc2887f700000701985c8e62887f6001c066139398a21fc5d7001c0661594e4e62887f700000701984e4e61fc3e6001c066139398a21fc167001c066139398a21fc597
  | 7, 0, 2 => 0x1c066139398a21fc217001c066139398a21fc4a700000701984e4e62887f6001c0661724e4e62887f7001c066139398a21fc757
  | 8, 0, 0 => 0x701984e4e62887f6
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
private theorem z2_0 : span (Z 2) 4 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 4 0 = true := z2_0

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
private theorem z4_288 : span (Z 4) 14 288 = true := by decide +kernel

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

private theorem z4_a12 : span (Z 4) 302 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 14) z4_a11 z4_288

private theorem z4 : span (Z 4) 302 0 = true := z4_a12

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
private theorem z5_720 : span (Z 5) 21 720 = true := by decide +kernel

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

private theorem z5_a30 : span (Z 5) 741 0 = true :=
  span_join (f := Z 5) (a := 720) (o := 0) (b := 21) z5_a29 z5_720

private theorem z5 : span (Z 5) 741 0 = true := z5_a30

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
private theorem z6_456 : span (Z 6) 8 456 = true := by decide +kernel

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

private theorem z6_a19 : span (Z 6) 464 0 = true :=
  span_join (f := Z 6) (a := 456) (o := 0) (b := 8) z6_a18 z6_456

private theorem z6 : span (Z 6) 464 0 = true := z6_a19

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12439

theorem PEqualNP.Outside.L_meta_12439 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133032 * 2 ^ 32 + 3941116040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133032 * 2 ^ 32 + 3941116040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12439.mainG PEqualNP.Outside.L_meta_12439.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12439.CG, PEqualNP.Outside.L_meta_12439.CG_mono, by
      have : PEqualNP.Outside.L_meta_12439.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12439.CG_eval⟩
