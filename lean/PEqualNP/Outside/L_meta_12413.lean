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
namespace PEqualNP.Outside.L_meta_12413

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3939035848 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 0, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 37, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 53, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 13, 14, 15, 7, 7, 7, 19, 7, 7, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 7, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 7, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 7, 13, 13, 13, 13, 13, 13, 14, 15, 13, 13, 13, 19, 13, 13, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 13, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 13, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 14, 14, 14, 14, 13, 14, 15, 14, 14, 14, 19, 14, 14, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 14, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 14, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 15, 15, 15, 15, 13, 14, 15, 15, 15, 15, 19, 15, 15, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 15, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 15, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 7, 19, 19, 19, 19, 19, 13, 14, 15, 19, 19, 19, 19, 19, 19, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 19, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 19, 19, 51, 19, 19, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 7, 22, 22, 22, 22, 22, 13, 14, 15, 22, 22, 22, 19, 22, 22, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 22, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 22, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 23, 23, 23, 23, 13, 14, 15, 23, 23, 23, 19, 23, 23, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 23, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 23, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 25, 25, 25, 25, 13, 14, 15, 25, 25, 25, 19, 25, 25, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 25, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 25, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 27, 27, 27, 27, 13, 14, 15, 27, 27, 27, 19, 27, 27, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 27, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 27, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 29, 29, 29, 29, 13, 14, 15, 29, 29, 29, 19, 29, 29, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 29, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 29, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 30, 30, 30, 30, 13, 14, 15, 30, 30, 30, 19, 30, 30, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 30, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 30, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 31, 31, 31, 31, 13, 14, 15, 31, 31, 31, 19, 31, 31, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 31, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 31, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 35, 7, 35, 35, 35, 35, 35, 13, 14, 15, 35, 35, 35, 19, 35, 35, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 35, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 35, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 38, 38, 38, 38, 38, 38, 38, 7, 38, 38, 38, 38, 38, 13, 14, 15, 38, 38, 38, 19, 38, 38, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 38, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 38, 54, 55, 38, 57, 38, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 39, 39, 39, 39, 13, 14, 15, 39, 39, 39, 19, 39, 39, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 39, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 39, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 41, 41, 41, 41, 13, 14, 15, 41, 41, 41, 19, 41, 41, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 41, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 41, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 43, 43, 43, 43, 13, 14, 15, 43, 43, 43, 19, 43, 43, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 43, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 43, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 45, 45, 45, 45, 13, 14, 15, 45, 45, 45, 19, 45, 45, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 45, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 45, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 46, 46, 46, 46, 13, 14, 15, 46, 46, 46, 19, 46, 46, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 46, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 46, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 47, 47, 47, 47, 13, 14, 15, 47, 47, 47, 19, 47, 47, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 47, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 47, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 51, 51, 51, 51, 13, 14, 15, 51, 51, 51, 19, 51, 51, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 51, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 51, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 54, 54, 54, 54, 13, 14, 15, 54, 54, 54, 19, 54, 54, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 54, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 54, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 55, 55, 55, 55, 13, 14, 15, 55, 55, 55, 19, 55, 55, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 55, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 55, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 57, 57, 57, 57, 13, 14, 15, 57, 57, 57, 19, 57, 57, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 57, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 57, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 59, 59, 59, 59, 13, 14, 15, 59, 59, 59, 19, 59, 59, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 59, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 59, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 61, 61, 61, 61, 13, 14, 15, 61, 61, 61, 19, 61, 61, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 61, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 61, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 62, 62, 62, 62, 13, 14, 15, 62, 62, 62, 19, 62, 62, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 62, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 62, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 19, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 63, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 63, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1537153715371f7f1537153715371f7f1537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f1537153715371f7f000000000000000000000000000000001537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f1537153715371f7f1537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f1537153715371f7f000000000000000000000000000000001537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f1537153715371f7f1537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f1537153715371f7f000000000000000000000000000000001537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f1537153715371f7f1537153715371f7f000000000000000000000000000000000000000000000000000000000000000000000000000000001537153715371f7f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e080eac8eac8eac8e08000000000000000000000000000000000eac8eac8eac8e080000000000000000000000000000000000000000000000000eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e080eac8eac8eac8e08000000000000000000000000000000000eac8eac8eac8e080000000000000000000000000000000000000000000000000eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e0800000000000000000eac8eac8eac8e080eac8eac8eac8e08000000000000000000000000000000000eac8eac8eac8e080000000000000000000000000000000000000000000000000eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e08000000000000000000000000000000000000000000000000000000000000000000000000000000000eac8eac8eac8e0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080eac8eac8eac8e080

def cMZZ : Nat := 0x1537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f000000000000000000000000000000001537153715371f7f1537153715371f7f00000000000000001537153715371f7f1537153715371f7f1537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f000000000000000000000000000000001537153715371f7f1537153715371f7f00000000000000001537153715371f7f1537153715371f7f1537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f00000000000000001537153715371f7f00000000000000001537153715371f7f000000000000000000000000000000001537153715371f7f1537153715371f7f00000000000000001537153715371f7f1537153715371f7f1537153715371f7f0000000000000000000000000000000000000000000000001537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f00000000000000001537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f1537153715371f7f

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
  | 3 => 20
  | 4 => 209
  | 5 => 573
  | 6 => 380
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x81a70dca568db65d2a162a1f
  | 3, 0 => 0xf241e28de9b34f6ce7b6f035d855757abdaf093dbcfb63d5bb3f63f7a2c34b06a18405f99830404f8d78867e7337590e7256fbeb578c757a438775ae41159aac3e57b56e12d047a70f8b9b1b0deb5fcd
  | 4, 0 => 0x3f78a79a3e8f812f3ba2dfba397bb29538bbd835369c4f983492b57a33ec84e333a4219333952cb932ad3fd6329a09003224fd5d32123824320a3306306cc8712fb025d92e620c522e0a88aa2b6d281f29a77f7528df99bd27a15bb02767e91c2507a57c25020258238d523922b95af2228371a81f91b4e91f3beb401ec109d11ea1c05b1e9b9c211cb1c2b01b76e3b71ad5f16a1aced3051a07312c19393b8115c933df14a85b55147702a913a9cb8a13a4599b1219e0b41142dc4e10298c270e7e50300e6834e10dd6078e0acf8cad0a747d8409dbafa109d4c54a092d7897081396c9063f18a503cb93df02a567c301bd0f4000dcb21d008d492e001cb74b
  | 4, 1 => 0x8e97d5138c6d9e0f8c0bea488a66b0db8833f14b87fb24a08612f42182688c4581f3c3047f8842fa7d6529c07d3280b77cddcb3b7cb682657adc894977a8cb3575f7a16f75717585751b23087494b5b973802e9f7316a5f072557409720353f270b48efc70b427976e64cc2e6e224c076cd1ceb86c81f42d6b0358766acde2a06a99819669b4611c68ab02ea62030d8861e67f255e2e54895baa28b35aebb93a5a16cc8c57801e1956e9750c569abddb55920348544ca45554390e27536b32f95302a9d1511b99344e249db24d1547604b811a074b7c12bb4b5c3c0d496c799248c0cbe948b0d59947ad2ab445159327440d128f432a217141f68b1f40a9b5ce
  | 4, 2 => 0xdee30416decb77abdc114381d879f71cd86b793dd7a603a0d6120d1cd5aeb9fad4b0af86d36cdeefd3502abbd23ed484cff88b66cd7d0d23ccba9ba2cb2e3f01ca072307c7c982a4c78ee8bfc74ebfefc2dc7575c2cea543c26190f5bf819b2cbea29078be9a3d93bd1a37dcbc67b688b8aa4178b46d98b7b16d2f0bb137f356b09976e7b0665c4eae7959e1ae2d6d84adf0dc71acd04631ac7dce2fac65c774ac24855fabff3565abde7298abac2bf6a957a577a747ba2fa48dfabea3dc6f01a28959b7a1de80649d96b58c9d6aff079d2770889bc8c36c9ae82f299aa9c9469a241edb990fea79987a66b6973d321296b59dfb94cdd29f937bf65992567fab
  | 4, 3 => 0xfd4dab45fd43fb99f8e9397ef8267ac9f53553acf4e24444f4dd1cfbf4d5498ff3494579f26e762af0ad07eff01617adefb17c0fea627681e87e8882e3268febe05400d8
  | 5, 0 => 0x1189613610ded2ca10d20cad108d33ff107979361064441110298c27101c636b0fd55a410fac75250f95fdbf0f2b82250ed257230eb91d770eacab8d0e82303e0e4cdcde0e47c6180e3e28670e2f10630e2b327d0e1041120de8b8710daee68e0cce16400c8c2cea0c1fed4e0bc0150c0b6684d10b66495e0a66f9c609c10cc6094774230920971708f236ca08dadc3708d16333087a8699085460fa0812834f0702eec1067c830c06481a19062e81670620e2ae0597660f0569fe1a053353110525c8fe0423004003ea35990331a56f031a6beb0300f68302e1c47e02ada4b20279a11601f6487b01b62e0e019c5c220154985c00db2a3b007922f500558a7a
  | 5, 1 => 0x2991e7dd296b5b6628a9d50d288b7f72283ad98328029d1d27e3869d2784615b275493da27001ce826ebf55426eab923263b51d325f2688b2525a98e250990582484d6be242df4e624270dab23e4f11723bdb85a22b225d5229191ff22786f6321fe77b621ebebfa2183f3f5210f72d520340a341f4b6b151f3beb401ec109d11e9b9c211dbc8e901d8a3c731d3524251ccea7d71c71bd721c63eaf01c2d36e01b77c1511aad956f1a25743b1a07312c18ec670d189bb43b17dbf9d317659991171bc9881712dbbe16248ea21614c7a215b448ac151d5e3d1511319814f9c2fb14dc87d81498aa531484d939147702a913b3787e13900ebc121de41611e6532f
  | 5, 2 => 0x455ab20b45391a5d4495cc83442daa3343d27d3843bf9e92439e960c437eb78e432f5bcc43156793427f7523421fa67440cd3afd40bfb9a23fbda9883fae84573eec12803e8df94d3e7bd3bb3e11c5d83d9c6c4a3d953e133d202dcb3b5625dc3b55fc633ae221283aa415853a124d1c39f35fba39caf2c7396c683d396b778d37f3d64b371e22c8361dc56f358d049e353bc805351e275034925c16339454883379cc183369fab7329a090032496a92323e408332350f0331788e4e3139e24b30f57e4530362fc8301fdf672ee523a42e8abca42e769fe62d7d3ed42cb44b092c1c6bbe2be635b32bad26ba2b7254012b2479802ad16c4e2a94cc6a2a008be9
  | 5, 3 => 0x5a9e38b45a40bb185a16cc8c59bc469b59535f5b591b14df58e50cbb58b9a62658aa3056579a1cbf573db09456f3970a56e7164156e4778656aefbeb55d4762155bfb1e8556b08795544e2da541cefb153494413534104bd52b43ebc526b73d651df1af351999ad3518fd27750e7472750df6f2e509376294fa5e7fd4f6adee34f1ce1f44ed99b594e80e1614d1ff3c54d1547604d02be164cacf5214bc8de864af38f294aed6cba4aec9b434a96e73f4a95a2f64a2656224a204ef349db85e249b7f24c499884194989525749743bfe4903d6aa48b0d59948adc25748646136482d5aac47768fe9474e820047411fd4472ff7aa4715bcc545b2592645807a5b
  | 5, 4 => 0x715e32e87116f41570dc1ca270cc13b0706ed4d9703f1d507012f9786fb32ac96f68f1436ed9b70a6ed22b6f6e69d0c06e32e3876e224c076cde4bab6c46e7966be5eb3c6bda7d236a9981966a1a2a486a10274969f4321a69e095cf69bc4d6269ac77b6699b485b68aace5668559584684ff95a683b19866783ba56677d0bb2673e66b466ffad4e65f122a8658c361b6587cd68654d5929653bf735653aac84652ca50964fd834c64995cc16497c34e6434702c6433ede2637eadc062de2a0e6217edaf61d5e0ed60db773460c120ec5fed20b95fb664ad5f721c585f453a465ed6d50f5dd9529c5d69fb165cd9eb415cacd4145ca2fe085c7d5a675b2ce097
  | 5, 5 => 0x8d9d9abd8d113e068cea69dc8c0136cf8bec3e228bea195b8bd361778bc9b1cb8baf0c088ba8d7da8b962f388b5a41568b2fa6d78af2df178a66b0db8a10da8789a87f75884220b687de8130876eefb0862373408600a8838486c4cf840ea4a8835affc182db14a781f3c30481cefbab81a69aa480f8af5980f42c5c7feb96477fbf34997f7224b37e9bcddf7e4c5d567e3732417e1ba6c47b0eb58d7a97be367a95f62c7a86a05c7a4a088079e195fa79797e027971ab2b78f0ed6d78970cac7883362b785446f878395e347835cdc977c6901b76cf57dc76b1cddd7628e56875eee7d6757a239f756c2a357519c40e7419eeb273db3b03735ac05d71f2c0ff
  | 5, 6 => 0xad21524eac8c861cac4d1513ab35ae6aa9fc99e4a964af9ea9548932a88ce759a82b8086a805fc9da7ba5cb2a747ba2fa6139f62a5d86578a501a690a40d6362a40cf325a384237ea2f70e16a22f81b7a1f97042a1efadd1a1e73f3ea128b8bca1151995a0e685dba0a1e5a39fe3f7c69eaf42549d6aff079bf8c6859bf5135a9b37ff779a6ca06f9a1e79c699cc515099a053e09967f2a697d52fdf97bc677b97b32ec496c130ec96b59dfb959e44379563aa2e9537e65b9517a74694e47dd794c4ced29463a5b3944c9a849426f3a9937bf65992a576e991771dee9127aa1e911023128fad9d528fa7b7d88f12ff5b8e5d8c428e0894f98dd23cae8d9f097e
  | 5, 7 => 0xd7f22fbfd7774364d76e0bbed7468216d7368bc6d705573fd66194f7d5aeb9fad57b9881d55d0077d3680c8fd336d382d22305f9ce44355ccd7d0d23cd15375ccb8eb8efcad651a3ca906be6c74ebfefc73ca582c63a962bc6353501c6069589c5e75de5c427366ec381bc19c341b75fc25bcb0fc16dd8f0c11fbf2dc0aab38ac08fe933c040abb4bfc6ca2dbef27e9ebe9a3d93be0f0811bd0bb25abd037b58ba66d0b4b9c4a162b9ab5126b8c097bfb8608008b7885726b6cfae67b630df54b62711ddb4c56d29b4bdecf5b38d5ba9b329a1bbb27d2ee1b2076326b178bb34b0dde1d6b09bb0a9afbf2f14af9f9453ae777bfcae176b16ad92f15bad6aef80
  | 5, 8 => 0xffe61558ff39ddc4febc7e73fca80234fc7eca15fc606e3efbcdd5c5fa9007cafa379fbcf9fb7b6bf8e9397ef8be258cf83a1749f8390102f732128ef56e26f4f527f6a2f4ff5ff7f4e490fcf4e24444f4763989f3d48f3bf3d09726f29b579ef151defaecd4d000ecd2b796ebde51a0ea5ceb55e9716f67e89c82b9e86e45cfe6b63796e56f2b39e4f5cb55e46c4edae2d25a82e2bec454e1f0e926e1a87ebbdfe250c9dfcbb772dfc57e77df83621bdeff674bde96fa89de080ed9dd0ea04adcaa53dfdc3e88a2dc3c4896db9afd8ddb60970bdb3b1261da10738dda01c8e8d9d98654d9b91c56d8ec9d06d8e44538d8575c44
  | 6, 0 => 0x212b2d1b20d0ea1d20af526f1ffcd4201fad60501f95d9441f34fc8a1e3353841d17f4721cb6b6661c8e4b2b1b70200e1a71f4541a6fcf8d1a34c23a19b55d09197895491944c657189690b9189665dd1864f9e61728d44116c7d6e814f0f8951386d9f8136a0e5d12945ada127fa6bd1160cad910d20cad10797936104f4df4102c50d60f57a8dd0f144d7f0df7dae50c9345d30c5c589a0c585f520bac67da0ac20dc309fa15aa09946bbf0947742309394a2d091d746808d16333087a8699085460fa083dbff0081b1f1007cd1053079980fb071cc2de0708ec5d06bb83fb0436b5d403f1e06702e1c47e02ada4b20260f13501f6487b01f1eb9f0066bd1e
  | 6, 1 => 0x41181319400f94d33ffe71663ff40d4a3fefdb7c3fb23ffa3f6398083f2166db3f123ffc3eb2714d3e44e5463d202dcb3cfd322e3cf327ed3c18a78d3bf0a5b23b123c4e394f8aae385023533819361a37f3d64b371e22c8368bb2cf364012e43630a40e361c661735b6f32a357c766c3569fca834995594345e1baa342068683409f5b533f14cf333875cc2329319943292a9573209d9b0317cc448307f267430756403306cf57030362fc83033d9ec2f9acfc72f9327c32f6c3c0d2f279bd52e2a76ce2d0fd2e52bcc65dd2b1c33912a8836522a182e9329a8313028260a1227f84a8426eab923265ae6112546e71e24270dab22e95be522d250b622aca9db
  | 6, 2 => 0x658da089658b0d7164e74b2964995cc16434702c64014eb363e2b6a961edc2c161bc89b45ede7e9f5e6590bf5dd9529c5d36c6e25cd9eb415ca2fe085c8b7c9e5c05af3b5a6342205a40bb185a301c7f5a1b2586595c07d558aa305656f3970a5693a19e55d4762154baeb33548c4bbb541cefb153d9bb3a53ac05db53358d17530740f852b43ebc526740fa5207724b51c76d9151999ad351924a2b50e1814150ac4db5508db5ab4ec661e64d68f9114d1ff3c54ce65d394c94be434be50ceb4b91688c4b0e843e493dbaa848ec86e648d1776a48c2280748b0d59946e6363a455ab20b45391a5d44b69586435a32b0434b235b42f343c442ae37a1418bce41
  | 6, 3 => 0x8d9f097e8d4234a58cea69dc8c02c1dc8ae624708a538bf78a00cdc489366ba28915bdfc88bd55ee876eefb0875782e586beb7348402186283d60e5b83adacd4836a472e82fbefbb825a7e88825a456d82564d588193099a7fd7952c7e1279ad7dde59e17c1160df7bb7b32c7b586dc87b16ca8c7ac7c5317a6407d278e2a1877877752e7835cdc97791237276f3fc0175c0bcfe753bedc8737b818772f2050c71f2c0ff706ed4d96f371ee26f05446f6e697dc16e6806fb6e516da46e09184d6df2cbd56d851d7d6c1879aa6c031cfd6b94567c6ac43ed46a1a2a4869c0c89369bc4d6269ac77b6684ff95a683ed288677d0bb26769fb6a66adf77665f3c1f0
  | 6, 4 => 0xc7b84711c6798c78c5e75de5c3c17e32c381bc19c11fbf2dc0cf20bfbd6ad9d1bd1072d1ba394774b957227bb91a8297b8c097bfb26aa744b2436e87b09bb0a9aeb9d7f9ae777bfcadd12142ac0ff2a0ab545e04aab2ed0da8ab2a68a7386ad0a661b000a5eb4fbea396e7c5a3623e05a30a8f66a1e73f3ea177b92fa00f17639ff7c2d89f57c2da9f12ea2c9eaf42549e1bb3ec9d3ed3a49d07e66b9aa5a37b99ebff8b98ecaff39846c2f397cd2a509777ecf79757196095c1f94a9588a4ee9502393994cdd0469426f3a993b9093e926febc69186acb0917d44a391677aab91335adf9127aa1e90ff5743903be43b8edb40a78e6bcb8a8e323b628e0894f9
  | 6, 5 => 0xffe61558ff51c9ddfef48b06fec4d37dfcef86edfcb899b4fc606e3efb6401d8fa9007cafa603350f602c1dff3d48f3bf3c062b1f3833979f31f12eef163e03bedf7d285eb5fa16eeb328a41eb28b435eb031094eae9dcf4ea5ceb55e923eee1e8c67145e73f5c53e72fe683e61fd2ece56a2db3e3f0bea6e2a2a5dee268b4bee1cefa40e064d120e01f5100deff674bdb9afd8ddb6cebd4d9794556d91c9d6cd91b5923d8a60520d83da879d7f9f22bd7368bc6d66194f7d59b72f2d57b9881d55d0077d3bed08ad31b82b0d2046dbbd0a55ca1cf456fcfce343a84cde4f3ebcd13af7acba5e3f8c967d755c87915e7
  | 7, 0 => 0xf602c1dff31f12eeeb5fa16eeb28b435e8c67145d7368bc6cba5e3f8ba3947749f57c2da97cd2a509757196091677aab91335adf8e6bcb8a8e323b628ae624708915bdfc825a456d7ac7c5316d851d7d64e74b2964014eb3530740f85207724b48d1776a48b0d5993f2166db3cfd322e3569fca8306cf57024270dab22aca9db1fad60501b70200e06bb83fb
  | 8, 0 => 0xd7368bc6
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000cccccccc00000000aaaaaaaa0000000055555555000000000f0f0f0f0000000000ff00ff000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xf000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff000000ff000000cccc0000cccc0000aaaa0000aaaa0000555500005555000033330000333300000000ffffffff00000000ffff0000
  | 0, 2 => 0xf0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000ffff00000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff0000ffff000000ff000000ff0000
  | 0, 3 => 0x333333333333ffff33333333333333333333333333330000333333330000000033330000ffff000033330000333300003300ff003300ff00330033003300ff0033003300330033003030303030303030222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff00000fff00000f0fffff0f0fffff
  | 0, 4 => 0x55555555ffffffff555555555555ffff55555555555555555555555555550000555555550000000055005500550055005050f0f05050f0f050505050f0f0f0f0505050505050f0f0505050505050505044cc44cc44cc44cc44444444444444443f3f3f3f3f3f3f3f33ff33ff33ff33ff3333ffff3333ffff33333333ffffffff
  | 0, 5 => 0xa0a0a0a000000000a0a00000a0a00000a000a000a000a00088888888888888888888888888880000888800008888000088008800880088008080808080808080777777777777777777007700770077005f5f5f5f5f5f5f5f5f5f5f5f5f5f00005f5f5f5f0000000055ff55ff55ff55ff5555ffff5555ffff5555ffff00000000
  | 0, 6 => 0xaaaa8888aaaa8888aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00ff00aa00ff00aa00aa00ff00ff00aa00aa00aa00ff00aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a0a0a00000
  | 0, 7 => 0xaaaaaaaaaaaaafafaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa88aa88aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0
  | 0, 8 => 0xc0c0c0c0f0f0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaffaaff0000aaff0000aaff0000aabbaabbaabbaabbaaaaffffaaaaffffaaaaffff00000000aaaaaaaaffffffffaaaaaaaaaaaaffff
  | 0, 9 => 0xcccccccc88888888cccccccc00000000cccccc00cccccc00ccccc8c8ccccc8c8cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000c8c8c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0ccc0ccc0ccc0ccc0c0f0f0c0c0f0f0
  | 0, 10 => 0xccccffffccccffffccccffff00000000ccccccccffffffffccccccccccccffffcccccccccccccfcfccccccccccccccccccccccccccccccc0cccccccccccccc88cccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0
  | 0, 11 => 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaeaea0000eaeaeaeaaaaaaaaaeaea0000eaea0000eaaaeaaaeaaaeaaaea00ea00ea00ea00e0e0e0e0e0e0e0e0e0c0e0c0e0c0e0c0ddddddddddddddddcfcfcfcfcfcfcfcfcfcfcfcfcfcf0000cfcf0000cfcf0000cfcccfcccfcccfcccdcdcdcdcdcdcdcdccffccffccffccff
  | 0, 12 => 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecceecc0000eecceecccccccccceecceecc00000000eecccccceecccccceecc0000eecc0000eeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececececcceccceccceccc
  | 0, 13 => 0xf0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccc
  | 0, 14 => 0xf0f0ffff00000000f0f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f0a0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f000000000
  | 0, 15 => 0xfaaafaaafaaafaaafa00fa00fa00fa00fa00fa00fa00f000f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f3f3f3f3f0f0f0f0f300f300f300f300f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f3f0f3f0f3f0f3f0f0fffff0f0ffff
  | 1, 0 => 0xfcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafa0000fafa0000faf0faf0faf0faf0faf0faf0faf0f0f0faf0faf0f0f0f0f0
  | 1, 1 => 0xff000000ffff0000ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000
  | 1, 2 => 0xff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff000000ff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00ee00ff00ee00ff00aa00ff00aa00
  | 1, 3 => 0xff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff55ff55ff00ff55ff55ff00ff00ff33ff33ff33ff33ff11ff11ff11ff11ff0fff0fff0fff0fff0cff0cff0cff0cff05ff05ff05ff05ff00ffffff00ffffff00ff00ffffffffff00ff00ff00ffffff00ff00ff00ff0fff00ff00ff00ff00ff00ff00ff00fc00
  | 1, 4 => 0xffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ffc0ff00ff00ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffa0ffa0ffa0ffa0ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00
  | 1, 5 => 0xffeeffeeffee0000ffeeffee00000000ffccffccffccffccffccffccffccff88ffccffccffccff00ffccffccffccf000ffccffccffccccccffccffccffcc0000ffccffccff88ff88ffccffccff00ff00ffccffccccccccccffccffcc00000000ffccff88ffccff88ffccff00ffccff00ffccff00ff00ff00ffccccccffcccccc
  | 1, 6 => 0xffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffcfffcfffc0000fffc0000fffc0000fffafffafffafffafffafffafffa0000fffafffa00000000fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff00000fff0fff000000000fff0ff00fff0ff00fff0f0f0fff0f0f0ffeeffeeffeeffee
  | 1, 7 => 0xffff8888ffff0000ffff5f5fffff0000ffff5555ffff5555ffff5500ffff5500ffff3333ffff0000ffff1111ffff1111ffff0fffffff0000ffff0505ffff0505ffff00ffffff00ffffff00ffffff0000ffff0000ffff0000ffff0000ff000000ffff0000fafa0000ffff0000f0f00000ffff0000eeee0000ffff0000cccc0000
  | 1, 8 => 0xffffeeeeffff0000ffffcfcfffff0000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffc0c0ffffc0c0ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaa00ffffaa00ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa000ffffa000ffff8888ffff8888
  | 1, 9 => 0xffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffefeffff0000fffffcfcfffffcfcfffffafafffffafafffffafaffff0000fffff0f0fffff0f0fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000fffff000ffff0000ffffeeeeffffeeee
  | 1, 10 => 0xffffffff80808080ffffffff55555555ffffffff55550000ffffffff33333333ffffffff30303030ffffffff0f0f0f0fffffffff0f0f0000ffffffff00330033ffffffff0000ffffffffffff00000000fffffff0fffffff0fffffff0ffff0000ffffffeeffff0000ffffffccffff0000ffffffcc00000000ffffffaaffffffaa
  | 1, 11 => 0xffffffffeecc0000ffffffffeaea0000ffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffc000c000ffffffffaaff0000ffffffffaaaaaaaaffffffffaaaaa0a0ffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffff88888888
  | 1, 12 => 0xffffffffffccffccffffffffffcc0000ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00ffffffffff00f000ffffffffff000000fffffffffcfcfcfcfffffffffcfc0000fffffffffafa0000fffffffff0f0f0f0fffffffff0f0f000fffffffff0f00000fffffffff0a0f0a0fffffffff000f000ffffffffeeee0000
  | 1, 13 => 0xffffffffffffa000ffffffffffff8888ffffffffffff8080ffffffffffff5555ffffffffffff5500ffffffffffff3333ffffffffffff3030ffffffffffff1111ffffffffffff0f0fffffffffffff0505ffffffffffff00ffffffffffffff0033ffffffffffff0000fffffffffffc0000fffffffffffa0000fffffffffff0fff0
  | 1, 14 => 0xffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff0a0fffffffffffff000ffffffffffffeeeeffffffffffffccccffffffffffffcc00ffffffffffffc0c0ffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0
  | 1, 15 => 0xfffffffffffffffffffffffffffffff0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1e8469a8eb68d3c9d691a7e3
  | 3, 0, 0 => 0x98c2da4aa4e9b611a6a4ad3b1547e4e0dd51a6a498a8d1a794adc2d547e49728d1a7e4e9cc56e6a4e9bfdd8ca4e9bf5247e4ac3611a7e4f556d1a7e498ba554794f43b1546a498b216e7e4e9bb14e6a4
  | 3, 0, 1 => 0xe9cc524794f45751a7e4adbb154794f43b1947e4
  | 4, 0, 0 => 0xe9cc5f6aa3f2ed2a4ec551f974731762a8fcbc1bad751a7e5c64c610aa3f2efe62ec651f97a79f762a8d4bd39dbb1547e5e94c5d8aa3f2f4dd8b9551f973731762a8fcbc698bb1267e5d35d662b7352e9aeaff763297a731761f88abd398aa91c7e5
  | 4, 0, 1 => 0x973b154a33f2f4e630b551f97a731762a4fcbd398bd5547e5df4c5d8aa3f2f4e94ec551a97a73176294fcbd3a63b1547e5e9cc5d8a83f2f4e62aa3f11d7a73182aa8fcbd376361947e5e9d5dd8aa3f2e3dd8c2551f97a75c762a8fcbd398bb1546a5
  | 4, 0, 2 => 0xf6f4dd8aa352f4e62aa3f1217a7317631cfcbd3973b14a7e5f1cc5d8aa3f2faa62e9551f97a73176234d4bd198bb1547e5e9d75b08d3f2f6662ec551f96631b762a8fcbd39fbb1547e5efcc5d8aa3f2f4e6eec551f973131762a8fcbd3ab3b1547e5
  | 4, 0, 3 => 0xe9cc5d8a53caf4dfeec551997a7317caa8fcb3176329907e5e9cc5d8aa3b2cc5d8bd551f97a731762f954bc1babb1546a5b4cc5d8aa3f2cc5d8aa3f0c9662ec5528cf2bd398ae1547e5e9f1662933f2e8a62ec551a97a73176244fcbd398bb174aa5
  | 4, 0, 4 => 0x98c2dcaaa3f2f4e6301551f97a6ec6c2a8d4bd398bb1267e5d35d5b08d352f4e62b7551f97a73185a48fcbd398b69546a5e9cc5d8993f2f4e62ec551f97db31762a8f2b7e98bb1547e5e9cc616aa3caf4e62ec509f974d9276328fcba2ab3b1547e5
  | 4, 0, 5 => 0xd14c5d8aa3f2f4e62ec552117a72e55234fcbd398bb14c7e5f14c616aa3f2d6262ec551a97ad31762a8fcbd398bb1546c5e9cb9d8aa3f2c25fcec551f97a751762a8fcbd394bb1547e5e9cc5d0aa3f2f4dd8ca611f97a719762a8fcbd398b6d547e5
  | 4, 0, 6 => 0xe9d75d8a73f2f4e62ec491f97a731752a8fcbd3e5bb1947e57634584aa3f2f4e6cec551f97a6ec65258fcbd398bb1927e598bb168aa3f2f4e7cec551f97a6ec551f8d0bd398bb154795e9cc5548f3f2f4e62ec551fd7a72d762a8fcbd390bb1547e5
  | 4, 0, 7 => 0xe1cc60aaa3f2cc5d8aa431f97d53151a34fcbd3adbb1547e5e9bb1547e1c2db262ec551f97a742762a8d4bdd98bb1547e5e9cc5b4aa3f2f4e5cec551e571f315c2a8fcb3185c25547e5dfcc5d8aa3f2f4e62aa469e57d15d762a8fcbd3762a8fc565
  | 4, 0, 8 => 0x98bb1caaa3caf4eb6ec469f97a731802a8fcbe098bb1547e5e9cc5d8ca352f4e62ec551e976f31762a8fcbd39e3b1547e5e9cc5c4aa3f2f4e60ec551f97a73176300fcbdb98bb1547e5ac4c5d8aa3f2f4e62ec551f171f31762a8fcbd398bd9547e5
  | 4, 0, 9 => 0xea4c5d8aa3f2f4e62e4551f978cfe762a8fcb5898bb11a7e5e9cc5d8ab3f2f4dd8aa4b1a9662ec642a8fcbd3762a8fc675e9cbdd8aa3f2f8262aa469f97a741762a8fcb3184bb1267e5e9c2dfaaa3f2cc612ec551f97d0ec551f8ccba298b69547e5
  | 4, 0, 10 => 0xe34c60aaa3f2f6262ec551f97a74d762a8fcbd376309547e5f04c5d8aa3cade662ec551f97a75d98ae0fcbe998bb1547e598bb1547e2a2f4e84ec551f97a732762a8fcbd3762a8fc395e9cc5d8b13f2faba731499f97c531762a8f2bd3612e1547e5
  | 4, 0, 11 => 0xf44b9d8aa3f2cc5a2b8551f97d13155234fcbd398b296e7e5add61d8aa3f2d7e62ec551f97a74276234fcbd398bb1947e5ac3b1b0aa3f2f4dfaec551f97a739762a8fcbeaadbb1547e5ac4c5b4aa3f2fa262ec551f971d31762a8fcb5b762a8fc775
  | 4, 0, 12 => 0xe9cc5e2aa3f2f4dfcec551f97db3185aa8fcbede9bb1947e598bb1a2aa3f2f4e62eb551f97a731762f154bd37a3b1547e5e9cc5e6aa3f2cc5d8d2551dd7a731762c8fcbd398c11547e5e9cc5d8aa3eadd6ad08551f96630b5528cfcbd3a53b1947e5
  | 4, 0, 13 => 0x1d37f3b1267e5
  | 5, 0, 0 => 0xe9cc5d8aa3f005ba73176331547e6e9d1662ec551f9bc131762a8fc616e5e9aeaec651f9ba73187bb1547e6e9cc5d8aa3f0b9ba731762a8fc5c6e9cc5d8aa3f02daeb3176339547e6e9cc5d8aa449f9b4d759b3b1547e6e9cc5d8aa3b985b4d75763292c7e6bacc60cec499f9ba731873b1547e6
  | 5, 0, 1 => 0xe9cc5d8dd551f9aeb3177bb1547e6e9cc5d8bf551f9bd19298bb1547e6e9cc5d8d8551f9b4d31762a8fc106d35d6a4ec551f9ba731762a8fc3c6e9cc5d8aa3f129ba731762a93e7e6e9cc5d8aa3f09db4d75762a8fc566e9cc5d8df551f9ba7a6adbb1547e6d35d680ec551f9ba74398bb1547e6
  | 5, 0, 2 => 0xc7cc5d8d4551f9b8731762a8fc6e6f874e62ec551f9b4d92762a8fc666d364662ec551f9ba77598ae1547e6e9cc5d8aa3f0f5b4d7a98bb1547e6e9cc5d8aa3f195ba75b98bb1547e60074e62aa268b974d3182aa9367e6d33b196c2551f9ba731762a8fc4b6e9cc5d8aa3f059ba73188bb1547e6
  | 5, 0, 3 => 0xe9cc5d8aa3f071ba78098bb1547e6e9f4e62ec551f9ba731762a8fc5a6d35d662da551f9ba7318bbb1547e60074e62ec551a974d7598aa8fc496bacc5d8ae551f9ba731762a8fc416e9e6662ec551f9ba731762a9007e6aa53e62ec551f9801d3762a89a235d363e62ec551f9801d398bb09a3e5
  | 5, 0, 4 => 0xe9f2ebaec551f9ba75b762a9467e698bb154a33f1ddb4d31762cd547e6e9cc5d8d0551f9b4d7598bb18a7e6e9f3e62ec551f9aeb6898bb1547e6e9d75d8aa4b1f9b4d75a13b1546a6e9eb262ec551f9801d398c15547e5d34c5d8aa3f0c5b4d8298bb1547e6e9cd662ec551f9b4d5898bb1547e6
  | 5, 0, 5 => 0x74e630b551f974d9698bb1547e6e9cc5feec551f9bd531762a9467e6e9cc604ec551f9b6d7598c21547e6d35d64eec551f9ba78c98bb1547e6e9d9a62ec551f9ba75098bb1547e6e9cc5d88d3f171801d398bb14a7e5d35d6b6ec551f9bc1a698bb1547e6e9cc5d8aa3f0a5ba7316c2a91a7e6
  | 5, 0, 6 => 0xe9cc5d8ad551f9ba731762a8fc796e9dd662ec551f9ba731762a9347e6e9d8662ec551f9ba76598bb1547e6bacc5d8c6551f9b4d3184bb1547e6e9cc5d8aa3f191ba731762a9447e6da4c5d8aa4d9f9b4d7398bb1547e6d35d662fa551f9ba7317e3b1547e60066262ec551f9401d3ab3b1547e5
  | 5, 0, 7 => 0xe9cc5d8d3551f9b8d3181bb1547e6d35d662e2551f9ba77598bb1267e6e9f2662ec551f9ba7a598bb1547e6e9cc5d8aa3f035ba73185aa8fc776cf4c5d8aa4f1f9b4d7598bb1807e6e9cc614ec551f9b4d3181bb1547e6d4dd662ec551f9b4d31762a8fc216de65e62ec551f9ba73176bb1547e6
  | 5, 0, 8 => 0xbacc610e0551f9b4d9e98bb1547e6e753e62ec551f9ba73176328fc666e9cc5e4ec551f9bb5d398bb1547e6d8e0e62ec551f9bc3d398bb1547e6d35d66300551f9b81a698bb1547e6d35d662ec651a9ba79c98bb1547e6f6cc5d8aa3f1ddba79d98bb1547e6e9cc5d8da551f9bd5d398bb14a7e6
  | 5, 0, 9 => 0xe9cc654ec551f9b4d9298bb1547e6d34c5d8aa3f0b1ba775973b1547e6e9d8262ec551f9b9da698bb1547e6e9cc5d8aa3f1c5ba731762a8fc786e5dd66308551f9ba78a98bb1547e60074e62b8551f97a731762a8fc1e6d369262ec551f9bdbea98bb1547e6e9e1a62ec551f9b857598bb1547e6
  | 5, 0, 10 => 0xd35d662e4551f9ba6ec55258fc666e9d2662ec551f9ba731762a9187e6d34c5d8ca621f9b97a6babb1546a6e9cc630ec551f9b4d7c98bb1547e6d35d5d8aa4b1a9ba73186bb1547e6bacc5d8aa3f141ba731903b1547e6e9cc5d8b6551f9ba7a6a13b1547e6c7cc5d8ce551f9b4d4f98bb1546a6
  | 5, 0, 11 => 0xe9cc5d8aa3f061ba73176395547e6e9cc5d8aa3f099b4d7898bb1547e6e9cc5d8aa3f13dba731893b1547e6e9ec662ec551f9ba7318e3b1547e6e9cc5d8aa3f015ba79398bb1547e6e9e99d8c2551f9ba6ec6a309547e6e9f2dd8aa3f199ba74298bb1547e6d35d584b8551f9ba75d98bb1546a6
  | 5, 0, 12 => 0xe9ce262ec551f9ba77598bb154796e9cc658ec551f9ba73176309547e6d35ae62ec551f9801d398bb1547e5f469a62ec551f9b577598bb1547e6e9cc5d8aa3f1edba7b998bb1547e6e9cc644ec551f9b4d7598bb1387e6d35d662ec589f9ba73a98bb1547e6d364a62aa469f9ba731762a8fc0c6
  | 5, 0, 13 => 0xd35d696ec551f9ba731762a9487e6e0e4a62ec551f9b4d75a13b1547e60074e62ec499f97a731762a8fc5e6d35da62ec551f9a630681bb1547e6e9cc5d8aa3f1b5b4d75762a8fc396e9f2262ec551f9ba731762a8fc006e9d1a62ec551f9aeb56aa3b1547e6e9cf662ec551f9ba731883b1547e6
  | 5, 0, 14 => 0xd35d662ec551c9ba731762a8fc106e9dd6a4ec551f9bc5d398bb1547e6e9d7662ec6a1f9ba731773b1547e6e9eda62ec551f9a630c84bb1547e6e9cc5d8aa441f9ba731762a8fc776d34c634ec551f9b4d75aecc5707e6e9e9a62ec651f9b4d75762a8fc696d360662ec551f9bc18398bb1547e6
  | 5, 0, 15 => 0xe9cc5d8aa3f10d801d398aa8fc2e50074e5cec551f97a7318abb1547e6e1e5e62ec551f9b699f98bb1547e6d35ee62ec551f9ba73176379547e6f574e62ec551f9ba731762a8fc626dadd662ec551f9b637598bb1547e6e9e8262ec551f9ba731762a8fc1b6e9cc5d8aa3f055b4d7576309547e6
  | 5, 1, 0 => 0xe9cc5d8e6551f9b4d759cbb1547e6d35d662aa481f9ba75498bb1547e6e9cc60aaa3f1b9ba731762a9027e6e9cc5d8b5551f9ba731762a8fc086e9d6262ec551f9ba78d98bb1547e6e9dd662da551f9801d3762a8fc235e9e2e62ec551f9801d398bb0fc3e5e9cc5d8aa3f1adbd5d398c31547e6
  | 5, 1, 1 => 0xf574e62aa469f9b4d7598b296e7e6e9cc5d8d2551f9bc1d398bb1547e6d8dd662aa469f9ba731762a8fc2d6f774e62ec551f9ba731762a8fc576e65d662ec551f9ba73176365547e6e9dba62ec551f9b4d75a13b11a7e6d35d662ec651f9ba73176355547e6e55d662ec551f9ba731762a8fc556
  | 5, 1, 2 => 0xebf4e62ec551f9ba731762a8fc2a60068a62ec551f97797598bb1547e6f574e5cec551f9ba77d98bb1547e6e9d2262ec551f9ba7cb98bb1547e6e9cc63cec551f9ba78498bb1547e6e9cc5d8aa3f01dba731762a94e7e6d365662ec551f9ba75998bb1547e6d45d662ec551f9ba731762a92c7e6
  | 5, 1, 3 => 0xd7dd662ec551f9b5b7598bb1547e6e9cc5d8aa3f1d1801d3761f87c235f374e62ec551f9ba79498bb1547e6d34c5d8d1551f9a62ec6a345547e6e9cc612ec551f9b4d75a53b1947e6f674e62ec551f9801d3551f85c2350074e627e1f0b9401d398bb154795e9cc5d8aa3f0d9ba731762a8fc026
  | 5, 1, 4 => 0xe9e4262ec551f9b4d52762a8fc6e6d34c5d8aa3f0edba75d98bb1547e6004c5d8aa2682574d31762a90a7e6d34c596b8551f9b4d7198bb1547e6e9ca9d8d8551f9b897598bb1547e6e9cc5d8ca551f9b4d31762ed547e6e9e99fcec551f9ba73181bb1547e6db61a62ec551f9b4d4f98bb1547e6
  | 5, 1, 5 => 0xf5f4e62ec551f9ba731762a9287e6d35d662ec591f9ba73195bb1547e6d35d66304551f9bd5d398bb154796e9cc5fcec551f9ba731762a8fc526e9cc5d8aa3f0bdaeb31762a8fc536e9e9a6308551f9b717598bb1547e6d35d646ec551f9b8da698bb1547e6e9cce62ec551f9ba742762a8fc5c6
  | 5, 1, 6 => 0xe9cc5d8e9551f9ba73183bb1547e6c34c5d8e0551f9b4d757f3b1547e6bad7a62ec551f9a62ec72aa8fc776da5d66305551f9ba79298bb1547e6d35d662ec5e2a9ba75da53b1547e60074e62da551f974d757a3b1547e6e9cc5d8b0551f9ba7317635d547e6d35d662f3551f9bb9d398bb1547e6
  | 5, 1, 7 => 0xf44c5d8d8551f9bd53176395547e6e9cc5d8aa4d9f9b8f7598bb1547e6e9d3a62ec551f9ba731762a8fc376d35d5fcec499f9b4d7598bc5547e6e9cc5d8aa3f069b4d75a9bb1547e6d34c63eec551f9ba7a698bb1546a6e9cc5d8aa3f111ba7c398bb1547e60074eb6ec551f97a731762a8fc6f6
  | 5, 1, 8 => 0xd35d5d8b9551f9ba76f98bb1547e6e9cc5d8dc551f9ba731762a8fc6e60063e62ec551f97a731762a9407e6e9cc5d8aa3f095ba76798bb1547e6e9d59d8aa4f1f9ba75d98bb11a7e6e9e9a6305551f9b4d7598bb0fc456e9cc5d8aa3f181ba731762a8fc096e9d1e62ec551f9b4d7598c21547e6
  | 5, 1, 9 => 0xde5d6a4ec551f9b4d9898bb1547e6d157662ec551f9ba7a698c2d547e6e9cc5d8aa3f0d5b4d8898bb1547e6e9cc5d8aa3f161bdbd3aebb1547e6d35d676ec551f9ba7317c3b1547e60056262ec551f97d1d398bb1547e6e75d662ec551f9ba7a698bb14a7e6e9cc5d8aa3f091bc531762a8fc776
  | 5, 1, 10 => 0xe9c31fcec551f9ba7a798bb1547e6e9cc5d8aa3f075b4d7576361947e6e9cc5d8aa3f0adba73176305547e6e9cc5d8aa3f199ba7317639d547e6e9cc5d8aa451f9ba75698bb1547e6f8f4e62ec551f9b4d7f98bb1547e6d35d662ec551a9801e098bb1547e5e0dd6baec551f9bd5e298bb1547e6
  | 5, 1, 11 => 0xd35d6630b551f9ba74a762a8fc666bac19fcec551f9b4d4f98b69547e6d35d662f5551f9b8d31863b1547e6d35d694ec551a9b4d7598bb14a7e6f2f4e62ec551f9ba731762a92e7e6e9cc610ec551f98013184bb1547e5e9db662ec551f9ba731762a8cc5c6e9d8a62ec551f9ba731762a8fc286
  | 5, 1, 12 => 0xd35d662ec469a9ba77798bb1547e6f7f4e62ec551f9b4d75aeb611a7e6d0dd662ec551f9aeb3184419547e6dd5d662ec551f9ba75d98b69547e6e9eaa62ec551f9ba731762a8fc4d6e9cc5d8aa3f0cdb79318f3b1547e6e9cc5d8aa3f185b4d759bbb1547e6e9d8e62ec551f9ba7316a2e1547e6
  | 5, 1, 13 => 0xd35d662ec489f9ba731762a8fc0f6e2dd6acec551f9b4d7598bb174aa60074e84ec551f97a731762a8fc306e9cc5548d3f185ba73176345547e6e9daa62ec551f9ba731762a94a7e6e9cc5d8aa3f16db697598bb1547e6e9cc5d8aa3f109a62ec6732d547e6eaf4e62ec551f9ba75d76361547e6
  | 5, 1, 14 => 0xe9cc5d8aa3f011ba73198bb1547e6ef74e62ec551f9801d376309547e5e9cc616ec551f9abb5898bb1547e6e9cc5d8aa3f1a9ba74498bb1547e6004c5d8aa3f0257a731762a92a7e6e9cc5d8d4551f9ba731762a8fc206e9cc64cec551f9bdbd3762a8fc666d35d662b8551f9b8ba6bacc5267e6
  | 5, 1, 15 => 0xd35d662da551a980131551f85c095e9cc5d8aa3f175b4d7598bb1327e6d35d662ec551f9ba731762a9167e6e9f1662ec551f9801d398bb1947e5e9d2a62ec551f9ba731762a9467e6e9eee62ec551f9ba731762a8fc196d95d662ec551f9ba731762a8fc4e6007a262ec551f974d757fbb154666
  | 5, 2, 0 => 0xbacc5d8aa411f9ba731762a8fc036e9cc5d8c3551f9b4d7576361546a6e9cc5d8aa3f0d1ba731973b1547e6d35d662ec499f9ba731762a8fc066e9cc5d8b8551f9800ec551f846095d35d662b7551f980131761f87c095e9cc5d8cb551f9b1931762a8fc736e9f16630c551f9ba7318b3b1547e6
  | 5, 2, 1 => 0xd35d662ec551b1b4d75973b1547e6e9cc5d8aa551f9ba78598bb1547e6d35d6a2ec551f9ba7c598aa91a7e6e9cc5eeec551f9b4d7576329847e6d35d632ec551f9b4d7598b6d547e6e9cc5d8aa3f0fdba6ec6c2a8fc666e9cc5d8e3551f9bcfd398bb1547e6e9cc5d8aa4c1f9ba731762a8fc236
  | 5, 2, 2 => 0xe9cc618ec499f9bc9d398bb1547e6e9d9262ec551f9ba731762a8fc466e9e9aa4ec551f9ba731762a8fc1f6004c5d8d1551f97a7318ebb1547e6e9cc618ec551f9ba731762a8fc596e9cc5d8ac551f9ba731763b1547e6e9cc5d8a3469f9ba731762a9267e6e9cc5d8aa3f049bdbd398bb1547e6
  | 5, 2, 3 => 0x3a731762a91a7e6d35d67cec551f9ba731762a8fc7e6d35d662ec551e5a632a762a9467e6e9cc5d8aa3f0f9ba731762a90e7e60074e62ec551357a731762a8fc0a6e9cc5d8aa3f089801d37f3b1547e5e9cc5d8aa3f131b4d7598bb154846
  | 6, 0, 0 => 0x69aeb52762a8fcdc5bacc5d8e0551f9fa7a698bb1549b3f3e9a62ec6eaa8fc6e7d34c5d8d465aa8fcfa6bad09d8aa3f171f4d90bacc5d8aa3f3e9aeb5d98bb1547e7da5d662ec551f8dcfa6bacc5d8ca551f9c01d398bb1547e173003a731762a8fc5c6d35d66303762a8fce00bacc5d8ce551f9b977598bb1547e39be9b3f75aebb1547e7
  | 6, 0, 1 => 0xd35d662ec582a8fcfd3d34c5d8aa3f1b9f4d7598ca1d8aa3f3e9aeb31762a9287e700699d8aa3f08c30c00d34c5d87e1f061ba7a6b3cc5d8aa3f3e9b3d7598bb1547e7e5f16eb31762a8fce00d34c5547e17061b4d7598bf9d8aa3f3803a73176375547e6e9e9a62ec551f812fa6bacc5d8aa3f149c01d398bb1b0aa3f30034d31762a8fc106
  | 6, 0, 2 => 0xe1e9aeb31762a8fcfa6bacc5d8aa3f1d5f4d7598bb1547e37bf4eeb318c3b1547e7d35d662f0762a8fcfa6bacc5d8d6551f9f4d7598c1dd8aa3f3e9aeb31762bd547e7d360e62ec551f8c2fd3bacc654ec551f9f4d92bacc5d8aa3f3e9aeb31842a8fc737d35d6bb4a762a8fce00e9f4e62ec551f9801a6bacc5b4aa3f369b357598bb1547e7
  | 6, 0, 3 => 0xd35d662ec55280fcfd3bacc5d8aa3f061fa77598bb1caaa3f3e9aeb31762a8fc257d35d6cf31762a8fcfa6bad59d8aa4f1f9f4d7598bb1547e1d3e9aeb5d98bb11a7e7e9e9a62ec551f8ccfa6badd262ec551f9f4d7598bb1547e04be9aeb31762a9367e7d35d69d31762a8fcfa6bacc5d8aa3f0ddf4d7598bb1547e0d3e9aeb31762a8fc447
  | 6, 0, 4 => 0xe9edaeb31762a8fcfd3bacc5d8aa3f1ddfa7a698bb1547e26be9aeb31762a8fc147d35d662ec551f880fa6cfdd5d8aa3f199fa7a698bb1547e30be9aeb31762a8fc357d35d66313762a8fce00d34c606ec551f9b4d7598bb1547e2c3e9aeb317c3b1547e70074eeb31762a8fcda6badbe62ec551f9f4d7598bb1b8aa3f3e9aeb31762a8fc6e7
  | 6, 0, 5 => 0xd35d6e531762a8fcfb4d35d662ec551f9f4d75b14c5d8aa3f3e9aeb31762a8fc287d35d618fe762a8fcfa7d35d662ec551f9f4d7598bb1547e0ebe9aeb31762a8fc2b7d35d662ec60aa8fcfa6bacc5d8aa3f199c01a6cf4c5d8aa3f369aeb31762a8fc517d35d662ec55228fcfe2e9dd662ec551f9f4d75ab4c5d8aa3f3fc74d7598bb1547e7
  | 6, 0, 6 => 0xd35d694ec551f8ccfd3c6dd662ec551f9c01d3babb1547e11b003a77598bb0fc3e60074e632a762a8fcc00d364a62ec551f9b4d7598bb154973f3e9aeb31843b1547e7e9e9a62ec55278fcfa6bacc5d8cf551f9c01d3bacc5547e17374f4d31923b1547e7d35d662ec551f822fa6badb662ec551f9f4d7598bb154662e3faba77598bb1547e7
  | 6, 0, 7 => 0x69a62ec551f812dd3badba62ec551f9f4d75aecc5b4aa3f3e9aeb5598bb1547e7bacc648ec55278fcfd3d367e62ec551f9f55a6bacc5d8aa3f3e9aeb31762a8fc4d7e9e9b4d31762a8fcfd3d34c5d8d4551f9f4d7598bb1547e19b803a7318c3b1547e6d35d662ec551f8c2fa6badc262ec551f9f4d75b1cc5d8aa3f3e9aeb316a2e1547e7
  | 6, 0, 8 => 0xd35d662aa469f8c2faed35d662ec551f9f4d97c3cc5d8aa3f3e9aeb6a98bb1547e7d35d66324762a8fcfd3d34c5d8aa3f1cdc0000e9cc5d8aa3f2e9aeb31762a8fc4270074e62ec551f830c00e9cc5d8e5551f9b4d75aebb1b0aa3f3e9aeb31762a9067e7d35deeb31762a8fcfd3bacc5d8aa4b1f9fa77598bb1c0aa3f3e9b1931762a93c7e7
  | 6, 0, 9 => 0xd367eeb31762a8fce00e9eda62ec551f9b4da6bacc5d8aa3f3e9aeb3176351547e7d35d662ec551f840e00e9cc5d8aa3f1ddba7c5d34c5d8aa3f3e9aeb31933b1547e7e9e9a9531762a8fcfd3d34c5d8aa519f9f4d7598bb1547e07be9aeb4f98bb1547e70069aeb42762a8fcdcdd35d662ec551f9f4d7598bb1547e183f9ba77598bb1547e7
  | 6, 0, 10 => 0xe2dd662ec55278fcfd3d365e62ec551f9c0000e9cc5547e172f4f4d31762a8fc237d35d662ec551f8e0fa6bacc662ec551f9c01eae9cc5d8aa3f3003637598bb1547e60069f4d31762a8fcc00d35d5d8c2551f9b4d7598bb1547e353e9aeb4498bb1547e70078ba731762a8fcda6bacc5d8aa3f17dfa775aecc5d8aa3f3dd662ec55278fc737
  | 6, 0, 11 => 0xf6f4f4d31762a8fcfa6bacc5d8aa459f9f8ba6bacc5d8aa3f3803a76e98bb1547e60069aeb3176328fcda6bad2a62ec551f9f4d7598bb154a33f3eef4d7598bb1547e7d35d662ec551f832fc3bacc5d8dd551f9f4d759a4c5d8aa3f3803a78d98bb1547e6d35d662ec551f8c6e000074dd8aa3f08d40000e9cc5d87e1f2f26eb318f3b1547e7
  | 6, 0, 12 => 0xd35d662ec70aa8fcfa6bacc5d8aa3f08dc017598bb1544d08b69aeb3176335547e7d35d662ec61aa8fcfa6bacc5d8aa3f0d1c01bcbacc5d8aa3f369aeb31762e1547e70074f9731762a8fcc00e9cc63cec551f9801a6cacc5d8aa3f369aeb317632d547e70074e62ec55258fcdc5d35d6630c551f9f4d31762a8fc11083e9aeb31762a8fc5d7
  | 6, 0, 13 => 0xd3626eb31762a8fce00e9d7662ec551f9ba7a698bb1547e1f3e9aeb31762a9547e70074f4d31762a89ada6c2dd662ec551f9f8ba6bacc5548d3f3e9aeb317bbb1547e70069a9f31762a8fcc00f374e62ec551f9b4d7598bb1547e09bf4f4d31863b1547e7d9e9aeb31762a8fcfa6babb1b0aa3f199f4d7598bb1c6aa3f3e9aeb31762a9307e7
  | 6, 0, 14 => 0xd35d662ec551f83efa6bacc63aec551f9fa77598bb1547e08be9aeb31863b1547e7d35d662ec551f8b2fa6bacc5d8aa4e9f9f4d7598bb1d8aa3f3f4f4d31762a8fc2e7e9e9a62ec551f8b8fa6bacc628ec551f9fa1a6bacc5d8aa3f3e9aeb31762a9267e7e9e9a62ec55234fcfbdd35d662ec551f9f4d7598bb1547e093fb74d7598bb1547e7
  | 6, 0, 15 => 0x69aeb31842a8fcda6bacc5d8aa3f1f9c01d398bb1549b3f374fa7a698bb1547e7d35d662ec551f87cfa6bacc5d8aa439f9f4d7598bb1547e073e9b077598bb1547e70069aeb31762a89ada6bacc5d8aa3f029c01a6babf9d8aa3f369aeb3192bb1547e7d35d6630c7624cfcfd3d34c5d8d8551f9f61a6bacc5d8aa3f3e9aeb31762a8fc467
  | 6, 1, 0 => 0xd35d662ec5527cfcfa6bacc5d8aa3f09dc01d398bb1547e37369aeb4398bb1547e7d35d68b31762a8fcfa6bacc61eec551f9c0131762a8fc180bb69aeb31762a8fc2e7d35d662ec551f8b8e00e9d9e62ec551f9b4d7598bb1547e05be9aeb31762a9127e7d35d6630e762a8fcfa6bacc5d8aa469f9f4d87bacc5d8aa3f3803a731762a8fc096
  | 6, 1, 1 => 0xe9e7eeb31762a8fcfd3d35d662ec551f9f4d7598bb1547e2d38034d7598bb1546a6d3666eb31762a8fce00d35d5d8aa2688d801a6bacc5d84d1f30034d7598aa89a2e6d35d662ec551f896fa6bacc5d8aa3f059f4d7598c45d8aa3f3e9aeb3176375547e7d35d662ec5faa8fcfa6bacc5d8d8551f9fa77598c91d8aa3f3e9aeb31762a8fc4a7
  | 6, 1, 2 => 0xe0dd662ec6c2a8fce00e9cc5d8aa3f185b4d7598bf1d8aa3f3e9aeb317fbb1547e7d35d66302762a8fcfa6c65d662ec551f9f4d7598bb11a7e2e3dd6630c833b1547e7d35d662ec551f852fa6bacc5b0aa469f9f9fa6bacc5d8aa3f3e9aeb5d762a92c7e7d669aeb31762a8fce00e9cc5d8aa3f199b4d5da7cc5d8aa3f3e9aeb31762a8fc1c7
  | 6, 1, 3 => 0xe9ef6eb31762a8fcfa6bacc654ec551f9c000098bb1547e04ae9aeb6098bb1547e70074e62ec6a2a8fcc00d35d662b8551f9b4d7598bb1547e0f3e9aeb3176328fc667d35d662f2762a8fce00bacc5d8aa3f045b4d9dbacc5d8aa3f3e9aeb3176369547e7006d2eb31762a8fcda6bacc5d8aa4d1f9f4d75b0cc5d8aa3f3803a731762a8fc4d6
  | 6, 1, 4 => 0x69aeb31762a8fcc00e9f1662ec551f9b4d759d4c5d8aa3f3803a74a98bb1547e60074e62ec5528cfcda6bacc5d8e5551f9f4d7598bb1547e133e9aeb318e3b1547e7d35d5d8d4612a8fcfa6bad0a62ec551f9f4d75aecc5d8aa353f4f6da698bb1547e7d35d5d8aa4b1f8ccfa6bacc630ec551f9f4d7598c35d8aa3f3e9aeb31762d9547e7
  | 6, 1, 5 => 0xd35d662ec551f836fa6bacc5d8aa3f041fc5a6bacc5d8aa3f3f4f4d3176381547e7d35d6bb3176350fcfa6bacc5d8aa441f9f4d7598bb1547e3bb803a731762a8fc2360069aeb317624cfcc0098bb1547e0c045b4d7598bb1547e36be9aeb31762a8fc007d35d68d31762a8fcfa6bacf662ec551f9f4d759c4c5d8aa3f3e9aeb3176309547e7
  | 6, 1, 6 => 0xd35d662ec551f8aefa6bacc5d8d9551f9f4d75b74c5d8aa3f3e9aeb31762a8fc557d35d662ec5aaa8fce00d35d5d8aa3f08db4d8bbacc5d8aa3f38034d7598bb0fc3e6d35d662ec551f8d6fb6bacc5d8aa3f1cdc01ede9cc5d8aa3f369aeb31762a8fc4370069aeb31551f85cda6bacc5d8de551f9fd5a6bacc5d8aa3f3e9aeb31762a8fc627
  | 6, 1, 7 => 0x74e62ec55234fcc00d35d5d87e1f08dbcda6bacc5d8aa3f3e9b297598bb1547e70069aeaaa3f0b846c00d35d6627e1f0b9801d398bb1547e1f369aeb31762a8fc36700003a731762a89aba6bacc5d8aa3f0a9f4d7598bb154963f3803a731863b1547e6
  | 7, 0, 0 => 0x69aeb31762a8fc237007174d7598bb1547e70069aeb4a98bb1547e70069b3f7598bb1547e70069aeb3176351547e70069aeb31923b1547e70000001d398bb1547e50069aeb31762a8fc4d70069aeb31762a8fc6170069aeb31762a8fc1170069aeb31762a8fc66700003a77598bb1547e60069aeb31762a8fc6e70069aeb6798bb1547e70069aeb31762a9367e70069aeb5d98bb1547e7
  | 7, 0, 1 => 0x34d7598bb0fc3e6000034d7598aa8fc2e6000034d7598bb1547e60069aeb318c3b1547e700002eb31762a8fc1160074f4d7598bb1547e70069aeb3176375547e70069aeb3176361547e70069aeb31762a8fc2e70069aeb31762a8fc5c70069aeb31762a91a7e70069b0f7598bb1547e70069aeb31762a8fc3e7000034d7598bb1544d60069aeb31863b1547e7006f74d7598bb1547e7
  | 7, 0, 2 => 0x69aeb31762a92c7e70069aeb6e98bb1547e7000034d75762a8fc236
  | 8, 0, 0 => 0x34d7598bb1547e6
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
private theorem z2_0 : span (Z 2) 3 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 3 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 20 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 20 0 = true := z3_0

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
private theorem z4_192 : span (Z 4) 17 192 = true := by decide +kernel

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

private theorem z4_a8 : span (Z 4) 209 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 17) z4_a7 z4_192

private theorem z4 : span (Z 4) 209 0 = true := z4_a8

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
private theorem z5_552 : span (Z 5) 21 552 = true := by decide +kernel

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

private theorem z5_a23 : span (Z 5) 573 0 = true :=
  span_join (f := Z 5) (a := 552) (o := 0) (b := 21) z5_a22 z5_552

private theorem z5 : span (Z 5) 573 0 = true := z5_a23

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
private theorem z6_360 : span (Z 6) 20 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 380 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 20) z6_a14 z6_360

private theorem z6 : span (Z 6) 380 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12413

theorem PEqualNP.Outside.L_meta_12413 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939035848 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939035848 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12413.mainG PEqualNP.Outside.L_meta_12413.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12413.CG, PEqualNP.Outside.L_meta_12413.CG_mono, by
      have : PEqualNP.Outside.L_meta_12413.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12413.CG_eval⟩
