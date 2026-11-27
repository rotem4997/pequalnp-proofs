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
namespace PEqualNP.Outside.L_meta_12491

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 17, 7, 19, 7, 21, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 7, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 7, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 9, 9, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 17, 9, 19, 9, 21, 22, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 35, 9, 37, 9, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 9, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 11, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 17, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 11, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 11, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 13, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 17, 13, 19, 13, 21, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 13, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 13, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 17, 14, 19, 14, 21, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 14, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 17, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 15, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 17, 17, 17, 17, 17, 17, 17, 7, 17, 9, 17, 11, 17, 13, 14, 15, 17, 17, 17, 19, 17, 21, 22, 23, 17, 25, 17, 27, 17, 29, 30, 31, 17, 17, 17, 35, 17, 37, 17, 39, 17, 41, 17, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 17, 59, 17, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 7, 19, 9, 19, 11, 19, 13, 14, 15, 19, 17, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 19, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 21, 7, 21, 9, 21, 11, 21, 13, 14, 15, 21, 17, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 21, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 22, 22, 7, 22, 9, 22, 11, 22, 13, 14, 15, 22, 17, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 22, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 22, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 17, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 23, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 17, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 25, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 17, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 27, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 17, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 29, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 17, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 30, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 17, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 31, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 35, 7, 35, 9, 35, 11, 35, 13, 14, 15, 35, 17, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 35, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 35, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 37, 37, 7, 37, 9, 37, 11, 37, 13, 14, 15, 37, 17, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 37, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 37, 59, 37, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 17, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 39, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 17, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 41, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 17, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 43, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 17, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 45, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 17, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 46, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 17, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 47, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 7, 49, 9, 49, 11, 49, 13, 14, 15, 49, 17, 49, 19, 49, 21, 22, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 35, 49, 37, 49, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 17, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 51, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 17, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 53, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 17, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 54, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 17, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 55, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 17, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 57, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 17, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 59, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 17, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 61, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 17, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 62, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f000000000000000000000000000000000000000000000000151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea80000000000000000000000000000000000000000000000000eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000eaeaeaa8eaeaea800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80eaeaeaa8eaeaea80

def cMZZ : Nat := 0x151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f000000000000000000000000000000000000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f000000000000000000000000000000000000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f000000000000000000000000000000000000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f000000000000000000000000000000000000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f000000000000000000000000000000000000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f0000000000000000151515571515157f151515571515157f151515571515157f151515571515157f151515571515157f151515571515157f151515571515157f

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
  | 3 => 29
  | 4 => 245
  | 5 => 614
  | 6 => 357
  | 7 => 29
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x729ffc286b37fe8916bdd4f4
  | 3, 0 => 0xd7ef566ed36569bbc412f3f5b9c7ccd6982eac068607df5c7c950c417988dc8f7328122f7225bf7b7166275c5c4c9307595ee2e05732007853163ffc4b78b033436bb54642479ed037d1e5453086d7082afee4822a8c482c23b7178a1fee41fe1fbfdf781b599a7c198428510345cdc3015cc5e9
  | 4, 0 => 0x20e85e8f20e42d1b1fbbf3561edca9151ed75bdf1e358df21e27a4821de25cfc1dc629971d20d6a81cbcd99a1c5fcc431c4d50ff1c2bb1751c15d2241bdbd6a21b907ff21abb10e518dc9fee18844ba71814e74c17c8f33f17859c1c1752ce6a16e4286516b3c989162a945715ead556150ebf9d14ab315214a2db7b13e7dd6d13b9482d0e4db1a70df6ca5c0cfdbf980c3cbc410bd34d440b35e1690b0824590b0226970a338eb50973f69609530d17092cda7b08f8d427089d9e630708ae62067a681e06043f1305dbfcef05da97d904d518ad0483791d04780cd60424ab0a03cebbfc03c8beb4020bb61001e9753d01e4d82101e398ca0193e5c201369da7
  | 4, 1 => 0x54cb49095396a79e534635b352ea9cc252a346a751e41a314fe522b84fa632d84e0220134df7b89f4c32d7e64c23a2fd4be6e3d94b5711884b39c87948bac59148a53bd14572affa4403d838422fa36a3fe6f1683fd50a793fab98733ebac5ac3e1d9d873c29fcef3bee06803b1c42493adb3f053a4fb76e3a42b0c93a23c82e39d7d421385c0bf63859fb4c36da216a36981079367a623a35c19c1d355984fe30f5e0b02f117d032eb5e8082e8676672dfcdc252d767ce02d4ee83f2cd937322c2da9f82c2ac3762c1411902ba7655828d9c9b42884fb7527a413a8278743ab275285d5274c4dbc27289a2f252a8bef22cea641228218f52201af15217e7c24
  | 4, 2 => 0x87cf5d9a87c8ae338794b85086f7897d85ce5fb384a84f64848a76a781fd310e81e69d5681c7dcda818f80ac808cdd7b8039923c7f80a41e7ef9b5f37a94a06879cea04877f3ef80764a99d2738ca0a371da1336717fee047166275c71247fb270dd55ed6ffd25a86fee68c26e7764716e2a82846ca1d0536c8b5acf6c28d0eb6bdcdcde6b975ef26b7338f56ab6a98269983e3f690ee90a68b8b404688e58d9687d94ff67669b7565a701836555456b654159d764b2565f62e776d662e5b60062bb7dac5ffb02ca5fc8a3095df1a4695d7544d95d6095235c9b327c5c512f2f5c20c32f5bc45cf259fcdd6359c1aaa758419dda5771acef5682e3d9563a27eb
  | 4, 3 => 0xfbaf7224f45a623ceffca653eea6a70ce71889f3e03f7961dbcf0132da556e05d0476a6ecfb1cf1fcb1da505c83a85abc72c1469c5d76546c516a6a4c429efcac3ae5ad2c16b56cfbf4ecd63bf21fc76bcf9f499bab92e5eb99b9270b48384b9b3c8558eb21ae012b08bd040af4eaadcac6f3f14ac448922aa571f44a9d3ce11a7ee823ca702e20ca619f777a3fa9730a2b00092a1b256eaa02f8b41a00da8039d213f8b9c87e05099407a799888b6e194e0fd7294d30d9390db94678f58b1d78df5a3d48d8b3e628b80de768b1aaba18a7fb678
  | 5, 0 => 0xd1e8ddb0d0531970ce8ecd10c8c77450c7ae0880bba0a210bb886770ba706550b60ac090b0226970abc7ae70a3cfbe70a3350cb09d71d8909b6aef00973f696096315d40935c15508f92ae308cd3d5b08695550080df7f207dc1d8407c1515407a1cd540768d8be073460bc068beced067b87c5067a681e0643b68e05fe7a6705f1316b05ae28fb058c95f805624d9f0518da850506f3960505fbed04dd819004b4d8bd04a2f1ce047aa2570479a65c03d6f15f03d0cacf0372d51f03385b6b030a3f1e03025dba02c66c4a029944ed0222663f020bb6100208399b01d23667015be60c00fdbd6800a3b5f0007378fe006ece8a004e2b66001c754e000e582b
  | 5, 1 => 0x1c4d50ff1c1957081c08f5891c046bcc1bdbd6a21bc7e2581bb4ccf61ba59db91ba06a041a88c6a619f99ab919eb2d3c19a6782019648b7918c890bb183980271716034e17150ba516e4286516ce2bb616bd760a16b2018616335e0a15f90beb15bfdf19159ae1ec15789e9f1571bcd7151fed4f14bbeb871473b62f145396b91412cc63140f40f013ac51b41324be4712fc994412e30c9a129470ed128c2c0a127dc6a71269956f120dac54116c5a8d116608ac11558c1a114d8abf111b14ba1118ccf61100bf3b10b4cb2e1088faa50fe1093e0edcaef50ed09f2a0e6233f30e0a33060ddf284f0dafc0840da2f8a80d98216a0d69335f0d664e360d2ea3e1
  | 5, 2 => 0x2ad8eaa02abf4c112a7393c92a7342f42a63ead22a2949d029e43f7c29590ed9292e4f0c28ef23e82852977028195ff327bca761274e36f126ed843326d12b1d2604425625a42200255846a4252cebe724f5036d249101a524705a1723c94fa02387c234237b6a4523238d86231a41dd22dedda522d201ae22bd9e16222b563021fe32a021cd1b9921c82f6c2183184c21492b0320f6460f209f8a3e207859eb204b6c8b1ff79c6e1fa2878a1f9099071f31df4c1f2ec6801f066dc71f00db3f1ef7fc891ef393c41ee437f81e92efb81e8de9011e74598e1e27a4821e1663de1de25cfc1ddd63b61dcb9efe1dc629971d7ce77a1d7386f71d363f3c1ca3960c
  | 5, 3 => 0x3f0089653ecccf863ea5d01b3e5e97ad3af43cfa3ad51b0d3a7d7cab3a61a72839f52a7b39e126413951262938dd0c9838be89c038aa7ff438a340ac385c0bf6379b454f378a4279370bfc53370bbb8d370b04aa36b8409e36ad2e4036981079365668cf36492c783622ce7d360f3f0a353e17f3352f0ec5352051df346c1c00343a65e834081a3833ee3cba33b484c53306c58631d1c7d031009c7230b9de2930b2de053077a9a32fe8929f2fa7024c2f2f68f22f2d6ebd2f0f38b22ef25d402eefbd3f2ec117932e89239d2dea9d212dc041f62daf7e1c2d005e512cc4376b2c9884922c3ae8542c12aeb32ba765582b8a0e932b7c3d6c2b6ef4352b1079bd
  | 5, 4 => 0x51a961aa505add985057fcb84f79e3cd4e5f9dd64e22cc734db37f014d0146b74cc6a16d4c32d7e64be6e3d94be0cd0d4bd0e4404b5711884b52e1894b3105004b0048d04aec1c504ab98fac4a7d7e764a123b8849da38814924481148a0b3034831de3547cd6ef047c33d1f47b2a066473f9d09471e68614718867346b238e646a344774614f1f84614559945c6a50645bec698456b7b5944e02ad144c2c2ab445760d243afc8bb43902c6f4371634a43580be542c8a9ae42b30f774264ee7e4223ff3041b6120441a290424140c02e413c7e75401b93e53ffc51763ffa5e313fe6f1683fd7fabb3fd50a793fc689853fc4f58b3f73f8f33f3b7c083f1aa269
  | 5, 5 => 0x6736bc9266e4400765a7b2cf6561745e651f9f7b64b2565f644e3f806264902b62271d4d61b9c96d61b856bd61ac0b0961a8fa3b6132777a6049ee9a5fcdf3c05fc28eb95f39e3a35efccad15ec2c88b5eaddd4f5e9bc9205dba9ffe5ca34fb95c986d2e5c512f2f5c46dce85ba938b15b9fc7425b4ee5705ab628d65a7d3b535a57a02d5a12e68f59fb19ec59b3db9758b2542f58aedd065835fbff582365515784e2e7571bffe856f3734956b7611356aa386655671b9d5478070554305eed5422f9115419f99d540346f253e64c5853ca2bd7538148cb534fcfe653278cf1532282d252b4434e52a636e9524338545241e2e952262ef9520ad26951e41a31
  | 5, 6 => 0x7fb887be7ecd7b8d7e302c227dbb110a7cff97ca7ccd2d927cbea39d7ca13a837c36608c7bc0fea97a89c1c77a42b8117a31578a79f112f179dc27b579b56dd679a879977963470778a84d3478a4d60b78195e567789a1ed76c3e0a376aef332768e94e47683c6d87669874475bdb95d75bcc1b47594c5b3756ee387755d14a2749bbe58733ff8e472e6fad87269be7a720e5d5771da133671bc1fb071b1c8ed70b2295f70a5e8986f8908616f05b72e6ef7ff246d9d626e6d9bc4026cfc15676cd7c9266ccd94cf6c34cb296bc6dd456ba9079a6b73fcfc6ae215556a88c42e6a1836c5692c804d692b0fa068b8b40468b33f7c6876161c6859cbac6827d73a
  | 5, 7 => 0xa88600bea7256550a71ae4a2a571627ea46ec737a459dbfba3f5da33a355b08ea100ea4fa08ef056a02aee8e9fe434849f64cdf39ee37d4d9e71ea1e9c9fb1669c87e0509c2dcbd09c01c1e39b645f829a19854599d1679b99bf80ac9926cfda9888b6e197b3b4539754486e9634654b9579538b94e8742e94e3b83c9409882b93bd415e93211b96915c3da991582e058ff2a2398f89d0eb8f4fdc168f15c1fa8e91cb438d7e70378c5dfd868a69d1f78a488fc18a13837e89554fca88ab039d88347bda880a758d87f4764287ab5e1687301e5486a6f407869d3fec856c4c2d8485aa298478ce3283ce95488362594a831b4aca80af4356808f29908039923c
  | 5, 8 => 0xd5a05c50d48b6a3fd12cc800d0e4f996d01717d3d016465bcfe2b689cfb1cf1fcea5dfaece49e37bcbc48969cb744a3ecad04e54ca303c30ca2b3138ca1e5541c73d9f28c4a78583c4822b96c2a556bec23bab2ec13f341fc0e15b41c024eeb7bf616c82bf6074d9befd6ababcd43642bb5a5887bb195a45ba0f7e4ab98c4b59b80f4589b7b507adb7a741edb7589a76b7434025b5f0b020b5b49c93b48384b9b43980aab3d89029b39e4f27b3207718b2e3565cb288651bb2731bdeb14c4fe8b1449417b136cefbb0faed98b08bd040adf9922faddba695ac4a7310ac360ea1abce9064ab35df92ab102b20aac5268aaac1fd9eaa53a2cfaa1d9f9ba9d52a3b
  | 5, 9 => 0xfc3039f5fc235dfefbaa70fafa8b6e16fa000259f880b50ef6ea1b26f4232efdf39f193ef301feccf2bf60e4f1609ddaf0d94e70f00b10cdeff929deefc326aaef356b5bee0bb2cceb47b172ea144e46e99b6142e733982de69a79f7e478249be338fea3e1c9af60e15d9a8de147bb3ce123b83be0e3002ae0b0512ce03f7961dcca2f47dc3a40f0dc2d64f9db958189db39b4c9d5d1bde9
  | 6, 0 => 0x177521711773cc061716034e17150ba516db4ac716b2018616072cc0158cc6b5151fed4f14abccea14a03238111b14ba1102cd5d10d70d2c1088faa5101e056d0fba03a50f4424a50ed4e9140dd29c200d69335f0d63c7520cffc58a0ce489830c7186260b46db150ab5e2630a7945930a3cfbe70a3350cb0a1213ee09ece74f098949ef09283f1608f92ae308e1b1d808c2158c07fa92cb0796d79b0755e84d06e7fb2106d4795f0683f959066e6792060a65ca05ae28fb052c474e0506f39604f6dea804a6e54304a5e21004a2f1ce046d6525044c8b860442e37b03feb8a3039080ca02dcacc5024dbde70208399b01d2366701a1fdc50089309d0007042a
  | 6, 1 => 0x346c1c00343a65e832cf4b8b32cdad1f3209b24331ff7dec31fb1cbb31f31a6331009c7230f8c6623013fe722ea326c82de528992d8438032d68dcb02d59c0572d234c0c2c68a5af2b74609c29e43f7c2980289d28bc30352796794826ea3fda26ddf4262664609725919c1824f5036d24f477d6246bccc023f4b1a8237b6a45233f11c4229044f221d538d62080ce8d1faf24701f89894a1ecdf1361e0d3ebb1de43d4c1de0c6231dc629971dbf79181d5c41991d554e6e1cb6cc041c9251261c255c661c046bcc1b245a2b1a9904ba1a8fbb8a1a3502f219eb2d3c1962480a1954e22e1918357518fc14f418b9c4b018b331e81881b903181db73b17e62c6b
  | 6, 2 => 0x55f8e8fa557f5a84556937af55671b9d556038285481c5335447ab1753c3b460534fcfe652ff686651e41a3150d4bc9e5070bad64f0a4a8f4ddcecba4dbfbc6a4d6664f74d265f5f4c6207714c0b201c4bd8dd244bb6fbb34aec1c504a9e354a49df1b6849b7934649aab74f4946b5874831de3547d7e0a845c112ad458eb818456b7b5944ea70db44c19bf34443dddb4362153f41f08cba41b61204413c7e7540f2e7c64028f753400a40503fd7fabb3fd50a793fbbaae43eda62b43dda36513dd6bf283be0dc4f3aeeaad13a61a72839236ce23914cf4238b0cd7a3877b2083818e3f5379ba79737404674370bfc5336ad2e4035e4127c35d7d1b535cd2c17
  | 6, 3 => 0x866499868578ac418556d7d484925df68478ce32842f53d782061f5f808c41a4804b43627f4167677ce6f0ca7b22993d79b56dd6796b69c77693cad276767d347668b8187651bdb2761cb4e275bdb95d755f30b474acd6987448add7730d8fb271da1336710079817067c8af7042143d6f4f88b86f0713586eac842c6d5e5eb76c6b91446c4ccdbf6b4098c869a0b0546927c35068c74cf1688799ab66fe8ed866839fd665161da16496b7106415666a61c60d0a61b9c96d61b365a3615fb4ed6096489f5fc28eb95f4b6e625e823f165dba9ffe5d4d15cd5d2b8fb75c86318b5b664e685a31f9f75a1a5d4b5966283458ef2a7b58b2542f585304b358236551
  | 6, 4 => 0xc5a56216c4a653c7c4822b96c41585cdc3bc2643c1622312c155471bc1405bdfc13f6436c0dc5a17bf616c82bf31eb76befd6ababcd43642bb456d4bb955181ab7a741edb5af3086b4675478b3238374b29a1c4eb0799a8fafd8818caf336455aecd4a5faeb9d0c6ac32922cac0c4f07abfc8ef8abce9064ab35df92a9aa0db8a88600bea6fb987da655a158a64db694a638cb58a614e947a5d4c990a459dbfba1b7b839a16c2a0da15f4e16a0c76aa6a06b9de69de0b1409b645f829ad2456d9a1985459880786b965eb11d9647b6b79616e2b3954900f095149fa690a6335b905dc1b4900237718f503e5e89d96ea089b414b388dea0cc87d73fdb87687f8d
  | 6, 5 => 0xfc3cedc2fc235dfefbaa70faf5e4c71df0d94e70ee210d00ecee9079ec802009ec1f6d4bec031435e810c6bde803eac6e6fa1884e5298586e14b4020e0d2531cdf1d1654deb9148cdc46f4bddc3a40f0dbef5f22d7c65a05d7be1522d7afafbfd64cfdd2d512f256d4028842d2440eedcea5dfaece2b13fbccf33a6ccc9ac1d6cb759fa6cae01213ca1e5541c73d9f28c7041f7f
  | 7, 0 => 0xdf1d1654dc46f4bdd64cfdd2ce2b13fbc7041f7fc155471bc0dc5a17bf616c82a16c2a0d89b414b37067c8af6096489f5f4b6e62556937af51e41a3150d4bc9e49aab74f3914cf42370bfc5324f477d61de43d4c1881b9031716034e16b20186101e056d0d63c75206e7fb21066e679204a6e543
  | 8, 0 => 0x1716034e
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0000000f0000000aa000000aa000000aa000000000000005500000055000000330000003300000000ffffffff00000000ffffff0000000000ff00ff0000000000cccccccc00000000aaaaaaaa000000005555555500000000333333330000000000ff00ff000000000000ffff00000000000000ff0000000000000000
  | 0, 1 => 0xff0000ffff000000ff000000ff000000f000f000f000f000aa00aa00aa00aa0000ffffffffffff0000ffff0000ffff0000ffff0000ff000000ffff000000000000ff000000ff000000cccc0000cccc0000aaaa0000000000005555000055550000333300003333000000ffffffffff000000ff000000ff000000ff00000000
  | 0, 2 => 0xfff00000fff00000f0f0fff0f0f0fff0f0f0fff000000000f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f000f0f0f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ff00ff00ff00ff00ff00ff000000ff00ff00000000
  | 0, 3 => 0x50f050f050f050f05050f0f05050f0f0505050f0505050f050505050505050503f3f3f3f3f3f3f3f3f3f3f3f0000000033ff33ff33ff33ff33ff33ff0000000033333333ffffffff333333333333333333333333000000003333000033330000222222222222222211111111111111110fff0fff0fff0fff0fff0fff00000000
  | 0, 4 => 0xa000a000a000a0008888888888888888888888880000000080808080808080805f5f5f5f5f5f5f5f55ff55ff000000005555ffff5555ffff5555ffff00000000555555ff555555ff555555ff0000000055555555ffffffff5555555555555555555555550000000055555500555555005500ff005500ff005500550055005500
  | 0, 5 => 0xaaaaaaa0aaaaaaa0aaaaaa88aaaaaa88aaaaaa00aaaaaa00aaaaaa0000000000aaaaa0a0aaaaa0a0aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa00ff00aa00ff00aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a8a8a8a800000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a000a0a0a000
  | 0, 6 => 0xaaaaaaff00000000aaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88aaaaaaaaaaaaaa80aaaaaaaaaaaaaa00aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaa88888888aaaaaaaa88888800aaaaaaaa88880000aaaaaaaa88008800aaaaaaaa80808080aaaaaaaa00000000aaaaaaa8aaaaaaa8
  | 0, 7 => 0xcc00cc00cc00cc00cc000000cc000000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c0ccc0ccc0ccc0ccc0c0f0f0c0c0f0f0c0c0c0ccc0c0c0ccc0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c000c0c0c000c0c00000c0c00000bbbbbbbbbbbbbbbbafafafaf00000000aaffaaffaaffaaffaaaaffff00000000aaaaaaffaaaaaaff
  | 0, 8 => 0xcccccccccccccc00ccccccccccccc0c0cccccccccccc0000ccccccccccc0ccc0ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000ccccccc0ccccccc0cccccc88cccccc88cccccc00cccccc00cccccc0000000000cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8cc88cc88cc88cc88
  | 0, 9 => 0xeaaaeaaaeaaaeaaae8e8e8e8c0c0c0c0e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0e0a0e0e0e0a0ddddddddddddddddcfcccfcccfcccfccccffccffccffccffccccffffccccffffccccffff00000000ccccccffccccccffccccccff00000000cccccccccfcfcfcfccccccccccccccccccccccccccccccc0cccccccccccccc88
  | 0, 10 => 0xeeee0000eeee0000eecceecceecceecceecccccceecccccceeaaeeaa00000000ee00ee00ee00ee00ececececececececececececccccccccecececec00000000ecececccecececccececccccececcccceaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeaea00000000eaeaeaaaeaeaeaaaeaeaea00eaeaea00eaea0000eaea0000
  | 0, 11 => 0xf0f0c0c0f0f0c0c0f000f000f000f000f000f00000000000eeeeeeeeeeeeeeeeeeeeeeeeee00ee00eeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeecceeeeeecceeeeeecccccccccceeeeeeaaeeeeeeaaeeeeeeaa00000000eeeeee00eeeeee00eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaacccc0000
  | 0, 12 => 0xf0ff0000f0ff0000f0f0f0f5f0f0f0f5f0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f000f0f0f0f0f0f0c0c0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f0e0f0f0f0e0f0f0f0a0f0f0f0a0f0f0f000f0f0f000f0f0e0e0f0f0e0e0
  | 0, 13 => 0xfafaf0f0f0f0f0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faaafaaa00000000fa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f8f8f800000000f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f0f3f3f3f0f3f3f0f0f3f3f0f0f1f1f1f1f1f1f1f1f0fff0ff00000000
  | 0, 14 => 0xfcfcfcfcccccccccfcfcfcfcc0c0c0c0fcfcfcfc00000000fcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fafafafafafafafafafafafafafafa00fafafafaf0f0f0f0fafafafa00000000fafafaf0fafafaf0fafafaaaf0f0f000fafafa00fafafa00fafaf0f0fafaf0f0
  | 0, 15 => 0xff00ff00f000f000ff00ff0000000000ff00ee00ff00ee00ff00cc00ff00cc00ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefefe00fefefe00fefe0000fefe0000fcfcfcfcfcfcfcfcfcfcfcfcfcfcfc00fcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfcf0f0f0f0
  | 1, 0 => 0xffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ff88ff88ff88ff88ff88ff88ff00ff00ff88ff00ff88ff00ff80ff80ff80ff80ff55ff55ff55ff55ff55ff00ff55ff00ff33ff00ff33ff00ff0fff0fff0fff0fff00ffffff00ffffff00ffffff00ff00ff00ff00ffffffffff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000
  | 1, 1 => 0xfff0f0f0fff0f0f0fff00000fff00000ffeeffeeff00ff00ffeeff00ffeeff00ffeaff00ffeaff00ffccffccffccffccffccffccff00ff00ffccff00ffccff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaaaaaaff000000ffaaaaaa00000000
  | 1, 2 => 0xffff0000ff000000ffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff000000ff0000ffff000000000000fffeff00fffeff00fffcfffcfffcfffcfffcfffcff00ff00fffcfffc00000000fffafffafffafffafffafffa00000000fffaff00fffaff00fff0fff0fff0fff0fff0fff0f0f0f0f0fff0ff00fff0ff00
  | 1, 3 => 0xffffc000ffffc000ffffaaaaffffaaaaffffaaaaffffaa00ffffaaaaffff0000ffffaaaaff00aa00ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffa8a8ffff0000ffffa0a0ffff0000ffff0505ffff0505ffff00ffffff0000ffff00ff00000000ffff0000ffffffffffff0000ffff0000
  | 1, 4 => 0xfffffcfcfffffcfcfffffcfcffff0000fffffc00fffffc00fffffafaffff0000fffffafa00000000fffffa00fffffa00fffff0f0fffff0f0fffff0f0ffff0000fffff0f000000000fffff000ffff0000ffffeeeeffffeeeeffffee00ffffee00ffffccccffffccccffffccccccccccccffffcc00ffffcc00ffffc0c0ffffc0c0
  | 1, 5 => 0xffffff88ffffff00ffffff80ffffff80ffffff55ffffff55ffffff33ffffff33ffffff05ffffff05ffffff00ffffffffffffff00ffffff00ffffff00ffffee00ffffff00ffffaa00ffffff00ffff0000ffffff00ffccff00ffffff00ff00ff00ffffff00fafafa00ffffff00f0f0f000ffffff00aaaaaa00ffffff0000000000
  | 1, 6 => 0xfffffff0f0f0f0f0fffffff000000000ffffffeeffffffeeffffffeeffffff00ffffffee00000000ffffffccffffffccffffffc0ffffffc0ffffffaaffffffaaffffffaaffffff00ffffffaaffff0000ffffffaaff00ff00ffffffaaaaaaaaaaffffffaa00000000ffffffa8ffffff00ffffffa0ffffff00ffffff88ffffff88
  | 1, 7 => 0xffffffff0f0f0f00ffffffff0f000f00ffffffff05050505ffffffff03030303ffffffff00ff00ffffffffff00ff0000ffffffff0000ff00ffffffff00005555ffffffff000000ffffffffff00000055ffffffff00000000fffffffcfffffffcfffffffcffffff00fffffffc00000000fffffff0fffffff0fffffff0ffffff00
  | 1, 8 => 0xffffffffaaaaaaaaffffffffaaaaaa00ffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffffa0a0a000ffffffffa000a000ffffffff80808080ffffffff55555555ffffffff55555500ffffffff55550000ffffffff44444444ffffffff33333333ffffffff33003300ffffffff11111111
  | 1, 9 => 0xfffffffff000f000ffffffffeeeeeeeeffffffffeeeeee00ffffffffeeee0000ffffffffee00ee00ffffffffccccccccffffffffccccccc0ffffffffcccccc00ffffffffccccc0c0ffffffffcccc0000ffffffffccc0ccc0ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffc0c0c000ffffffffc0c00000
  | 1, 10 => 0xffffffffffcc0000ffffffffffc0ffc0ffffffffffaaffaaffffffffffaaff00ffffffffffaa0000ffffffffff55ff55ffffffffff00ff00ffffffffff00f000ffffffffff000000fffffffffcfcfcfcfffffffffcfcfc00fffffffffcfc0000fffffffffa00fa00fffffffff0f0f0f0fffffffff0f0f000fffffffff0f00000
  | 1, 11 => 0xffffffffffffffccffffffffffffffc0ffffffffffffffaaffffffffffffff55ffffffffffffff00ffffffffffffccccffffffffffffc0c0ffffffffffffaaaaffffffffffffaa00ffffffffffff5555ffffffffffff0000fffffffffffaff00fffffffffff0fff0fffffffffff0ff00ffffffffffccffccffffffffffccff00
  | 1, 12 => 0xfffffffffffffffffffffffffffffff0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1594f1b4ec478369d7d386d3
  | 3, 0, 0 => 0xacb25226d461248c25d4acb2d0c6a4acbb8f06d49b404f06d4984053c6d498438f86d4acb151e6d4acb2d246b4aca70da4d4b3b2d6e6d4acbc4f06d4acb2d1e6c4acb5cf06d4b132d246d4b032d246a4
  | 3, 0, 1 => 0xacc98f06d4acbccf06d4bad64f0604acb10f86d4acb95526d4acbd1486d4b9564f06d4acb15146d4acd38f06d4b9d64f06d4acbb4f06d4ac9e0da534afb2d746d4
  | 4, 0, 0 => 0xcc565969236ad65cccb491b572f5965a48dab596db2d246d5ddd65968636ad6596b2369856eb5967248dab8dacb2d646d5cd565968a36ad659692368656eb597a1e0dab59659f0da615bad65969336add6b2e0591b57534a65a48daba3a532d246d5
  | 4, 0, 1 => 0xbad65247a36add6b3434e9b57555965a48daba9acb2cfa6d5dad65968e36aeeeb2cb571b56b34e65a48dab75acb2d186d5cfd65969236adceb2cb491b56b2ed65a48dab5965ad1246d5bac6d969236add584923697566101771e0dab75a9b2d246d5
  | 4, 0, 2 => 0xaccc1da7836ad659696491b57735965a48dab9d65acd246d5dab2d669236aed6b2cb5b9b57535970248dab75acb49246d5bad65968636add638cb591b5596b859a48dab599232d246d5dfd65968f36add5c6e1491b56e55965a48dab75acb2d026d5
  | 4, 0, 3 => 0xacc11969236add6b2cb512496eb59491b47cb59a632d246d5b6565969236ae76b2cb491b56eb2365a48dab75acb2d5c6d5dad65969236ad65ca92369457515965a48dab5f65a48da615acb2d246d342d6588883c1b56eb5965a7d24b5965ae1246d5
  | 4, 0, 4 => 0xbad6596a936ad9d9692369756b2cb491b4c8b92acb2d246d5acb2d748836aea6b2cb451b566b0172a48dab66acb2d246d5c0d65969236ad659692369217015965a48dabb5a532d246d5acb2d246d1c2d65e4cb491b56b2f43c1b4c2b30809e0da535
  | 4, 0, 5 => 0xddd6596b736ae32b2cb491b569d30809e0dab5965a18da61598405da7836addab2cb491b56b2cb54248dab597bb2d246d5bac8d967d36aecab2cb491b56eacb599b49cb7aacb2d246d5bad65389236add6e2e1491b56eb596b248dabb7acb2d246d5
  | 4, 0, 6 => 0xddd69969236ad659692369956eb593e9b4a4bbbb8b05246d5acb2d246d082eeeb2cb491b570f5965a48dab3080b15146d591b2d246d30ae22b2cb491b57455964a48dabb5acb81246d5b1d65849236ad659692309796d15965a48d4bbb65acd246d5
  | 4, 0, 7 => 0xd4d65849236add6b2df491b57775965248dabb491b2d246d5ddd65967d36add6b2cb491b56b2cb491b41ab3080bc8f06d58e32d709236add6b2cb3c9b56eacb59a48dab5965aa4da615bad6596b736ad65969236881661017a290dab99acb2d246d5
  | 4, 0, 8 => 0xc756596b736ad667acb491b5661166e248dab5965a48da235bad6d969236acc202e5549b56b2cb491840cb5965a48da6a5bad659692302eaeb2cb491b57255965a28dab9cacb2d246d5bad6596ad36ad65709d491b56b33b65a48dab7facb2d246d5
  | 4, 0, 9 => 0xacb2d6e6d30acc2027c369456b2f365a48dab5965ac1246d5bad6596a736add652cb491b571d5965a48dab5965b11146d5acb2d246d312dd6b2aa3c1b56b2cb51a48dab75acb29246d5bad65e07836add6b2cb3e9b56b2cb5da48dab3080aa0f06d5
  | 4, 0, 10 => 0xbad65a29236ae26b2cb491b56b2cb491a8a4b596fa48da615acb2d246d30add6b2c2431b540159769e0da95965a48e26d5bad65968b36ad664ccb491b56b2cb491b42ab75ac32d246d5ddd65968a36ae46b2cb491b56b2cb491b45aacb59a48da615
  | 4, 0, 11 => 0xc9d65969236add5669d491b56eb59a79e0dab75aca6d246d5acb2d489236ad65967d369856eb6165a48dab85acb2d246d5acbb5967836adaeb2cb491b56b2cb491bcdab8bacb2d246d5bad65968a36ad667ccb491a966101621f0dab78acb2d246d5
  | 4, 0, 12 => 0xacb2d247336ad65968a369856eb5969a48dab3093404f06d5acc51969236ad6596923691974f5965a48dab90acb2d246d5bab2d429236adc6cecb491b56eb5965ad8dab83acb2d246d5bad65c6b736ad659694491b56eb4970a48dab75acb0d246d5
  | 4, 0, 13 => 0xddd81969236ad65e8ed3c1b56b33c65a48dabbbacb2d246c5ddd65969036ae1ab2cb491b56b2cb5b1b4c2b75af32d246d5b432d24612eaea6b2f43c1b56b33265a48dab75ba564f06d5d2565969236ace22ccb491b56b31165a48dab757b32d246d5
  | 4, 0, 14 => 0xb1d65969236ae4ab2f43c1b566d0165a48dab7cacb2d246d5b3d65969236aefab2cb491b574b5965a48dab75ac9e0da545bad659692362d6620cb491b56eb5965a40dabbcacb2d246d5c2565969236add6b292368f56eb71ac9f4dab597132d246d5
  | 4, 0, 15 => 0x175acbb4f06d5acb2d246d29aeeeb2f43c1b56b2cb491b474b5965a48da675
  | 5, 0, 0 => 0x9840596ae36985aeb308132d246d6bad659692421b5aeb5965a48da2e6d94c240cb491b580175acbd0f06d5005d59692368456eb5965a48f06d6c44c202cb491b5b535965a48da2b6cacc202cb491b58015965a48880a5d4d65969236975b6b3080b81246d6dad6596bc491b5aeacb60a48da5d6
  | 5, 0, 1 => 0xbad65d4cb491b5aeb68acb2d246d6bacc202cb471b5aeb3780b2d246d698405969236841b773080b2d246d6ddd65969236911b0f3080b2d246d6acc05969236841b775980b2d246d6bad6ab2cb491b5b6b599532d246d6bad659692368b1ab33065a48da186bad2a60cb491b5a61228b32d246d6
  | 5, 0, 2 => 0xbad65969236935aeb30809f4da526c7dd6b2cb491b5aeb0165ac95e6d6ddd6692cb491b5b539aacb2d246d6ddd65fccb491b5b3d75acb2d246d6bad664acb491b580159491b4560a59832d246d3085da612780b2d246d6accc19692369a980198acb2d246d5dad65969236869aeb5965a14da4e6
  | 5, 0, 3 => 0x6d6b2cb491116eb5989b2d246d6deeeeb2cb491b5a830165a48da616006a6b2cb368d976b306d32d246d6bac8dcecb491b5aeb597e32d246d6bad65d8cb491b58019facb2d246d5bad65969a491b5aeb5680b2d246d6bad6686cb491b5aeb5965a5d246d6bad661acb491b58015976b2d246d5
  | 5, 0, 4 => 0xbacc202cb5b9b5aeb0165acd246d6bad6602cb5b9b5a610165a48da206bad6596a5491b5aeb599832cfa6d6bad6596923681daeb5780b2d246d6984059692368c1aeacb57aad246d6bac0596923687daf50165a48da1e6dad65969236949aeb3089b2d246d6a5cc202cb491b5b435965b05246d6
  | 5, 0, 5 => 0x9840596ac491b5b5d3080b2d246d69c405969236985a61014e248da616bad76b2cb491b5b1d599832d246d6d35d6b2cb491b5aeb597a32cf06d6bad65969236819b613080b2d246d6d056660cb491b5b775965a490a6d6dd6d6b2cb491b5a610165aa4da616dacc202cb451b58015965a48da0a5
  | 5, 0, 6 => 0xbacc202cb491b5aeb5965a48da446005d6b2cb431b576b599f32d246d6bad6596bc36939aeb5980b2d246d6bac0596a0491b5aeb5965a48da1e6d9dd6b2cb491b5aeb5965a48da0f6d4cc21ecb491b5aeb4465aad246d6cb4c202cb491b5b2d5980b2d246d6bad1a02cb491b580175659b46c115
  | 5, 0, 7 => 0x5659692369a16b2cb491b4c2616bad6596b2491b5ab33065a48da6160056596b8491b56eb5965a48da3569dcc202cb491b5b1b599832d246d6acd65969236985afd3080b2d246d6bad665acb491b5aeb597f32d246d6bad6596c7491b5aeb5998381246d6bacc202df491b5aa93065a48da616
  | 5, 0, 8 => 0xdedd6b2cb491b5b393080b2d246d6acb2d246d30959aeb5965a48da396dacc2029d491b5ab30165a48da186005d646cb491b56eb4a80b2d246d6005d6b2cb571b56eb307eb2d246d6bad65969236859801b5acb2d246d5d7cc202cb491b5aeb3080b2d5a6d6bad6596923689da61015c275246d6
  | 5, 0, 9 => 0x32d246d308456610165a48c2066acb2d247836985a610165a48da6a6dad66a0cb491b5b573080b2d246d6bad6596b1491b5aeb0165a48da2f6bad659692439b5aeb598932d246d6bad669ecb491b5aeb3080b31246d6dad65969236969b253080b2d146d6bad6632cb491b5ab2cb5f248da616
  | 5, 0, 10 => 0xdacc602cb491b5ad15965a48da6169bc05969236985a7b3080b2d246d6bacc240cb491b5aeb599032d246d6bad92b2cb491b5aeb3080b2d326d6d4cc230cb491b5aeb5965a490a6d69840596923688daeb3080b2d4c6d6d3d65f4cb491b5b4f75acb2d246d6bacd202cb491b5b775965af1246d6
  | 5, 0, 11 => 0x9840596a3491b5aeb3089b81246d680b2d246d10079aeb3080bc0f06d6bad6660cb451b5ab34365a48da616bacc202cb3e9b5ab2cb491b4c24d6bacc218cb491b5b1f5965a48da616ddd65969236869a610165aed246d6bad659692369b5aeb599632d246d6005659692369156eb598a32d246d6
  | 5, 0, 12 => 0x9847602cb491b5aeb596cb2d246d6bab2d78b3491b5b1d3080b2d246d69840596c4451b5a610165a48da626c6cc226cb491b5b53a9acb2d246d6bacc202aa3c1b5aeb6dacb2d246d6bad6674cb491b580192acb2d246d59840596ba36935aeb3065a48da576bac059ecb491b5aeb5991248f06d6
  | 5, 0, 13 => 0xbad6596bc491b5aeb5980b81246d6d4d6644cb491b5aeb5965af5246d6bad3602cb491b5aeb3083b2d246d6bac05969236879aeb5965a48da476bad65f2cb491b5aeb559832d246d69840596b0491b5b775965a48da526bad6596923696d801bbacb2d24445d14c202c5491b5b535997b2d246d6
  | 5, 0, 14 => 0xd6ea6b2cb491b580175aca48882b598405969236985aeb59a132d246d6acb2d246d30911b6b016eb2d246d6c6cc202cb491b58013080bb4f06d5984059692389b5b1b5980b2d246d6006eeb292368ad6eb3080b2d166d6bad659695491b5a612680b2d246d698405969236855aeb3080b81246d6
  | 5, 0, 15 => 0xbacc202d1491b5aeb599e32d246d6bad65969236971aeb5982b2d246d6d04c240cb491b5b0d75acb2d246d6bad6596923b1b5aeb5965a48da1a6bad65969236899ab2fe65a48da61698405969236885b77599f32d246d698405be9236985b81bbacb2d246d6dad659692469b58018cacb2d246d5
  | 5, 1, 0 => 0xacb2d246d0d061aeb5965a48da526bad65969236895b775965a48da5a6005d6b2cb49111602cb5c2bd246d6badd2b2cb491b5aeb5965a48da4f6005659692368416eb306d32d246d6006eeb2cb491b56f13080b2d246d6dad65969236889aeb596d32d246d6bad65969236891aeb5998b2d246d6
  | 5, 1, 1 => 0xddd659692368adaeb59a3b2d246d6ddd65969236975b4375acb2d246d6c5cc202cb491b5aeb3080b2d146d6bad65969236815a610165a48da636bad6596883c1b5b535965a48da0a6bddd6b2cb491b5ab2cb49214da616ddd66a0cb491b5aeb5965a48da086d3d6660cb491b5b53597a32d246d6
  | 5, 1, 2 => 0x9840596a4491b5aeb599f32d246d6e05d6b2cb491b5aeb6facb2d246d6dad65969236809a6101659f4da61698431969236985b6b5965a48da696005d6b292368ad6eb5965ad5246d6bada6b2cb491b5ab2cb491b4da616bad65a8cb491b5b6b308c32d246d698405dacb3c1b5ab3308a32d246d6
  | 5, 1, 3 => 0xacbd1dacb491b5b6ba9acb2d246d6bad66a2cb491b5b355965a49106d6bad659692431b5aeb017ab2d246d6dde6ab2cb491b5b273080b2d246d6bad3e61013c1b58017565acd246d5005d6b2cb5b9b57535965b05246d6bad659692369658015965a48da205badaab2cb3c1b5b6b3080b21246d6
  | 5, 1, 4 => 0xbad6596923684db535965a48da116c6cc202e0491b5aeb597db2d246d6bad65969236801b535965a49066d6bad65969236969b073080b2d246d6bacc245013e9b5b295965a48fe6d6bacc1b4cb3e9b5aeb5973b2cfa6d60056596923680d6eb5965adcda5d6d4cc202cb591b580175acb2d246d5
  | 5, 1, 5 => 0xacb2d246d30869b213080b2d246d6bad9eb2cb491b5aeb3080b61246d6bad659692368adaeb5972b2d246d6cdcc196ab491b5aeb5965a48da5d6dad6644cb491b5b775965a491e6d6bad6596923692daeb5cacb2d246d6bad6660c2491b5aeb59a832d246d6acce660cb491b5ab2cb5e248da616
  | 5, 1, 6 => 0xcd5d6b2cb491b5aeb5965a48da546bacc210cb491b5ab33c65a48da616accf260cb491b5ab2cb491b4c25c6d3cc202cb491b5b535965a48fe6d6bacc20292368fd8015965a48da6a5bacfa26cb491b5aeb59a4b05246d6bbdd6b2cb491b5aeb597432d246d6c356660cb491b580175ac9b46c2b5
  | 5, 1, 7 => 0xbad659692368d1a610165a48e66d6d0d6660cb491b5a610165a28da616d4dc6b2cb491b580175acb2cfa6d5bad6680cb491b5aeb5965b2d246d6bada1969236975a611480b2d246d6bad6612cb491b5ab2cb491b4c2526bad6596923682d8015965a48c2445bada2b2c2491b5a60da65a48da616
  | 5, 1, 8 => 0xbad6596923a1b5b535965b11246d6d24c202cb491b5ab2cb491b4c2596bacc216cb491b5aeb3080b2cf66d6accf9969236985aeb63acb2d246d6bacc202c0491b5a611180b2d246d6bad659692479b58018eacb2d246d5bad6644e7491b58015965a48da015bacc196923690580159491b4c22b5
  | 5, 1, 9 => 0xbad66a4cb491b5ab3308b32d246d6c6d65969236969b77a9acb2d246d60056606cb491b54015965a48da615bad65969236831aeb3080b09246d6bad6596bf491b5aeb5970248da5a6d4cc202f43c1b5a653080b2d246d6c7565969236975aeb597232d246d6bad660ccb491b5aeb6aacb2d0a6d6
  | 5, 1, 10 => 0xbad65decb491b5aeb3080b715c6d6acb2d246d308adab2e565a48da616acb2d246d30975aeb5965a48da42698405aecb491b5aeb5965a48da496bad82b2cb491b5a611665a48da566bad659692368a5b0d3080b2d246d6c3565969236911aeb308532d246d698405a0cb491b5ab35065a48da616
  | 5, 1, 11 => 0xcd565969236985a61017a3b4f06d6bad65969236809aeb6aacb2d786d698405e2cb491b5aeb5970b2d246d6bad659692369a5aeb5965a48da506bac81969236969b6b598bb2d246d6ca5d6b2cb491b5aeb5965a48da0960056ab2cb491b56cf5965a48da616b3d6660cb491b5a793080b2d246d6
  | 5, 1, 12 => 0x565969236819777597a32d246d6bad659692449b5b593089b2d246d6c55d6b2cb491b5aeb5997b2d246d6c24c202cb491b5aeb5965a49006d6d4d65f4cb491b5b5375acb2d246d699cc202cb491b5aeb5965add246d6bacfe02cb491b5b433080b2d246d6bad6596923686d80175acb2d146d5
  | 5, 1, 13 => 0xbad65dacb491b5aeb5966b2d246d6bace196923f9b5b593080b2d246d6db4c202cb491b5b533065a48da176d6dd6b2cb491b5aeb5965a48ee6d6bad65969236901ab3307232d246d6bacc2027836951ac7599832d246d69844202cb491b5aeb2e80b2d246d6ddd65969236829aeb5965a48da436
  | 5, 1, 14 => 0x56628cb491b56eb5965a48fa6d6d4ce202cb491b5aeb5965a48da0a6bad65e8cb491b5ab2cb491b422106ddd65969236845b775965a49066d60069eb2cb491b56eb70acb2d246d6bad663ecb491b5aeb5965a48da1c6be4c202cb491b5aeb5965ae5246d6b3cc202cb491b5ad163acb2d246d6
  | 5, 1, 15 => 0x98405c8cb491b5aeb3080b2cf86d6c15d6b2cb491b5ac73080b2d246d6d4d65969236985b53599832d246d6d4d66b2cb491b5ab33e9cb2d246d6c94c202f43c1b5b53549832d246d6d4d66a8cb491b580186acb2d24445bad659692368edb4575acb2d146d6becc202cb491b5ab33065a48da696
  | 5, 2, 0 => 0xd4e3eb2cb491b5aeb5965a48da456bccc202cb491b580186acb2d246d5d4da2b2cb491b5aeb5965a48da3c69840596923699daeb59983d0f06d6bad65969236845aeb5965a49066d6bad65969236811b7771acb2d246d6bad65969236839801a965a48da115d4d6596923c1b5b8375acb2d246d6
  | 5, 2, 1 => 0xddeeeb2cb491b5aeb5965a49146d6984059692369a5a610165a48da4a6acc059692369a5b2575acb2d246d6d4cc226cb491b5801599e32d246d5acb2d8892441b5a610165a48da3a6accc1dacb491b5b6b3065a48da176bad6596923697db535680b2d246d6ddd6596c4491b5acb3080b2d246d6
  | 5, 2, 2 => 0xbacc202f43c1b5aeb5965a48e46d6bad6596c4491b5b1975acb2d246d6bad65d6cb491b5800cb491b4220a5bacc202ed3c1b5aeb5965a48da146d4cc202cb491b5b535965a48da446d4d6602cb491b5aeb71acb2d246d6acb2d246d30829aeb5965a48da666acbd1969236985a610165a48da536
  | 5, 2, 3 => 0xbad65969236881b775965a48da6a6acb2d246d30915ab2e77232d246d6bad65f0cb491b5aeb6eacb2d246d6bad659692368a180167acb2d246d598405dacb491b5aeb5965a48e06d6acb2d246d30845aeb5965a48fc6d6dad65969236959aeb5965a48da106ddd65f4cb491b5b7775acb2d246d6
  | 5, 2, 4 => 0xbad659692369a9ab2cb62248da616bad65969236849aeb5965a48dc6d69840588883c1b5aeb3080b2d3e926bad65247836949b53599532d246d6ddd6596923680580163acb2d246d5b8d65969236985aeb597d32d246d6badd6b2cb491b5b255965a48f06d6bad6596923a9b5b25599832d246d6
  | 5, 2, 5 => 0xdde3eb2cb491b5b459aacb2d246d6ddda2b2cb491b5b1d75acb2d246d6bad659692368058017565a4888115c94c202cb491b5800cb491b422105006ed9692368457775965a48f06d6bad66accb491b5a610165ae9106d6bad65969236931b775965a48da616ddd66b2cb491b5a61017a1e0da616
  | 5, 2, 6 => 0xacbe9969236985aeb5965a48da616bad66b2cb491b5a61017bb2d246d6bad65969236955aeb2b80b2d246d6
  | 6, 0, 0 => 0xdacc202cb491b444f7598405cecb491b5eeb3080b69969236b803775980b2d246d6bacc202cb491b448f7598cc202cb491b5eeb5980b9d969236bdd6793080b2d246d7bacc20b0165a48daf75accc19692368adeeb599832d246d2eb800017565a48da115005d6b2cb491e0dadb5d14c202cb491b5e611a80b2d246d30be1aeb3080b2d246d7
  | 6, 0, 1 => 0xbacc202cb441e0dafa9984059692368d9c018fbad65969236b6a6610165a48da0a7bddd6610165a48daf7598405969236821f533080bd1969236bcc202cb491b434187bacc202cb491b4a4f7598405969236895eeb5980b2d246d293802eb3080b2d24446005d6b30165a4888c00bada2b2cb491b5aeb3080b2d246d27b803773080b2d246d6
  | 6, 0, 2 => 0xbad667d0165a48dafb598405969236809eeb3089b2d246d2d3ed6610165a48da697005d6611365a48dac00bacc20292368ad80175acc05246d15b4c202cb491b4da617bacc202d465a48daf75a3cc202cb491b5f757598405969236bea6610165b19246d7005d6ad0165a48dac00bad6686cb491b5aeb3080b2d246d02be6aeb599832d246d7
  | 6, 0, 3 => 0xbacc202e7659f4dae009840596923680d8017598405969236b002eb5965a48da44698405e8ed65a48dae00bad6602cb491b5aeb308f405969236bed7533080b2d246d70065a610165a48dad9a984059692441b5c010165a48da1a053000015965a48da0a5bacc202cb491b4b2f759845602cb491b5c013080b2d246d1035d67d3080b2d246d7
  | 6, 0, 4 => 0xbacc202cb491b496e00accc1969236985aeb3080b2d246d1bbdd6a13080b2d246d7bacc202cb57248daf75acd4202cb491b5c0175acbf9969236b4c202cb5e248da617bacc202cb491b426f7598405f6cb491b5eeb3080b2d246d003802eb3080b2c88366d4cc202cb4920cdaf7598405969236969eeb5980b2d246d2d3e52610165a48fe6d7
  | 6, 0, 5 => 0xbad22610165a48daf7598405bccb491b5f533080b2d247f36bdd661017432d246d7005d66101368d856d3080b2d246d30869eeb3080ba5969236bdd6b33065a48da227bacc202cb491b456f7598405cacb491b5c0000dad65969236acc2550165a48da617d4cc22f0165a48daf7598405969236975f6b3091405969236b803533065a48da226
  | 6, 0, 6 => 0xbacc202ff65a48daf75984059692368d1f63a998405969236b802eb3080b2cfa6d6bad02610165a48daf7598405aacb491b5eeb3080b2d969236bdd6610980b2d246d798405969236984a4e00984059692309118017565a48da1a0bb002eb309032d246d6cd5d6610165a48daf7598405969236951e793080b2d246d30b802eb5965a490a6d6
  | 6, 0, 7 => 0x5d6610170248dac00bad6596bc491b5aeb3080b91969236bdd6610680b2d246d7bacc202cb491d0dafa99840596c4491b5eeb3087c05969236bdd6610165a491a6d7005d602cb491b43cd3080b2d246d30965e7d3080b2d246d30bea6eb599832d246d7bacc2450173a48daf75984059692368c5eeb3073b69969236b8026101491b4c22b6
  | 6, 0, 8 => 0x98405cacb491b4c2f7598405969236925f0d3080b2d246d223802eb5965a48da1a6daed6610165a48daf7598405969236889eeb5980b2d246d113cc202cb491b4c25a7c6cc202cb491b4b4fbbd4cc202cb491b5c013081c05969236b002610165a48da61600636610165a48dad759840596bf491b5eeb3080b81246d2d3dd6b3309132d246d7
  | 6, 0, 9 => 0x5d6610165a28dad9a98405969236985c017580b2d24440d35d6b3307a32d246d7bacc202cb491b404f75984059692369a5c0175acb2d246d2930000175acb2d24445dacc22f0165a48dae00dacc1969236889aeb308c405969236b802eb306d32d246d600003775965a48dab94bacc202cb491b5eeb3080bbd969236bcc202cb491b4c22b7
  | 6, 0, 10 => 0x4c202cb491b40cd75984059692449b5f157598405969236bed661018032d246d7bacc25f0165a48dae00bac05246d1586980175accf9969236b5d6610165a49006d7bacc2510165a48dafa998405f4cb491b5f537598405969236bea6eb5980b2d246d700002eb59491b456b75a1cc202cb3c1b5eeb3080b2d246d0dbdd6b33065a48da0a7
  | 6, 0, 11 => 0xbad6660cb491b422f75984059692368c9c017580b2d246d0d3002eb59a832d246d6bad6660cb4920cdafadbacc202cb491b5eeb3080b2d247736bdd6610165a48da407005d6b2cb491b4b4d7580b2d246d11079c0000bad65969236add6612280b2d246d7bad66450165a48daf75a0c0596923f9b5eeb3080b2d246d21bdd6b33065b05246d7
  | 6, 0, 12 => 0xbacc202cb491b414e00cd5d6b2cb491b5aeb3080bd1969236bdd6b33065a48fe6d70069e610165a48dad759845d969236959c010165a48da1a0c35d6611f80b2d246d7bacc202cb491b438f75984059692411b5eeb3080b2d729236b802eb0580b2d246d6bacc202ed65a48dae00bad659692368adaeb3080b35969236b802eb5965a48da5d6
  | 6, 0, 13 => 0xd4cc202cb491b4acf82bacc202cb491b5eeb3080b2d246d2c3ea6610165a48da617d4d66610165a48daf759840596c1491b5e7d3998405969236bdd6e3599832d246d7bacc202cb491b454e00c34c202cb49111aeb3080b2d246d1dbe8aeb3080b2d146d7bacc196923f9b4ace009845202cb491b5aeb4598405969236bdd6610165a48fa6d7
  | 6, 0, 14 => 0xbacc202cb491b48af7598405969236945f71b598405969236b8030d3080b2d246d60040596923698434d75acc5e02cb491b5f7775accc1969236bdd6610165a48da3c700002b2cb491b4c2b7598405969236845eeb3080b2d248336bdd6610165a48da047d4cc202cb491e0dafc1bacc202cb491b5eeb599832d889236bdd6612180b2d246d7
  | 6, 0, 15 => 0xbad6660fa65a48daf75984059698491b5eeb3080b2d246d0a3ea6610165a48da447006a6eb5965a48dada99840602cb491b5eeb7198405969236bcc202cb491b4c20a7bacc202cb491b4ccf3080bd1969236985eeb3080b2d248a36be4aeb3080b2d246d7004f2610165a48dad3080b2d8892441b5eeb3080b2d246d0ebea71f3080b2d246d7
  | 6, 1, 0 => 0x5d6b2f465a48dad75984059692368cde610165a48da6122bcc202cb491b4c251798405cee465a48daf7598405f0cb491b5eeb3080b2d246d143dd6610165a48fc6d7984059692419b4c2fb598405969236959f777598405969236bdd6610165a48e46d7bacc202cb62248dafa99846a02cb491b5f197598405969236bea661017f32d246d7
  | 6, 1, 1 => 0x4c202e465a48dad75984059692371b5eeb3080a48f06d293dd6b33065a48da617bad66613065a48dafa9984aa02cb491b5eeb59accc1969236b80353599832d246d6d4cc202cb5e248daf7598405f4cb491b5eeb7598405969236be4a610165a48f06d7bacc202cb491d4daf759c4c202cb491b5c0175acb2d246d0535d6610165a48da207
  | 6, 1, 2 => 0x4c202cb491b4d2c00d4cc20292368adaeb5698405969236be3eeb599832d246d7005d596923688834d7598405969236931eeb68accc1969236bea6610165a48da527ddd66610165a48dae00d4cc202cb49111801759832d246d08b5d6610165a48da177bad6660cb491e0dae00bad6596923684580175acb2d248336b4c202cb62248da617
  | 6, 1, 3 => 0x4c202cb4911014d759840596aa491b5c0175acb2d889236b5d6b3307f32d246d7bad6602cb491b4acf3080be9969236985eeb3080b2d246d30bdd6613080b2d246d7bad6660cb491b488f75accc202cb491b5c01a998405969236b5d6610165a48da557006a6b30165a48dac00badc6b2cb491b5801599832d246d05368b353080b2d246d7
  | 6, 1, 4 => 0xd35d6610165a48daf7598405e8cb3c1b5eeb3080b2d246d033802610165a48da0a6bacc202cb52a48daf759840596923681deeb5680bf9969236b802610176b2d246d6c7dd6610165a48daf9ebacc202cb491b5c013080a48da2b0536d6610165a48da1a7bada2610165a48dae00dddd6b2cb491b58017598405e87836b5d6610165a48f06d7
  | 6, 1, 5 => 0xc7cc202cb491b4c2f75984059692369b5eeb3096405969236b802610165a48da456bacc2290165a48dafa798405f4cb491b5f4f7598405969236bcc202cb491e0da617bacc2250165a48daf3080b2d246d30985eb33080b2d246d30bdd661017f32d246d7bad6602fe65a48daf7598405969236911c0175acbe9969236b5d6610165af0da4e7
  | 6, 1, 6 => 0x4c202cb491b4c2447005d6b2cb491b4c2c00bad66b2cb491b5aeb3080be5969236b803253080b2d246d6
  | 7, 0, 0 => 0x2eb0165a48da1a6000000175acb2d246d5005d6612280b2d246d7006a6eb3080b2d246d7005d6610165a48da22700002610165a48da6160066aeb3080b2d246d7005d6610165a48da2b7005d6610165a48da5a700002eb3080b2d246d600002eb5980b2d246d6005d67d3080b2d246d700002eb3080a48da2b6005d6610165a48da52700002eb3080b2d24446005d6610173b2d246d7
  | 7, 0, 1 => 0x5d661017f32d246d7005d6610165a48da44700002610165a48da0a60063eeb3080b2d246d7005d6610165a48f06d7005d6610165a48da617005d6b33080b2d246d700003533080b2d246d6005d661017d32d246d7005d6610165b11246d7005d6610165a49066d7005d6610165a48da0a7005d661017a32d246d7
  | 8, 0, 0 => 0x2eb3080b2d246d6
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
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 5 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 29 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 5) z3_0 z3_24

private theorem z3 : span (Z 3) 29 0 = true := z3_a1

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
private theorem z4_240 : span (Z 4) 5 240 = true := by decide +kernel

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

private theorem z4_a10 : span (Z 4) 245 0 = true :=
  span_join (f := Z 4) (a := 240) (o := 0) (b := 5) z4_a9 z4_240

private theorem z4 : span (Z 4) 245 0 = true := z4_a10

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
private theorem z5_600 : span (Z 5) 14 600 = true := by decide +kernel

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

private theorem z5_a25 : span (Z 5) 614 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 14) z5_a24 z5_600

private theorem z5 : span (Z 5) 614 0 = true := z5_a25

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
private theorem z6_336 : span (Z 6) 21 336 = true := by decide +kernel

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

private theorem z6_a14 : span (Z 6) 357 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 21) z6_a13 z6_336

private theorem z6 : span (Z 6) 357 0 = true := z6_a14

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

def CG : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12491

theorem PEqualNP.Outside.L_meta_12491 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12491.mainG PEqualNP.Outside.L_meta_12491.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12491.CG, PEqualNP.Outside.L_meta_12491.CG_mono, by
      have : PEqualNP.Outside.L_meta_12491.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12491.CG_eval⟩
