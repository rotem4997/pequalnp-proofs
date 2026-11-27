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
namespace PEqualNP.Outside.L_meta_12543

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008242912 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 5, 5, 5, 5, 7, 5, 9, 5, 11, 5, 13, 5, 15, 5, 5, 5, 5, 5, 21, 22, 23, 5, 25, 26, 27, 5, 29, 30, 31, 5, 5, 5, 5, 5, 37, 38, 39, 5, 41, 42, 43, 5, 45, 46, 47, 5, 5, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 7, 7, 7, 7, 7, 5, 7, 7, 7, 9, 7, 11, 7, 13, 7, 15, 7, 7, 7, 7, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 7, 7, 7, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 9, 9, 5, 9, 7, 9, 9, 9, 11, 9, 13, 9, 15, 9, 9, 9, 9, 9, 21, 22, 23, 9, 25, 26, 27, 9, 29, 30, 31, 9, 9, 9, 9, 9, 37, 38, 39, 9, 41, 42, 43, 9, 45, 46, 47, 9, 9, 9, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 5, 11, 7, 11, 9, 11, 11, 11, 13, 11, 15, 11, 11, 11, 11, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 11, 11, 11, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 11, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 5, 13, 7, 13, 9, 13, 11, 13, 13, 13, 15, 13, 13, 13, 13, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 13, 13, 13, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 13, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 15, 15, 15, 15, 15, 5, 15, 7, 15, 9, 15, 11, 15, 13, 15, 15, 15, 15, 15, 15, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 5, 21, 7, 21, 9, 21, 11, 21, 13, 21, 15, 21, 21, 21, 21, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 21, 21, 21, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 21, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 5, 22, 7, 22, 9, 22, 11, 22, 13, 22, 15, 22, 22, 22, 22, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 22, 22, 22, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 5, 23, 7, 23, 9, 23, 11, 23, 13, 23, 15, 23, 23, 23, 23, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 5, 25, 7, 25, 9, 25, 11, 25, 13, 25, 15, 25, 25, 25, 25, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 26, 26, 5, 26, 7, 26, 9, 26, 11, 26, 13, 26, 15, 26, 26, 26, 26, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 26, 26, 26, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 26, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 27, 27, 5, 27, 7, 27, 9, 27, 11, 27, 13, 27, 15, 27, 27, 27, 27, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 5, 29, 7, 29, 9, 29, 11, 29, 13, 29, 15, 29, 29, 29, 29, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 5, 30, 7, 30, 9, 30, 11, 30, 13, 30, 15, 30, 30, 30, 30, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 5, 31, 7, 31, 9, 31, 11, 31, 13, 31, 15, 31, 31, 31, 31, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 5, 37, 7, 37, 9, 37, 11, 37, 13, 37, 15, 37, 37, 37, 37, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 37, 37, 37, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 5, 38, 7, 38, 9, 38, 11, 38, 13, 38, 15, 38, 38, 38, 38, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 38, 38, 38, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 5, 39, 7, 39, 9, 39, 11, 39, 13, 39, 15, 39, 39, 39, 39, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 5, 41, 7, 41, 9, 41, 11, 41, 13, 41, 15, 41, 41, 41, 41, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 41, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 42, 42, 5, 42, 7, 42, 9, 42, 11, 42, 13, 42, 15, 42, 42, 42, 42, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 42, 42, 42, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 42, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 43, 43, 5, 43, 7, 43, 9, 43, 11, 43, 13, 43, 15, 43, 43, 43, 43, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 5, 45, 7, 45, 9, 45, 11, 45, 13, 45, 15, 45, 45, 45, 45, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 5, 46, 7, 46, 9, 46, 11, 46, 13, 46, 15, 46, 46, 46, 46, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 5, 47, 7, 47, 9, 47, 11, 47, 13, 47, 15, 47, 47, 47, 47, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 5, 51, 7, 51, 9, 51, 11, 51, 13, 51, 15, 51, 51, 51, 51, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 5, 53, 7, 53, 9, 53, 11, 53, 13, 53, 15, 53, 53, 53, 53, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 5, 54, 7, 54, 9, 54, 11, 54, 13, 54, 15, 54, 54, 54, 54, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 5, 55, 7, 55, 9, 55, 11, 55, 13, 55, 15, 55, 55, 55, 55, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 5, 57, 7, 57, 9, 57, 11, 57, 13, 57, 15, 57, 57, 57, 57, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 58, 58, 5, 58, 7, 58, 9, 58, 11, 58, 13, 58, 15, 58, 58, 58, 58, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 58, 58, 58, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 58, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 59, 59, 5, 59, 7, 59, 9, 59, 11, 59, 13, 59, 15, 59, 59, 59, 59, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 5, 61, 7, 61, 9, 61, 11, 61, 13, 61, 15, 61, 61, 61, 61, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 5, 62, 7, 62, 9, 62, 11, 62, 13, 62, 15, 62, 62, 62, 62, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 5, 63, 7, 63, 9, 63, 11, 63, 13, 63, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f000000000000000000000000000000000000000000000000000000000000000000000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f000000000000000000000000000000000000000000000000000000000000000000000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0000000000000000000000000000000000000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa00000000000000000eee8eee0eee0aaa000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0eee8eee0eee0aaa0

def cMZZ : Nat := 0x1117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f0000000000000000000000000000000000000000000000001117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f00000000000000001117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f1117111f111f555f

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
  | 2, 0 => 0xb6ec564b8f66bd5618cacc24
  | 3, 0 => 0xe9bd9f3be2c8c2acde3e9dbbd4781aaecbc4fe19c75ac375c30bdb76c1138444c0dbed8ab9c537eab929ff81b5d0e8e6b2c52822b152599ca96d9f2ba61caf8aa2d963459ff68ecf9efbe0b79a505fc397770cf5957104a793d3a39791dafddf888ddec0759bce606e5fa40469cb1ded68659584613c611459ed726959af670856a1c5545533027f500af97549abdc8246faf2ea452204d73aa545cb39fd74e629000b17264670c8253d3075206af1f21d2b2e381abb780f1a9f775f19f6453b1580d01f1175e76e0fc30cf00d0fcfc30a3de372093524e40684d18406259dff05b10e89052c5c80049e08be
  | 4, 0 => 0x1a72408719d6245919b352271992135c192f194c18ff72011826577c1820b79e1755075d1682df9b14ca4a74147ddbc213f626251368879d126f3b9911e7b53f1116668e10b7beaa0f2c7e4c0f114a950f09c5cc0ef8dd2f0ee085b00e73ce090e457a1e0deb97cb0d65b99c0d5fb5ad0d25caba0cbc3ad20c83b90f0c5e668a0c216d130c125d460bc2c0ec0b2ff3590ae098710a9d08d80a6548f90a3de37209f8915209e8ba1009a2062808d7bef30819ccc507fa17d307cf6fb107a3a7340728406406a8f91c067cb081062907f7060a46e0055e75270443f70c038d67f402b00f6c02a1599901dead0e01aaafc90131997601194990010e7f5700323751
  | 4, 1 => 0x3c2533133aff21c83ab4f9dc3a8c48513a7554313a73f6b839930ed1393a103b38e9dcad3746d987371c3d9636c364613625e18235eb3796357e7fef3417dbf533d9eaaf3372167e33426e423002be7d2fb63e5a2f20d8fc2f1c1ce42f17b2312cf6ceae2c8749532c762e3e2c0367352bc0224f2ba9e45d2b244e092a2ea0dd29317ae4290cffa6286131a32807b6fd27607873264f8bdd257868f624a75c3f237fb153234702d122f18f6522f0eaae22b955d3225f84752254ba3c217e5b2921037c3820d717e6206a603f200767591e8896db1e4683ea1e3c74c91d7e014b1d6917c81c54c0311bc5daf81b6c69621b313de01b1e52d71aa8320a1a7f9c08
  | 4, 2 => 0x656c131e6554b487646338a3642de06e635b5004630735966251792c6139d14d6122558a610c87b55ff4699c5ef6e5885bd154075bb3100d5b9e72405998dd3d5731727b55ee0421556ffafc552e915854d1fa4e54b8516353d85be05381a4ea526d1c2d5110a3605034c1ae4d6d0af94d6011094d02dba84d0091b24cab8c124b69905a49f01013498e8c8b48bda3da489a29a14832604d4795c6c24631a3cb45f4722645ebb620454a698d45390078449655704447305e44172c33440e79a243f383c743c8c84643100e7442e0b42a421d52cb41a78dae419e91d7404643203ec9c9823ec43c303e5d47923dbf078a3d96cc763d4f38a23d3ed66a3c2a8db9
  | 4, 3 => 0x9a6ba1259a39597b9a09a3eb993218c998eacd06989ecd3d987958b09767ab53963091179602c09495cca2609519d3569463bb4593c9581b9372590f92352fac910eb38b8fe5d1248de647ad8cea48d58caa3dad8b02022f8a5298e389900d7c87592cf684de114d83683a1c8268906f81d207be809532aa8052fba4802cb5a47f8868187f207e8c7ead0cdd7da2377b7b4382947a5c0663781b554677ebdde4776172b776691c5d74480b62736a28c7730c0be872a2ccb3723b11c5713c1f4e70e54f7070d3e19e702e6c726f047db66e9700476e46cc976dc5585a6d5e26e96a0b4c7668693fe067d912716731f10566d59e4e662cf7b265f54bae65ee8a5c
  | 4, 4 => 0xfbd335b4f99a3abef5609a83f3e4cd34f3ad367af223a941f0488ae9eccba574e8e4a87ee5b85d1ae2d77c92e0071bb6dfcf84fcdcb7f565dbc9c297dbb002a2d8edf87ad81d96f3d69310c4d67331c5d4781aaed02eada2d012ade4cea47b2ec90f6d62c7b5e3f5c71a674fc6a4ec87c51046fcc29ce862bdc2de58bd41aef0bc9d7b57b929ff81b60f60cdb54cd5dfb2c73b09abcc4c22aa070b54a96d9f2ba86d1750a7ba6ba6a701e80da61caf8aa2373628a1fe6885a1bd11d9a1aa8d46a193140da188e908a16fabb39e6dee049c0febcc
  | 5, 0 => 0xe646c670e457a1e0e30127f0e26d3fd0dcbb8da0d2d522b0d1fa4590cf6e42e0cecc86a0c599ac60c125d460b9aff150b3f341f0ac55b0809e44e8d09c6591209c05c6409bfb9d309a20628097b006b09464eee09402c72092008ee089d430c0861e1170813d1d607fbe9c607fbe19d07d83ff507ade33f07612da306f4a1bb06e2923806b182db06a17af905a2d9a2052627c004be63e804bcb43104603a8a04593000042328560422cd0a0406d30d03f5f5a503ec8a6803919cdf035ba15702a446d9028c8403025237d5021f77300208436301fec34301e671e00122ce6a00c5ab0100a2360e0079a3060072ffb00049dd9f00267115000a757a000021ff
  | 5, 1 => 0x1b427f5a1b336dbf1b19b3231b00a30c1ac6cd2b1aa8320a19d4ea161933f73c18d9246e18a3dcc2188dd23517f8a4c117b4245b1785adfa1711fad116ae26341690976415e861e615e31c9e15d6e1dd159e348715882f1514d7b10d14b71b041421e1fa141609661407300613f5557913ed078f13d0c6a513afe33913796487133e9f2213366bb2130cace012e4b84a12d864ab12c99f7412c2eaef12a0cdf1126d34cb126b56a0122f187a116862391151de0811361a8f110d8cc2110c100210ce611110ab3c1d107804ca104c87750fa454460f94505c0f900f5d0f7619c40f48b0e50f3c22600f114a950f09c5cc0ee085b00edfaee00ed879ea0ecdd396
  | 5, 2 => 0x2c762e3e2c59510e2c534d1f2bd6563f2ba9e45d2b7750812b71b99d2b2a89722b05f4b82ab6585e2a9ee55d2a9c4ec52a8667572a6982db29d42fe329d151bf297277fd2958e06b28e13b9a28ccaf3027fd494027cb566527bdc6ca270d643726edaf4526bcf8cc2622cca925e12d2925cf2f7e25c6a4d825a6756f2586f616256d0acc2410926423703ae02347605e232cacc5231827bc22f0eaae22cba7992254ba3c222a833f21f5f9e9216cabfa213466ba20d717e620d2448020a4e968209e473b207f0399206a603f205afe9d200ce1021fe93f451fdc27211fd565381fc24b101f23e4611eea547c1e9681e21e2c7c7c1dbc79321d10716f1c0e4fd1
  | 5, 3 => 0x4071f29b4030fe9d3ff713aa3fed3f6a3fcaaf583f79a6223f02b4173efafecb3ee76c6c3ec43c303e8efe203d6e51c83d3a1b5c3c8426b53c2533133b4857a33aea6ea43a7554313a11ea4939a490ff399bc97c3961c287392cc59038c9bbcb38a6e99937d7425d37851386372e9ccb3719eeee37144f1036b822383673e91c35f61d6935479b7235221099351eff0934bf9f6c3480eb0133e359d533ba7eb03374ed5f3371733432f5abe7314e87a3313108f9311a769730eeba7830e0e6b230db4cb130adb18c30365daf300e6c523009fe002ffedb4e2fab561c2f62fc5a2ecde8b02ec77fb42dfd5d3e2dd41d222d347e062d0c21e12ce0b0a82cdf2f3d
  | 5, 4 => 0x58b93c6957f5a34e5731727b56fa27a655ee042155c725e655a11990557ae9ac54bb284453b0098e53911b4e535da777530b736752cd82215279dd52523605b451876908516f5a6c50c78dcb50a9373f50a853914fd4477b4f9dcd4e4ef655ef4e7ab8eb4e56a9864df33bfb4db9fd9f4bea66204be154f54bad3a444b7ae0c54b69c5b04a9d7bcf4a795f754922384f4909a2e748544584480097184795c6c2476f7eb646540fe5462249d745ce71ca45b110e64539007844eb27ed44650dca44405ae24403647143d093b0427348c54272d9894241d6bf421d52cb41e9cd9d41e4822041aced45415512db41531be7414851ae41226206411e382c4091ef45
  | 5, 5 => 0x734c24b5729cfedf7294d7dd72753c5c7212615971a5a9b27160b39f6fa730336f75cdca6f02b0be6e58ebd36e0125956c4a17ea6c2fd3916c27b3c26b1e334d6a5d27cc69bec9b569a47468698bc56e697e859c688223fd678dc1136731f10566895e3465ab48af64c04bf6646d6924642c97ea637cb986630ac3a563073596630211146249a044622ca5926203a5e661c8e37061b4cd51618635e16110ea3d60a66ca960922949606c89ee5e32c74c5dd41e415db7d3a25d0181165cb29efc5c8a63e85c62599d5c3d38755bc9befe5b6cd5195b6c41c85b18ca855abcc7725aab87915a86e2f859f2b93a59d43da659a8914e5968eba3592bf80758c7ef0e
  | 5, 6 => 0x97d3d8f5977049a596df755696deeb1096c4ca9196550a29955cb3cf9372590f9362735e93589c3e933ba2d492da914c925dc03991ffa35a91c5eea791966425912ea93790ed6b188fcbc6c98f905dfa8f448af58f2203e48d6deea78cb8efcc8c38eaa68bd9b3ac8bbf83888b3fb23e8a666e33892b738988186fe588114dce87b47fb986f0761786cca9e3853e651d84e8e32084dadb7184484bf9824ee77681facd0880f7d64d7f807ca37ecc30c07ea45f257e92421d7cf394407c7762d47bdb6d9b7ae7328c7aa6a77f793bde33792ffc2a7919b13378a770d8781a4c55768d9e10766c9039764e38dd762509ed75b1fd1a74480b62739d5c8d73571564
  | 5, 7 => 0xd183b40dceb85fa4cd01cce7cc0361b9cb903430cabfe394caa8daefc9fe918cc86c9a4cc849ce23c6b25acfc51046fcc49523abc41f452cc25fc9a3c12acd9abea78084bdc2de58bd2e64dabb13ed42ba3c5deeb92cf0edb929ff81b825b03bb80b0576b7d29501b76c36a5b74d2137b5c4eae0b51a2359b4f65806b35752b7b2d1bd69b2bcef8db265f081b13ba4ebb0474201b032c834af6431ccaed96896addfedb0ace7f8a5ac6f15d3abe43fd2abbb9202abaca918aba48a4bab9dd51faabd26d4aa71ae6ea56c1feaa4e266a5a1a01466a0c59f30a00bc4209dbd9db99d4c4cec9c95ceed9b6354689a371a069a0e62d5993218c998215e38980a3dcd
  | 5, 8 => 0xfb0f810df7e18fecf5a9cdecf586a836f22299f0ef2990deef224514eee89ef3ed050c03ecd1c007eb44cc71eb1ac31ee930e63de91e37bce8001404e7188141e60dfec1dcb675cad8edf87ad81d96f3d811f645d80948c4d69310c4d6605e3ed502f83fd4406d51d30747a3d281dfd0
  | 6, 0 => 0x1f1a9a0a1f1a08871ed06f771eb7c0e41eaea3401cd140ee1c2673e31ad6e3b01a03188419e4b46519ccf62a192f171318d9246e17c39b5417314eed168680fb15ffe2d315e31c9e15ac431615882f15156fdad21416096613f555791390792b1336638a11cb65e7110d8cc210837a4610502a9c101cf41a0f95473f0ebae94f0e3aeec50ddc366a0d27c63d0cb8110a0bc5577e0b41c5660b035ce30ac55b080a3863e80a1304230a0e5a9509464eee092008ee08d1a96008b069160872b79508586896082a7bb608247db40811cf3307fbe19d0736c02306ff868605cd091e05a93e2a04bcb43103b5b0e003919cdf036b0adb025237d5023858840015bb25
  | 6, 1 => 0x38278eae37ccbbe036a7bbcd3605924334dbf95834d6b41034bf9f6c347bc68733c4aea733aab276326cfbf931d84fbc31b682613029b201301ca0de300124342fc1f8832f9ed38f2f401ee72e97ebb82e87e7ce2e69b1362e3c48572dd41d222db16fb82d23a9f12d1a6b6f2c20e99d2be05fdc2b2a89722b05f4b82a8667572a31f3472a01ef0c29b8f27a29806e922932023028d7e5ff2898edd62839e6602826048e27c35684279604f326ef813826ef790f25a6756f249671142419bf3223c0d9c223b1fb5a232cacc522fa6a7f22e021da21e5953521ab9039216cabfa20da095220d717e6205afe9d1fc24b101f95cd801f6d3a781f3d75111f23e461
  | 6, 2 => 0x67fd3a5966631628642c97ea63765f6f6358a53c62f6fbe362c42b226110ea3d6011cf9e5e3cdc9d5df64b895ddb03de5d8295925b18ca8559de061658982871585559f956cad9cf5678aaf85622343d55c725e654cf0a1654bb284453b336de526884d151e9435950a9373f50471f10500e0e094fe251ea4fa148fe4e7ab8eb4e5693cc4dc180224dbb17264bffb9534ac9edb14a9d7bcf4a1e20e449927ccf4979fec9495fc5bb4817b3c84735b30e46b15e3c4516641b44c2c6f04460a23e42204437421d52cb420bbf2e41e48220412262064060436c4027fe2c3fcaaf583f4e960f3f02b4173e177bd33ddd97cd3cb010a43a81a2593a0d4a9538c88188
  | 6, 3 => 0xa60a5389a5e40d89a4f85930a431fc8f9e7414159dbd9db99d97f6979d85d98f9c31f267982f75a59823939c95813582956027ab9541d04f937cb03f93589c3e9105f8cb90ed6b188e9ac7a58e69653c8d6deea78d4c83458b236b038b1b4b3488980bda88721d0e8808d111849ee02183610096827050f8813d37b681203d0480a864c38079cd537f9a041b7d265ebe7cc7b5b37bf518887ba55c067b55f10f7aebb7827abd56707a5fd93a799f1f03793bde3378b2efc0781f8f7976e93ac0747ee72d746e811e73aebfb6732462de7284b2c0716d74c46f9cceb16f9beb036f45e4706e9164c06e5181866d6e505d6d4a40f86aa0d1b6696cf6e768c76659
  | 6, 4 => 0xf7e18fecf586a836f553f5b0f1757742eb44cc71eaf6f92be76031bee5a5f241e1536115de30374ddcb675cada0784b4d92ff560d81d96f3d6c62c73d6605e3ed4b88252d281dfd0d02f3c5dcf265fa6ce57c93eccd38522cc0361b9cb62ad45cad7d744caa0408ac9b0be46c96545e0c74a6bf2c6b25acfc45fb75cc3d5fe17bcb1352bba56ebdab901fa47b825b03bb81792a3b80b0576b714f5aab6c77067b5d28282b59d2909b2560ad0b24c33b0b0da0e01afe1028aaecfc7e0ae83f56cac618619aacd4b1eaab31afaaa71ae6eaa3349b0a95a05a5a81f0afba6a8172b
  | 7, 0 => 0xf1757742eaf6f92be5a5f241c96545e0b24c33b0afe1028aac6186199c31f267982f75a573aebfb66f9cceb16110ea3d5df64b8953b336de4a1e20e442204437421d52cb4060436c3fcaaf583e177bd337ccbbe034d6b4103001243429b8f27a26ef790f1eaea34015ac431615882f15
  | 8, 0 => 0x6110ea3d
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30003000300030000ffffffffffff0000ffff0000ffff0000fff00000fff00000cccc0000cccc000033330000333300000f0f00000f0f00000000ffffffff00000000ffff000000000000ff00ff0000000000cccccccc00000000aaaaaaaa000000005555555500000000000f000f000000000000ffff0000000000000000
  | 0, 1 => 0xff00ff00ff00ff00ff0000ffff000000ff000000ff000000f0f0f000f0f0f000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000fffff000fffff000fffff00000000000f000f000f000f000f000f00000000000c000c000c000c000a000a000a000a0005000500050005
  | 0, 2 => 0x333f333f333f333f3333ffff3333ffff33333333ffffffff3333333333333333333333330000000033303330333033303300330033003300222222222222222211111111111111110fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f00000f0f00000f000f000f000f00030303030303030300ffffff00000000
  | 0, 3 => 0x55ff000055ff0000555f555f555f555f555f555f000000005555ffff5555ffff555555555555555555550000555500005550555055505550550055005500550050f050f050f050f04c4c4c4c4c4c4c4c44cc44cc44cc44cc444c444c444c444c44444444444444443f3f3f3f3f3f3f3f3f003f003f003f0033ff33ff33ff33ff
  | 0, 4 => 0xaaa0aaa0aaa0aaa0aaa0aaa000000000aa88aa88aa88aa88aa00aa00aa00aa00aa00aa0000000000a8a8a8a8a8a8a8a8a0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a0a000a000a000a0008888888888888888888888880000000088880000888800008880888088808880880088008800880077777777777777775f5f5f5f5f5f5f5f
  | 0, 5 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaa0000aaaaaaaaaaa8aaa8aaaaaaaaaaa0aaa0aaaaaaaaa0a0a0a0aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa8aaa0aaa8aaa0
  | 0, 6 => 0xcc00cc00cc00cc00cc00cc0000000000cc000000cc000000c8c8c8c8c8c8c8c8c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c00000c0c00000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafaaafaaafaaafaaafaaabaaabaaabaaabaaaaffffaaaaffffaaaaffff00000000aaaaaaaaffffffffaaaaaaaaaaafaaaf
  | 0, 7 => 0xcccc8888cccc8888cccc8880cccc8880cccc8080cccc8080cccc4444cccc4444cccc4444cccc0000cccc0000ffff0000cccc0000cccc0000cccc0000ccc00000cccc000000000000ccc8ccc8ccc8ccc8ccc8ccc8ccc0ccc0ccc8ccc800000000ccc80000ccc80000ccc0ccc0ccc0ccc0ccc0ccc000000000ccc00000ccc00000
  | 0, 8 => 0xcccccccccccc0000ccccccccccc8ccc8ccccccccccc0ccc0ccccccccccc08880ccccccccccc00000ccccccccc0c00000cccccccc88888888cccccccc88008800cccccccc00000000ccccccc0ccccccc0ccccccc0cccc0000ccccccc0ccc0ccc0ccccccc0ccc00000cccccc00cccccc00ccccc0c0ccccc0c0ccccc0c0cccc0000
  | 0, 9 => 0xdddddddd00000000cfcfcfcf00000000cfcf0000cfcf0000ccffccffccffccffcccfcccfcccfcccfcccf0000cccf0000cccdcccdcccdcccdccccffffccccffffcccccccfcccccccfccccccccffffffffcccccccceeeeeeeeccccccccccccffffccccccccccccccccccccccccccccccc0cccccccccccccc00cccccccccccc8888
  | 0, 10 => 0xeecceecc00000000eecccccceecccccceecc0000eecc0000eeaaeeaaeeaaeeaaeeaaeeaaaaaaaaaaeeaaaaaaeeaaaaaaee00ee00ee00ee00ececececececececececececa0a0a0a0ecececec00000000ececa0a0ececa0a0ecec0000ecec0000eccceccceccceccceaeaaaaaeaeaaaaae0e0e0e0e0e0e0e0dddddddddddddddd
  | 0, 11 => 0xeeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000cccc0000eeeceeeceeeceeeceeeceeecaaa0aaa0eeeceeec00000000eeeccccceeeccccceeecaaa0eeecaaa0eeec0000eeec0000eeeaeeeaeeeaeeeaeeeaeeeaaaaaaaaaeeeaaaaaeeeaaaaaeeea0000eeea0000eee0eee0eee0eee0eecceecceecceecceecceeccaa00aa00
  | 0, 12 => 0xf0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f00000f0f00000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeecccc00000000
  | 0, 13 => 0xfcf0fcf0fcf0fcf0fcf0fcf0f0f0f0f0fcccfcccfcccfcccfccc0000fccc0000fafafafafafafafafafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaaf8f8f8f8f8f8f8f8f8f0f8f0f8f0f8f0f3f3f3f3f3f3f3f3f0f0fffff0f0fffff0f0f0f0fff0fff0f0f0f0f0f0f0f0f0
  | 0, 14 => 0xff00ff00ff000000ff00ff00aa00aa00ff00ff000f000f00ff00ff0000000000ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcf0f0cccc0000fcfc0000fcfc0000
  | 0, 15 => 0xffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ff55ff55ff55ff55ff50ff50ff50ff50ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff00ff00ff00ff00ff00ff00ff00aa00
  | 1, 0 => 0xfff0fff0eee0eee0fff0fff000000000fff0ffc0fff0ffc0fff0ff00fff0ff00fff0ff00ff00ff00fff0fef0fff0fef0fff0ccc0fff0ccc0fff0aaa0fff0aaa0fff00000fff00000fff0000000000000ffe0ffe0ffe0ffe0ffccffccffccffccffccffccff00ff00ffccffcc00000000ffccccccffccccccffcccccc00000000
  | 1, 1 => 0xfffafff000000000fffa0000fffa0000fff8fff8fff8fff8fff8fff800000000fff5fff5fff5fff5fff3fff3fff3fff3fff1fff1fff1fff1fff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0ffa0fff0fff0fff0f0f0fff0fff0fff0aaa0fff0fff0fff00000fff0fff0ff00ff00fff0fff0faf0faf0fff0fff0f0f0f0f0
  | 1, 2 => 0xffff000000000000fffefffefffefffefffe0000fffe0000fffcfffcfffcfffcfffcfffcfff0fff0fffcfffc00000000fffcfff0fffcfff0fffcccccfffcccccfffcccccfff00000fffc0000fffc0000fffc0000fff00000fffc0000cccc0000fffafffafffafffafffafffaaaaaaaaafffafffa00000000fffafff0fffafff0
  | 1, 3 => 0xffff3333ffff3333ffff3333ffff0000ffff3330ffff3330ffff3030ffff3030ffff2222ffff2222ffff0f0fffff0f0fffff0033ffff0033ffff000fffff000fffff0000ffff3333ffff0000ffff000fffff0000ffff0000ffff0000fffc0000ffff0000fff00000ffff0000ff000000ffff0000eeee0000ffff0000cccc0000
  | 1, 4 => 0xffffccccffff0000ffffccccccccccccffffcccc00000000ffffccc0ffff0000ffffccc000000000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaaa0ffffaaa0ffffaa00ffffaa00ffffa0a0ffffa0a0ffffa000ffffa000ffff8888ffff8888ffff8880ffff8880ffff8080ffff8080ffff555500000000
  | 1, 5 => 0xfffffff0fffffff0fffffff0ffff0000fffffff0fff0fff0fffffff0fff00000fffffff000000000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00fffffcfc00000000fffff0f0fffff0f0fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000ffffeeee00000000ffffccccffffcccc
  | 1, 6 => 0xffffffffa0a0a0a0ffffffffa0a00000ffffffff80808080ffffffff55555555ffffffff55550000ffffffff33333333ffffffff33330000ffffffff22222222ffffffff11111111ffffffff00050005ffffffff00030003ffffffff0000ffffffffffff0000aaaaffffffff00000000fffffffafffffffafffffffa00000000
  | 1, 7 => 0xfffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffccccccccffffffffcccc0000ffffffffccc0ccc0ffffffffccc00000ffffffffc0c0c0c0ffffffffc0c00000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaaa0aaa0ffffffffaaa00000ffffffffaa00aa00
  | 1, 8 => 0xfffffffffffffffffffffffffffffff0fffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffffcfffcfffffffffff0fff0fffffffffff0aaa0fffffffffff00000ffffffffffccffccffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffafafafa
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1174795ce2e852d9c5d065f3
  | 3, 0, 0 => 0x8ba1cf25b49945d1e5f49ac5d688748bb0cf25948babd5a5f4b12dd645f49ac5d1e5b482b08f25f48ba890e7949ac5d165f48ba14be59497c5d205f497c5d165f48ba690e5f48ba1d0a5f4c4c5d085f4
  | 3, 0, 1 => 0x8ba2cf05f48bafd0e4448ba98f25f497c51265f48ba20f25f48baecf25f4ae45d265f4af45d1a5f49ac5d185f48bac0f25f48bad50e794b145cf65f48ba1cf05f4adc5d1e5f4ad45d165f48badd0e5f4
  | 3, 0, 2 => 0x8ba1cf25145f2c90e5f48ba1cfc5f4b12c8f25f497c5d1e5f48bb00f25f48bacd0e5f48ba1ce65f48b9d0e65f45921cf25f48bae96e5f4a9c5d1e5f48ba28f25f4c3c5d0a5f4aec5d1e5f49ab8d645f4
  | 3, 0, 3 => 0xc4c5d2657499c5d165f482a1cf25f48baf90e5f48ba1cf2504b14d5645149aca9645f48ba3cbe5248ba3cee5f4c2c5d265848ba1cf25f4
  | 4, 0, 0 => 0xb8cd62e932fad8a2e933997d5e2d0579e4beb0c6821cf25f5b145dce932fac962e934397d6c54c8ba4cbeb5b8ba4cf25f578b410e7d2fadbe2e933c97d62f04439e4beb628bac4f25f5b04d62e932fadd62e933c97d70b17499e4beb629345d885f5
  | 4, 0, 1 => 0xb145cec732facd62e873c97d66b1781310beb628ba4cf2585a04d62e932fae1e6b174797d62f17439e4bea009ac5d165f49ac5d64872facce2f0e4997d5e2d0611e4beb358ba4d145f5b15122e932facbe2e873c97d6c5174d9e4beb628bacd265f5
  | 4, 0, 2 => 0xb74d62e932fad8a2ec13c97d6b7358ba4cb0b62a345d265f5b14d62e8d2facd62e932f88162e93439e4beb355924d0e5f5b145dfe932fac5e06873c97d6c5398ba4cbeb829ac5d1e5f5a93c5a08f2fabc5a0bd4397d66b174fa4cbeafd6821cf25f5
  | 4, 0, 3 => 0xb12f964932facd62ec04997d6611749a1cbeb878ba1cf25f59545d26792fad8a2e933f17d6c5358ba50beb177621cf25f5b14962e932fad8a2e9d4997d62e873c97c9ea008b9e4be2d4a5cd62e932fad8a6b045917d66b174c21cbeb629ac5d5c5f5
  | 4, 0, 4 => 0xc4d4a2e932fad8a2e933c97d6c5355924cbeb358bb050e5f578b410e802fad8a2e932f8fd70b2f8ba4cbeb628ba4cf2515b14d4e44f232e0a2e873c97d6c5358524cbeb798ba1cf25f5b14d62e93322d8a6b174a97d6c5338ba4cbeb358ba4d0e585
  | 4, 0, 5 => 0x9abc5a08b2fad8a2ea44997d6c5348ba4cbeb177024d0e5f59ac5d7c872fad8a2e793b17d65ef168240beb629ac59265f5b14de2e932facd639174997d6cb358ba4cbeb629ac5d625f58ba1cf2772fadd66b174997d70b358ba4cbeb17439e4be2c5
  | 4, 0, 6 => 0xb14f22e932fad8a2e933c9416b31749a1cbeb8997c5d1e5f597c5e26932fad6e6b174317d6c5358ba48bea00439e4be144b145d7e9329adf26b174997d6c5358ba4cb0af1682890e7959ac5d4e932fad8a61174997d6c517431e4beb175f24d0e5f5
  | 4, 0, 7 => 0xb145d7c932fac5e04ff4997d66b1755a4d0eb869ac5d265f59acaa2e932facd62e874317d5e2d0619e4b2b358bb8ce45f578b415ead2fad8a2e932f95166b2a8ba4ca2b629ac5d0c585b14d62e972fad8a2ebc3c97d6c5355e2c8beb628bac55a5f5
  | 4, 0, 8 => 0xb14922e932fad8a6b174997171317439e4beb2f8bbc51e5f5b14d62e932fad8a5b174997d6c51770a4cbeb689ac5d265f5b14d62e752fad8a6b174994570b5a8ba4cbeb1763a1cf25f59ac5d84792fac5d0e793717d6c5368ba4cbeb629ac5cbe345
  | 4, 0, 9 => 0xb145d267d2fad8a6b173b13d62e873c97c76b62a2c5d505f58ba1cf25f262d8a6ae65897d6c5358b9d8beb6278ac8f25f5b145d70932fad8a0a933c97d66b1f8ba4cbeb62acc5d265f5ba4d62e8d2fae266b174996d6c5173c97c66b175fa1cf25f5
  | 4, 0, 10 => 0xb14d62ebc2fac5de2873c97d6c5173c97c16b669ac5d265f5af56e2e932fad8a6b17499416c5358baf0a2b358ba1d045f5b145d1e5f29ad1e2e934397d6e9338ba4cbeb2c8ba1cf25f5b151e2e932c2d8a6b144997d62e873c9c0beb629ac5d56935
  | 4, 0, 11 => 0x6821cf25f112cd62ebf4397d66b174997c7ab5e8ba4cbe595b145d12792fad8a8f174997d62e873c9c8beb6282af9265f5b145d68933cad8952a13c97d66b1749a2cbeb629acb1645f5c4d6e2e932fac5d84be4997d655268ba4cbeb6278b40f65f5
  | 4, 0, 12 => 0xb14d62eb92fad8a7b174997d6c5558ba4cbeaf150a1cf25f5b145d1a782facd62e873817d62e873c9bcbeb628ba69265f5b14d62e852fac5d0e792f9116c7358ba4cbeb629ac15265f5b15062e932fad8a6b172f8d562e8f439e4beaf1682c0f25f5
  | 4, 0, 13 => 0x90c5d26792facae2e873c97d6c4793917c9eb628ba4cf45f5a7cbe2e932fad8a85174997d6c5478baf0beb628ba3cf25f5b14d62ea32fae2a5f174997d6c5173c9c8beb629ac5d225f5abcd62e932fadc28d174997d6d53f8ba4cbeb1778af90e5f5
  | 4, 0, 14 => 0xb14d62e93302c5d0e792f91966b2a8b9c8beb628badd265f59ac5e00932fabc5be873c97d5e2be50a1cbeb629ac5d325f578b417e87222da66b174997d713628ba18beb629ac5d689358bbf10e792fad8a63174997d62e873c97c28af86821cf25f5
  | 4, 0, 15 => 0xb145d6c792fac5d0e792f9656c55e8ba14beb629ac5d1e5f5b147a2e762facd62f0e4996d62e873c97c1ab178721cf25f58ba1d0e792fad3e2e933b97d6c51e8ba4c9eb6297c5d1e5f5b5cd62e932fad8a2edc4997d6c51e8ba4cbeb629ac5ce4515
  | 4, 1, 0 => 0x8bb110e792fadca8f174997d40162591e4be989aec5d265f5b14d564872facd62ef14597d4012f8ba3cbe97a8ba1cf25f5b145d78b72fad8a6b174995d6c517499e0beb238ba1cf25f5b14d61e932fad8a6ab22f91966b174997c2ab62622c8f25f5
  | 4, 1, 1 => 0xb14d62e7c2fad8a2ebf499116c5358ba38beb629ac65265f58ba1cf25f122c5d88be4397d713538ba4cbeb2f78b411e5f5b14d62e932f2d8a2ec43c97d6ef17499e4beb629ac5d085f50045d0e792fa52a2e873c97d6d517499e4beb5378b411e5f5
  | 4, 1, 2 => 0x90c7a2e932fa8022e873c8ed2c51783a18beb679ac5d265f59ac9e2e932fad8a0ac43c97d5e2d04797ca4af16823cee5f58ba1cf25f172e16bf174997d6c5358bb10a2b8997c5d265f578b410e792fadaa6b174997d6c54a8ba4cb0a008baf90e5f4
  | 4, 1, 3 => 0x12f8ba4d1e5f5b14d62e902fad8a2f0e4297d713174997ca4b898ba4cee5f5
  | 5, 0, 0 => 0xb14d62e932f96da6af16824cc45f6b1515e2d04997da6b1749a1cd45f6a8cd5e2d04997da6af16fa4d0e5f6b145d26792f965ac4f168258f25f6b14f9e2d04997dac53a9ac5d265f6b14d62e932f9059e2d0439e4be1f6b14d62e932f901ac517499e4be0d6b149a2ef14997da6af16830d26456
  | 5, 0, 1 => 0x9ac5d26872f919a6af168279265f6b14d5be932f931801628ba4c760d5b9d8a6b174997dac5358bbc9265f69abc5c6d04997dac5126824cf25f6a7bc5a0873c97dac5358dc5d265f6b14d5e2e64997dac5358bab1265f6b14d60af14997da6b176624d0e5f69ac5da0934397d801354997c28085
  | 5, 0, 2 => 0x9abc5a0872f8159e2d0439e4f25f6003c5a0c23c97d6c53578b5d625f6b14d62e932f851ac5238ba4cf25f6b14d5f0d04997d9e2d0439e4be456b14d62e932f885ac53595c5d265f6b14d665174997dac5358bb91265f6b3cd5e2d04997dac5357c24cd45f6b13c5ae933c97dac53578b45265f6
  | 5, 0, 3 => 0x9ac5e1c934397d801628bbfd265f5c5d8a6b174997dac5358bba9265f69abc526872f86da6b1749a1d0e5f6b14d62efc4993d9e2d0439e4da5f6b14d62f0c4997dac53b78b41265f6004d62e873c97d66b17813c5265f6b14d631174997dac5358bbf1265f6bd58a2e933c97db0f629ac5d265b6
  | 5, 0, 4 => 0xb258a6b174997dac5358bb10f25f678b410e792f8b5ac5358ba71265f6b14d62e932f811ac5358ba4cbe556b145da0be4997da6b1749a1cbe0d6b14d62ef64997d800f16821cf23b50058a8d174997d401629ac5d1a5f50045d26873c97d6c55e8bbc5265f6b1519e2d05897dac5358bb61265f6
  | 5, 0, 5 => 0x3c50e792f8916c5358ba4cbe436b14d588b24997dadf629ac5d265f6c4bc5a0932f949a6af174341265f60058a2e932f8b9712f16824cee5f69ac5e1c932f9659e2d0439e4be086b14d62ed049945ac5358bad9265f6c2d8a6b174997da6b1749a1cbe596b14d62e932f921ac517789e4e45f6
  | 5, 0, 6 => 0xb14d5e2d02f8d9ac517499e4d25f6b14d62ecc4997db135878b41265f6c2cd62f074997dac5358bb41265f6b14d5e2d05524daf5629845d265f6b13c5a0a54997dac5358ba4cd45f6b6cd5e2d04997dac53578b7d265f6b13c5a0932f879ac55b9ac5d265f69ac49a0934397dac5176224cf25f6
  | 5, 0, 7 => 0x7fbc5a0934397dac5358ba4c9e466b14d62ed24997dac5358bb40ec5f697bc5a0934797d8016299c5d265f50045d265f068216f5358ba4d0e5f6b14d62e932f919ac5598bb41265f6b14d5e2d04817da6b2f78b411e5f6b14d62e932f895a6af161285265f6b14d62e932f92dac53578b3d265f6
  | 5, 0, 8 => 0xb13c5a0b13c97dac5358ba4cbe2360058a6ab24997d6c5358bc39265f6babc5a0933c97dac5358bb65265f6b134152933c97dac5358bb410c5f6b14d5e2932f86dac5358ba4d0e5f69abc5bc934397dac5356824cbe316b14d62e932f83dac54a8ba4cf25f6b14d62e932f969a8cf16824d0e5f6
  | 5, 0, 9 => 0xb14d62ed54997dafd3586341265f69ac5e0e934397dac5358bc19265f6b14d62e932f965b13629ac5d1e5f60058a6b175897d6c5358bc4d265f6006166b174997d6c5359445d265f6b14d5a0b15497dac5358ba4cbe0d6b14d62e932f80d801628ba4cf25f5823c5a0873c97dac5358ba4cbe326
  | 5, 0, 10 => 0xb14d655174997da2ef16821cf25f6b15866b174997dac5358ba4cbe4e6b14d62af14997da6af16824d145f6b14d62f046217dac54478b41265f697bc5a0873c97daf1629ac5d265f6b14d62e932f8e1ae5358bbc5265f6b14d62e933617dac53578a4cbe496b14d624d04997dac5358ba4cb24f6
  | 5, 0, 11 => 0x58a6b17499616c53978b41265f6c14d5e2d04797db133597c5d265f60058a61174997d66af16827d265f6b14d63b174997daf5629ac5d265f69abc5a0873c97da6b0278b41885f6b14d62e932f869ac5358bb41785f6b14d647174997dac5176da4cf25f6a04d5e2d04997dac5359645ce45f6
  | 5, 0, 12 => 0xb14d5e2d05717dac53f9ac5d265f6b147a2ef14997da6b176524d0e5f6b74d5e2d04997dac53591c5cec5f6b13c5a0c13c97dac517499e4be246c658a6b174997dac517622f9265f6b14d5e2d04697d9e2d049a1cf25f6b157e2e933c97da95358ba4d0e5f6b14d647174993da06f16821cf25f6
  | 5, 0, 13 => 0xb14d62ef14797daff749ac5d265f6c058a6b174997dae1358ba4cbe4c6b14d62ec44997dac5568ba4cf25f6b14d5eed04997da6b1749a1ce25f60058a2e792f8b1400f1681e4be2d5b14d62e934097dac52f8bc1d265f6afd6e6b174997dac5629ac5d265f6b14d62f014997dac53578b79265f6
  | 5, 0, 14 => 0xb152a5f174997d801359545d265f5b14d5e2d04a97dafb629ac5d265f6b14cde2d04997db03358bbad265f6b14d62e932f8e5a6af168301265f6983c5a0934397daed629ac5d265f6b14d62ed64997dac5358ba4cd25f6b14d5e2d04a17d9e2ec6821cf25f6b14e26b174997db11629ac5d265f6
  | 5, 0, 15 => 0x78b410e792f8b1b13829ac5d265f6c4d49e2d04997dac5358ba4cbe2f6b13c5a0933c97dac5298ba4cf25f6b152a6b174997da6af1683050e5f6b54d62e932f8b1801629ac5d26515b14d62ed34997db13879ac5d265f6b13c5a0932f8fdabf358ba4d0e5f60058a2ebe4997d704f16821cf25f6
  | 5, 1, 0 => 0xb14d62ef15417dac5358ba4cbe006ab4d62e934397dac53778b41265f6b84d62ef14997da6b1781341265f60058a6b174997d6c53578b51265f6b14d5e2d05897d9e2d0439e4ee5f6b14d5dad04997daeb3578b41265f6c2cd5e2d04997dac535682a5265f6b14d62e933f97dac5358bb15265f6
  | 5, 1, 1 => 0xb14d5e2d049961ac53078b41265f6b14d62e932f8a59e2d05f24d0e5f6b14d62e932f805ac5358ba4cc25f6b13c5a0a44997d801629ac5cec5f5b150e6b174997da6af1682f90e5f6b14d62ef14996dac5358bc25265f6b14d62e933897d80162acc5d265f5b145de2873c97dac517499e4be2e6
  | 5, 1, 2 => 0xb15522ed04997dac55a8bc1d265f6b14d62eda4997dac5358ba4cbe246b14d62ec24997dac53586b41265f6b14d62e932f899b132f78b411e5f6b157e6b174997dac5358bb2d265f6b14d5e8d04997dac53585b41265f6b13c5a0bf4994dac5358bbb9265f6b14d62e932f819af93578b41265f6
  | 5, 1, 3 => 0xba4d62e932f965801628ba4cf23b50058a6b175e17d6c517823fd265f60045de2873c97d6c5569ac5d265f6b14d5e2932f8ddac5358ba4ccc5f60058a6b172f8b16c5358ba4cbe136b14d62e932f825a9b358bbc5265f6b13c5a0b15697dac53c78b41265f6b14d62e932f815ab2f16824d0e5f6
  | 5, 1, 4 => 0x9abc5a0c23c97da9f358ba4d0e5f6b14d5e2932f871af7629ac5d265f6b14d62ee43917dac5358ba4cbe196b13c5a0be4997dac53588bc5265f6b15226b174997dac51778b10f25f6813fde2d04997dac53582b11265f69abc5a0ab49a1da6b2a78b41265f6b14d62e964997dac55f9ac5d0c5f6
  | 5, 1, 5 => 0x78b417e873c97dac5358bb39265f6b14d62ee94997db12f16821cf25f69ac5d26873c97dac5358ba4cbe3a6b658a6b174997dac53578b41265f69ac5d26872f915ac4f170b41265f6b15766b174997dac5358ba81265f6b14d62f024997dac53578b4126516b14d62e932f8ad9e2d063a1cf25f6
  | 5, 1, 6 => 0xb13c5a0933e97dac5359145d265f6b14d62e932f8f1ac5178224cf25f6c558a6b174997d9e2d0439e4be3b678b410e792f931801629ac15265f5b14d5e2d03b17dac5358ba4cbe2e6b14d62e934697dac5358bb25265f6b1565e2d04997d801358ba4cbe055b13c5a0792f8cd80162a3c5d265f5
  | 5, 1, 7 => 0xb14d659176217dac5358ba4cbe456b14d62e873917da6af16821d045f6b145e2e933c97dac5358bac9265f6b13c5a08f2f94dac52f8ba4cf25f6b14d62e932f81dac5358ba4cbe3e6b153e6b174997dac5358ba4cca5f6b14d62e722f919ac5358ba4cbe2260045d26792f8216c53579b41265f6
  | 5, 1, 8 => 0xb148e3d174997dac5358bb41505f678b4184be4997d801629ac5d263b5b14d62e932f861ae1358bb41265f6b14d62eb14997dae5629ac5d265f6b145d26933c97dac5358baa0be486b145dc4933c97dac53578b41785f6c4cbe2ef14997d801628b9e4e45f5b13c588a13c97dad5358bbc5265f6
  | 5, 1, 9 => 0xb14d62ec14997dac5358bbe1265f6b1cd5e2d04997db13628ba4cbe53678b411e873c97dac53578a4cd65f69abc5a0bf4397dac4f168224f25f6b151de2d04997dac5358ba4cbe026b153a6b174997dac5358ba6d265f6b154e6b174997dac5359845d265f6b14d62f084997dac517499e4be4f6
  | 5, 1, 10 => 0xb54fde2d04997dac53597c5d265f6b14d643174997dac5358ba4cbe0a6b14d5ead04997dac55578b41265f6004d62e932f8215e2d0439e4de5f6b84d5e2d74997d801629ac5c762c5b14d62ec84997db09629ac5d265f6b145d26793b97dac517499e4be2c6b14d65d174997dac5358ba4cbe0c6
  | 5, 1, 11 => 0xb14d62e934997dac5358ba4cbe4a6b13c5a08f3c97dac5358bc0d265f60058926792f8516c53578b41465f6c54bde2d04997d801628f45d265f5b14d62e932f909ac5358bc5d265f6b13c5a0793917dac5358ba4cbe2a6b14d5e2d04897daaf3578b41265f6c3cd62f0e4997dae14678b41265f6
  | 5, 1, 12 => 0xc4d8a2e933c97dac5358ba4cbe2c6b145d8e933c97dac5358ba4cce5f6b14d62e932f8599f8f16821cf25f6004d62e5f160216c5358ba4cbe4f6b14d62e933b17dac4f16824cf45f6b14d62e932f97da9f2f78b41265f6c758a6b174997d801629ac5d1e5f5b15666b174997dac5358ba4cbe516
  | 5, 1, 13 => 0xb14d62ebc2f93dac4f16e341265f6b1479e2d04997dac517499e4be3b6b145d26792f931ac5358ba4cbe476b14d62edd4997d9e2d0439e4be466b14d62eef4997dac5358baf1265f6b14d62ea14997dac5358ba4cbe526b145d7e933c97dac5358ba4cee5f68bbc526873c97da6b0078b41265f6
  | 5, 1, 14 => 0xb151e2e932f93d801628bb10f25f5b14d5e2b24997dac5358ba4cbe336b14d62e932f8399e2d0439e4be596000022e873c97d2c53578b411e5f60058a6a932f8516c5358ba4cbe286b14ce2ef14997dac53572b41265f6b14d62ec42f919ac52c8ba4cf25f6a7bc5a0933b97dad73578b41265f6
  | 5, 1, 15 => 0xb14d60aa14997da6b2c9545d265f6b14d62ebf4997db13629ac5d265f6c6d8a6b174997d9e2d06221cf25f60058a6a5f160516c517499e4e45f6b14d62edf4997dac5358ba4cbe106b14d62ec74997d8012f78b411e5f5b14d641174997dac5358ba4cbe116b14d62e933417daf4f16821cf25f6
  | 5, 2, 0 => 0x5aa6b172f8b16c5358ba4cbe5d6b145d26792f851ac5358d45d265f678b4188be4397dac4f168310f25f6006265f174997d400f16821cf25f5c3dd26b174997dac53554a85265f6005aa6b174997d6c5359645d265f6a53c5a0873c97dad4f16824cf25f6b14d6591749945ac5358ba4cbe3b6
  | 5, 2, 1 => 0xb14d62e873c97db132f78b41265f6b14d526722f93dad53578b41265f6b14d5e0d04997d801629aa4c76145b14d5e2d03e17dac5358ba4d1e5f6b14d62e932f849ac5499ac5d265f6b14d62e933917dac5358ba4cbe276
  | 6, 0, 0 => 0xb14d5a0933797c98f629ac5da0c44997dc016a9abc5a05f16358a6af16824cbe5d70058a6b177224cbed629ac5de2932f87df1362ad3c5a0932fbcd5e2d061a4d0e5f7b13c5c8d0499e4bee009abc5c6d04997da6af16824d0e6f2fb8026b176824d0e5f6ba58a6b1778a4cbee00b1515e2d04997db07629abc5a0932fb802c4f16817c580d6
  | 6, 0, 1 => 0xb15426b176824cbef629abc5a0934797dec53578b41265f0bbdfe6af16824d0e5f7b15266af16824cbef629abc5a0932f959ec53578b41265f183802c5358bbf1265f6b14d5e2d0499c8bef629abe5e2d04997dec53578b41265f13b802c5358ba4cbe1460058a6af86824cbed629ac5e0ed04997dec53578b41265f0ebd89f8f16824cf25f7
  | 6, 0, 2 => 0x58a6b1778a4c76c00b14d62ecc4997dac53578b41266f2fb802c5358bb41265f6b14d62ed06524cbee00b14d62e933517d801629abc5be932fb589e2d06624cf25f7b14d5f6f16824cbef6f9abc5a0932f921c01629ac5d265f24358a6b1778a4cf25f7b14d5e2d04997c88f629abc5a0cd4997dec53578b4126632fbd89e2d0499e4be487
  | 6, 0, 3 => 0xb14d62edb6824cbef6278b4126792f835ec4f172381a0932fbd8aad4a78b41265f7bfd8a6af16824cbef6278b4126873c97dec53578b4150932fbd8a6af16824cbe4d7b14d5e2d0439e4bef629abc5a0c64997dec5357d3c5a0932fbd8a6b1778a4cbe0870058a6b174997c8cd629abc5a0c34997dec54a78b41265f29bd89e2d0499e4be467
  | 6, 0, 4 => 0x58a6ad0498ec3ed629abc9e2d04997dc01629ac5d265f2cb58a6af1682b1265f79abc5a0cc49a1cbef62afcd62ed04997dec5358bb41265f29b802c5358ba4cbe0d6b13c5a0933c97cb2e000058a2e933c97d401629ac5e1c932fb002c53578a4cbe1b6b14ea6af16824cbef629abc5a0932f905ec53578b41265f203802c5358ba4d0e5f6
  | 6, 0, 5 => 0x4d62ef14997c10d629abf9a0933517dec5357e3c5a0932fb802c5354997c48226b155a6b176824cbef7ab13c5a0933c97dc016278a4cbe2406b58a6af16824cbe1470058a6b176817c58c00b14d5265f1207dac5358bc11e2932fbd8a6b3278b41265f7b14d5e2e46824cbee00b14d624d04997d8016278b41263b06b5cec53578b41265f7
  | 6, 0, 6 => 0xb258a6af16824cbef629abc5a0c43c97dec53578b4138932fbd8a6af16824cbe047b14d5e2d04997caaf3578b4126872f835ec5357b3c5a0932fb801e2d049a1cf25f6b14d65f1778a4cbef8bb14d5e2d04997dec53578ba9a0932fbcd5e2d049a1d0e5f7b14d618f16824cbee00bd58a6b174997d8013578b410e792fb002c53591c5d265f6
  | 6, 0, 7 => 0xbd4d5e2d049a1cbef629abc5a0932f919ec53578b41265f12bd8a6af16824cbe4b7b13c5a0933c9a4bef629abc5a0cc4997dc01629ac5d88932fb58a6af168341265f7b14d5a0c454a4cbef7ab14c1e2d04997dec4f16831126792fbdbec53578b41265f700589e2d04997c5cd3578b4126872f965ec5358bc5de2932fbd8a6af16824cbe487
  | 6, 0, 8 => 0xb14d5e2d04997cb2e000058a6b174997d713629abc5a08f2fb802c53578b41625f60058a6ad054a4cbed629abc5a0932f835ec53578b41265f01b802c4f16824cf25f6b14d61cf16824cbee00b152a6b174997dac53578b4126872fbd8a6b176824cbe1f7b1529e2d0499e4bef629ac5de2932f93dec53578b49a0932fb801e2d04997c1a086
  | 6, 0, 9 => 0xb13c5a0933c97c48f8cb14d5e2d04997dec4f1683117c932fbd2a6af16824d0e5f7c4cd65ef16824cbee00b14c1e2d04997daf5629abc5a0932fbd8a6af16824cbe1a7b14d646f16824cbef629ac41e2ec4997dec53578a4cbe1f0dbd8a6b1778a4cbe2c7b14d608f168310bef629abc5a0932f8e1ec53578b41266c2fbd8a6af16ab41265f7
  | 6, 0, 10 => 0xc0cd5e2eb6824cbef76b14d5e2d04997dec53578b59a0932fbd8a6af16824cd25f70058aad358ba4cbec00b14d5e2932f85180000b14d62e5f162d8a6af168311265f700589e2d03c97c58d629abc5a0934097dc01629ac5d265f123002c535793c5265f6b158a6af16824cbef629ac05e2d04997dec53f9abc5a0932fb802c55f9ac5d265f6
  | 6, 0, 11 => 0xb14d5e2d04997c02f62a1cd5e2d04997dc0162acbc5a0932fb58a6b1778b1d265f7b13c5a0933c97c5cf629abc5a0932f801ead3578b4126872fb802c53578b41265f6b14d5e2d0499fcbef629ac5e08d04997dec54a9abc5a0932fbdaa6af16824cbe2c7b14d5e2d36824cbee00b13c5a0be4997dac54a97bc5a0932fbdf6c53578b41265f7
  | 6, 0, 12 => 0xb14d62eec6824cbef629abc5a0933317dc01629abc5a05f16358a6b2c8bbc5265f7b14d5e2d04997c12f629abc5a0932f815ec53578b41265f123d8a6af168309265f7b14d62ef14997c76f629abc5a0932f899ec5358bbc5265f263d8abf3578b41265f7b14d5e2d065a4cbef629abc5a0932f819ec53578b41265f14be26c5358bbc5265f7
  | 6, 0, 13 => 0xb14d5e2d04997c74f6cb14d5e2d04997de6af16824d0e5f22bd8a6af168281265f7b14d604f16824cbef629abc5a0932f8adec5358bbc5e2932fbd3e6af16824d0e5f700589e2933c97c48d7bb14d5e2d04997dec53578b41265f0cbd8a913578b41265f700002c5358ba4c76b82b14d62ed04997dec53578b412c932fb802c4f16824cf23b6
  | 6, 0, 14 => 0xb145de2d0499e4bee00b14d65f174997dac52f78b4126792fbd8a6af16824cbe077000026b174997c10b62a7cd5e2d04997dec53578b41265f113801e2d0499e4be086b14d5e2d04997c78f8ab14d5e2d04997dec5358bbc526722fbd8a6af16824cbe2e7b14d5e2d064a4cbee009abc5a0932f815ac53578b419c932fbd8a6af174b41265f7
  | 6, 0, 15 => 0xb14d62ef14997c28f629abe1e2d04997dec5358bb41265f263e26c4f16824cbe537b153a6af16824cbee00b14d62e932f93dac5539abc5a0932fbd8a6b3078b41265f70058a6af14997c48c00b14d5e2d0498edac53578b41265f0c3d89e2d049a4cf25f7b14d5e2d05417c90f6278b89a0933c97dec5358bbc5266f2fb802c5358bc5d265f6
  | 6, 1, 0 => 0xb14d606f16824cbef629ac5de2932f919ec53578b41265f213d8a6b1778b41265f7b14d62ef1499a8bef629acbde2d04997dc01629abc4be2c12358a6af16824cbe0a7004d5e2d04997c10c00b14d5e2d01d8b1ac53578b4190932fb802c5358ba4cbe2c6c258a6af16824cbef6278b4126793b97dec4f16824cf25f163d8a6af168305265f7
  | 6, 1, 1 => 0xb14d5e2d04997ca4f629abc5a0933b97df136278b4126792fbd8a6af16824cbe2c7b14d6471778a4cbee00b14d62ec74997dac4f16831d26792fbd8a6af16824cce5f7b14d5e2d04997c9ef629abc5a0932f97df1d629abc5a0932fb802c53578b411e5f6b14d5e2d74997c98e000058a6a932f8516c5599abc5a0932fbd8a6af16824d265f7
  | 6, 1, 2 => 0xb14d5e2d0499a0bef629ac5df8d04997dc016278b4188792fb58a6af16824cbe337b14d5e2d04997c1ce00003c5a0873c97d6c53578b41265f143802c5359645d265f6b14d5e2d06217c8ce00b14d62e932f8edac4f16824cf25f1dbd8a6af16824cbe477b14d5e2dd6824cbef629abc5ded04997dc0189b14d62e932fb58a6af168285265f7
  | 6, 1, 3 => 0x6265ef16824cbec00b54d5e2d04997dac535963c5a0932fbd8a6af16824cbe3b70058a6b17499c8bed89b14d5e2d04997dec53578b7da0932fbd8a6af16831d265f7
  | 7, 0, 0 => 0x58a953578b41265f70058a6af168311265f7005eac53578b41265f70058a6af16824cbe5970000001629ac5d265f50058a6af16824cbe0d700002c4f16824cf25f60058a6af16824d0e5f70058a6af16824cbe4670058a6af168331265f70058a6af16824cbe4870058a6afc78b41265f70058a6af172341265f7005fec53578b41265f70058a6af16824cde5f700002c5358bb41265f6
  | 7, 0, 1 => 0x58a6af16824cbe3b700626c53578b41265f70058a6af16831d265f70058a6af16824cbe2c70058a6b1778b41265f70058a6b2f78b41265f7000026af16824cbe08600002c53578a4cbe24600002c53578b41263b600002c53578b40be2c60058a6af16824cbe24700002c53578b41265f6
  | 8, 0, 0 => 0x2c53578b41265f6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 256), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12543

theorem PEqualNP.Outside.L_meta_12543 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242912 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242912 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12543.mainG PEqualNP.Outside.L_meta_12543.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12543.CG, PEqualNP.Outside.L_meta_12543.CG_mono, by
      have : PEqualNP.Outside.L_meta_12543.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12543.CG_eval⟩
