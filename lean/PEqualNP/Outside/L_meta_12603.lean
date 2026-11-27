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
namespace PEqualNP.Outside.L_meta_12603

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 6, 6, 6, 6, 6, 6, 6, 7, 6, 6, 6, 11, 6, 13, 14, 15, 6, 17, 6, 19, 6, 21, 22, 23, 6, 25, 26, 27, 6, 29, 30, 31, 6, 33, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 11, 7, 13, 14, 15, 7, 17, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 11, 11, 11, 6, 7, 11, 11, 11, 11, 11, 13, 14, 15, 11, 17, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 33, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 13, 13, 13, 6, 7, 13, 13, 13, 11, 13, 13, 14, 15, 13, 17, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 14, 14, 14, 6, 7, 14, 14, 14, 11, 14, 13, 14, 15, 14, 17, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 6, 7, 15, 15, 15, 11, 15, 13, 14, 15, 15, 17, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 17, 17, 17, 17, 17, 17, 6, 7, 17, 17, 17, 11, 17, 13, 14, 15, 17, 17, 17, 19, 17, 21, 22, 23, 17, 25, 26, 27, 17, 29, 30, 31, 17, 33, 17, 35, 17, 37, 38, 39, 17, 41, 42, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 58, 59, 17, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 6, 7, 19, 19, 19, 11, 19, 13, 14, 15, 19, 17, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 33, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 6, 7, 21, 21, 21, 11, 21, 13, 14, 15, 21, 17, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 22, 22, 22, 6, 7, 22, 22, 22, 11, 22, 13, 14, 15, 22, 17, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 6, 7, 23, 23, 23, 11, 23, 13, 14, 15, 23, 17, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 6, 7, 25, 25, 25, 11, 25, 13, 14, 15, 25, 17, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 33, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 26, 26, 26, 6, 7, 26, 26, 26, 11, 26, 13, 14, 15, 26, 17, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 27, 27, 27, 6, 7, 27, 27, 27, 11, 27, 13, 14, 15, 27, 17, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 6, 7, 29, 29, 29, 11, 29, 13, 14, 15, 29, 17, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 6, 7, 30, 30, 30, 11, 30, 13, 14, 15, 30, 17, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 6, 7, 31, 31, 31, 11, 31, 13, 14, 15, 31, 17, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 33, 33, 33, 33, 33, 33, 6, 7, 33, 33, 33, 11, 33, 13, 14, 15, 33, 17, 33, 19, 33, 21, 22, 23, 33, 25, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 42, 43, 33, 45, 46, 47, 33, 49, 33, 51, 33, 53, 54, 55, 33, 57, 58, 59, 33, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 6, 7, 35, 35, 35, 11, 35, 13, 14, 15, 35, 17, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 37, 6, 7, 37, 37, 37, 11, 37, 13, 14, 15, 37, 17, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 38, 6, 7, 38, 38, 38, 11, 38, 13, 14, 15, 38, 17, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 6, 7, 39, 39, 39, 11, 39, 13, 14, 15, 39, 17, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 6, 7, 41, 41, 41, 11, 41, 13, 14, 15, 41, 17, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 42, 42, 42, 6, 7, 42, 42, 42, 11, 42, 13, 14, 15, 42, 17, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 33, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 43, 43, 43, 6, 7, 43, 43, 43, 11, 43, 13, 14, 15, 43, 17, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 6, 7, 45, 45, 45, 11, 45, 13, 14, 15, 45, 17, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 6, 7, 46, 46, 46, 11, 46, 13, 14, 15, 46, 17, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 6, 7, 47, 47, 47, 11, 47, 13, 14, 15, 47, 17, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 6, 7, 49, 49, 49, 11, 49, 13, 14, 15, 49, 17, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 6, 7, 51, 51, 51, 11, 51, 13, 14, 15, 51, 17, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 6, 7, 53, 53, 53, 11, 53, 13, 14, 15, 53, 17, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 6, 7, 54, 54, 54, 11, 54, 13, 14, 15, 54, 17, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 6, 7, 55, 55, 55, 11, 55, 13, 14, 15, 55, 17, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 6, 7, 57, 57, 57, 11, 57, 13, 14, 15, 57, 17, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 58, 58, 58, 6, 7, 58, 58, 58, 11, 58, 13, 14, 15, 58, 17, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 59, 59, 59, 6, 7, 59, 59, 59, 11, 59, 13, 14, 15, 59, 17, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 6, 7, 61, 61, 61, 11, 61, 13, 14, 15, 61, 17, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 6, 7, 62, 62, 62, 11, 62, 13, 14, 15, 62, 17, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f0000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f111511151115173f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c00000000000000000eeeaeeeaeeeae8c0000000000000000000000000000000000000000000000000eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0eeeaeeeaeeeae8c0

def cMZZ : Nat := 0x111511151115173f000000000000000000000000000000000000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f0000000000000000111511151115173f0000000000000000111511151115173f000000000000000000000000000000000000000000000000111511151115173f0000000000000000111511151115173f111511151115173f111511151115173f00000000000000000000000000000000111511151115173f111511151115173f111511151115173f111511151115173f111511151115173f111511151115173f

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
  | 3 => 18
  | 4 => 207
  | 5 => 586
  | 6 => 382
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x971769ae848f68433bc682d6
  | 3, 0 => 0xfdf51218f8514ac5cbc13dcfca672dd0b52c2cabb1212d0da4fcb6d798061006893f54aa85a5bd7b7f7679bd7476fbb8731dbc10676950156764cf684df0634f2dd91e87065128df
  | 4, 0 => 0x4526e7a944abbdb1446030d943d25a62428b3558427309d3421229d940d833953c34010d3ba872d73b589d9d3a5cbacf39a1978d388bd3e435a71ea93306c942317507002e4f61c82e21f2652db1e55f2d9e60992d9716972bc71a5b2b85a3df2b04b08e28f5951e282dd0392689c7e425d2c75a24d7af9a24d40692225b27d120f5e29c202112441e6260b11c3e8d4c1c0ddf0c1bbd20781b4da2e11a819cde1a79a9d3198aeaef18c28aad187ace9316590fc613413e7312a0151e12008cd61110f565100779900fb85c740f837b050eb77d590c80b6020ba076c80b692a730ab9f28d0a45eec80860cbc806d0d7020678346605476b8804cdcb46021b5c28
  | 4, 1 => 0x80e632a7806520157e110ace7b3d0b5579f16b1f7973d87178eed07578a9b12377cda87777bf3344770e944b768d15e3766e7454766746067600a74275bf3c6e753fac81753f54c074a71275747c0e9b7473f2b274727853742a501d738f596d72050257719e64b97170ae8b715c30246abb625c6a63754a68bc6cc16739e4206449b975644731f663a38933612141c7611c66d15f092c835ecc53045c550e3059cd9de0597701b1593f106058f597ef5899d1e1585d481c5823363b5618662555f7a3e255a9e80d52ed400852b56a6a524a2ad750b43e164f07bccc4ec1cd254e897d024d3f0a7e4c1b063b4c0a21d84ac1e6c7493e5a7a46362e9945ca2472
  | 4, 2 => 0xde3afdf2ddd7e35ddd9e2e72dc66699bda87e1f5da559039d6bf8d32d5fb79e0d592395dd29389e8d27249a7d178ae09d09b0369cff55bb1cb4fe1f2cabbeccfc94511dcc3eec3f2c3ad2847c2bc25dac2359c91c0cf6213c0a3e4d9bfda1d86bf303a27be93d283bc110ff4b60d3273b5c3ba02b4b39da6b489c7cbb17ccdf1b14bd3d1af1599a4aef7a8d1aa2fe45da978e3d3a90c4049a3725cb3a36e90cfa329c976a2cc68aca25a05ef9ef5b9f59d02ecbf9a2aff10996090ea9902232097507a1995be9ca7955052b89498049d93bb43f792e4175f91342f60912156cc910f831a904690aa8f80cbb88852343087292fe8869463d3867637838269ba66
  | 4, 3 => 0xfe91e4fbfd7e4b78fcc95408fa712644f9bd91ecf90d854af4e5659eedf23d18ed962b90ec8365e5ec1fb8d7e6df9e92e0cef9eae074356fdfe33d34
  | 5, 0 => 0x16bd4c7d167e82c4160dd21e1546a5ff148057be1404a89c13b45a121397725a1367fb7b132c3b18132240dd12f0643d12ea7f57129135bd121ea5a8119337221162c09c10eac9d310da9d9c109d5381108108df1066072c0fb6cf460f42cb810ebc13710d4fced30c5a7b5e0bcdb3bb0bab507a0ba076c80b83adf90b63f7170aebed040ab9f28d0a58944b08f8f9390862b4b107ed89f50783572e076fd78207301e46071838e10709226006b2494605fe2ed70599a0aa04e7639304dc7d5004dbf6c504cdcb46048e8de9047dee6303db9ced03ab442f038ec1b9037a53b7027b28360267b73601e20ff301c630c60186cee60132d80d00f2ed15005bd450
  | 5, 1 => 0x2a627e662a389a2b2a17c29a29d48c532945d6ee285aa650283b61392832c99e281d52a02758048a26aab3632689c7e425f2bf5525dbdac325d2c75a25c46739257ea6fd257d99d3251deefd24d221072407d61323b5b6d3239f0f6b23829b622372c9bd2333c2cb22e12ede227dc3112217938321f9ffc2213b6a052135ed0d21266b66210abbc52107e7ee20b9fd3120a679f1206aee6720669dc2203f092120357a491fee10241f7e79971f76b5ac1edc46ac1e87c7a81e6c434e1dbf67661d86b8471d77ab4c1cda3f751c34aed51bc775e81bba259e1b50a7be1a7df5281a3e67be19fa8e1819d79fc919c30fbf18dc8b8418c6af80185b63cf1740e184
  | 5, 2 => 0x4130ddc64129623940a54e80407e454f4019f708401987c83fa52e103e1a12b33e1604993d88b09d3cfc6cf93c98595a3c5055c43c34010d3c21cfb43c16b5143aaf098a3a5df4163a5cbacf3a4cfd2c3a0f1857394e842639274985390d11e438edd581381dece7380f15303803a5fb3793b4b33750911f36a32e3a3671e3b9365b75b53592e58234bf56f934ac60db347ac1263455bded33f5605133cfb89a334c3e81331413673306c94232e3c45e32aec2183293f350327e77af31877d3b3157d64c30f4f38d305d4aef304f63012fdd310e2e76ba092e73d7802e6591ff2dd9ff872d2aacf22c9cc9502bb466162b82db782b04b08e2ad193582acfa413
  | 5, 3 => 0x5819449357b2472357a8771c5780cd425746ab9556c521795633bd3955b75993557fdc3e552db3a354d573ed549f1ee754924b6e541fb0fc541f037f5404998553bea9de53ab79b1538659bb5362e3a452ab1dc852823d755278e8585168e1ef5117e2f45106fe9150f7b76c50df01b550cc6c8f4fbec3804ef9b6494ebebfc94e3b693b4d250b6c4ca72a634ca4d0184c007bd84beeee114ba0883d4b3c9fe54b05d1ea4ac925404a569a044a02379a49e3a87149cd4a3e49a89a6a496c9936495d0d92494512e24904b05048d02b7448ab7325487f53c64868dac6481a6860476fe68c47600b4345d5104e45d3fa0b44b58bcc4209586441cf0b1b417bcd49
  | 5, 4 => 0x6f43dabe6f3a3e796efeb5196ec742a36e59b2096de0f94e6dd7042b6d9413c56d20d39b6bfcf0a36b92b1326b4aa12a6b0448c96946962e68a065ec688df10d686552216761a957671830e666fd227766dc281666baae226675f8d2661e1e806619438a64f599d364ee67a464cf629364b8675964b175c26415f36563fb8ac263a38933631736d9630b3428630a6268621641526179e057616248346144e2dd612141c76106f89760f383915fcd49cc5f85c0f35f2f5f0e5ea515d45e46d45a5e0c101a5df459445df274a85db785535d96ae9a5cd321a85ca0d8dd5c4476805be35fbd59d9df49593f106058f597ef58ea5ab45890c2a5581fe8d3581c29d2
  | 5, 5 => 0x873ee84c8722c6e9870c359886cc4a1a86b1969b868b0de18561fcce85405177850da6e384d35cab843def2b83d181c9831db3ea8301a1af8245894d821e6f8a8174b9bb80bc541e8039e80e7fe8974d7fcf6eb97f46c5837ef1e3247eee47d87ddd32237da68ddc7d096a8c7cbc0ffd7c68705a7c5ac7ba7b89f29c7b819d457b4938747b3d0b557b392a807a3c893a7a130bb479f16b1f79e253d179a3ef2e7978eb547909f82a78f3f96e78a9b123785c7fda784a175d783a897e77cccec97701df1076d3476b768930d7766d8b4475d4396775bf3c6e75bc4bc675abf1967383eac273815cd5728b1c0c71c6222a714544577108684e7006c5786fca7c4a
  | 5, 6 => 0xa61108f5a5b99d31a586e74fa4ab65ffa3e37113a33f3b4ca2410b53a1dddceea0f5c7dca0b783289f27dbc99f2262609eff2b769eb65b349dfeffd9999508ef9902232098b820b098b5325c98abdad897e0f41897d5b96597d4815f97d342f0972aa2cf96d4949a96745f7c961e3385960c5fd39593ce579553e285952b4d2d94c491df9425111793bfcd0593bb43f792d78a3791b81d43911fd94390fa045190e0f6598fb6e4368f4ffca88ed4819a8eaadffc8e2a6ed28d9960648d4f10e98d34811e8cf32b728cf069f28cead9338c8569238c45ec8b8c260ca18b91408c8b73143c8adc90638a2275a0895fa44c894e932088140416876b68bc8754602d
  | 5, 7 => 0xca22fdabca1f1507c9d81259c91bc4a5c8aa0500c8680ba4c866cd35c82b5905c732794ac5b4ff79c4d6fa3fc44aaadbc433fee4c3eec3f2c390af3cc24b0623bfda1d86bf109c7ebe60b89fbdda3446bcd976d0bc68efb7bc35fc05bba2a34cbb04fc62bac096bbb9b07a5fb9a984b1b98fb645b93bb543b8524cc7b83bed6db7f3e872b757018fb6144422b5b6ea2bb457a4a6b412765db3f4858ab3bae29ab29a1450b1fbd5b6b1b66fbbaf1599a4aeee27f0aea6be10ae091d02ac6c7317ac5a338eac2ab7c1abecfad5ab8e8069ab7515d5a9b43671a99ccf64a8c23408a8631869a826a62fa825b14ca7c94565a756e2a8a73f9b88a72a5fcda724bc17
  | 5, 8 => 0xf6820588f5146ba1f3a2b5cbf38045caf2ef19d1f19683c0f118eb13f102ace4f08b4ccbf07a3365ee497a78ed193fdeecd9b68bec903e1aec543786ec0c9f45ebffc02febab1ed8eb57a7d5e975926de93202bce64cdbffe60c6255e582ce92e5286417e4822f3ae3840f63e1fbedb7e1960e39e09be864e033f9dbdfc94e30dfbd4b1fdf84beaedf224fcbdec689b5de60348dddeb3301dcc8ad2bdc8090e5dc444249dbbc69ebda87e1f5d808fa4ed76f2660d6758ac2d52d7be8d45f78ccd401aed1d4006e09d34e641dd3087c15d27249a7d262e522d2020ae5d1d48ce2d0dd09cfcfcea738cfb8c988cf79b462cf5d4db7cecb4cb6cc11a199cae51e34
  | 5, 9 => 0xffeaeca6fe0a6203fcc95408fc1f8f67fba0a905fae0182bf9e3fd3df9e24257f90d854af7cb9140
  | 6, 0 => 0x25a356aa2567cb2025542877253be5da24eaecdd239f0f6b23829b622320c4ca2283950021318b8e20c452a120b702572019032f1f7ad1e11f3b44771dc38c391d2a2feb1c6de2371bba29361a7d14551a4382b81911f0bd19018555178e1276171b8261169013db15e7a68c13b8f02a1367fb7b11575817109d538110808ab2104cf4d10fb6cf460d7f0d680cea66ae0ce1d3d70c6cb43b0c5a7b5e0c0b27b10c05ff190baf25ff0a6dff4109d95a09097acb1c08a820e808773070073e2a7005ee2a3c057a117804e7c96404a8ef29049a67e602e9474901fe95f201c630c6019f4bad0148430301447c8301349c6c0132d80d009d85c3006547760064863a
  | 6, 1 => 0x4312e152429d5a1d427856e441953613414d327d4130ddc6411391cd401987c83fabe6433f5ad0cf3f178c843f0bf5103ea9c5673e4b60df3d1ac9a03d0bf1e93c9670773c4d6dd83c34010d3b58526e39779ddf39529aa638cc95533810f02036d62cf536a32e3a368459f43654b30535f1d04635ea72b6355a27a8347ac1263455bded3370b43933626eb8331b6bc231c1a86231bd4b9e31a534593199a60930f4f38d30b142cf307fb8312fce70112f3576e42f149f532e73d7802e4894bf2e42b3a72d5783092d2fa6572d1a2f592b5b17e02b5504e82a7b83b629cefdc02904b2cc289bec24287f997a287f781b281d52a0277a9fca2714703c26f6dc7b
  | 6, 2 => 0x675eb1f767131e0b6676bd10663ec2c96603d55065f0604a64d427d9642c3bc76415f36561cffe6161a45308619db59660e03c76609b814f5df274a85d77377b5d1989755d19068b5d16214c5c7da9fb5bc1fe325b47a4635b3099f25a2a905c59d250a6598f282758ea5ab45890c2a5587932fb581c29d257a7fa81577f1a2e5775c5115665bea855f4942553f693025336f74052ab1dc85278e8585221e82551a4071c50ebcaca50cc6c8f50397c9e4f9d83d74f5376bd4eff14534e3c20bf4e018d094dcd082d4da84fde4d65b77f4d250b6c4c6daf064a569a044818cbdf4706351d46cbe7d44678aa0245d3fa0b45906ad6451664814454ca764316ef6c
  | 6, 3 => 0x91e7b5ec91620f2e90fa04518fd96d1c8d34811e8c513ce68c3bc5058c1fa3a28b87ea9a8a0a839c89d0396488ce5e82881a90a38804ecc887ccdeb3870c359885b930d783f6d25e83eebfdd82da0edc80dae6068039e80e803607397f0fe86d7eee47d87edf308a7e06d4e37df0d6277da68ddc7d5cd7707d595c937d3766377ce9db9a7cc9ab827b860d907b6f702d7ad1162079e253d1785c7fda7642211075d439677503a23174371b3273c41f5c72d3e0e47290f07e72388c5c722af661721db05470f9cd5c70ac96996f3a3e796ec742a36d622eda6bf9ff306bd904cf69eb445d69cc3f4c69b5441269ae527b6912d01e68f8677b68a065ec68073f21
  | 6, 4 => 0xc132d8bec1230ec0c09f8005c089c884be8c92febd4f2980bd38ca26bcf0c52bbcd976d0bc53de48ba8f0c0eba7ccc85b98fb645b954815fb8b7bf53b6f8b26fb6b34c74b412765db1694fd0b1571047b0e9d78eb071f28eb063a44aae99ac1dadbf10c1ac6c7317ac5a338eac3c7841aa83c408a9a842b8a8e04dcca8c23408a73de80ca6ce73cfa5fd3b55a3fc082fa3b337eda2410b539eff2b769e91e5a89dfeffd99da8b7919cd2961e9cd01fa99b571a159a90ab109a50bf3e9a2829e69921edd098e2886398bca9be98b820b098abdad896b4f9fc961cb5fc95ddd312952ece8f93a7bcb5936ba55593274b8b92963d1d92315dd791f0082b91ed46ab
  | 6, 5 => 0xffdcf4e4fee0d9f6fcc86df9fa11485af89f9284f7cb9140f5ff899df5882984f18d1ad3f118eb13f1097bfef102ace4f0fc9ce8f0a7fb91f054848eeb57a7d5eb49b8b8ea7fab4bea2540d0e97f0bf3e880ec1ce530d694e4c62ae9e4ba27d8e41f2c84e3c3666ee3840f63e2e80fbae1c589e4e17d6d9edfc94e30dd05d707da2a58a1d95c5585d8fe8b8ad8fd4ac2d84b40d6d808fa4ed80558ced6fee79ed5d9e688d52d7be8d4cb83f1d476911bd3087c15d2020ae5cfcea738cf1fda64ced4ef12ce18a15ecd63a9eecb1d7036cab1dc32c9d81259c930db9dc91bc4a5c8680ba4c747e2dcc729fe29c6dba316c40d7937c165cc70
  | 7, 0 => 0xf5ff899df054848ee4c62ae9dd05d707d80558ced6fee79ed4cb83f1ce18a15ebe8c92feb1571047adbf10c1a73de80ca3fc082f9da8b7917edf308a7d595c937ad1162073c41f5c6912d01e57a7fa815775c5115221e8254a569a04451664814130ddc63c34010d39779ddf39529aa63370b4392d1a2f592b5504e8289bec24287f781b1157581701484303
  | 8, 0 => 0x4130ddc6
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff00ff0000000000f0f0f0f0000000005555555500000000333333330000000000ff00ff000000000000ffff000000000000ff00000000000000f0f0000000000000cccc000000000000aaaa000000000000555500000000000033330000000000000f0f00000000000000ff0000000000000000
  | 0, 1 => 0xff0000ffff000000f000f0f0f0f0f000f000f000f0f0f000f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f00000000ffffffff
  | 0, 2 => 0xf0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f000000000f00ff000f00ff000f000f000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00000000
  | 0, 3 => 0x33333333ffffffff333333333333ffff3333333333333333333333333333000033330000ffff00003333000033330000330033003300330030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fff0fff0fff0fff0fff0fff0fff00000fff0fff000000000f0fffff0f0fffff0f0fffff00000000
  | 0, 4 => 0x555555550000000055005500ff00ff00550055005500ff0055005500550055005050f0f05050f0f0505050505050f0f0505050505050505044444444cccccccc444444444444cccc44444444444444443f3f3f3f3f3f3f3f3f3f3f3f3f3f00003f3f00003f3f00003f003f003f003f0033ff33ff33ff33ff3333ffff3333ffff
  | 0, 5 => 0xa0a0a0a0a0a00000a0a00000a0a00000a000a000a000a0008888888888888888888888888888000088888888000000008800880088008800808080808080808077777777777777775f5f5f5f5f5f5f5f55ff55ff55ff55ff5555ffff0000000055555555ffffffff555555555555ffff55555555555555555555555555550000
  | 0, 6 => 0xaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa00000000aaaa8888aaaa8888aaaa0000ffff0000aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0
  | 0, 7 => 0xc000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafafafafafafaf0000afafafaf00000000af00af00af00af00aaffaaffaaffaaffaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaa88aaaaaaaaaaaaaa00aaaaaaaaaaaaa8a8aaaaaaaaaaaaa0a0
  | 0, 8 => 0xcccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00ff00ff00cc00cc00cc00ff00cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000cc000000cc000000c8c8c8c8c8c8c8c8c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c00000c0c00000
  | 0, 9 => 0xccccccccccccffffccccccccccccccccccccccccccccccc0cccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888cccccccccccc0000ccccccccccc0ccc0ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00ccccc0c0ccccc0c0cccc0000ffff0000cccc0000cccc0000
  | 0, 10 => 0xececececececececececececececccccececccccececccccecccecccecccecccec00ec00ec00ec00eaeaeaeaeaeaeaeaeaeaeaeaeaeaaaaaeaeaeaeaaaaaaaaaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0e0c0e0c0e0c0e0c0ddddddddddddddddcfcfcfcfcfcfcfcfccffccffccffccffcccfcccfcccfcccfccccccccffffffff
  | 0, 11 => 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeecccccccccccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceecceecceecccccceecceecccccccccceeaaeeaaeeaaeeaaeeaaeeaaeeaaaaaaeeaaeeaaeeaa0000eeaaeeaaaaaaaaaaeeaa0000eeaa0000ee00ee00ee00ee00ee00ee00ee00aa00
  | 0, 12 => 0xf0f0f0f000000000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f000f0000000f000f00000000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeecccccccc
  | 0, 13 => 0xf1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f3f0f3f0f3f0f3f0f0ffff00000000f0f0f0f0fffffffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0f0f000f0f0f0f0f0f0e0e0f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0a0
  | 0, 14 => 0xfafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafaf0faf0faf0faf0faf0faf0faf0f0f0faf0faf0f0f0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f3f3f3f3f0f0f3f3f3f3f0f0f0f0
  | 0, 15 => 0xfcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcf0f0f0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fcf0fcf0fcf0f0f0fcf0f0f0fcf0f0f0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf0f0f0f0fafafafa00000000
  | 1, 0 => 0xff00ff00ff00aa00ff00ff00ff000000ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff0000000000ff00fc00ff00fc00ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefefefe0000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0
  | 1, 1 => 0xff33ff33ff33ff33ff33ff33ff33ff00ff33ff33ff00ff00ff11ff11ff11ff11ff0fff0fff0fff0fff03ff03ff03ff03ff00ffffff00ffffff00ffff00000000ff00ff00ff00ffffff00ff00ff00ff55ff00ff00ff00ff00ff00ff00ff00fc00ff00ff00ff00fa00ff00ff00ff00f000ff00ff00ff00ee00ff00ff00ff00cc00
  | 1, 2 => 0xffaaffaaffaa0000ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff88ff88ff00ff88ff88ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff50ff50ff50ff50
  | 1, 3 => 0xffeeffeeffeeffeeffeeffeeffee0000ffee0000ffee0000ffccffccffccffccffccffccffccff00ffccffccffccccccffccffccffcc0000ffccffccff00ff00ffccffcc00000000ffccccccffccccccffc0ffc0ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaa
  | 1, 4 => 0xfffaff00fffaff00fffaf0f0fffaf0f0fffa0000fffa0000fff0fff0fff0fff0fff0fff0fff0ffc0fff0fff0fff0ff00fff0fff0fff0f0f0fff0fff0fff00000fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0ff00fff0ff00fff0ff00ff00ff00fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff00000fff00000
  | 1, 5 => 0xffff3333ffff3333ffff1111ffff1111ffff0fffffff0000ffff0f0fffff0f0fffff0f0fffff0000ffff00ffffff0000ffff0000ffffffffffff0000ffff0000ffff0000f0f00000ffff000000000000fffcfffcfffcfffcfffafffafffafffafffafffafffaff00fffafffafffaf0f0fffafffafffa0000fffafffaf0f0f0f0
  | 1, 6 => 0xffffcc00ffff0000ffffc0c0ffffc0c0ffffc000ffffc000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffff0000ffffa0a0ffffa0a0ffffa000ffffa000ffff8888ffff8888ffff8800ffff8800ffff8080ffff8080ffff5555ffff5555ffff5555ffff0000ffff3f3fffff0000
  | 1, 7 => 0xfffffafafffffafafffffafaffff0000fffff0f0fffff0f0fffff0f0ffffc0c0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0c0fffff0c0fffff000fffff000fffff000ffff0000ffffeeeeffff0000ffffeeee00000000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00
  | 1, 8 => 0xffffffff50505050ffffffff33330000ffffffff00ff00ffffffffff00550055ffffffff0000ffffffffffff00000000ffffffccffffffccffffffaaffff0000ffffffaa00000000ffffff00ffffff00ffffff00fffff000ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffefeffff0000fffffcfcfffffcfc
  | 1, 9 => 0xfffffffff0c0f0c0fffffffff000f000ffffffffeeeeeeeeffffffffeeee0000ffffffffeeaa0000ffffffffccccccccffffffffccccc0c0ffffffffc0c0c0c0ffffffffc0c00000ffffffffafaf0000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a00000ffffffff88880000ffffffff55555555
  | 1, 10 => 0xffffffffffff00ffffffffffffff0055ffffffffffff0000fffffffffffa0000fffffffffff0fff0fffffffffff00000ffffffffffee0000ffffffffffcc0000ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00ffffffffff000000fffffffffcfc0000fffffffff0f0f0f0fffffffff0f0f000fffffffff0f00000
  | 1, 11 => 0xffffffffffffccccffffffffffffcc00ffffffffffffc0c0ffffffffffffc000ffffffffffffaaaaffffffffffffaa00ffffffffffffa0a0ffffffffffffa000ffffffffffff8888ffffffffffff8800ffffffffffff8080ffffffffffff5555ffffffffffff5050ffffffffffff3333ffffffffffff1111ffffffffffff0f0f
  | 1, 12 => 0xfffffffffffffffffffffffffffffff0ffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffcfcfffffffffffffafafffffffffffff0f0fffffffffffff0c0fffffffffffff000ffffffffffffeeee
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1c2469d4f868d391d493c723
  | 3, 0, 0 => 0xd6d253c724e0a2504754e35493c7546cac13c6e497b653c724d6b251a754cfd611a754e15313c754e14d53c754d6a9512754e1d313c724d6b651a724a94c53c754d6aad04754a4a78dc6446cad13c644
  | 3, 0, 1 => 0xe370d1a754e0b651a754
  | 4, 0, 0 => 0xd6b253c893aaeb62ad954a7962ad94f1d488bad8ab65509e5d6c55b2973aaeb696d94f1d575b2e6ca78eabad95bbd3c755d6c55de9e3aaeb644d94f1d5753156ca78eabad8ab493c755cf561b28d3aaf0a2ac94f1d5739156ca78eabad8abe13c755
  | 4, 0, 1 => 0xd6c69b29e3aaeb62aca4f1d578d2f6ca78eabad6ca78ea425d6c75b29e3aaeb62ad9561d570d2f6ca78eabad863653c755d6c55d69e3aaeb66ad9469d575b156ca9d3cbadd14551a755c561afa8d3aaeb6a6d94f1d5787ad8aaa93cbad8ab6570755
  | 4, 0, 2 => 0xd6c553c750f2eb683154f1d562ad95a278eabad99b653c755d6d4a2a9e3aaeb62ad959a796a52f8aa78eab2f6ca78ea645d6c55b2c03aaeb22ad94f1d575b096ca78eab156cb053c755d6c55e89e3aaeb62ae54f1d561cd94f1b8c8bada84553c755
  | 4, 0, 3 => 0xe36b6929e3aaeb5b29e459d575b1577278eabad8ab6536755ce4554c9e3aaeb62ad93a92175b86a4a78eabad8ab651c755d6c55b29e3aae062ad94f1d572d156ca78eab2f8ab653c755aec55b29e3aaeb62ad95b9d575b1e6ca78eabad8ab653c725
  | 4, 0, 4 => 0xd6d31b29e392d262a9e3a9b97155855a08eabad8ab753c755d6d253c75322eb626d94f1d575ad95ca24eabad8ab655a755d6c55b2bc3aaece2ad94f1d575b236ca78eabad8ab6542755d6c55c09e3aaeb62ad84f1d56ed156cb00eab156ca78ea335
  | 4, 0, 5 => 0xd6d3db29e3aac5582a64f1d575b1564a78eabada4c553c755d6c55c89e3aae2af089411d575b154f20ceab9c6cac53c755d6c55f29e3aae5285154f1d577b156ca78eabad9ab653c755d6c55a29e3aaeba2ad94f1d5787156cb0ceabad98b6586755
  | 4, 0, 6 => 0xd6b1d12823aaeb62ad64f1d575ba29aa78eabadd2b651a755d6c91b29e3aaeb628d94f1d576b156ca78eabb68ab653c755d6b653c7515ae7eb1354f1d575b436ca78eabc16ca7912755e1cc5b29e3aac55b2c24f1b96c1156ca78eabad8ab653c765
  | 4, 0, 7 => 0xd6c553c750eaeb66ac94f1d55b2c158a78eabada23653c755d6c554c9e3aae2ab0a5449d5763156ca78eabad7b3653c755cfd62989e3aaeb654d94f1d5737156ca78eabad8e3653c755d34adb29e3aaf0f5b15469d577b356ca78eaba68ab653c755
  | 4, 0, 8 => 0xd6c9db29e3aacfa2ad94f1d575b346ca78eab156ca78f8755d6b65629e3aaeb5b29e3d1d575ad94f1d454bad7b27904755d6c55d49e3aaeb62ad93a91d75b1573278eabad6ca78ea4e5d6c09b29e3aaeb698c94f1d575b1552a78eabad8b3653c755
  | 4, 0, 9 => 0xd6c55b29e3a2eb68b154f1d575b154f210eab156cb0d82755d6c55e8c33aaeb5b2b64f1916b15097278eabbc8ab653c755d6b658e8d3aaeb64cd94f1d575b476ca78eabad993653c725c5561928d3aaeb62a9e3a92d75b1570a78eabad8ab65549e5
  | 4, 0, 10 => 0xd6cc5b29e392f062ad94f1d575b156fa78eabad873653c725d6c55b29e1bac5608d94f1d575b156ca74eabad8ab6586755d6c55b29e38aeb640d94f1d575b317a278eabbd8ab65549e5d6cd5b2aa4f2eb745155527975b116ca78eabad6ca78ea4d5
  | 4, 0, 11 => 0xd6c553c75252f0a2ad94f1d5711508aa78eabc18aa7904755d6d29b29e3aad462ad94f1d575b15552993cbad8ab655c755d6b65609e3aaf0f5b354f1d575b316ca78eabad58a993c75598cbdb29e3aaeb5b29e451d5787156ca78e4bad8abbd7a755
  | 4, 0, 12 => 0x6b62aaf411d575b3c6ca34eabad8ab651a755d6cb9b2c03aaeb62ad94f1cd75b0f6ca78eabad6caad3c755d6b651a75322c3db29e3a9b978dc3a6278eabb88ab653c755e0d31b29e3aaf1b5ad9469d575ad94f224e4bad8ab656a9e5
  | 5, 0, 0 => 0xdf6b62ad94f1d58019c8ab653c755d6c55b4d94f1d5b5b157ab65889e6c56128b154f1d5b5b728ab653c756c55622aaf411d5b5b708ab653c756c556278d9469d5b5b8aa2c553c756c556256d95e9d5b15588ab651a756ac4557ca64f1d5b15588ab657a756d6c55b29e3a80db456b8ab653c756
  | 5, 0, 1 => 0xd6d622ad9469d5801ad8abbd3c755d6d622ad95e9d5ae7156ca78ea6b6ce455b2ba4f1d5b5ba08ab653c756e1efe2ad94f1d5b5b448ab653c756d6d621ed94f1d5b15588abe13c756d6e8a99154f1d5b5b156cb413c756c55e1b29e449d5b11588ab653c756c561afb4c4f1d5b5b157b3653c756
  | 5, 0, 2 => 0xc55a22ad94f1d5b5b938ab653c756d6c55b2c33a9b9b1558973653c756d6c55b29e3a81db155895bbd3c756c55622aef4f1d5b1558913653c756d6c55b2c84f1d5b15798ab653c756d6c5602d94f1d5b15588ab493c756d6c55b29e3a9bd801ad973653c755d6c55b29e3a989b2f588ab653c756
  | 5, 0, 3 => 0xd6cb22ad94f1d5b1d588ab653c756c5561929e449d5b5b86993653c756c55622ad954279b5b828ab653c756c55622ad94b9d5b5b157fb653c756c55ee2ad94f1d5b5b8a8ab6586756d34a62ad94f1d5b39588ab653c756c3d622ad94f1d5b5b948ab653c756d6c55b2be4f1d5b5b7d8aa7904756
  | 5, 0, 4 => 0xd6c5588a64f1d5b458aac4551a756004553c751702575ad963a7912756d6c55c6d94f1d5b5b428ac1d3c756ac3657cb14f1d5b5b156ca78ea146d6c55b6d94f1d5b155a8ab653c756d6c55b2c64f1d5b5b58973653c756d6d622aef4f1d5b5b15713653c756e36b664d94f1d5b838a8ab653c756
  | 5, 0, 5 => 0xe2eb62ad94f1d5b15588eb653c756d6c55b29f4f1d5b15588ab6558756d6c55b29e3a919b5b9e8ab653c756e0eb62ad94f1d5b5b388ab653c756c55b62ad94f1d5b5b156cac53c756c556218d94f1d5b47588ab653c756c55fa2ad94f1d5b15589ab651a756cadae2ad94f1d5b15588ab654e9e6
  | 5, 0, 6 => 0xd6cc9b29e3a991b87156ca78ea6e6c55622aca4f1d5b5b1580a7904756d6c55b29e3a84db154d8ab653c756d6c55b29e3a981b5b156ca78ea3d6d6cc5b29e3a9b9b19588ab653c75600455b29e2882575b8d8ab653c756d6cb9b29e3a9adb5b156ca78ea456c5561b29e3a909b5b15793653c756
  | 5, 0, 7 => 0xd6c55b29e3a941b5b458ab653c756d6d662ad94f1d5b15588ab953c756d6c55b29e3a931b5b578ab653c756c5455b29e3a9a5b5b156ca78ea5d6d6c55b29e4a1d5b1558a84553c756c55ba2ad955279801156cb053c755c556234d94f1d5b15156ca78ea436006b62af44f1d575b8a98b653c756
  | 5, 0, 8 => 0xd6c55b29e3a8d1b87ad8ab653c756d6e9e2ad94f1d5b155b8ab653c756d45622ad94f1d5b5b156ca7932756d6c55b29e3a889b5b156ca78ea2c6d6e2a94d94f1d5b155884b653c756d6c55b2aa4f209b5b7f8ab653c756d6c55b29e3a979801ad8ab6580755d6c55b2cd4f1d5b15588abd13c756
  | 5, 0, 9 => 0xd6c55b2cb4f1d5b156f8ab653c756c55e62ac94f1d5ab1156cb053c756d6c55b29e3a855b5b328ab653c756d6d622af44f1d5b5b446cb313c756c556283154f1d5b5b15843653c756006b62ad94f1c975b8aa14553c756c556266d94f1d5b15588ab65669e6994be2ad94f1d5b5b157e3653c756
  | 5, 0, 10 => 0xd6c55b29e3a8d5b5b9d8ab653c756004be2ad94f1d575b156ca78ea5f6d6cda2ad94f1d5b5b15743653c756d6d622ad9601d5b5b86873653c756c55de2ad94f1d5b5b1585b653c756006b53c7517089715588ab653c726c55f22ad94f1d5b5ad9622c53c756c5455b2ba4f1d5b15588aa78ea1e6
  | 5, 0, 11 => 0xc55622ad94f1d5b5b588ab653c726d6c55b29e3a885b5b156ca78ea3c6d6c55e6d94f1d5b5ba58ab653c756ca455b29e481d5b5b156ca78ea006006b5b29e28889715588ab656e756d6c55b29e3a805b5b156ca792a756d6c55b29e3c1d5801ad8ab653c755e36b61cd94f1d5b5b154f208ea606
  | 5, 0, 12 => 0xc55622aee4f1d5b5b0e6ca78ea646d6c55b29e3a845b5b017b3653c756d6eae2ad94f1d5ab12f8ab653c756d6c55b29e3a8d9b15428aa78ea686c55622ad93a921b5b156cb513c756c55622ad9471d5b15738ab653c756e370e2ad94f1d5b5b156ca78ea4f6d6e922ad94f1d5b5b156cb00ea6b6
  | 5, 0, 13 => 0xd6c55b29e439d5b5b156ca78ea2e6d6c55b29e3a849a2b0e6ca78ea6e6d6c55b29e3a9c9b5b198ab653c756c553a53154f1d5b5b156ca78ea416d6d6256d94f1d5b15888ab653c756d6d622ad94f1d5b5b156ca2504756ac4622ad94f1d5b151581b653c756c5561b29e459d5b87ad8aa7904756
  | 5, 0, 14 => 0xc55622ad9569d5ab1156ca78ea306c55622ad95e1d5b7fad8ab6588756d6c55b29e3a9adb5b156ca78ea0b6d6d5a2ad94f1d5b5b156ca78ea286c556246d94f1d5b15588ab6542756d6c55b2a24f1d5b5b308ab653c756c5455b29e3a83db15588ab813c756d6dce2ad94f1d5ab1156ca78ea326
  | 5, 0, 15 => 0xd6d7e2ad94f1d5b15588ab753c756964a62ad94f1d5b5b2d8ab653c756c55862ad94f1d5b5b866ca7912756d6c55b29e3a881b1f588ab653c756ac455b29e3a951b5b156ca78ea756d6c55b29e3a829b5b157f3653c756d6c55ced94f1d5b4558973653c756c2455b29e3a9adb15586cae512756
  | 5, 1, 0 => 0xd6e2a2aef4f1d5b5b156ca78ea026c55626ad94f1d5b43588ab653c756c55622ad14f1d5b5b156ca78ea566d6c55fad94f1d5b5b156ca78ea636d6da62ad94f1d5b8dad6ca7912756006f62ad94f1d5401ad9ab653c755cc5622ad94f1d5b15788ab653c756ce62a2ad94f1d5b5b15873653c756
  | 5, 1, 1 => 0x6b62ac94f1d575b156cb553c756ac455b8d94f1d5b5ba5a63653c756d6daa2ad94f1d5b5b157d3653c756c56162ad94f1d5b15668ab653c756006b693154f1d575b156cae53c756d6c55e2d94f1d5b155e8ab653c756c55ee8cd94f1d5b5b156ca78ea676d6cc62ad94f1d5b5b156ca7924756
  | 5, 1, 2 => 0xd6e022ad94f1d5b7b588ab653c756d6d626ad94f1d5b5ad94f224ea646d6c55b29e3a961b5b4a8ab653c756c55ae2af14f1d5b1558a4c553c756c55622ae44f1d5b87ada64553c756d6d9e2ad94f1d5b5b156ca78ea246d6c55b29e3a999b5b15763653c756006b62ad93a8f575b156ca78ea656
  | 5, 1, 3 => 0xd6d6293154f1d5b7fad8ab653c756d6c5e2ad94f1d5b5b156cb1d3c756e06b62ad94f1d5b4d328ab653c756006b62a9e288b975b156ca78f2756d6c962ad94f1d5b5b5c8ab653c756c8d622ad94f1d5b61ad8ab653c756d96b62ad94f1d5b1558a7b653c756c55622ac94f1d5b5b156ca7938756
  | 5, 1, 4 => 0xc5561b29e3a8adb5b157a278ea6e6d6cf1b29e449d5b1558a1b653c756d6c55b29e449d5801a68ab653c755e4eb62ad94f1d5b31589ab653c756d15622ad9601d5b5b4a6cb4d3c756c54f62ad94f1d5b5b588ab253c756d6c561ad94f1d5b15788aa7904756d6dea2ad94f1d5b5b15893653c756
  | 5, 1, 5 => 0xc95622ad94f1d5801ada23653c755d6c55b29e3a895b155863a2504756d6c55b29e3f1d5801ad8aa993c755d6c55ead94f1d5b458aac4d53c756d2e2ab0d9469d5b5b156ca78ea0e6d6c55b29e3a8e1801ad7b3653c755d6c560ed94f1d5b5b3a8ab653c756d6c55b29e461d5b5b15783653c756
  | 5, 1, 6 => 0xd6ce62ad94f1d5b5b1576b653c756c556288d94f1d5b15156ca78ea3b6d55622ad94f1d5b5b156cb0d3c756d6c55b29e3a85db15588aa993c756d6c55b29e3a94db15587b3653c756d6d262b0e4f1d5b1558953653c756d6c55de9e3a9a1b6fad8ab653c756c556238d94f1d5b1578a63653c756
  | 5, 1, 7 => 0xd6c558e9e411d5b5b156ca791e75600455b29e3a82575b587b3653c756ddeb61ed94f1d5b5b156ca8d3c756c55626ac94f1d5b5b1587b653c756d6c55b29e3a9b5b5b156ca78ea0d6ca5622ad95e9d5b5b156ca78ea6c6d6c55b29e3a95db5b156cb053c756c5455b2b24f1d5b5b156ca78ea086
  | 5, 1, 8 => 0xd6c55b29e3a9b9b5b658ab653c756d6c560cd94f1d5b5b748ab6588756e26b62ad94f1d5b156b973653c756c556204d94f1d5b1558a63253c756c55622aa54f1d5b5b408ab653c756d6c55b29e3a8fdb5b58a23653c756d6c55b2bb4f1d5b5b588aa993c756e3eb62ad94f1d5b5b157bb653c756
  | 5, 1, 9 => 0xac455b29e3d9d5b95ad8ab653c756d6c55b29e3a9a9801ad6cac53c755d6c55b29e3a88db5b4c6cb1d3c756d6c55bcd94f1d5b15848ab653c756d6c55b29e3a869b5b488ab653c756c55922ad94f1d5b5b156cb093c756d6dc62ad94f1d5b5b156ca78fa756d6c55b29e3a865b15586ca78ea4e6
  | 5, 1, 10 => 0x6b62ad955279715586cac53c756c5455b29e3a87db5bad8ab653c756c5561b29e3d1d5b5b156ca78ea316ac4ba58d94f1d5b5b2e8ab653c756bad622ad94f1d5b5b2f8ab653c756d6d628cd94f1d5b15587b27904756c55622aea4f1d5b5ba28abd53c756d6d562ad94f1d5b5b156ca78ea616
  | 5, 1, 11 => 0xd6c55b29e409d5b5b156ca78ea2d6d6c55b2af4f1d5b5b156ca813c756d6c55b29e3a861b8dad8ab653c726006b5b29e3a88975b586cac53c756d6c55e8d94f1d5b5b156ca78ea056c55622a9e3a92db5fad8ab653c756d6c55b2cf4f1d5b5b156ca78ea3a6c55622ad955279b5b378ab653c756
  | 5, 1, 12 => 0xd6c55b29e3a971b5b156ca78ea526d6d322ad9469d5b5b156ca78ea3e6d6c55b29e499d5b5b156ca78ea706d6c55b29e3a8e5b5b748ab653c756ce455b2c44f1d5b15586cb1d1a756e0e7a2ad94f1d5b1558933653c756c55628ed94f1d5b5b988ab653c756ccd622ad94f1d5b5b588ab65549e6
  | 5, 1, 13 => 0xd6e262ad94f1d5b5b156cb653c756d6c55b29e3a96db7bad8ab653c756d6c55b29e3a871b1558a2c553c756c55622a9e421d5b5b156cb393c756ac455b2c05f1d5b5b156caa93c756d6ca22ad94f1d5801ada2c553c75500455b2751e825715156ca7922756c5561b2b64f191b8dad8ab653c756
  | 5, 1, 14 => 0x6b62ad9619d575b156ca78fe756ddc55b29e3a9b9b5b156ca78ea046c55ae2ad94f1d5b5b156ca78ea5a6d6c55b29e469d5b5b156caf53c756d6c55b29e3a819b15589ab65549e6d162ab11555279b75ad8ab653c756d6c55b29e3a991a2ad95f2e93c756d6c55b29e3a955b5b156cb153c756
  | 5, 1, 15 => 0x6b5b2751e88962ad9623053c756ddeb62ad94f1d5b5b3c8ab653c756c55622adf4f1d5ab12c8ab653c756d6c562ad94f1d5b5b15883653c756c55622ad94f0ddb5b156ca790a756c55622ad9619d5b7b988ab653c756d6c55b29e3a859801c18ab653c755c556240d94f1d5b5b838ab653c756
  | 5, 2, 0 => 0xd6c55d2d94f1d5b5b156ca7900756d6c55b29e3a8a5b5ba28ab653c756006b662d94f1d575b156ca78ee756006b62a9e3a8b9773ad8ab653c756d6c55b2b64f1d5b5b156ca7904756c55622aef5e9d5b5b1f8ab653c756e36b698d94f1d5b91ad8ab653c756d6cee2ad94f1d5b5b156cb5d3c756
  | 5, 2, 1 => 0xd6c55b29e3a89db1558a53653c756d6c55b29e3a965b5b156cb253c756d6c55b29e4d1d5b5b156ca78ea0c6d6d522ad94f1d5b5b4c6ca78ea646d6d262ad94f1d5b15588aaa94c9e6006b694d94f1d5401ad8ab653c515c556262d94f1d5b155858a993c756d6c55b2d34f1d5b5b157db653c756
  | 5, 2, 2 => 0xd6c55b29e3a925b5b1582b653c756d6d322ad94f1d5b3d788ab653c756d6d8a2ad94f1d5b5b1b8ab653c756b5c5614d94f1d5b5b156ca78ea266d6cd62ad94f1d5b5b218ab653c756d6c55b29e3a825b15638ab653c756cc5ba2ad94f1d5b5b156ca7910756d6c55b2a44f1d5b5b156cb113c756
  | 5, 2, 3 => 0xe0c55b2c74f1d5b5b156ca993c756d6c55b29e3a86db87ad8abd53c756c5561b28d3a991b5b156ca78dc646d6e562ad94f1d5b5b156ca78ea516d6cf22ac94f1d5b5b15803653c756da6b62ad94f1d5800d94f1d444095dec55b29e411d5b5b356ca79047568ab653c983a9b9b5b4c9e3653c756
  | 5, 2, 4 => 0x6b62ad9288f57155887b653c756006b62ad9469d575b156ca78ea2f6d6c55b29e4f1d5b5b3f8ab653c756006b62a751e8b9715586caad3c756006b61ed94f1d575b156ca7930756
  | 6, 0, 0 => 0xd6d622ad94f260eafa2cd5622ad94f1d5c018aac455b2511eb67ab1156cb1d3c757c55622ad94f218eafadac455b2cc4f1d5f15588ab653c963ab80315588ab651a756c55622ad95fa78eaf8ab65622ad94f1d5f15588abc53c7535beb715156ca78ea6870062ab1156caf4ead8aac455b29e4f1d5f218aac455b29e3abe2ab1156ca78ea407
  | 6, 0, 1 => 0xd6e6b15156ca78eae00c55622aef4f1d5b15848ac29b29e3abe8315588ab653c757d6e2a2ad94f1d4c8f8aac5122ad94f1d5c01ad8ac05b29e3ab6b71515853653c757d162ab14c8aa78eaf8aac455b2d04f1d5f5b6cac455b29e3abe2ab1157b3653c757c55622af56cb113cf8ab95622ad94f1d5f1570ac455b29e3abeb6fb588ab653c757
  | 6, 0, 2 => 0xddeb715156ca78eafadc54f22ad94f1d5f155896455b29e3abeb6b11580b653c757c561ab1326ca78eafadc5455b29e481d5f1582ac455b29e3abe5315588ab653c757c55622ad95f278eaf8abed622a9e411d5f278aac455b29e3abe2ab1156cb213c7570062af7156ca78ead8aac45602d94f1d5c018aac4b9b29e3ab62ab1156ca78ea627
  | 6, 0, 3 => 0xc55622ad94f1d48cf9ec55622ad94f1d5c01adc54553c7517362ab1388ab653c757c55622ad958a78eae00d6c55b29e3a981801ad8ab653c751eb6b715156ca7904757c55622ac453278eaf8aac3658e9e449d5f15588ab8db29e3abe2ab1428ac1d3c75700455b29e3a85420d8aac455b29e3a851f15588ab6db29e3abe2ab115713653c757
  | 6, 0, 4 => 0xc55622ad94f1d498f8aac55e2ad94f1d5f15588ab653c752ebe2ab1156ca7928757006b715156ca78a2c00c5455b29e3a855b1558993653c75323e2ab11580a7904757c55622ad94f1d426f8aac455b29e3a981f5b8a8ab65a69e3abe2ab1156ca78ea3d7006b62ad94f250ead8dc55622ad94f1d5f1558973653c7535be2ab1156ca78ea457
  | 6, 0, 5 => 0x6b665156ca78ead8aac455b29e3a889f15588ab653c75163eb715156cb113c757d6d622ad94f1d4c0f8ab9c55b29e4a1d5f5b588ab653c751ebe2ab1156caa93c8270070f5b156ca78ead8abfd622ad94f1d5f15588ab653c752f3e2ab1156cb353c757c55628b156ca78eaf8aacd622ad94f1d5c01ad8ab653c7511362a2ad94f240ea687
  | 6, 0, 6 => 0xd6d622ad94f1d444f8aac36588b14f1d5c0000d6c55b29e3aae2ab1156cb2d3c757c55622ad94f1d42af8aac4ca2ad94f1d5f1558a2365989e3abe2ab115843653c757d6e2a2ad94f1d412e00c5455b2ba4f1d5b15588abf1b29e3abe2ab1156ca78ea347e1e2ab1156ca78eaf94ac455b29e3a9a1f4f8aac455b29e3ab8035b156ca78ea156
  | 6, 0, 7 => 0x62ab0d94f14444dadac455b29e3a855f5b5899455b29e3abe2ab1156ca792a757c55622ad94f1e0eae00c55622ad94f1d5b15588aa7904753038035ba58ab653c756c55622ad94f1d46af9dc55622ad94f1d5f87adac455b29e3abe2ab1368ab653c757d6e2a99156ca78eaf8aac455d0d94f1d5f15588ac2db29e3ab80315584f1d45c226
  | 6, 0, 8 => 0xc55622ad94f1d422f8aac405ecd94f1d5f578aac455b29e3abe2ab1156ca78ea367006b62ad94f1d45cdadc55f62ad94f1d5c01adac455b29e3ab6b715156cb313c757c55622ad94f1d49efa4c55622ad94f1d5f15588ab65807535b80315738ab653c75600455b29e3a8401eda5c55622ad94f1d5f5b8a8ab653c7528be2ab1156ca78ea007
  | 6, 0, 9 => 0xc5562ad156ca78eaf8aac455b29e3a8a1f15588ab65449e3abe2ae7588ab653c7570062a2ad93a8f42ac00d6c55b29e3a9ad801adab455b29e3ab62ab1156ca78ea2e7c55622ad94f1d424f8aac4662ad94f1d5c018a8ab653c7507b62ab1156ca78ea417d6e2ad9156ca78eaf8aac5622ad94f1d5f15588ab6512823abeb74b588ab653c757
  | 6, 0, 10 => 0xc561afb156ca78eaf8aac4561cd94f1d5f155fac455b29e3abe2ab12d8ab653c757c561ab0d94f224eafadac455b29e3a8b9f15588ab653c75103e2ab1156ca78ea757c55622ad94f1d414f8aac455ced94f1d5c0198ac455b29e3ab00315788ab653c756d6d62b1156ca78eae00d6c561cd94f1d5b15588ab653c7535be2ab1156ca78ea0b7
  | 6, 0, 11 => 0xac455b2c45f278eaf8ab55622ad94f1d5f15588abe9b29e3abeb6b115873653c757c55622ad95ca78eaf8aac455e2d94f1d5f156c8ab653c75343e2ab1156ca78ea677000035b156c9d47ab8aac455b29e3a959f157d8ab653c75343e2ab1157eb653c757c55a6b1156ca78eafadac55a2ad94f1d5c018aac4d5b29e3ab62add156ca7904757
  | 6, 0, 12 => 0xc55624b156ca78eaf8aae5622ad94f1d5c018bc5455b29e3ab0037fad8ab653c756006b62ad963a78ead8ac05622ad94f1d5f15586ca791275323e2ab1156ca78ea587c559eb1156ca78eaf8aac455b29e3a891f15588ab653c75333e2ab115763653c7570062ab1156c9d47ad8aac455b29e3a995c018aac455929e3ab6971558a63653c757
  | 6, 0, 13 => 0xd6d622ad963a78eaf8aac455e0d94f1d5f15589e3653c893abeb715156ca7928757c55622ad94f224eae00d6c55ead94f1d5801ad8ac1db29e3ab62ab11586b653c757006b62ad94f224ead8abd5622ad94f1d5f7f8aac455b29e3abe2ab1156cb1d3c7570062ab1154f1445cd8aac455b29e3c9d5c01adac455b2751eb682b1156cb313c757
  | 6, 0, 14 => 0xc55622aed6ca78eafadac455b29e449d5f15588ab653c750bbe2ab1156ca78ea537ac45614d94f1d4d6e00c556288d94f1d5b15588ab653c7512be2ab1156ca78fc7570062ab11553278ead8aac455ead94f1d5f15588ab653c75073e2ab1156ca78ea3870062ab0f66ca78eadbfd6d622ad94f1d5f15588ac1db29e3abe2ab1156ca7918757
  | 6, 0, 15 => 0xc55d2b1156cb10eae00c53653c75110558018ac2455b29e3ab62ab1408ab653c757006b62ad94f1d4dcd8aac455eed94f1d5f15588ab1d3c823abe2ab1156ca791e757c55622ad951a78eaf8aac455b29e3a9b5f15588ab653c7506be2ab1156ca78ea6c7c55622ad94f1d4aefadac455ead94f1d5f5b8a8ab653c750ab80001156ca78ea095
  | 6, 1, 0 => 0xe562ab1156ca78eaf8a8ab653c750803df15588ab653c7535380315586cac53c756006b75b156ca78ead8aac531b2c74f1d5f15588ab79b29e3abe2ab1156ca78ea1a7005622ad94f1d412d8ab8d622ad94f1d5f5ba5c5455b29e3abe2ab1156ca78fa757c55622ad94f1d432f8aac455b29e3a9b9f1565ac455b29e3abe2ab115833653c757
  | 6, 1, 1 => 0x62ab0d94f1d444dadd6d622ad94f1d5f5b8a8ab653c7535be2ab1156cb3d3c757c55622ad94f1d474e00006b5b29e3a889401ad8ab659e9e3ab62ab1378ab653c7570062ab1156caa93cdadc55622ad94f1d5f15588ab653c7518be2ab12e8ab653c757d6d622ad94f1d4dcfa2c55622af54f1d5f1558aac55b29e3abe2ab1156ca78ea617
  | 6, 1, 2 => 0xc556251156ca78eae00c55628b154f1d5b8d8aac455b29e3abe2ab1156ca78ea5c7c556299156ca34eaf8aac455b29e499d5c01adac3653c7511362ab1156ca78ea397c55d2b1156ca78eae00e36b62ad94f1d5801ad8ab653c752e366315588ab653c757c55622ad957a78eaf8aac455b2a04f1d5f15588ab653c750c38035b748ab653c756
  | 6, 1, 3 => 0xc55622ad94f234eae00c54553c7517055b15588ab657a9e3abd62652c8ab653c757c55622ad94f1d4c8f8aac455b29e3a955f15588ab658a9e3abe2b13588ab653c7570062ad7156ca78ead8aac455b2d94f1d5f8dadac455b29e3abeb6b1156ca78ea5c7006b62ad94f1d4c8d8aac455b29e3a871f15588ab659c9e3abe2ab1156caa93c757
  | 6, 1, 4 => 0x6b62ad94f208eac00c5561b2751e889b778aac455b29e3abe2ab13c8ab653c757c55622b156ca78eafadcd5622ad94f1d5f15588ab653c853ab80377ad8ab653c756c55622ad94f1d42ce00d6cf22ad94f1d58015896455b29e3ab62b07588ab653c7570062a2ad94f1442adadac45614d94f1d5f15588ab653c7f3abe2ab1156ca78ea5a7
  | 6, 1, 5 => 0x6b62ad962278eac00c55622ad94f145b15588ab65a69e3abe2ab1157db653c757c55622ae96ca78eaf8aac455b29e401d5f15588ab653c7514b80001ad8ab653c515d162ab1156ca78eae00c55622a9e3a8b9b15588ab656c9e3ab8035b156cb4d3c756c55622ad94f208eaf8aac47e2ad94f1d5c01add1455b29e3ab00001ad8aa78ea2e5
  | 6, 1, 6 => 0xc556299156ca78eae00d6d322ad94f1d5b15588dc55b29e3abe2ab1156ca78ea267c55626b156ca78eaf8aac4862ad94f1d5f15588ab653c7504be2ab1156ca913c757c55622ad962278eaf8aac455b29e3a89df15588ab653c752cbe2ab1156cb253c757006b62ad94f1d412d8aac455b29e3a831f1558aa455b29e3abe2ab14c6ca78ea647
  | 6, 1, 7 => 0x315589fc55b29e3ab80315588a9d47a2e6c55622ad94f260eaf8aac455b2a64f1d5f15588ab653c750db8035b156ca7930756c55622ad94f1d4a2f8aac4f22ac94f1d5f15589ab653c823ab8035b958ab653c756c5562993c6ca78eae00d6c55b29e3a945b15588ab653c7524be2ab11582b653c757
  | 7, 0, 0 => 0x62ab1156ca78ea6b70062ab1568ab653c7570062ab1156ca78ea2e7000035b588ab653c7560069715588ab653c7570000315588ab653c7560000001ad8ab653c7550062ab1156ca78ea1570062ab1328ab653c7570062ab1156ca78ea2270062ab1156ca79287570000315156ca78ea1560062ab1156ca78ea6070062ab1156ca78ea3d70062ab11580b653c7570062ad9588ab653c757
  | 7, 0, 1 => 0x315588ab653c5160068b15588ab653c7570000315588aa78ea2e60062ab1156ca79047570062ab13c8ab653c7570062ab1156ca78ea6470062ab1156ca78ea5c70062ae9588ab653c7570000315586ca78ea2260062ab1156cb3d3c757006b715588ab653c7570062ab1157ab653c7570062ab11583b653c7570062ab1156ca79127570062ab1156cb1d3c7570000315588ab64ea3d6
  | 7, 0, 2 => 0x62ab1156ca78ea5170062ab14c8ab653c7570062ab1156cb113c757
  | 8, 0, 0 => 0x315588ab653c756
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
private theorem z3_0 : span (Z 3) 18 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 18 0 = true := z3_0

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
private theorem z4_192 : span (Z 4) 15 192 = true := by decide +kernel

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

private theorem z4_a8 : span (Z 4) 207 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 15) z4_a7 z4_192

private theorem z4 : span (Z 4) 207 0 = true := z4_a8

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
private theorem z5_576 : span (Z 5) 10 576 = true := by decide +kernel

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

private theorem z5_a24 : span (Z 5) 586 0 = true :=
  span_join (f := Z 5) (a := 576) (o := 0) (b := 10) z5_a23 z5_576

private theorem z5 : span (Z 5) 586 0 = true := z5_a24

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
private theorem z6_360 : span (Z 6) 22 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 382 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 22) z6_a14 z6_360

private theorem z6 : span (Z 6) 382 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12603

theorem PEqualNP.Outside.L_meta_12603 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373994 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12603.mainG PEqualNP.Outside.L_meta_12603.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12603.CG, PEqualNP.Outside.L_meta_12603.CG_mono, by
      have : PEqualNP.Outside.L_meta_12603.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12603.CG_eval⟩
