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
namespace PEqualNP.Outside.L_meta_12589

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008234184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 5, 0, 0, 8, 9, 0, 0, 12, 13, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 3, 6, 7, 3, 3, 10, 11, 3, 3, 14, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 42, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 6, 6, 6, 3, 6, 6, 6, 7, 6, 6, 10, 11, 6, 6, 14, 15, 6, 6, 6, 19, 6, 21, 22, 23, 6, 25, 26, 27, 6, 29, 30, 31, 6, 6, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 3, 7, 7, 6, 7, 7, 7, 10, 11, 7, 7, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 10, 10, 10, 3, 10, 10, 6, 7, 10, 10, 10, 11, 10, 10, 14, 15, 10, 10, 10, 19, 10, 21, 22, 23, 10, 25, 26, 27, 10, 29, 30, 31, 10, 10, 10, 35, 10, 37, 38, 39, 10, 41, 42, 43, 10, 45, 46, 47, 10, 49, 10, 51, 10, 53, 54, 55, 10, 57, 58, 59, 10, 61, 62, 63, 11, 11, 11, 3, 11, 11, 6, 7, 11, 11, 10, 11, 11, 11, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 14, 14, 14, 3, 14, 14, 6, 7, 14, 14, 10, 11, 14, 14, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 15, 6, 7, 15, 15, 10, 11, 15, 15, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 19, 6, 7, 19, 19, 10, 11, 19, 19, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 21, 6, 7, 21, 21, 10, 11, 21, 21, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 22, 6, 7, 22, 22, 10, 11, 22, 22, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 23, 6, 7, 23, 23, 10, 11, 23, 23, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 25, 6, 7, 25, 25, 10, 11, 25, 25, 14, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 26, 6, 7, 26, 26, 10, 11, 26, 26, 14, 15, 26, 26, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 26, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 27, 6, 7, 27, 27, 10, 11, 27, 27, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 29, 6, 7, 29, 29, 10, 11, 29, 29, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 30, 6, 7, 30, 30, 10, 11, 30, 30, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 31, 6, 7, 31, 31, 10, 11, 31, 31, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 35, 6, 7, 35, 35, 10, 11, 35, 35, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 37, 6, 7, 37, 37, 10, 11, 37, 37, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 38, 6, 7, 38, 38, 10, 11, 38, 38, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 39, 6, 7, 39, 39, 10, 11, 39, 39, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 41, 6, 7, 41, 41, 10, 11, 41, 41, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 3, 42, 42, 6, 7, 42, 42, 10, 11, 42, 42, 14, 15, 42, 42, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 42, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 42, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 3, 43, 43, 6, 7, 43, 43, 10, 11, 43, 43, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 45, 6, 7, 45, 45, 10, 11, 45, 45, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 46, 6, 7, 46, 46, 10, 11, 46, 46, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 47, 6, 7, 47, 47, 10, 11, 47, 47, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 49, 6, 7, 49, 49, 10, 11, 49, 49, 14, 15, 49, 49, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 49, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 51, 6, 7, 51, 51, 10, 11, 51, 51, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 53, 6, 7, 53, 53, 10, 11, 53, 53, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 54, 6, 7, 54, 54, 10, 11, 54, 54, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 55, 6, 7, 55, 55, 10, 11, 55, 55, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 57, 6, 7, 57, 57, 10, 11, 57, 57, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 58, 6, 7, 58, 58, 10, 11, 58, 58, 14, 15, 58, 58, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 59, 6, 7, 59, 59, 10, 11, 59, 59, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 61, 6, 7, 61, 61, 10, 11, 61, 61, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 62, 6, 7, 62, 62, 10, 11, 62, 62, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 63, 6, 7, 63, 63, 10, 11, 63, 63, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115111711173337111511171117333711151117111733370000000000000000111511171117333711151117111733371115111711173337000000000000000011151117111733371115111711173337111511171117333700000000000000001115111711173337000000000000000011151117111733370000000000000000111511171117333711151117111733371115111711173337000000000000000011151117111733371115111711173337111511171117333700000000000000001115111711173337111511171117333711151117111733370000000000000000111511171117333700000000000000000000000000000000000000000000000011151117111733371115111711173337111511171117333700000000000000001115111711173337111511171117333711151117111733370000000000000000111511171117333711151117111733371115111711173337000000000000000011151117111733370000000000000000000000000000000000000000000000001115111711173337111511171117333700000000000000000000000000000000111511171117333711151117111733370000000000000000000000000000000011151117111733371115111711173337000000000000000000000000000000001115111711173337000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8000000000000000000000000000000000000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc80000000000000000eeeaeee8eee8ccc8000000000000000000000000000000000000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc800000000000000000000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc800000000000000000000000000000000eeeaeee8eee8ccc8eeeaeee8eee8ccc800000000000000000000000000000000eeeaeee8eee8ccc8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8eeeaeee8eee8ccc8

def cMZZ : Nat := 0x1115111711173337000000000000000000000000000000000000000000000000111511171117333700000000000000000000000000000000000000000000000011151117111733370000000000000000111511171117333700000000000000001115111711173337000000000000000000000000000000000000000000000000111511171117333700000000000000000000000000000000000000000000000011151117111733370000000000000000000000000000000000000000000000001115111711173337000000000000000011151117111733371115111711173337111511171117333700000000000000000000000000000000000000000000000011151117111733370000000000000000000000000000000000000000000000001115111711173337000000000000000000000000000000000000000000000000111511171117333700000000000000001115111711173337111511171117333711151117111733370000000000000000000000000000000011151117111733371115111711173337000000000000000000000000000000001115111711173337111511171117333700000000000000000000000000000000111511171117333711151117111733370000000000000000111511171117333711151117111733371115111711173337

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
  | 3 => 43
  | 4 => 288
  | 5 => 606
  | 6 => 359
  | 7 => 29
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0x4cf6da9c1987bc91150d7e74
  | 3, 0 => 0xdb43fff0d09b3505ac608d80ab46f55ea9c4a6c2a6ac55059761abd594f0fc6993d458f090afec68904c879d8deda61a79adb7707456703a66ef3dfa5fbe97c65f2b8a6258632b754e14690749d1297f4972d0583e8651a3390a2921351d1ea33509bc39344a08463405681e3316cdda3245959431c9ad44317443ad2ec7f0ff2250abb921a0697d1d1e91f817ce3ef9150d7e74104fef9e0ac83cee0a07632b0666e971061d064a04e23e1a
  | 4, 0 => 0x1ce4f7fc1cc2abb91c4ace9e1c23b8231c07d4d81bb6e2871af0ed831a912f0f19552ae118449ad5175a5e45171f778e15b0081215a1487e158e10ba15259807150919431494e13a139ac96c13622a4312bba0c4126a689d125cd5aa1111830a10ef6b6910ad7b02101b5ce60fe038db0f8f9e540ea7b3b10e8c392c0e7ef8690e70f57f0dfbc5040dd231100da3259f0cff286f0ca318f80b1d13530aa94a3c0aa5e8a60a1387710963e7a20957166209256289086bf4e20819b08306e6607e06d406fb069b3bce0679eccf066cfb8d063946ec054f680f0533e4c7040bd08c03e5897503c4a20a034087ff033b9a8b02ff41ed02dc51390299ed9700d0874d
  | 4, 1 => 0x41dfd54b4117b5d3403741473efc6e303ec856953ebe264e3d6732013d06a4c23cb28f6c3c3fe1d73c1a3f1f3b33582c3a7bf49b381e05a9379112dd378829ba36daca1836b9429636ad4441350c740134a1ca61347d16a1343d410233eac13033bc763232ef7a2e32dd4d8a327e827032573bcf30c4f2e33003d3ca2f6e56cc2e603a922df356302d6e12872cafbe6d2b351a5d2a775dc028eb963c28bdde2e28baef54287d17542802fb7927a272cb275f0c03274e7b972685cf52265af3b2255d71b824af299e249730a72487662f2286d2f721f7eca220351ea71edaa1781ed2232e1e99c8791e648d1e1e0ead0e1dd85bbc1d96db551d8211f41cf9ae3c
  | 4, 2 => 0x78e01d3b7808f67f77dcd56f778e15ba7631255c74ac00cc7290ccd97252781f721d9e00714589476dcb94656ce10a856cd7c5956b4026c76b2a742c6aa321466aa25eb16a9f9c596a5ff60569ccf3c868bb4a40676db92e66631c8064e1614b63cbf40d6390cd5762443a1f615a1c2b605b07f75e96b0795df4f75b5d8c1bd25d2175ea5c7bd1425b4637c85a1f5ae7592d32dc58632b7557a3664b572d263756fafadb55a63ca1555c62b2546fdb90542371cc53a16dc2533149c1513f9d30506be7d04fba374b4ddfe1e94d3e93d14ce628cc4c0e7c264b8803354a9143834a7def9349ab470247ca4335476ce377463b5ba544955a68435038a142045a1a
  | 4, 3 => 0xbaffce82b79e11a5b76636b6b710d3a9b6e47a1bb4752f7cb451df17b3f089bfb38e8e27b2a16db8b1d5ba46b060f864aca70b8baca32f81ac5c60e9aaf9737baa44eafba9c4a6c2a80ffa41a73b56bda53cc253a4fd425ca4e71818a123b6909ebe8b799c6f799298221297965a551e9604efba95dd375695aeaaef94c39f3493cedcf9937a2a2893415098922a3cce915f3ba7913f666f90afec689028fedb8d3f87a58b9461858b73cd778adb14988a5209018818a8d487e801ec8719a9f78543b4b384bd2cd8848b0642825650ef817e25f67e9f40477dc5daf67d8c9f1d7c4dcccc7b5c2fee7b593a7c7b53f9d87b3835787ab280da7a4107ad79ff843d
  | 4, 4 => 0xf5e0cd87f349d4d1f1f40e1af1011b34ede04815ed8178d4ed1a53c3ea2af6bae7260410e01342f9dd13a151dcdf1feedb949656db758d17dac1d5f4d846a96ad22088add0df6e6ecfe00677cf4d0392ccf8a6fdcbef0a7acafce26fc96e5353c704574ac6fcbde2c4c0a9c6c3520f13c17baaa9c1086e2fbeb5d85fbc60f316
  | 5, 0 => 0xc076cb40b7496780af79d890af1d0680ac618870aa53ab60a3977d309e1b1c409ca182609298ced0913cf340903e4fa08ed886408bf226b08574b4e08571b09084ecd0407e136f407de13f007d74b5607b83305078b56e4072410220713852b067eff09066ef05f0661a1d2063946ec05fcb19a05f51d4605c7787405c070bf05a3623e056c853f05338c5d051ea37605048e5a04fa5c8e04dd069504afb7ff04ad966c048cf9a40448d1240435461d040dd8e5033161df02dc513902d1d4b702c7b6380293ac8e0252db6e017e5249016102a0016040a90129cb7a0100815c00f8392e00d38c7b009c21640086b8b1005855b2003af53f000861e70001f5c9
  | 5, 1 => 0x1c9f8dd91c59f7601c24a25f1c1df85d1c110d951bfd1cc51bfb2c461bd3e5a51b751b2a1b1a00141ad5936b1a7f92761a5732cc19e33ffe19807da0196073d4193e978818eb00a218ad287f185cb91a1802eebe17e5326d1742fb3a1716b2f016a011d01696991516747d96162c6843158a9ded153c7988150448b31483fcfb1474931b13fe613313f40796139ac96c139a7b3b138030e612bba0c4128e5677125cd5aa1240016e123a88041237043011f9c12a11e28b5411e0f2d211d596a611a196a6119416be113aa0711122633d10dbb5d910cb256d1079da1f0fab5f360f5c664c0ed608d50e4195650e2bd3740e0410050cf27e0f0cee29140cb2984c
  | 5, 2 => 0x2aa6f2662a945fa92a14964d29985fbb298c2bdf29715762290759a828791806286dc5582854c838284d7a4e282ca94827fd334127b8a3fc274d095a27338a972729c6812710f98126cc682e26834e98262f39422611dd762602c63125d4f04c2572baf624fd2fd024caa10424c63de624af299e249f18632487cc9524120e502410b20923f89e7122f8838d22f4a75922c732ed22748834224cd392219e5d53219aaf7f206f7ea42029ee171f9d59fb1f81e60d1f585ba31f4d1b0d1f3b10fd1f1f9d0e1f1ac2611ed2232e1e96c48d1e2f31c61e1e74371df9c0771dd72ade1dcbc2a11db9ead81d676b061d5181ba1d3920081ce5b51c1ce4f7fc1cd4b497
  | 5, 3 => 0x3f14b8b33ed90c883e6414ec3e4a64de3e083fd03df597693dec85663d5ce4cc3d5a38333d3b1c8c3d22904f3d1e17983c93ead83c4593d83c121a0d3bf058a73b7115d83abc47063aa1623b3a1e98f839e4e36e3936e12137dbb34c37b5970d378b4aa5375cf8d737389d9537385fb636f6c32836bb3da736ad4441366e78a735dd2cce35b1c767358b25fc35857cac351d2bd93504ad0b340ded5933fa9969336d06673327f0d83274107a32532e333204381a318c172530e98d4d30cdf78f3086fb902fb8057b2f6e56cc2f36ec5a2ec61c982e7a41e92e6a9a382e25bccb2dbd492a2cbd231e2c62cbfb2c2da53d2ba44c952b5894e32b5642e62b21ec0a
  | 5, 4 => 0x5274daf95139b4e450d5ac5250ac0a09509602e7505752da4ffa60d14fc219bf4f93e8134f90f0f54edabd374ea2d0174e5e0b214e48c73e4e2c850f4e1564c74d489de34d0d772d4cfa5d274ceafc304c7755294c2356c04bbb2dc94b43aa054ad6c6014ad673064a9143834a538fc849f1284c49c821c949ab4702491e800848135a4f47e24e0347a13bb1478077384771a131476ce377472b32c94726a5de4708c5a8469e1fc04652b3f445c2672a45a495e744b0524944955a684468274a43bd512a439c04bd439b72fe437c279f430928c742a9dcb2420828eb41dfd54b4109e15940cadb9040a9d00d40a3fc124077a4b13f9f98a03f6479d23f22e677
  | 5, 5 => 0x64d0a3ae64ba611164a13a6a644ae801642f2ab063c2e2d463bdb1836311352762e240c8626cb7ba625cc71161336451610d6ecb605ddeaf5fc145665f6de45a5f54b8585f3665795f0d86215eebaecb5eb0a9205e4565af5dce918a5dcb6da65d7e91925cec819d5cd9acb25c83b3c75c67639d5c0d76af5bcf21f55ba6a6755b9a47d65ac2331d5abdc53f5a648a6a5a1f5ae7592d32dc591fc9a758b3ab1257e1b8fa57da3dd457d627b557483e3b570e8e9c56bfc7bf56783e00567313ea565db45b56546f6b55a729725513230654bcd09d54a71e025472a043543e69ad541c462f540323ea5379431d536534cd534139a352db9e7152a25707528e8086
  | 5, 6 => 0x8235b26281e27b4d80e1264f80b05d358008b4637ff5ca6d7f2b54c57f16eeca7e90d5af7df03e507d9965007d4b86cf7cf8d5397cf6d3fe7cb22eaf7c21af097c12c7b47bdd31107bb609047ba6e6a47b93ed8c7b2a2f5d7abc10457a536b557a4107ad79dc6473798c62ba7981428379483c7577e4b6e97789041576bc317b74f0774d7445fc9f73ceb2d773a1a5b3732e5d5c72fd4b3771d41b817164abc27067b3096e39d6ae6e07b0186dcb94656d793d846d4647206cfb26196c9e59456c7a99016c2768786b0e72456a14884469fde9b969f32b1f68f02f1c68569f856841c276681bea1d680fcd54674284cc670948f36649c29465e413f06545d33a
  | 5, 7 => 0xa4c26302a43d66d5a34b3ecaa3408b5aa282538da1b8fb5ca1353b83a131a02ba11abb7ba0969540a08d7d7fa07e9e39a06123f19f9037159f3c18119e99b8649e5e4ead9e41cb4b9df1d9529d8c55f89d6d33959d0b37fd9b7ae46d9b5e57ef9b59b8179b52641c99ba098396f910559623b561961fd95795ddeaad95d90abf95ca2238959b8b3f94af4f7193cedcf993c952f093c194d1934150989323657f92a1a34a918ca4178ec437158eb96c298eb366568e63c1ee8e1eed138c9010838c86ec9d8c7119e08c653ffc8b94c4928abe7e838ab846c18a4ab17689b7ae91883b354f87e801ec85d92a3c83a13eb483954e1b832fbd17831ede94824f3a6f
  | 5, 8 => 0xd509ba81d3a7a090d37a7dd0d0a2ade6ccf8a6fdcc4cde0bcc4b54aecbf38a6ccac949abca4be030c9e7dab2c953ca4ac7ec2c49c717b5c3c704574ac65bc9c4c642fdffc4e40fc8c472069ac45f139bc39b3328c093ba4cbe637811bc60f316bbecd07dbb3b3247b95cb04db924d80cb90293d0b8c9ad68b854e387b85351b9b8195c99b7e9a053b697836eb68001dcb67550d3b5bd3805b451df17b4507a66b37e85d3b1af6edeb1539c50b105a2e8b0810120af738777aed52e80ae52385bae1f9811ac5eb919ab77d51eaaf86c5daaf8547fa9cf8919a9b1112ea85529c4a80ffc6ea80ffa41a774f745a74c4f5da6b5b10aa68727b9a5dd9ceca4e71818
  | 5, 9 => 0xffce4ee3fb6cc09df9d265c8f521a096f1f40e1af071a98ded1a53c3ecd0d144ea4d311ee9c004f9e8b240cfe71db170e719264ce155964cdfe7a616dfc81cb2df5d775ddb74cf1bdb70b7f0da00001ed932e457d90cc7d5d8e1e1aed77a8680d77a43add75cf1ebd75aa648d696fd99d6407147d51fc248
  | 6, 0 => 0x169165ab1639ccf415df75d1149e95e0139140231384b10c1371d63d1308d5b513040abb1229e811120a383c11d87d1511ca242411a9531e1179dd1711354dd210c9b33010b0346d0fc647af0f8e874c0f7f70070f519a220eef64cc0e2bd3740de4e5590d8eb8260c752d630bf1320a0bc97d680b1b0729096ca58409668608095c87a108d5057908c9c4e3089c46e40881840408571b0908136e6307abdb9c06ce2b9006625ef20661a1d206515e6d05a14c35058db76b0579c69b04f1c5000496a9ea0439d78e0314243202dd1daa02bb415e0252db6e0229d255019b8be2017f98940161dc430106cedf00fa626600bfa51000b00d88007f2f97001342eb
  | 6, 1 => 0x33de10ec33d0399e33912a73336dd22232532e3331b4922d315ef7d931206f4a30fd210e30e98d4d30c879ff30a34fb42fcf5dca2f3f11002f213fbd2e2cfc1f2dea246b2de4d1202d39fb002d2dc1072d181cd42cf8d1752c85d29d2ba44c952b5def6d2b445ef62a4785662a14964d28e123a828916289286dc55827e0bec22772413f276f412826d98ea226d6e20925d88089256d027d2460cef0241e0c112107f47b20d9a2ad20b5476b2029ee171feb227d1f59d6a41e99d5af1e2f31c61e12d60b1d19e41a1cd4b4971c50ebcd1bf0ba501bcfd8091b80e1f01a93045d1a4aa1651a25e54c18eb00a21842c66e17f6ebbf17e7440e17e622831716b2f0
  | 6, 2 => 0x55a4124e55132306537a938f536fd4f5527526f7522f7a2c51d3495b518c772a50ec7a344f60bdc64ef3c2694ec27d104e370ae74e1de4404c70e75c4c5eea9e4be961904b7c82434b43aa054b24dacd4ad673064ab00e274a91438349ec5ad649da888548ea8e3048b30f4f482d52f647807738474b3b6046692b7346005d9d44b05249443a6f15439c04bd437c279f415e62d04156e7aa40fee4e9408b38723ff4e7d63f9f98a03f3fac893f14b8b33e8fccdc3def4a193d5ce4cc3cf5ecf33ce1dea33cbde3793c86e8d93c5848473c322f873c1f00dd3bf184cf3afdbe71390d9acb381f79ed37ab5e6137a92ee537920e9d35f3feff3541d098340ded59
  | 6, 3 => 0x83e457d783954e1b8075ba2b7f1835157e90d5af7e2bf9477d4b86cf7cf8d5397ca00f557c1e4d207b2a2f5d760cba5975b63a91743b28597434f09773c75b4c73a1a5b373993ece733458677067b3096f55d4126f286af16d1de88a6d11f7f16c9b886a6bcbe4456bb25c386a5dd02569f32b1f69855e3969727443689398a068569f85684d3db4680d7f85676ce82666f2c08566757f0f659e58df658f718a65726af76559dae66510976264a6d93363d0152b63bdb18362c4e64b616160bf6105adeb5dce918a5dc2a6755d5538605cf2c4515cec819d5cab07325c79f50d5b50c5575b1f6b375a1f5ae759e45cdf57483e3b56f5e75a56ee84b655f742d7
  | 6, 4 => 0xbfbd1b1dbe866457be637811ba85bef7b76e394bb70bf439b67550d3b5c987e1b445f381b411370db3648488b274ab73b1882ae5b168d61fb105a2e8b0810120b0703f79ae1f9811ad17dcfeac5eb919aaf8c603a7ec9d78a7e021e7a70a8d8ba5697a53a4c26302a4ba8024a4b7dc1da43d66d5a4151a87a27f3da6a1cffb8f9f39e1db9f312ef49cfb2fa99bd917499b2c18b498f0314d97cee23196f9105596833b8695db62ef959b8b3f94f47ef494af4f71919e8326918ca644918ca41790f1a11b90325ae09003d18f8ece5e378ea64c798e63c1ee8e3f0cd88cbd35308bfefd638932c4a1890ce0eb88b8c1e78816623a87fa4d4987be752186f52422
  | 6, 5 => 0xffce4ee3fbbcab3ff7be3f36f521a096f474475af2808ecbee59b066e9c004f9e9850bb8e94af8b9e5db927ee2cac633e1171c43e0c7d539decd5b5fde9e4a6cde125ae0dc4bc059db70b7f0da00001ed696fd99d64d7b1ad43aacd5d3f77d63d33caecfd124e3cccdb35a09ccf8a6fdcad24022c9644fecc953ca4ac8aee19dc801ceadc7ec2c49c716e127c5483b4bc0f73056c0f6ed83c0d7501e
  | 7, 0 => 0xe94af8b9de9e4a6cd33caecfb67550d3b168d61fa7e021e795db62ef94af4f7186f524228075ba2b7f1835156d11f7f164a6d93359e45cdf51d3495b4a914383474b3b6046692b73439c04bd3e8fccdc3afdbe71340ded5930fd210e2cf8d175289162891bcfd809139140231384b10c06515e6d
  | 8, 0 => 0x340ded59
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffffffff0000ffff0000ffff0000ffff000000000000fff00000fff00000ff000000ff000000aaaa0000aaaa0000555500005555000033330000333300000000ffffffff00000000cccccccc00000000aaaaaaaa00000000333333330000000000ff00ff00000000000f000f000000000000ffff0000000000000000
  | 0, 1 => 0xa0a0a0a0a0a0a0a0505050505050505030303030303030300ff00ffffffffff00ff00ff00ff00ff00ff000000ff000000f0f0f000f0f0f000f000f000f000f0000fffff00000000000f000fffffffff000f000f000f000f000f0000000f0000000c000c000c000c000a000a000a000a00050005000500050003000300030003
  | 0, 2 => 0x333333330000000033330000333300003330333033303330330033003300330030303030303030302a2a2a2a2a2a2a2a222a222a222a222a2222222222222222222200002222000011111111111111110fff0fff0fff0fff0f0fffff0f0fffff0f0fffff000000000f0f0f0f0f0f0f0f0f000f000f000f000c0c0c0c0c0c0c0c
  | 0, 3 => 0x5555555555555555555555550000000055550000555500005550555055505550550055005500550050f050f050f050f0505050505050505044444444444444443f3f3f3f3f3f3f3f3f3f3f3f000000003f003f003f003f00333f333f333f333f333f0000333f00003333ffff3333ffff3333ffff000000003333333333333333
  | 0, 4 => 0xa0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a0a0a0a0a000000000a000a000a000a000888888888888888888888888000000008880888088808880880088008800880077777777777777777777000077770000777077707770777070707070707070705f5f5f5f5f5f5f5f555f555f555f555f5555ffff5555ffff55555555ffffffff
  | 0, 5 => 0xaaaaaaa0aaaa0000aaaaaa00aaaaaa00aaaaa0a0aaaa0000aaaa8888aaaa8888aaaa8880aaaa8880aaaa8800aaaa8800aaaa0000aaaa0000aaaa0000aaa00000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aaa0aaa000000000aa88aa88aa88aa88aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8
  | 0, 6 => 0xaaffaaffaaffaaffaaffaaff00000000aaafaaafaaafaaafaaaf0000aaaf0000aaaaffffaaaaffffaaaaffff00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaaa8aaa8aaaaaaaaaaa88888aaaaaaaaaaa0aaa0aaaaaaaa88888888aaaaaaaa88880000aaaaaaaa00000000aaaaaaa8aaaaaaa8
  | 0, 7 => 0xcccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0ccc0ccc000000000cc88cc88cc88cc88cc00cc00cc00cc00c0c0c0c0c0c0c0c0c0c0c0c000000000c000c000c000c000bbbbbbbbbbbbbbbbbbbbbbbb00000000bbbb0000bbbb0000afafafafafafafafafaf0000afaf0000
  | 0, 8 => 0xeaea0000eaea0000eaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcfcfcfcfcfcf00cf00cf00cf00cccfcccfcccfcccfcccdcccdcccdcccdccccffffccccffffccccccccffffffffcccccccccccccccccccccccccccc0000cccccccc00000000ccccccc8ccccccc8ccccccc0ccccccc0cccccc00cccccc00
  | 0, 9 => 0xeeeccccceeeccccceeeaeeeaeeeaeeeaeeeaeeeaccc0ccc0eeeaeeeaaaaaaaaaeeeaeeea00000000eee0eee0eee0eee0eecceecceecceecceecccccceecccccceeaaeeaaeeaaeeaaeeaaeeaacc00cc00eeaa0000eeaa0000ee00ee00ee00ee00ececececececececeaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaeaea00000000
  | 0, 10 => 0xf000f000f000f000f000f00000000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeecccceeeecccceeeecccceeeccccceeeecccccccccccceeeeccccaaaa0000eeeeaaaaeeeeaaaaeeeeaaaacccc0000eeeeaaaa00000000eeee0000eeee0000eeeceeeceeeceeeceeeceeeccccccccc
  | 0, 11 => 0xf3f3f3f3f3f3f3f3f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0a0f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f000f0f0f000f0f0f00000f0f00000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0
  | 0, 12 => 0xfcf0fcf0fcf0fcf0fcf0fcf0f0f0f0f0fcccfcccfcccfcccfafafafafafafafafafafafaaaaaaaaafafafafa00000000fafaf0f0f0f0f0f0fafaaaaaf0f00000fafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaafaaa0000faaa0000fa00fa00fa00fa00f8f8f8f8f8f8f8f8f7f0f7f0f7f0f7f0f5f0f5f0f5f0f5f0
  | 0, 13 => 0xff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff000000ff00ff00cc00cc00ff00ff0000000000ff00f000ff00f000ff00cc00ff00cc00ff000000ff000000ff00000000000000fefefefe00000000fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0
  | 0, 14 => 0xffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaff00aaaa0000ffaa0000ffaa0000ffaa0000aaaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ff88ff88ff88ff88ff88ff88ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff33ff3300000000ff30ff30ff30ff30ff0fff0fff0fff0f
  | 0, 15 => 0xfff0ccc0fff0ccc0fff0aaa0fff0aaa0fff00000fff00000fff0000000000000ffeeffeeffeeffeeffeeffeeccccccccffe0ffe0ffe0ffe0ffccffccffccffccffccffccccccccccffccccccffccccccffcc0000ffcc0000ffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaacc88cc88
  | 1, 0 => 0xfff0fff0fff0ff00fff0fff0fff0fcf0fff0fff0fff0ccc0fff0fff0fff00000fff0fff0ffe0ffe0fff0fff0ffc0ffc0fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff0fef0fef0fff0fff0f0f0f0f0fff0fff0eee0eee0fff0fff0ccc0ccc0fff0fff000000000fff0ff00fff0ff00fff0fcf0fff0fcf0fff0f0f0f0f0f0f0
  | 1, 1 => 0xfffafffa00000000fffafff0fffafff0fffafff0fff0fff0fffafff0aaaa0000fffafff000000000fffaccc8fffaccc8fffaaaaa00000000fffa0000fffa0000fff8fff8fff8fff8fff8fff8fff0fff0fff5fff5fff5fff5fff3fff3fff3fff3fff30000fff30000fff1fff1fff1fff1fff0fff0fffffffffff0fff0fff0fff0
  | 1, 2 => 0xffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff0000aaa00000ffff000033330000ffff000000000000fffefffefffefffefffefffeccccccccfffe0000fffe0000fffcfffcfffcfffcfffcfffcccccccccfffcfffc00000000fffcfff0fffcfff0fffafffafffafffafffafffafff0fff0fffafffaaaaaaaaa
  | 1, 3 => 0xffff8888ffff8888ffff8888ffff0000ffff8800ffff8800ffff5555ffff5555ffff5555ffff0000ffff5500ffff5500ffff4444ffff4444ffff3333ffff3333ffff333300000000ffff00ffffff00ffffff00ccffff00ccffff000fffff000fffff000cffff000cffff0000ffff0000ffff0000fffc0000ffff0000fff00000
  | 1, 4 => 0xffffccccfff0ccc0ffffccccccccccccffffccccaaaa8888ffffcccc00000000ffffccc8ffffccc8ffffccc0ffffccc0ffffcc00ffffcc00ffffc0c0ffffc0c0ffffc0c0ffff0000ffffc000ffffc000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaacccc8888ffffaaaaaaaaaaaaffffaaaa00000000ffffa0a0ffff0000
  | 1, 5 => 0xffffff00ff00ff00fffffcfcfffffcfcfffff0f0fffff0f0fffff0f0ffffc0c0fffff0f000000000fffff000fffff000fffff000ffff0000ffffeeeeffffeeeeffffeeeeccccccccffffeeee00000000ffffddddffffddddffffccccffffccccffffccccffffccc0ffffccccffff8888ffffccccffff0000ffffccccfffccccc
  | 1, 6 => 0xffffffff0000000fffffffff00000000fffffffcfffffffcfffffffc00000000fffffffafffffffafffffffa00000000fffffff0fffffff0fffffff0ffff0000fffffff0fff0fff0fffffff0fff00000fffffff000000000ffffffccffffffccffffffaa00000000ffffff00ffffff00ffffff00ffffcc00ffffff00ffff0000
  | 1, 7 => 0xffffffffaa00aa00ffffffffaa000000ffffffff88888888ffffffff88880000ffffffff88808880ffffffff88008800ffffffff55555555ffffffff55505550ffffffff44444444ffffffff11111111ffffffff0f0f0f0fffffffff05050505ffffffff00050005ffffffff0000ffffffffffff0000ccccffffffff00005555
  | 1, 8 => 0xfffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffccccccccffffffffcccccc00ffffffffccccc0c0ffffffffcccc0000ffffffffccc0ccc0ffffffffccc00000ffffffffcc00cc00ffffffffc8c8c8c8ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaaa0aaa0ffffffffaaa00000
  | 1, 9 => 0xfffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffffcfffcfffffffffffcccccfffffffffffc0000fffffffffff0fff0fffffffffff0ccc0fffffffffff00000ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffcfcccccfffffffffcfc0000
  | 1, 10 => 0xfffffffffffffffffffffffffffffff0
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x11754984f189a2e1c4152633
  | 3, 0, 0 => 0xce4750a694992690a634954350a694882b152694c644152634974350a694882a90a5c4882a50a634c04790a6940044152633b75524c9e4c14750a694aa4415a63498c110a694b7441506949945d58694
  | 3, 0, 1 => 0xb73fd0a604b44850a694c6552209e4882a4c24b4c655134694882e95263488214c6594882b0c25c4881f0c2594882b0d25c4b7441585c4a24414e69488214c65c49948540694994410a654a64410a684
  | 3, 0, 2 => 0xce4414e694b34410a694b744152634954410a684c644152694bec4152694b2bfd0a6946f30952614991f0c25546f2e9585c48ba14c2594
  | 4, 0, 0 => 0xb7441a4a934ab7974a94298d6d110429a4c2b6e964410a6959947e208534ae129110429a56dd697fa14d2b849944124855c64ca1c8534adba6512429a566510429b8d2b6e7ca14d2595c6462208534adba6517429a57275488214d2b9c88214d2575
  | 4, 0, 1 => 0xb74ae208534ae326505429a57193285a14d2b6e8ea14d259599441488534acfa2085349855bcba55214b8b9a994410a695b74ca209c42adbe6510429a56f53288214d2b106f214c25c5bf4410a692cacca2085309716dd3260a14d2b8c994410c695
  | 4, 0, 2 => 0xb74ca2c8534adbaa710429a56651077a14d2b6e8f3f50a695c4cca208534acca2e853498571d3288214d2b8b994410a695a1cca208534adba7310429a56dd1a88214d2b6e93c410a695b7586208534adba64d44ba15704ed5d214d2b8c984410a695
  | 4, 0, 3 => 0xc34ca208534adba6507429a5665104b214d2b3291214c2555b54ca208534ae12a910429a55bcba562a4d2b32883890a695b74410a692d2e31bcba5498d7296888214d2b6ea3c410a695c64ca4c7b34acca20924821566510429ccd2b6e883b10a695
  | 4, 0, 4 => 0xce4c2208534adba7910429a566516429a4c2b7c994410a695a237974a734ae426510429a566526882b0d2b32882b0d24b5b752a208534ab797485319717193288264d2b63994410a695b74410a692dae3220a934965698de5d214d0b6e88214d8695
  | 4, 0, 5 => 0xa54410a6930acca3310429a56dd4a882790ab3288214d2365b74410a692c2e327f10429a572f5488214d2b3288214d2315cb552208534adc66510429a56dcde5d2b0b8b6e6f30952695becfe208534ae3265104ba156dd323e1a4aab1f88214d2595
  | 4, 0, 6 => 0xce3b5748534ae3264d4429a56dd10429a45cb7b994410a695aa506208534adba6510429a167910429a4c2b32883550a695883bd0a692cab7974ac3497171310429a4b2b8e88214d259599441e08534acc9a8aa429a56dd5588214d2b6e882a50a695
  | 4, 0, 7 => 0x6f2e90a632cae32dd10549a56dd3288214c0b1054a14d2615c64ca207c34adba6510428a57193286a14d2b8688214d2595ab552208534ac7e3110429a57193188214d2b32944410a695aa441948534acca20853488d5bcba56184b8b54882e958695
  | 4, 0, 8 => 0x6f2e9526125ad125510429a5665104da14d2b91994410a695b752e208534adba2085309716dd1075214d2b6e994410a695b74ca209834ad966510429a57115488214d2b6e88214d25c588214d261172dba649a429a566510429a42eb8c6f2e95a5c5
  | 4, 0, 9 => 0xc6441448534acca209e4da156dd3288208d2b3288214d2615b74ca209e42a802208531965265104298caab10552890a69588214d2612e2dba7510429a5620f242984b2b76994410a695992690a6930acca2085349896dd324f2690ab8cae4410a695
  | 4, 0, 10 => 0xb74410a6919adba2098349657396788214d2b6588214d2595994413c8530adba6710429a56dd1388214d2b328828d0a695ba4ca208534adc26510429a56dd32429a48ab5488214d22f5b74fe2e8534ad1220853495d6dd32882450ab6e8823d0a695
  | 4, 0, 11 => 0xb74be208534acca3f103e1a56cb107ea14d2b6e994993c855cccca208534adba65173e1a5665107d214d2b9cadc410a695c64410a632cacca20ad4298d7195488214d2b6e88214d25d5b754a208534adba8110429a56dd1062214d2b73994410a695
  | 4, 0, 12 => 0xc64ca2e8534adbaa910561a56af3288214d2b6ea84410a695b74ca1c8534ae7a9910429a56f35488214d2b6e88214d22759946e208534adba9f10429a56dd326325d0ab5488214d2635c452a208534ae729910429a56208534984b2b87994410a695
  | 4, 0, 13 => 0xa0cca208534acca2085351a5718de5d2a4d2b6e9ac410a695994410a612b2c4194c7429a5400de5d2b0b897d6f2e952695b74410a69232dba6505429a56dd4688214d2b32882750a695c2cca208534ae5e6510429a572d3288214d2b6e994413e695
  | 4, 0, 14 => 0x88214c25925a8031910549a52dd3f88214d2b6e8827cd2595994414e6930ae326510509a56dd328825d0ab96b4c410a695c655220ad34ac6e20853496571954881ecd2b6e88214d25f5cb4aa208534adb9bcba5498d6dd328829cd2b2a6f2e90a685
  | 4, 0, 15 => 0xb74ca1a8534acfe2085349856f13288214d2b799e4410a695c64ca2085342cca2097429856dd326a214d2b4188214d2595c4d52208534adba3910429a57191054a14d2b6c994410a695954410a6933ac410a69178b96dd104296414b9b994110a695
  | 4, 1, 0 => 0x914410a612cae026510429a57394e88214d2b9cafc410a695c64ca208534acca207c349856dd3288278f8b96984410a69599441548534ae32649a429a5738de5d29cd2b6e992790a555b74ca2085152cc9549a429a56dd4b881f0d2b6e99440f8695
  | 4, 1, 1 => 0xcf4aa208534adba6510441a57392a88214d2b8088214d2595b74ca208e42adba651d429a571910429a4b2b6eacc410a695882a90a692cae326510429996551086214d2b6e9dc410a695c64ca209e42acca4285349516dd32931f0d2ade61214c2595
  | 5, 0, 0 => 0x5ba2085348216dd6daa4410a696ca5ba6510429a5b3d8c994410a696c0dba6510429a5add32803790a696b756a6510429a5a6510429a4c2616c64ca208534855a64ed5d214d2616b751dbcba429a5add3263214f06969948a3f10429a5b31328840d0a696994415aaa429a5add328ac410a696
  | 5, 0, 1 => 0xb74ca20ab429a5a64de642e90a696c2551bcba429a5b196eaa4410a696b74ca2085348f5a64ba4a214d2616b74ca20cd429a5a6510429a4c2076b74ca20f7429a5b1932882c90a696b74ca4710429a5b193288214d204699389bcba429a5add106ba14d2596005ba6517429a56dcde5d214d25a6
  | 5, 0, 2 => 0xb7529bcba429a5b19326f2e932696c64ca208534939a652a8840d0a696b74410a692c889ac7326f2e90a696b7516208534965b18de5d2a4d2596b74ca20ba3e1a5a6510429dcd2616c34c9bcba429a5801328fc410a695c64ca20ad429a5adcde429a4b2186993797496429a5add54732e90a696
  | 5, 0, 3 => 0xc64ca20db429a5b21326f2e90a696b74ca20853490dadd3288214d2536b7552208534955a65105d214d22f6b74ca20f5429a5add10429a4b23f6cb4ca20fd429a58016eaa440d2305b74ca20fe429a5a6510429a4c20e6b74c9bcd4429a5add3288214d22b69937974ac3492dadd32883e10a696
  | 5, 0, 4 => 0xc64c9bcb9429a5add10429a4c2596b75522085348c1a65105d2a90a696becfdbcba429a5b19326f2e92e856b74ca208534891add36994410a69699442208534985add325d2290a696b74ca208b429a5add3c6f2e90a696be4c9bcba429a5add10429a4d2596b7409748534965add3288214e2696
  | 5, 0, 5 => 0xb7551d0ba429a5afb32882e90a696c64fdbcba429a580132883bd0a695b7441dc8534965add328830d0a696006266510429a56dd64994410a6960063a6510429a56dd3288214d20f6993797485348c5b096e994410a696b8cc9bcba429a5add3288214d2516ca4ca208534985add32883650a696
  | 5, 0, 6 => 0xb74ca208534885adcde5d2a50a696b74ca2085348ddadd326f2f90a696c660e6510429a5a65107c214d2616b7576a910429a5b1932882e90a696b74ca208534809add42994410a696b74ca20bc429a5a64de5d214d236699379a4ba561a5add3288214d2396b7441d6ba429a5b398f994410a696
  | 5, 0, 7 => 0xb74c9caba429a5b12de5d214d2596b74ca20f3429a5add327cab50a696c7dbaa910429a5b396eaa4410a696c7379748534965a64f06f2e90a696b74ca2106429a5add32883810a696b74ca20853d1a5add60882e90a696b7551bcba439a5add3290c410a696b7555bcba429a5b19328821506696
  | 5, 0, 8 => 0x9944198ca429a5add48882e90a696005ba9510429a56dd32883ad0a696b74ca4d10429a5aa9416f2e90a696b74c9bcba429a1add32882e924856b755220853d9a5a78de5d214d261699379aaba429a5add3288214d203677b79748534965add58aa4410a6960061a6510429a56dd3288214d24b6
  | 5, 0, 9 => 0xb74ca208534959aa8de652e90a696b755220b2429a5adcde5d214e0696c3525bcba429a5b296e88214d2596c64ca20853f1a58016e9e4410a3f59937974853488dadd326f3010a696b73797485348b9add3288214d2116b7441d6de429a5add3288214ea696c64ca5d10429a5b2d6e994410a696
  | 5, 0, 10 => 0xcc6326510429a5af332882e90a696b74b620ba429a5b0cde5d214d2596ab551bcba429a5aff6e994410a696b74ca20853482dadd32882b90a696b74ca20d0429a5add60883790a696b759e6510429a5add328821502696005ba7910429a5665105d214d2636005b90a690a8396dd60994410a696
  | 5, 0, 11 => 0xb74ca20a1429a5b196e6f2e952696b74ca20853c1a5add48883790a696b74ca208534979a652188214d2616b74c9bccf4ba159bcba54a14d2616b7545bcba429a5add328837924856b74ca2085348258018c88214d20e5b74ca208534929b076e96c410a696b74ca20b1429a5b093288214ee696
  | 5, 0, 12 => 0xc64c97485348859bcba429a4c22e6005ba20a9429a56dd326eae90a696c64ca5510429a5add3288214d20a6b74ca20a2429a5af8de5d214d25969949a208534985add5b994410a696994410a693092da64e55d214d2616b73798eba429a5add326f214d23a6b74c9bcc9429a5add41994410a696
  | 5, 0, 13 => 0xb74ca20853499db19326f2dd0a696b7379748530971add3273ae90a696b75326510429a5adcea6f2e90a696b74c9bcba429a5add326f2e930696c64c9e6ba429a5acb326f2e90a696b74ca2085359a5add32883690a696b74410a692c945add326f3390a696b7379748534971add3288214d2486
  | 5, 0, 14 => 0xb7521e6ba429a5b195c6f2e90a696b74ca208d429a5add326f214d24f6c65a66510429a5a892a6f2e90a696b74c9f0cf429a5add327cb790a696994410a6930929add32882d90a696b74e26510429a5b19105d214d2596b74ca4b10429a5b23326f2e90a696005ba2085348b97076eaa4410a696
  | 5, 0, 15 => 0xb75526510429a59e4de5d214c2596004ca2085349017116e994410a696ce6626510429a5add32883610a696bb4c9bcba429a5add328840d0a696b74ca208534879b1932833790a696c64ca14ba429a5a64de5d214d2626b74ca02de429a5b19606f2e90a696ce4aa20ba429a5add5488214d25c6
  | 5, 1, 0 => 0xb74ca20853b1a5a64de5d214d2616b74ca208534881add3288214d21b6b74ca2085421a5add326f2e93c856b755220ff429a5800de5d214c6595b75a220ba429a5b193288214d25966f2e954a2429a5add60833790a6966f2e90a6930971add32842e90a696b74ca20853491dadd3a6f2e90a696
  | 5, 1, 1 => 0xa237974853495dadd328838d0a696b7521bcba492158016e994410a3f5b74c9bcba48a158016e88214d25c5b74ca207b3492dadd328825d0a696b7379748f429a5b18de5d2890a696b74ca208534875add3288214d2416ce4ca5510429a5add32914410a696005ba649a429a54016e8821d0a695
  | 5, 1, 2 => 0xba4c9bcba429a5ae1326f2e90a696b74ca2eba429a5a651081a14d2616b74ca208534801add325d25d0a52600632648534855727326f2e90a696aa3797485348bdadd326f3090a696005ba6510429a571932883c90a696c74ca20b2429a5add3288214d2166005966510429a56dd326f2cd0a696
  | 5, 1, 3 => 0xb7441b48534965add4a88214f6696b74ca20853484dadd34994410a696b74c97485348d5a651f882e90a696b74c9c8ba429a5add325d25d28856c54c9bcba429a5add328832d0a696c64ca20fd429a5aa93288214d26169937974a3429a5add32883f10a696b74ca208534869add3288214e8696
  | 5, 1, 4 => 0xb7379748534975add526f2e90a696b739d748534965add32882bd0a696b7501bcba429a5adcde622e90a696005ba2069180b96652288214d2616b7379749834965add3288214d22d6cadba6510429a5add32882fd0a696b74ca20c5429a5b056e994410a696b74ca2085429a5add326f34924856
  | 5, 1, 5 => 0xc6379748531965a64de5d2b50a636004ca20851f81d664de61214d2616004ca2085349854016e994413c855b74c9bcb5429a5add3288214d2546b74ca20f1429a5add3288214d22f6b74c9bc8534911b19546f2e90a696004ca2085308fd6dd3270ae90a696b74ca208534821a64de552350a696
  | 5, 1, 6 => 0xb74ca208534841add5488214d2596b74f5bcba429a5adcde5d214e4696b74ca20f256a15b376e994410a696004ca20853481d729328840d0a696b7442068534965add3288214d2526c4cca20ba429a5add10429a4602e6c64c9bc8d429a5a64fa6f2e90a696ce56dbcba429a5add54833790a696
  | 5, 1, 7 => 0xaa37974853498dadd3288214fa696994415e8534985a80de5d214d2616ce531bcba429a5add328bb090a6966f2e90a6930965add32934890a696b74ca20fb429a5add3288214d2286b74bdbcba429a5afb6e994410a696b74ca4910429a5add328824d0a696b7421748534965add3288214fe696
  | 5, 1, 8 => 0x994410a6930949b193288214d23f6b74c9bc8534865add186f2e90a696c64ca208534889add3288214d2556b752a20ba429a58016e99440d2305994410a6930951b3d4c6f2e90a696c4cca20853f1a5af3546f2e90a696b737974853489dadd32884310a696b74410a692c9058016e994407e305
  | 5, 1, 9 => 0xb7519bcba429a5af36e994410a696c2cc9bcba429a5add32742e90a696cfdba6510429a5b056e88214d2596b74ca20853498db2d326f2e90a696b74ca2085348c1add546f2e958696abcc9bcba429a58018caa4410a695b74ca208534899add54883f50a696b74ca12ba429a5add3288214d2646
  | 5, 1, 10 => 0xb75626510429a5b193288214d20e6b74c9ccc2429a5add356f2e90a696004ca20691801d7396e994410a6966f3298eba429a5add3f88214d24b6004410a69309656dd3288c410a696b744174a9429a5a6510429a4c2556c64ca20853b9a580132881a4c2305c64ca20853481dadcde5d214d2466
  | 5, 1, 11 => 0xc64ca2110429a5aef326f2e90a696b74ca2085348c9add327a2e90a696b74ca2092429dda6510429a4c2306b74c9bcba539a5b3d6e994410a696b74ca20853485580110429a4b2075b74c95a9a429a5a83326f2e90a696b74ca20853d9a5a64de5d214d4696b74c9d2ba429a5af33288214d23f6
  | 5, 1, 12 => 0x994410a7b34985add3267a14d2526b74ca1eba429a5add32882790a7b6c64ca20f8429a5b393288214d2616b753a6510429a5add5f994410a696c6551bcba569a580196994410a695b757aa910429a5add3288214f2696b74ca20ad429a5a64e85d214d2616b74ca20a9429a5add3288214d21f6
  | 5, 1, 13 => 0xb74ca2089429a5b076e994410a696b74ca20ba429a580141994410a695b2cca20ba429a59bcba42984b24b600631bcba549a56651056a14d2616b75466510429a5add3f6f2e90a696b74ca208534925a64de5d29cd2616b74c9749a429a5add326f2e92e856994410a6930855add32882190a696
  | 5, 1, 14 => 0xb74c9e4c6429a5add32994410a69699379749742985add328fc410a696a0b79748534965b13546f2e90a696b737974a6429a5add324a2350a696b74ca4c853d9a5b18de5d2a50a696b74ca208534851add3288215066969537974853499d9bcba429a45e2e6b74ca208534909adcde5d214b20a6
  | 5, 1, 15 => 0xcc5ba6510429a5a65105d214d2616b74ca20ba4f215add1054a14d2596d0dba6510429a5add326f2ed0a696b74ca20ff429a5add4d6f2e90a6969fb79748534985b1932934410a696bccf1bcba429a5add3288214d23c6c64c9bcba429a1add3288214d2016c64ca20853492dadd3288214d2066
  | 5, 2, 0 => 0xb74c9748534885add32954410a696b74ca20c2429a5add3288214d20c6b74c9bcba428a9adcde5d25d2a856b75ae6510429a5add3f6f3090a696b74ca2085348958016e9fc410a695b74ca20d6429a5b416e994410a696b74ca20dc429a5a651042a0cd2616b74c9bcba3e1a58016e994412e855
  | 5, 2, 1 => 0xb74ca2f10429a5b1954882e90a696b4d966510429a5add3291440f8696c64c9bcba429a5b076e88214d2596005ba64d4429a57313288214d2616b74ca208534835add3288215006969bcc9bcba429a5add3279ae90a6969937974aa429a5a6510429f8d2616b74ca4485349558013288214d2055
  | 5, 2, 2 => 0x5ba64851f8557316e88214d2596b74ca20853e1a5a20ba429a4c2596b74ca208534931a64f35d214d2616b74ca2085349658016e99440f8695994aa208534985add3288214d2576ce539bcba429a5add328a4410a696004410a690701d7395f6f2e90a696b7571bcba429a5ae56e994410a696
  | 5, 2, 3 => 0xc64ca2085429a5add596f2e90a696b74ca5310429a59bcba55214d2596006326510429a56dd32882310a696b74ca4110429a5add3288214d2346994410a693095dadd326a2510a696006326510428fd4016e99214d2155b74ca20f2429a5b1932914410a696004ca20aa429a56dd3b6f2e90a696
  | 5, 2, 4 => 0xb7552a910429a5add32984410a696cf4a9bcba429a5add32914415a856ce4a9bcba429a5add326f2350a696b7379748531965add3269ae90a696004c90a693085571932882bd0a69699441e48534985add326f2e91c856b74ca2085348e1b18de5d214d2596b74ca20c6429a5add328ba14d24b6
  | 5, 2, 5 => 0xb74ca2110429a5add32882790a696b74ca209a429a5add3288214d2076006725510429a56dd3288214d2126006322085349656dd3288214d2696ce37974853495dadd3288214d23f6b74ca2085369a5add32429ecd2556005ba64691805573b6e994410a696
  | 6, 0, 0 => 0xb74c9c0de5d214d2f6e99379748534941edcde5d214d259073e3264de5d21506697b74c9bcba429a442e00ca5ba6510429a5add326f2e90a691bbdbad332882e90a697c660e64de5d214d2f327c379748534985c016e99214d22210b5ba652a883790a697b7576a8de5d214d2f6e9937dbcba429a5edcde5d214ee692cbdba85326f2e90a697
  | 6, 0, 1 => 0x63264de429a444d6e9937974853a9a5f193297379748534bcc9bccc652e90a697b74ca20ba429a4b2e00b74ca20f8429a5add3275b79748534bdba65266f2e90a697b74c9bcba429a406f6eac551bcba429a5c018699379748534b5ba64de5d214d24b7b74c9e6de5d214d2f8fb7551bcba429a5f396eaa379748534bdba65066f2e90a697
  | 6, 0, 2 => 0xb74c9bcba58a14d2f849937974853b9a5edd546f2e90a69273dfedd326f2e90a697b74c9bcba429a416f6e9937974ae429a5edd326f341748534b802dd3c6f2e90a696b7551bcba56a14d2f6eb04c9bcba429a5edd546f2e9648534be52dcde5d214d2597c64c9bcba429f8d2e00b74f1bcba428fdadd106f2e90a692cbe7add546f2e90a697
  | 6, 0, 3 => 0xb74ca20fd5d214d2f6eadcc9bcba429a5e64de5d214d26125bdba83326f2e90a697b74c9bcba429e0d2f6e99379a4ba429a5c016e992e90a690ab5ba64de5d214d25e7b74c9bcad46a14d2f6ea44c9bcba429a5edd32883c9748534bdd6dd326f2e90a697b74c9bcba429a412e00c6379748534839add326f2e90a69253e0edd2d6f2e90a697
  | 6, 0, 4 => 0x5ba64bd5d214d2d6e9937984853492dc016e994410a6925b5ba64de68ae90a697b74c9bcba429acd2f6e99379b4ba429a5edcde5d214d25928bdba64f8792e90a697b74c9bcba429a490f6e9944198ba429a5c016e6f2e9528534b632652a6f2e90a697b74c9bcba429a414f6e9937974a2429a5f396eb1379748534b8031932882e90a696
  | 6, 0, 5 => 0xb74c9bcd85d214d2f6e9937974b8429a5edd3281b79748534bdba64de5d214d21e7b74c9bcba429a47cf6eaa379748534971edd32812e9648534bdba64de5d2350a6979937974853498494f6e9937974b6429a5edd3899379748534b802dcde5d214d22e6c1dbaa8de5d214d2f6e9937974853499dedd4c99379748534b802dd32934410a696
  | 6, 0, 6 => 0xb7551bcba5a214d2e00b73797487429a5add326f2e90a7634bdba65106bae90a697b74c9bcba429a440f6e9937974853486dedd326f2e90a8434b802dcde63ae90a69699379b4ba429a4c2e00b74c90a691106db19326f2e90a692cb802dd3288214f0696b74c9bcba429a48ef6eaa4c9bcba429a5c016ea8b79748534b00264de5d214d2406
  | 6, 0, 7 => 0xb74ca20ba429a47ef8c993c9bcba429a5c016e5d214d21b07363a64de5d2c90a697005ba65106d214d2d6e99441748534889edd3271b79748534bdba8b32882e90a697005ba64de5d2147ec00b7379748534971b256e99379748534bdba64de5d25d0a697b74c9bcba429a43af6e99379748534905f393295379748534bdba65226f2e90a697
  | 6, 0, 8 => 0xb74c9bcbf5d214d2f6e993798aba429a5e64de5d214d2610dbe0add326f2e90a697b74ca20de429a444f6e993797485429a5edcde6d2e90a692cbdbac5326f2e90a697b74c9bccb5d214d2f5499379748534985edd3288379ae8534bdba64de5d214d21a7b74c9bcba429d0d2f6e99379748534801edd327b379748534b802dd326f2e90a696
  | 6, 0, 9 => 0x5ba652288214d2c009937974851f81d801326f2e90a6930b002dd3288214d21b6b74c9e2de5d214d2f6e993797485348bdedd32882e90a7734b80264de5d214c23f6b74c9bcba429a410e00b74ca10ba429a5add32882e90a6903b802dd54994410a696b74c9bcba57a14d2e00b73797469180b98016e99442068534b656dd326f2e90a697
  | 6, 0, 10 => 0xb74c9bcba429a450f6e99441bc853b9a5c019399379748534b5ba64ba429a444217005ba64de61214d2d7db74c9bcba429a5c0000b74ca208534adba6510882e90a697b74c9bcba49a14d2f6e9937974853f9a5edd546f2e90a692cbdba64f26f2e95a85700002dd32882147ea009937974853481dadd326f2e90a69293db9bcba429a4602e7
  | 6, 0, 11 => 0xc64c9bcba429a47ee00b74ca20af429a5b19326f2e90a69113dba64de5d214d2557b74ca20f85d214d2f6e9937974b0429a5c016e99379746918362664de5d214fc697993c5bcba429a4c2f6e6f2e90a692c905f19326f35d748534b802dd326f2e87e306b74c9bcba429f4d2f326f2e95e8534985f296e99441748534bdba64fb6f2e90a697
  | 6, 0, 12 => 0xc64c9bcba429a40ee00004ca20853481d6f36e99379748534bdba64f35d214ee697b74ca20f86f214d2e00b74ca208534949b3f6e99379748534be0adcde5d214d2597b74c9bcba429a4c6f6eb1379748534965c0000994410a6930adba64de5d214d230700632a8de5d214d2d6e99379748534899f296e99441bc8534bcc9bcba429a4c2527
  | 6, 0, 13 => 0x2dd32881a460b6e9949a20ba429a5edd326f2e90a690ab801bcba429a4b2076b74ca20ba429a496f6e9937974853d9a5ef3326f2e90a691fbdbab1326f2e90a697b74c9bcba429a49af8c99379748534839c01326f2e8d23003b672dd326f2e90a697b74fdbcba429a496e006f2e90a6930965b19326f2e90a7734b80264de5d1a4c2306
  | 6, 0, 14 => 0x5ba64e85d214d2d6e99379748534871edd5f99379748534b802dd3288214d2306b757aa8de5d214d2f6e993c9748534949edd326f2e90a7934bdba64de5d2b50a697b74c9bcba54a14d2f6e9937974853487df193288379748534bdba64de5d214d2327005ba6510429a4aad6e993797492429dde64de5d214d261183e7add326f2e90a697
  | 6, 0, 15 => 0x5ba64de428fc44c00b74ca20ad429a5add326f2e90a8334be0edd326f2e90a697005ba6510429a42ad6e9937974ba429a5c014199379748534b002dd3288214f66969937974ad429a4c2f6ea8cc9bcba429a5c019cb74ca208534b5ba64de5d2190a697b74c9bcd2429dcd2f8c993e1bcba429a5f39326f2e90a6930bdba9d326f2e90a697
  | 6, 1, 0 => 0xb74c9bcd65d214d2f6e99379b8ba429a5e64de5d215066930bdba6522882e90a697c1cc9bcba429a4c2e00b74c9bcba4ba15b316e99379748534bdb9bcba54a14d2597d0dba64de5d214d2f6eaa4ca20ba429a5edd326f2e90a6900be3264de5d214d24b7b74c9bcba429a40cf6e993798c8534949edd3299379748534b802dd326f214d2226
  | 6, 1, 1 => 0xc1db9bcba429a4b2f6e9944174af429a5edd326f2e90a6906bdba64de5d2950a697b74c9bcba42a00d2f326f2e90a7e34985c01326f2e90a6902b002dd328821506696004c9bc853498444d6e994a9bcba429a5c0183b74ca208534b5ba64de612e90a697005ba65105d214d2c00b74ca20ba428fdadd326f2e90a6912b802dd3f6f2e90a696
  | 6, 1, 2 => 0xb74c9bcba429bcd2e00b74c9748534885add326f2e90a69263802dd32954410a696c655264de5d214d2e009944174853481dadd326f2e90a692cbdba65105d214d2527994a9bcba429a4c2e00cc5ba6510429a58016e99378d2301135ba64de5d214d2577004ca20ba429a4c2d6e993797485348edc00de5d214d20e03b5cadd326f2e90a697
  | 6, 1, 3 => 0xb74c9bcc65d214d2f8c993797485429a5c016e994410a692cb5ba65105d214d230799379748534984b2f8db74c9bcba429a5c018c99379748534b5ba64de5d2310a69799379748534984aef6e99441748534955c018c9937974851fb002dd32882e8d2306b74ca20de429a4a4f6e993c9bcba429a5c016e993cd748534b00264de5d2a90a696
  | 6, 1, 4 => 0x4c9bcba429a408d6e993797485348fdedd326f214ee69273dba65105d2b50a69700003193288214d2b9db74c9bcba429a5edd54aa379748534b800016e99214d2155b74ca20ba429a42af6e6f2e90a692c965c016e99441e48534b5ba65105d214f6697ce5ba65105d214d2f8c9937974af429a5e64f26f2e90a6930bdba64de5d214d2387
  | 6, 1, 5 => 0x5ba6510429a47ed326f2e95aaa429a5edd3288379748534bcc9bcba429a4d2617993797485349847ef6e994417485419a5edd546f2e90a69043dba65105d2e90a697b74c9bcba429a40ef6e993797485348b1f19326f2e90a69183803392a6f2e90a696005ba64de46a14d2c00c6379748534965add326f2e90a6934b80319326f2e8d2306
  | 6, 1, 6 => 0xb74ca2110429a5add326f2e90a6907bdba64de5d22d0a697005ba6510429a40ed6e9937974853490de64de5d214d261073dba64de66ae90a697
  | 7, 0, 0 => 0x5ba64de5d214d230700002dd326f2e8d230600000016e994410a6950000264de5d214d2076005ba64de5d214d25270000264de5d214d2616005ba64de5d2bd0a697005bac5326f2e90a69700002dd326f2e90a69600002dd326f2e90a3f6005ba64de5d214d21b7005baa9326f2e90a697005ba64de6d2e90a697005ba64de5d214f0697005ba64de692e90a697005ba64de5d214d24b7
  | 7, 0, 1 => 0x5ba65106f2e90a697005ba64de5d214d2077005ba64de5d214d23f70000319326f2e90a696005ba64f26f2e90a697005ba64de5d214d2597005ba652a6f2e90a69700002dd32882e90a69600002dd326f214d2226005ba64de5d215066970060edd326f2e90a697005ba64de5d2b50a69700672dd326f2e90a697
  | 8, 0, 0 => 0x2dd326f2e90a696
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
private theorem z3_24 : span (Z 3) 19 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 43 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 19) z3_0 z3_24

private theorem z3 : span (Z 3) 43 0 = true := z3_a1

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

private theorem z4 : span (Z 4) 288 0 = true := z4_a11

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
private theorem z5_600 : span (Z 5) 6 600 = true := by decide +kernel

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

private theorem z5_a25 : span (Z 5) 606 0 = true :=
  span_join (f := Z 5) (a := 600) (o := 0) (b := 6) z5_a24 z5_600

private theorem z5 : span (Z 5) 606 0 = true := z5_a25

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
private theorem z6_336 : span (Z 6) 23 336 = true := by decide +kernel

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

private theorem z6_a14 : span (Z 6) 359 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 23) z6_a13 z6_336

private theorem z6 : span (Z 6) 359 0 = true := z6_a14

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

def CG : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12589

theorem PEqualNP.Outside.L_meta_12589 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008234184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008234184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12589.mainG PEqualNP.Outside.L_meta_12589.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12589.CG, PEqualNP.Outside.L_meta_12589.CG_mono, by
      have : PEqualNP.Outside.L_meta_12589.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12589.CG_eval⟩
