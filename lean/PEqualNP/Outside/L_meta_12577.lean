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
namespace PEqualNP.Outside.L_meta_12577

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 10, 0, 12, 0, 0, 0, 16, 17, 18, 0, 20, 0, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 5, 6, 7, 3, 9, 3, 11, 3, 13, 14, 15, 3, 3, 3, 19, 3, 21, 22, 23, 3, 25, 3, 27, 3, 29, 30, 31, 3, 3, 3, 35, 3, 37, 38, 39, 3, 41, 3, 43, 3, 45, 46, 47, 3, 49, 3, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 3, 5, 5, 6, 7, 5, 9, 5, 11, 5, 13, 14, 15, 5, 5, 5, 19, 5, 21, 22, 23, 5, 25, 5, 27, 5, 29, 30, 31, 5, 5, 5, 35, 5, 37, 38, 39, 5, 41, 5, 43, 5, 45, 46, 47, 5, 49, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 6, 6, 6, 3, 6, 5, 6, 7, 6, 9, 6, 11, 6, 13, 14, 15, 6, 6, 6, 19, 6, 21, 22, 23, 6, 25, 6, 27, 6, 29, 30, 31, 6, 6, 6, 35, 6, 37, 38, 39, 6, 41, 6, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 3, 7, 5, 6, 7, 7, 9, 7, 11, 7, 13, 14, 15, 7, 7, 7, 19, 7, 21, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 3, 9, 5, 6, 7, 9, 9, 9, 11, 9, 13, 14, 15, 9, 9, 9, 19, 9, 21, 22, 23, 9, 25, 9, 27, 9, 29, 30, 31, 9, 9, 9, 35, 9, 37, 38, 39, 9, 41, 9, 43, 9, 45, 46, 47, 9, 49, 9, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 11, 11, 11, 3, 11, 5, 6, 7, 11, 9, 11, 11, 11, 13, 14, 15, 11, 11, 11, 19, 11, 21, 22, 23, 11, 25, 11, 27, 11, 29, 30, 31, 11, 11, 11, 35, 11, 37, 38, 39, 11, 41, 11, 43, 11, 45, 46, 47, 11, 49, 11, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 5, 6, 7, 13, 9, 13, 11, 13, 13, 14, 15, 13, 13, 13, 19, 13, 21, 22, 23, 13, 25, 13, 27, 13, 29, 30, 31, 13, 13, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 5, 6, 7, 14, 9, 14, 11, 14, 13, 14, 15, 14, 14, 14, 19, 14, 21, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 5, 6, 7, 15, 9, 15, 11, 15, 13, 14, 15, 15, 15, 15, 19, 15, 21, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 5, 6, 7, 19, 9, 19, 11, 19, 13, 14, 15, 19, 19, 19, 19, 19, 21, 22, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 35, 19, 37, 38, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 5, 6, 7, 21, 9, 21, 11, 21, 13, 14, 15, 21, 21, 21, 19, 21, 21, 22, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 5, 6, 7, 22, 9, 22, 11, 22, 13, 14, 15, 22, 22, 22, 19, 22, 21, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 5, 6, 7, 23, 9, 23, 11, 23, 13, 14, 15, 23, 23, 23, 19, 23, 21, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 5, 6, 7, 25, 9, 25, 11, 25, 13, 14, 15, 25, 25, 25, 19, 25, 21, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 27, 27, 27, 3, 27, 5, 6, 7, 27, 9, 27, 11, 27, 13, 14, 15, 27, 27, 27, 19, 27, 21, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 5, 6, 7, 29, 9, 29, 11, 29, 13, 14, 15, 29, 29, 29, 19, 29, 21, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 5, 6, 7, 30, 9, 30, 11, 30, 13, 14, 15, 30, 30, 30, 19, 30, 21, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 5, 6, 7, 31, 9, 31, 11, 31, 13, 14, 15, 31, 31, 31, 19, 31, 21, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 5, 6, 7, 35, 9, 35, 11, 35, 13, 14, 15, 35, 35, 35, 19, 35, 21, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 5, 6, 7, 37, 9, 37, 11, 37, 13, 14, 15, 37, 37, 37, 19, 37, 21, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 5, 6, 7, 38, 9, 38, 11, 38, 13, 14, 15, 38, 38, 38, 19, 38, 21, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 5, 6, 7, 39, 9, 39, 11, 39, 13, 14, 15, 39, 39, 39, 19, 39, 21, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 5, 6, 7, 41, 9, 41, 11, 41, 13, 14, 15, 41, 41, 41, 19, 41, 21, 22, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 43, 43, 43, 3, 43, 5, 6, 7, 43, 9, 43, 11, 43, 13, 14, 15, 43, 43, 43, 19, 43, 21, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 5, 6, 7, 45, 9, 45, 11, 45, 13, 14, 15, 45, 45, 45, 19, 45, 21, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 5, 6, 7, 46, 9, 46, 11, 46, 13, 14, 15, 46, 46, 46, 19, 46, 21, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 5, 6, 7, 47, 9, 47, 11, 47, 13, 14, 15, 47, 47, 47, 19, 47, 21, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 5, 6, 7, 49, 9, 49, 11, 49, 13, 14, 15, 49, 49, 49, 19, 49, 21, 22, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 35, 49, 37, 38, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 3, 51, 5, 6, 7, 51, 9, 51, 11, 51, 13, 14, 15, 51, 51, 51, 19, 51, 21, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 5, 6, 7, 53, 9, 53, 11, 53, 13, 14, 15, 53, 53, 53, 19, 53, 21, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 5, 6, 7, 54, 9, 54, 11, 54, 13, 14, 15, 54, 54, 54, 19, 54, 21, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 5, 6, 7, 55, 9, 55, 11, 55, 13, 14, 15, 55, 55, 55, 19, 55, 21, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 5, 6, 7, 57, 9, 57, 11, 57, 13, 14, 15, 57, 57, 57, 19, 57, 21, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 5, 6, 7, 58, 9, 58, 11, 58, 13, 14, 15, 58, 58, 58, 19, 58, 21, 22, 23, 58, 25, 58, 27, 58, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 41, 58, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 5, 6, 7, 59, 9, 59, 11, 59, 13, 14, 15, 59, 59, 59, 19, 59, 21, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 5, 6, 7, 61, 9, 61, 11, 61, 13, 14, 15, 61, 61, 61, 19, 61, 21, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 5, 6, 7, 62, 9, 62, 11, 62, 13, 14, 15, 62, 62, 62, 19, 62, 21, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 63, 11, 63, 13, 14, 15, 63, 63, 63, 19, 63, 21, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1115151715171517111515171517151711151517151715170000000000000000111515171517151711151517151715171115151715171517000000000000000011151517151715171115151715171517111515171517151700000000000000001115151715171517000000000000000011151517151715170000000000000000111515171517151711151517151715171115151715171517000000000000000011151517151715170000000000000000111515171517151700000000000000001115151715171517111515171517151711151517151715170000000000000000111515171517151700000000000000000000000000000000000000000000000011151517151715171115151715171517111515171517151700000000000000001115151715171517000000000000000011151517151715170000000000000000111515171517151711151517151715171115151715171517000000000000000011151517151715170000000000000000000000000000000000000000000000001115151715171517111515171517151711151517151715170000000000000000111515171517151700000000000000001115151715171517000000000000000011151517151715171115151715171517111515171517151700000000000000001115151715171517000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8000000000000000000000000000000000000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8000000000000000000000000000000000000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae80000000000000000eeeaeae8eae8eae8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8eeeaeae8eae8eae8

def cMZZ : Nat := 0x1115151715171517000000000000000000000000000000000000000000000000111515171517151700000000000000000000000000000000000000000000000011151517151715170000000000000000111515171517151700000000000000001115151715171517000000000000000000000000000000000000000000000000111515171517151700000000000000001115151715171517000000000000000011151517151715170000000000000000000000000000000000000000000000001115151715171517000000000000000011151517151715171115151715171517111515171517151700000000000000000000000000000000000000000000000011151517151715170000000000000000111515171517151700000000000000001115151715171517000000000000000000000000000000000000000000000000111515171517151700000000000000001115151715171517111515171517151711151517151715170000000000000000000000000000000000000000000000001115151715171517000000000000000011151517151715170000000000000000111515171517151700000000000000000000000000000000000000000000000011151517151715170000000000000000111515171517151711151517151715171115151715171517

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
  | 3 => 88
  | 4 => 534
  | 5 => 950
  | 6 => 502
  | 7 => 37
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xfff1eb1fd6f6ba28940677ef03098be2
  | 3, 0 => 0x9a9d2cc799239f3e8f4b9c728d251c90899f384e87d8e2ad872fabe38527c909815861d38141c8fc81040c6e809a1c1c7f6ba25e7eebff8e7ca699137793dce5740142cd70eb04926c4893ff642eda015c09d78059f121ac572d211253aec8f65205b919497092fd47a535e04629fe8945f7a62145b536a44408a9e540113e863f58f4473ee131b33768c62236b62a0935baaabc34efc4423157b3992ff6f8ff2f23910b273579fe257ca39d24b4661b235b2cad202063141bd173b41bb583541b1b746a1a361dca18edf4c91820afa5177a15a115671175120d9c3412011d5a0c2418c30b90758206b767a70392d6e90357e67a0322cb11013b179b00df6ebc
  | 3, 1 => 0xfd0d76e3f11f09d1e93beec9e55f9c47e54a4339e3df2b68e3168374deed9a14de09d21bddbaa378db27e2fdd94ad1ded87b8f50d4c20076d2f8cef9d069bea2cf61dc90cdd16700c450a71dc3093c83b737935eb5634f8cb03be793ac2793eb
  | 4, 0 => 0x1a245c151a0ea6391a037ca8199701b41901c17b18cc8aaf18843b5017e8f77517c5b164178b4309174980e1155e44341545c1a714ff5a6214f3b77314ab7405141519c6140c5f6913c009c513b993bb128a2c0a11cd3ef811b136e711970e3c1191bfb1116b678d1135f80310a2bb4810a0e7030ed519cf0de2b6880d1a8d0a0cffa6f30c6bf3af0bc4d2d70b8a4c520b178e080a89c57e0a7a390609cc4f6c09b57933095bf9a80863f3b108538d6e075416ce0738b89d071046dc0678e7ed05fe62dc05d5f043059cadb104f53f5104d5355204d0164a0448ee4403305a33032c257502163f8501feb53301b2ea060186450d017ed60201184d53001c2405
  | 4, 1 => 0x3718943136cfdd4936b90fdb3616bae7358e4ffe351dbd4134efc4423499e211339d423b334e9d383323dc64330aad8a326835583187c07131545a98313c63f8308e5bd62ffcb5182f047e012ee792892de964672c36d1e32b784f6b2b369d372b3593622ace529f2aa0804d294979fb2939ecf829278e2d28a1540e2873f34a281c3e3e27fbb4a527c48a5127b275bc2719e9d626b257d22698844a268e4e612655e71625d960ec258fdaea254c14b2249ab3f4247b504a235cceee22e14b4421eceb8821127c64202cfcc81fbb0a5d1f8c4e451f220ae91e78eed31dc92d701d5901bb1d1828e81cc97a8c1bf83b061b5dad301b2a01e21af6ccd21a270379
  | 4, 2 => 0x5910f46858e21cdc581fe86757d4b61b57c468da56e25256568bfc87564824575618cf39554a5d66538d68df5205b91951e356b050b822354ffdb4c54edfdcfe4eadf3514e6328a64ddcce7a4ccf06264c076f124bb4f6234b4371f34b418ed64ae2291a4a098f9c495affc348b01ff84874a22248294211475f49a8470268f646c9ac0d46439f7845a51b034490a1ed446fb33744358d84439d1e354316a518430c41d742c6b9544105ed4940ea77fe40e0e1fb40ab557e409991574082f6a04077aa304030169a401772963f7204633f6939f43ed8ccfa3dd8f4e03c832c4e3b6580b13b52632439eacd4439656fde3933860839322f8038ff4f0937bbdbf5
  | 4, 3 => 0x71e482d671b4039e713924b970e77f7e7086438c705c387d6fa75d126e5d51026d704f9e6c48e63b6bc76b306bc4e0076b3d78d36b3be6466af2c3516acc3b1a6ac9b85b6a87904a6980f31968c6a84268c60eb36897c77b687b9f1b684e5a3467f3c9b867d577df678c49b6676be6d766c612fb666d18356641fd8165f3edc265c9fbe064fdda1164b6f8cb642eda0164185dcd63eb76e963867ad0632cb8cb628bda9061ba6b6e612383c76119e7d960dcbb1360361fe05ffe6fd55ff882285fe6f13d5fbfbca75fa8f3af5f87c0975e148d285d5430c25d4bf7b15d4996f45d095cc65ce772495c6bac335b771fa35b03ddc859c87136596ef3f55946ca83
  | 4, 4 => 0x8ee10fd48edfc0e48e8cd8b28e84c03b8da33dab8d2455018d20dd688cdf4c428cbe91cc8c84daa18c30074e8aac7c4a8a713e3a8a48533c899ef12488a5edea88891a7488840587886c6d568773337085dc70ed85bf24a98555ebb0854f18d1853cafc385338c6a848c75ec8400a0df836a82638326245b82fa36c88213cee881ea9f7a81b5288b8141c8fc8122b5f2808848ec7eef9e2e7eebff8e7e57c6357c5d51847bfbb40a7bd1cb7f7b45c61e7a62222079f99f7379e2f2eb79c32899793821c778d32a4278b6bc3b7804cc6477904990773bf0d476e65db776417eb576089ca174ff8335748a428f7351b2a0733dbfef73365c9c7320a39071f54a5f
  | 4, 5 => 0xadd296ccaa753476aa61d083aa3a318aa9bce3cca91283f4a8f4015da8783652a812c4d4a76e3d9ea73f5b36a6e21bc0a6a26e35a611c738a5880c6aa5877a6da5557b30a3c8e3a2a3c2c7dca3125b21a27d0a1aa24050e7a178a8a9a0dea16da0cc2b429f9195249efdbfbe9ea17ba99e833c9a9e27d3d79e03fa159de1d1149d74803d9cfb61ac9cf416999c7405f19bffd25b9bf38c069b93b5c49a2ed33499c659b19934680798e7e3fe98d6d87697f60d1f97d909c696f8e7c29670af95956f3b7e943cefd0942d6b1a93e5fc8893e1a0a393aba16193931d7893107d2b92e595809235aa8791e4208691501e789103c263907eb7af902e430690216e33
  | 4, 6 => 0xd1afa098d131154cd072cf95d05b95efcff83386cef4446ece05b875cddd8b8ccd7f4d47cb7e320bcb717246cb70bb8ccb054fb4c9d183a0c8d4baa2c867450cc7e544b2c77cffd5c71bad53c5fd6704c56d0b13c3575caac334088bc32789b1c3093c83c1854207c04a3d0fbfe5fcb0bf92fef1bf8e878fbf7387bbbf5f53a3befafc88be59add6bdc47d86bd9a8ec5bd7eded2bd6358dfbcb6e1d9bcac98afbbf156ccbad34082ba0a0b70b9c48e4db9aa4757b80279e2b7e833d1b7ae1776b7a4426cb7560d94b5fd311fb53fb10fb404e6aeb339ac43b2eec887b26cb120b26aa5f0b26183f2b1804f18b14fdecbb03be793b020ca39b01807efaefa155d
  | 4, 7 => 0xf137aaddf0c227b7f0bfb39aeecf0ed4ee1e36faee0c5a58edaf0aaeed53cc6ded13f183eca6fb3cec79fd4dec794566ec59c43aeb8b8e6eeb730af9ea7fc515e9da6cc4e99f78b5e99f0c9de9461b53e8fc52b7e88f3279e7418fa1e6e11713e63f1a21e6163099e5513c7ee4fa5c3be3e34636e23bda4fe233cadae10de0a0e0ff47c5e057eba8e049fd62dfd590e0dfa6577fdefd8433de644e39de362540ddf932e3dd71d513dd531d5edcfdd009dc8f762bdc6d846adbf646bbd8f62addd8d9ff07d8b18fdcd856a42dd7faa8ded6a30ff4d689c10fd6671407d573a5fad5186eb9d50e1837d4c20076d4a6d841d43206d9d36be3bfd2b6d976d1d7b9c8
  | 4, 8 => 0xfd878e80fd83fa8afd141f17faff18f2fa96ff54f90c323ff8a7ee78f7d2a478f76ece7df7506ae0f6771e6cf5ec79cff573b262f500df2ef4f99c31f4f06a53f371ec02f35c2c5df3175252f2bdd6daf2517b41f20bd4de
  | 5, 0 => 0xc8273250c1e516a0bc4d2d70ba897fe0a6491130a4f268e09f437fd09dbcaeb09cc4f6c09bec3fc09bd8c3a098f748108f07afa08ead53608c6a6470886cbff0845f02f0808beb2078239750740ce9a07321ec5072f4acd070d234c065d5eb2063f94c206077d7f05c275a90596d028056fa3f4055ae3d20526848d051e15f904e7972204ce327a04c37a4f04be07f404854a60047efb090458dcbf04401cad043d1cfa03b0ed93032c2575030875dd02eb129402d2585302c0f26e025b7d90025b388302354b68020429f001e890d301d1c50201229cc001184d5301084f4500fa7b3600cc32d200c89edc00a207c2008413fa0058c369004506ad000012eb
  | 5, 1 => 0x17bfa1e2178be6d5178b430917710513176869dd174ac7ec1730da36172a6dd71703e6e416fe380816f460d11671b8c7161ee1741610a08d15f84b2515f5c81e15f3a22515df8f441545c1a71540b506153eca29152155991511e3451509c34e14d28a1414ace72c14ab7405148e8db6146a02241460decb145e0599143a75f513bdc64d13a2afee139da74d137020cb13301028132af207131b440412f6cd8e12a546661284b33f12641114125a90cb11b136e711a035da11970e3c1191bfb111613c421117f1db110b0612110abf841039d8a40fce77390fb59b4d0f6307710f3fd9ac0f20ed4a0eeadf910e53dc170e4d57730d5494bb0d470c2f0c8a7535
  | 5, 2 => 0x23c3db9b23a9b2f023a46465239c1702237b05cd234293d1230aef3222e0e57522d8f3c222d0f29222b959a4223dcf8c2212e7e1220c86cc21991a96218930ce217ca69e21127c6420cf86ca20cdc96e205690641fafe4401fa0ce021f971cff1f566b0b1e8abd5f1dfdd6811de850231dd7778b1dacd24d1d55d4031d1828e81c8955031c67524f1c4e2fc91c41ae3b1c192fad1c022dab1bf2e9ad1bf2a7761bdef4201bca00f41badfca61b66faaf1b262a9b1b0471681a8b6e691a4838131a0b9d671a05578b1a037ca819be4976199e909b1975a59d196912ee1925358718d0827b18cc438518b099d41861489a181b86cd1819f34d17e1c94317c8ffb2
  | 5, 3 => 0x2eef9be32ebcf3b82e5544d02e2776112df440962dcece0a2dbf28b72d7c84e42d7486282d6acf972d625a7d2d2380492d117cf42d009fa72ca1823b2c667f4f2c3920d12c28b40d2c16215c2c0265a62beeebe52bd8d81a2ba158522b435c342b20de672b200bcf2ac108252a9e411f2a80f3432a38e73829d2f2ae299de7bd299bd30629491dc4290e698528f3ac1228ed4d6528c6eb87288b54f928625d30283e14fd283d626c279dcf68277adf4c2758665b2751133e273fa9a527235f8026ea954226e80d4926d12c2526be18b9264f1ce32625ef912540234525320b792524d70424f7f3f024ed63d024ae554b249ab3f424642c4b2422ae8c24101e8e
  | 5, 4 => 0x3d2f71913d232dd73d1cc1153cb23ecf3c3659353bd6951c3ba93b463a99a3c33a573d5d39ff869c39dc360439cc5a46398f22e438f5376838ea362d3843ec3d382d3c44382153be37a67eb53797442d371ac7213718943137145bcf36f45a4a36ad58a8369b8fff367c580c35cfc09635bef3cc35bb64d935a3a3d5359fcc1c3569bbc9354bb61434e46d3e34cc64be3490eebf3420a32433d41aa333892626333a3b4433252118331e9a4833126bac32f7f73932f6360332f086e032cc15983291eb273288f98932683558324455b431a33bca3178c94630784d41305dbc3a300bf3ce2ffcb5182f7e32912f7b70c02f5f68a82f2acd9c2f0457f02f028727
  | 5, 5 => 0x4981966c4952acb9492b38e5489a15b14845058647158632470259cb46d194cd46be6c1146835ff5464466bd462f82ef46065c5445fe094a45cdd1cf459a84984556769844f10e99447ada0c446fb3374438f98043d0bdb94332390f43285a1343010ba142da13db42c00fb442768ad442696a94422a2ebf420f59cc41e9914941d0e27841bf4cb64197f8514154af62414b982941274a4d40ab557e4077aa30406988683fd710a83fab2c973f7204633f6939f43f6278353f4e1c9a3f485e333ee786cf3ec895d03ea999f23e9f25a53e8c14613e6e142d3e4c71303e05b89e3df3825f3de4fe283ddb4e613dd8f4e03dab46fd3d8fbb263d87be2c3d75f583
  | 5, 6 => 0x599480d058f23677588ce7835808881c57f09b7257e0220757d072eb57a22ed4579ff3bf5794976d573c4dea5738339457306f0c56a46590568e1701568257eb55cf258455963f74554a5d6654cdf2ca54af4f84541abb6953a37676537d7945530ae92b52bdfa325295c301528a4ee4526b79b952615aec5254dc125205b919520367905184a9175115bbd050bbadf650b015215011c35550059e694f78c5a84f778f704f56988d4f10d7224eed0fcd4eb57e454e9aec994e828c2a4defebb64d9dc00b4cf1f3b24cc7e1264cac31334ca6f0e44bea93164be4343a4bbe041a4b8f1cb04b37f7974b29020c4b1ea92d4afcc9f54aa3edf54a727f5249e09c9f
  | 5, 7 => 0x6a6cbc4f6a601df46a39bebe6986a1ce6983c2b9696e174e6928e63e691ad7ad6907ca1d6902c8b8688ff0b867fed7d7675d021a675bc59e6727fb3f66d2f5b166cb1f1d65ffeb6b65d0625565ade1eb654e8ff4652d96ed64f25c2e64e3f6066460189f64185dcd641534e363ef502a63eb76e963d42aa263971ee5635712a06299362061e42bd761d2a54461b53f91613f253b610cc0ad61050c2960c9ec3960bb698360909bfe6026728e5fe02f075fadeb765f88e8505f2585e75ee306075ee297145e2aa49c5d0added5cf9de7b5c6ac33e5c3e40725bba2f0d5ba8047f5b9e88cc5b9ba0d25b609de65b090d275b064ccc5adddda15a8451995a82f1f2
  | 5, 8 => 0x794cff4d7949413f793821c7790b27947901061e78bb22b978a36c317843923477bc84da77a0002777832e847730b8537723ffac771cb81877162be17706ffaa76b7be1e7682643c760e697475fe1b9d75e7ca6a757b4745756c6c82754382fa7515b43e747dc906745e7f7073e6350773cae7d973a5525372972e10721aee0471ab725171a2e1a271692cb071611d3b70fcdc1970c856a570b96b4d704a84bf702c9a266feb65a66f801a326f774fc36ed349016ea5932b6e5c81056e37679e6e0dc5496e0260c36ddb35886c8a661a6c6670046c3e4dcd6c06ba896bbcc88c6b9ad6cb6b9925736b77f98f6b20269e6b0cc9056af8d85b6af2c3516ad0b3b3
  | 5, 9 => 0x877e7df2874240ad86fff6d986af26b0867dbd41863edb1585d7666c85cd583785a470cd8564b3ea855873358519cc3084428d4583b861db83ab23c283a9ad36839584ff836dbc81834d2b6e82f690b682bfedb4829128c78213cee881eb293b819c6a82819a95d68199a8b18195a7ee8122b5f280ebd363809827588064fd3e7fed05fb7fdaccc87fb0484f7fa50f997f5f37397f58f12b7f406cdc7f0fc89f7f08b6b57ef6d1887ea5b9a37e860cfd7e6e88fd7e088a897d3e43c07d0954937cdd1c777cd881217c811ece7c1e55ae7c1de87e7b6002f37ae108c17a8095217a5780d279fb26fe79ef5be479b5893e79a0dfb0799b1c427998fce979778087
  | 5, 10 => 0x98629eae983b98a39821a60697d3aa3a97be29a597920fc89780dfca96f8e7c296660af995e5e17b95c707af959a05ad957a5661951453dd9509b29294a9c3dc94956129944866b0943cb7ba940287ae93f98cb89372e7539354324f92e595809275e18d925977d19235aa879210ae7591bfaf6390ccc3db90bd5d96907f0f72906a67ff9023f08f900336198facbc188f5a70da8ed788778eb898ab8e98416f8e8c26e58e80351c8dfb99dc8d374c3f8cbcf2b78ca686c68ca4ad878c8519018c51fe328c134b3f8c01d0f28a9824c38a31142f8a006b6389d22f3689c451b5897d10898938ff1288e6736b88adcf88889a8ffd88457767883984a087d540d9
  | 5, 11 => 0xad054d43acf67fccacc025c2ac8f01d9ac87ff39ac457b44ac3301d4ab2e111aaab8c74eaa61d083aa26c00da9eeaadca9566b85a93bf895a8dea592a8c45410a8953ad9a82f13d7a7ad6994a76e3d9ea71649d1a69a1ebea616d6afa5a37d5ba51e4596a4ed83eba4731403a4633c85a3d8c661a2d2b3d2a2ce4d12a2a6f7c3a1f02b64a174661ca0e23b27a0c46098a0b9248aa04388aea0324298a02ade889ff57b309fb7ca8a9f4ee1f99e7761449e026c2b9dcd67989cab9db99c4e81bd9c3df5109c20d4949bc34f749b99460b9b00d9209af225339ab235099a882c5d9a44e06499c195ca9927a61f98e7e3fe98e0b80e98be953c98903c9c986c5e7f
  | 5, 12 => 0xc4bba25ac44b0f9dc42f4914c3be0b1ec38a5fd0c37ac96fc2f3ab4fc2d7a33ec2bd036bc27bef94c23fa0d5c19587b4c1538f68c11ae34bc1015d27c0de4f7ec0bde86dc029b576bfd309ffbf8e878fbceeeba4bc171b04bbced441bb48a7e6baf93c52bacae7a8ba7900fcba0a0b70b9d0e672b8c3df77b89b8652b86bafc5b7f8fb9db7e833d1b7adb5ecb79f5444b795bb4ab7792bb8b6f1dcadb6a9af32b69ec674b5c94717b46c5c35b3b40e31b33cabdcb2fb4780b2f6703db2d9a174b2affa84b2a54259b1d4ee36b0ca1681b0759158af32cc20aee85cb9aebff811aeadfadcaeaa66e6ae6f1af8ae3a8b73adb9d8c3ada49d2bad7ed5d7ad3b6d70
  | 5, 13 => 0xdc9ebbc2dc8f762bdc1ea354dbf4bef6dbc699cddb9b487adae2a3b3da6a8079da3673cdda21a03dda03456bd9f326cbd9f0b69ad9872f4fd8b84a47d87b91c7d85d1306d82c8753d7faa8ded733fcded6d3feb1d6328fdfd62af6f0d5efe474d5e4a556d55ca756d5186eb9d4fb7754d45f3ee8d43206d9d407b79bd39d0593d3152899d1f40bb0d0d99a22d05c5009cff83386cfd8a7dacfcac569cfa4fc8ccf4aa452ce9f56bfce8cc1cbce3bc034ce197876ce061f56cd9dec18cd7742a0cc195eefcbf28e88cbefc940cbaccb49ca1f04e6c994d11fc980909fc95a28c5c82ca165c6dc86a0c6046cf8c5fe1d86c5c85ed0c52c8ff6c4e00012c4c996b6
  | 5, 14 => 0xffb44c76fef47153fd00cd80fb763897fab372cafa2015adf9683e94f8b856aff8ae4575f8a1575af885b5fff854475cf8350ea0f7f3610ff61d3615f56a0daff413078cf3e44b27f3aa651df2b2914cf25a0b27f162db47f0bfb39aefeb9f89ef9420beef2bc231ef080f08ef004b5eee0578f1ed41df84ed1f1111ed110f9ceb11399bea18213fe94cfd1be806d7d4e7f649a0e74d3ac3e727ea83e63423ace6163099e477afc2e3eb1f57e2eafbcce2dffdace23bda4fe1ec0a67e0ff47c5df784571df0b346cddb9589fdd85be7cdd470b56dd44ebd1
  | 6, 0 => 0x164ef43115dc7911156c2d7615620dec153eca291511e3451504b8cd1492064b1485c5961345fba512db439012d6ff97126b681d1107f86e10c9bce310b93b2110884d060fd469520fc579b90ed261fa0e8c899a0e3d1b000dd30c040d9bdb5e0d1de3c60cc617830c8a1c210c6b96210c0a6ed80ba897fe0acafb680a8ce23b0a47b3590a0e5b2209ade7820984d33308c64f4a08acc17c07d0be9206b080e5065e0ab40651520d064cabaf05f853f605afb69d055ae3d204ce327a04c37a4f0443069f043f1f830429d67a03c4eaad039492e0038bd1d1032c257502d2a4b4027f619701fe44420104770300d0340300c89edc0071af200058c369002a2e7a
  | 6, 1 => 0x2cfab9f92cc218d42bd8f01a2b7bd41e2b6b47712af0a1d52aa2a1922a501e952a046a3529d2f2ae299f6a87297a9f382910dcbc28bcba4f27ebe79d2799b0e0277adf4c272487f926ee85a626eb7c06260aedfe2606395024a7a8c22441a63e243704f323e2548423d7163d2375b9112312f10b22a039b4223dbfd62212e7e1213e00d62126b6b6212413f0201420221ffa163c1fac61d31f97ba601f823d251f5142f01f30887a1ea247e21e3d8f1f1e04dad81de5eb0c1dc593d01dbb3cb21db979461cb6de951c4692fa1b7f509319c57724195e6690192dbdc4190a76e218ff81971826710117c7e25e17a42267176d888616fe380816d61f03166f930e
  | 6, 2 => 0x43d3bcdc43868dbc42f6bc674269fe3d4223c29e420f59cc41faadbf41d294ba40cf986c406aa2d5402e77f23fa2e3b93f5e236a3e601e813ddb4d3d3dd7b9473d2f71913cac6f143cac28383c68bfd13c3659353c329fa43bbc543a3bb5519a3b302cfb3ab138633a5b637b39e619af39dc36043954126e38d604f73883bde6381e651137c28d3a371ea0d736c8b05136c0dc6f35c7711f35c2b02935598fdb3544291034dc484934b740883455c777339498633291eb273200063331d44a24310fbdd43096f2d2301c1aea300f8d882ffcb5182fe676eb2f9841d42f5830e92f22cd912ebcf3b82e7c345a2e6a56932df27b362da4b3a52d6098392d361d68
  | 6, 3 => 0x5fe00cfd5f01d79b5e69e6095d46cad75d02aaeb5cf791555ca495015c8524065b090d275ada1daa5a3db6845a08606f59aa9521595469b358df5b2358de373458da409958ade30058314774577c46dd573c4dea5609d9015607953c55cf2584554a5d6654e0802d54601e21540d52735350b16352f6a38952eb5d7f52b7b2315220fdb05204f59f5189b6bb50c68d4b5080e1c94f5707d74f4216454f2d2fb84ed5ad0a4ebf13c84e5864fc4e48fde94dee1ecf4dc4ad1b4d8ca01b4c81a29b4c1c3e054beedab84b6e5b134b29020c4aec73844a727f5249f83a0948b7b26947c8d8b347b4546446db084d46cca6a546c30dab44f6997844f45a5044a48fdb
  | 6, 4 => 0x854a88768326c8f6829807fc819c6a828199a8b17fed05fb7f18f1ea7ec1731f7e4f75657d9af8867d3e43c07c4c63727a8095217a7f67a77a3e8bfc796fa6ce78f2b3b177342a3577162be17682643c766890d776553ce4759218e7754382fa73d7df65738befca725b785272265b3972184e2d720d500d71a3005f71692cb070f7d3d36e4ea0796e37679e6d1bb1db6ce6ab006cb310dd6c745db76c72c0b86c6670046bbcc88c6b4bf5b56afcbf1e6ac89adb6a39bebe6a0b69ec6986a1ce694ef29e68b481b0688ff0b8687e0759678a6567675d021a6727fb3f66e20d1966cb1f1d66015112655aa1f1651d36d56511f7b764abc5f1633509fc613f253b
  | 6, 5 => 0xa62b8a64a54c33d0a5259d81a5231a7aa4731403a43f35a1a3da3988a3d8c661a367c851a2f97275a2ce4d12a2caf9a9a1b04fdea0c46098a0b9248a9f6f749d9c745e8b9af225339abeb59f98eade9698629eae9818279297f66efe97f3f8a39736110e971715b5965c9d29958ab10e9488362e944866b093f0ccab93862f1b9372e753936a6f56926ed0e0925977d191888adf91317c4c90ff175e90bd5d96900336198ff9852e8ff5f1388f8615c58f7259098ee19ed78eb6ee618e966fd58d9d401a8c5444448bc910d48ba2786889e0c52b8938ff1288d8785d889a8ffd8870fb0a87e5a91087cea9bb87b30860878199bd8762610186af26b0863edb15
  | 6, 6 => 0xce8fca91cd330afaccd89959cc5cc3edc9098860c8f9aca2c899a307c80484cdc641ae2bc6046cf8c5a9aa68c4cd1e78c495b854c34df580c3016cffc2d7a33ec2d67f4fc2678da0c23fbe08c21c216fc19587b4be8cbb04be31aa4cbdea4614bd2192f2bceeeba4bc9821f3bc8facd9bb2fb802b8c92562b8767020b78faf8cb73b19cab55341edb4deb8e1b46d75a1b45f5dd5b4474f5eb3917ea7b2d9a174b2affa84b238418eb04c73ebaffb1bcaad7ed5d7ad15a27fac457b44ab6f0097ab468209ab1ff9d2aa3747deaa31c3c4aa26c00da9b8c0c5a9566b85a8eb9bd2a83c2bc3a7ddec30a7d387b1a7b8e3b4a71a659aa6ecf43ea695bc39a6313940
  | 6, 7 => 0xfff5a901ffe6bda9fead6c8efd64b9fafbb7b876fab372cafa262ab7f9fe060ff99a0eabf8b856aff856389af8350ea0f4db3447f47be250f41fae8af38d6afbf342873fefeb9f89ed1f1111eacbdb28ea8df042ea365f83e9b1a3f5e8c1d32ce735da78e66585f0e65dc168e477afc2e335ce4ce2eafbcce2d0c8d2e26a193ee198cc15dea61804de1a6229dd93b11fdc1f460edc1ea354db9b487ad9d14051d99fd1aed90deefbd8c9a072d77257e2d55cd54bd43206d9d212820bd2076637d1a3dd30d0fe34d4d08201becfd8a7dacfa4fc8cce9f56bf
  | 7, 0 => 0xfd64b9faea365f83e477afc2d99fd1aecc5cc3edc9098860a62b8a64a43f35a19488362e93f0ccab925977d18ff5f13889e0c52b87e5a910876261017f18f1ea72184e2d6b4bf5b5675d021a554a5d665204f59f4f2d2fb84c1c3e053cac28383954126e3883bde63455c777339498632df27b3622a039b42014202217c7e25e156c2d760c6b962109ade78205afb69d04ce327a
  | 8, 0 => 0xe477afc2
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333333333000033330000333300000f0f0f0f0f0f00000f0f00000f0f000000ff00ff00ff00000000ffffffff00000000ffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa0000000055555555000000000f0f0f0f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xf000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f0000ffffffffffff0000ffff0f0fffff0000ffff0000ffff0000ff00ff00ff000000f0f0f0f0f0f00000f0f00000f0f00000cccccccccccc0000cccc0000cccc0000aaaaaaaaaaaa0000555555555555
  | 0, 2 => 0xf0f00000f0f00000f0f0000000000000f00ff00ff00ff000f00ff000f00ff000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000ff00000000000000f0f0f0f0f0f0f0
  | 0, 3 => 0x333333333333333333333333000000003333000000000000330033003300330030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fff0fff0fff0fff0fff0fff000000000fff0000000000000f0fffffffffffff0f0fffff000000000f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f00000000
  | 0, 4 => 0x550055005500550050f050f050f050f05050f0f0f0f0f0f050505050505050504c4c4c4c4c4c4c4c44cc44cc44cc44cc4444cccccccccccc44444444444444443f3f3f3f3f3f3f3f3f3f00003f3f00003f3f0000000000003f003f003f003f0033ff33ff33ff33ff3333ffffffffffff3333ffff3333ffff33333333ffffffff
  | 0, 5 => 0x70707070707070705f5f5f5f5f5f5f5f5f5f5f5f000000005f5f0000000000005f005f005f005f0055ff55ff55ff55ff55ff55ff0000000055ff0000000000005555ffffffffffff5555ffff5555ffff55555555ffffffff55555555555555555555555500000000555500005555000055550000000000005500ff00ff00ff00
  | 0, 6 => 0xaa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a0a0000000000000a000a000a000a000888888888888888888880000888800008888000000000000880088008800880080808080808080807777777777777777777777770000000077770000000000007700770077007700
  | 0, 7 => 0xaaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa00aaaaaa00aaaaaa00aa00aa00aaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0aaaa8888aaaa8888aaaa888888888888aaaa0000aaaa0000aaaa0000a0a00000aaaa000000000000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00aa00aa0000000000
  | 0, 8 => 0xc0f0c0f0c0f0c0f0c0c0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0000000000000c000c000c000c000bbbbbbbbbbbbbbbbafafafafafafafafafafafaf00000000afaf000000000000af00af00af00af00aaffaaffaaffaaffaaaaffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000
  | 0, 9 => 0xcccccc00cc00cc00ccccc8c8ccccc8c8ccccc8c8c8c8c8c8ccccc0c0c0c0c0c0ccccc0c000000000cccc888888888888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00ff00ff00ff00cc00cc00cc00cc00cc00cc0000000000cc00000000000000c8c8c8c8c8c8c8c8
  | 0, 10 => 0xcfcf000000000000cf00cf00cf00cf00ccffccffccffccffccffccff00000000ccff000000000000ccccffffffffffffccccffffccccffffccccccccffffffffcccccccccccccccccccccccccccc0000cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00
  | 0, 11 => 0xee00ee00ee00ee00ee00ee00aa00aa00ee00aa00aa00aa00ececececececececececececccccccccececccccececccccececcccccccccccceccceccceccceccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaaaaaaaaaaaaaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0ddddddddddddddddcfcfcfcfcfcfcfcfcfcfcfcf00000000
  | 0, 12 => 0xeeeecccc00000000eeeeaaaaaaaaaaaaeeeeaaaa00000000eeee0000eeee0000eeee0000e0e00000eeee000000000000eeeceeeceeeceeeceee0eee0eee0eee0eecceecceecceecceecceecccccccccceecccccceecccccceecccccccccccccceeaaeeaaeeaaeeaaeeaaaaaaaaaaaaaaeeaa0000eeaa0000eeaa000000000000
  | 0, 13 => 0xf0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f000f00000000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeecceecceecceeeeececececececeeeee0e0eeeee0e0eeeee0e0e0e0e0e0eeeecccceeeecccceeeeccccececcccceeeecccccccccccc
  | 0, 14 => 0xf0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0f000f000f000f0f0e0e0f0f0e0e0f0f0e0e0e0e0e0e0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0f0f00000f0f00000f0f0000000000000
  | 0, 15 => 0xfa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f8f0f0f8f8f0f0f8f8f0f0f0f0f0f0f8f0f8f0f8f0f8f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f0f0f0f0f0f0f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0fffffffffffff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0
  | 1, 0 => 0xfafafafaaaaaaaaafafafafa00000000fafafaf0faf0faf0fafaf8f8f8f8f8f8fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafaaaaaaaaaaaaafafa0000fafa0000fafa000000000000faf8faf8faf8faf8faf0faf0faf0faf0faf0faf0f0f0f0f0faf0f0f0faf0f0f0faf0f0f0f0f0f0f0faaafaaafaaafaaa
  | 1, 1 => 0xfef0faf0faf0faf0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcf0f0f0f0f0f0fcfcccccfcfcccccfcfcccccccccccccfcfc0000fcfc0000fcfc000000000000fcf0fcf0fcf0fcf0fcf0f0f0f0f0f0f0fcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafaf0f0f0f0
  | 1, 2 => 0xff00aa00aa00aa00ff003300ff003300ff00330033003300ff000f00ff000f00ff000f000f000f00ff000000ff000000ff000000f0000000ff00000000000000fefefefefefefefefefefefef0f0f0f0fefefefe00000000fefef0f0f0f0f0f0fefe0000f0f00000fefe000000000000fefaf0f0f0f0f0f0fef0fef0fef0fef0
  | 1, 3 => 0xff00ff00ff000000ff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0000000000ff00fa00ff00fa00ff00fa00fa00fa00ff00f000ff00f000ff00f000f000f000ff00ee00ee00ee00ff00cc00ff00cc00ff00cc00cc00cc00ff00aa00ff00aa00ff00aa00fa00aa00
  | 1, 4 => 0xff33000000000000ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff0fff0f00000000ff0f000000000000ff00ffffffffffffff00ffffff00ffffff00fff0fff0fff0ff00ffccffccffccff00ffccff00ffccff00ff55ff55ff55ff00ff00fff0fff0ff00ff00ff55ff55ff00ff00ff00ff00ff00ff00ff00aa00
  | 1, 5 => 0xffaa0000aaaa0000ffaa000000000000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0ff00ff00ff00ff88ff88ff88ff88ff88ff88ff00ff00ff88ff00ff88ff00ff88ff00ff00ff00ff80ff80ff80ff80ff55ff55ff55ff55ff50ff50ff50ff50ff33ff33ff33ff33ff33ff3300000000ff33ff00ff00ff00
  | 1, 6 => 0xffaaffaaffaaffaaffaaffaaff00ff00ffaaffaa00000000ffaaffa0ffa0ffa0ffaaffa0ff00ff00ffaaff88ff88ff88ffaaff00ffaaff00ffaaff00ff00ff00ffaaff0000000000ffaaf0a0ffaaf0a0ffaaf0a0f0a0f0a0ffaaaaaaffaaaaaaffaaaaaaaaaaaaaaffaaaa00aa00aa00ffaa0000ffaa0000ffaa0000f0a00000
  | 1, 7 => 0xffeeffee00000000ffee000000000000ffe0ffe0ffe0ffe0ffccffccffccffccffccffccccccccccffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffccccccccccccccffcc0000ffcc0000ffcc000000000000ffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ff00ffc0ff00ffc0ff00ff00ff00
  | 1, 8 => 0xfff0fff0f0f0f0f0fff0fff000000000fff0ffc0fff0ffc0fff0ffc0ffc0ffc0fff0ffa0fff0ffa0fff0ffa0ffa0ffa0fff0ff00fff0ff00fff0ff00ff00ff00fff0faf0faf0faf0fff0f3f0f3f0f3f0fff0f0f0fff0f0f0fff0f0f0f0f0f0f0fff0aaa0fff0aaa0fff0aaa0aaa0aaa0fff0000000000000ffeeffeeffeeffee
  | 1, 9 => 0xfffafffaf0f0f0f0fffafffa00000000fffafff0fff0fff0fffaff00ff00ff00fffafaf0faf0faf0fffaf0f0f0f0f0f0fffaf0f000000000fffa000000000000fff8fff8fff8fff8fff3f0f0f0f0f0f0fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0ffc0ffc0fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff0faf0faf0
  | 1, 10 => 0xffff0000aaaa0000ffff0000aaa00000ffff0000aa880000ffff0000aa000000ffff0000a0a00000ffff0000a0000000ffff000088880000ffff000050500000ffff000033330000ffff000033000000ffff000011110000ffff000000cc0000ffff000000550000ffff000000000000fffcfffcfffcfffcfffafffafffafffa
  | 1, 11 => 0xffff0000ffff0000ffff0000fff00000ffff0000ff000000ffff0000fafa0000ffff0000faf00000ffff0000fa000000ffff0000f8f80000ffff0000f0f0f0f0ffff0000f0f00000ffff0000f0c00000ffff0000f0000000ffff0000eeee0000ffff0000e0e00000ffff0000cccc0000ffff0000c8c80000ffff0000c0c00000
  | 1, 12 => 0xffff00ffffff00ffffff00ff00ff00ffffff00ff00000000ffff00f000f000f0ffff00f000000000ffff00ccffff00ccffff00cc00cc00ccffff0055ffff0055ffff005500550055ffff0000ffffffffffff0000ffffff00ffff0000ffffccccffff0000ffffaaaaffff0000ffff5555ffff0000ffff3333ffff0000ffff0f0f
  | 1, 13 => 0xffff880000000000ffff808080808080ffff808000000000ffff5555ffff5555ffff555555555555ffff555500000000ffff505050505050ffff333333333333ffff3300ffff3300ffff330033003300ffff3030ffff3030ffff303030303030ffff303000000000ffff111111111111ffff0f0f0f0f0f0fffff0f0f00000000
  | 1, 14 => 0xffffa8a8a8a8a8a8ffffa8a800000000ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa0a0f0f0a0a0ffffa0a0a0a0a0a0ffffa0a000000000ffffa000ffffa000ffffa000a000a000ffff8888ffff8888ffff8888ffff0000ffff8888f0f08080ffff888888888888ffff888800000000ffff8800ffff8800ffff880088008800
  | 1, 15 => 0xffffc00000000000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaf0f0a0a0ffffaaaaaaaaaaaaffffaaaa00000000ffffaaa0ffffaaa0ffffaaa0aaa0aaa0ffffaa88ffffaa88ffffaa88aa88aa88ffffaa00ffffaa00ffffaa00faf0aa00ffffaa00f0f0a000ffffaa00aa00aa00ffffaa0000000000ffffa8a8ffffa8a8
  | 2, 0 => 0xffffe0e000000000ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc00ffffcc00ffffcc00cc00cc00ffffcc0000000000ffffc8c8ffffc8c8ffffc8c8c8c8c8c8ffffc0c0ffffc0c0ffffc0c0f0f0c0c0ffffc0c0c0c0c0c0ffffc0c000000000ffffc000ffffc000ffffc000c000c000
  | 2, 1 => 0xfffff0f0f0f00000fffff0f0ccccc0c0fffff0f0c0c0c0c0fffff0f000000000fffff0c0f0c0f0c0fffff0a0f0a0f0a0fffff0a000000000fffff000fffff000fffff000ffff0000fffff000f0f0f000fffff000f000f000fffff00000000000ffffeeeeffffeeeeffffeeeeeeeeeeeeffffe0e0ffffe0e0ffffe0e0e0e0e0e0
  | 2, 2 => 0xfffffaf000000000fffffa00fffffa00fffffa00fa00fa00fffff8f8f8f8f8f8fffff8f888888888fffff0f0fffffffffffff0f0fffff0f0fffff0f0fffff000fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0ff00f000fffff0f0fcfcf0f0fffff0f0fafaf0f0fffff0f0faf0f0f0fffff0f0f8f8f0f0fffff0f0f0f0f0f0
  | 2, 3 => 0xffffffaa00000000ffffff00ffffff00ffffff00ffff0000ffffff00fff0ff00ffffff00ff00ff00ffffff0000000000fffffcfcfcfcfcfcfffffcfcccccccccfffffcfc00000000fffffafafffffafafffffafafafafafafffffafaf0f0f0f0fffffafaaaaaaaaafffffaf0fffffaf0fffffaf0faf0faf0fffffaf0f0f0f0f0
  | 2, 4 => 0xffffffff00f000f0ffffffff0000ffffffffffff0000f0f0ffffffff00000f0fffffffff000000ffffffffff00000000fffffff0fffffff0fffffff0fff0fff0fffffff0ff00ff00fffffff0f0f0f0f0fffffff000000000ffffffccffffffccffffffccffccffccffffffcc00000000ffffffaaffffffaaffffffaaffaaffaa
  | 2, 5 => 0xffffffffcccc0000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffc0c00000ffffffffaaaaaaaaffffffffaaa0aaa0ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffff88888888ffffffff80808080ffffffff50505050ffffffff33333333ffffffff11111111ffffffff0f0f0f0fffffffff00ff00ff
  | 2, 6 => 0xffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffaaffaaffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffff8f8f8f8fffffffff0f0f0f0fffffffff0f0c0c0fffffffff0f00000fffffffff0c0f0c0fffffffff0a0f0a0fffffffff000f000ffffffffe0e0e0e0ffffffffcccccccc
  | 2, 7 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffcccc
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x668c7204d87340813610d6204d9b29c813
  | 3, 0, 0 => 0x6891f29c8144bcf0340814610a72047b46696829c8148c19529c8148119529c814881732dca748819531c8148ecf0308a74881953248145052129c8146552429c814809952dca748859529c8148819d29c8149218429c814
  | 3, 0, 1 => 0x8c59529c8148718729c8148819729c8145790429c8148819525c8148817329c8148819329c8147c98729c814881952dca7491d8429c8148819029c8148318729c8148199529c8146759a29c8144a10d29c81468995274814
  | 3, 0, 2 => 0x578f031c8146699529c8148ed9a29c8146898729c81480d952dca74880c829c8148817d29c8148817429c8148819529c8148815329c81483195270814881a12588147a9412dca74668a72047146dd952dca748817c258814
  | 3, 0, 3 => 0x8819527481490d8429c8146895c2dca747c98429c814689412f0b748814125c8147659529c814881953548146898431c814881412dca7486d9529c8146116829c8146594129c81480d9529c81461ca72047448ed8729c814
  | 3, 0, 4 => 0x654d329c814881953408148e595270814881952f08148ed1429c8148ed8429c8148417d29c8148c58729c8148812029c8148419529c8148b19729c8146694129c814611413408146897d2dca74689952dca74588f029c814
  | 3, 0, 5 => 0x841412dca744bd0a29c8146898629c8146697c29c8148818c29c8144a0f03588148818729c8148b19529c814
  | 4, 0, 0 => 0x7c92a3c0a72055a2504fb29c815689413f4a720560c6114129c815689743c0a720563b610f029c815871893c0a720561b504f029c815689953c0a72056206551d29c81580d95504a72055e3504fe29c8156894129c81135620654a72043f580d413c0a72055e0504f029c815
  | 4, 0, 1 => 0x68968428a72055a265511364a75689593c0a72055bd4e8f029c815688f0320a720562b504f029c81597605654a72055413c0a72042e5689343c0a72055d9504f029c8158a620654a72055a25f4f029c815881413c0d52055a23c0be29c815505283c0d02056206558e29c815
  | 4, 0, 2 => 0x72d413c0a72056206154129c8158ed844a0a7205620654a72040a571d413c0a72056206551129c8158814129c8d2055a2644f029c8157a5413c0a720561c504f027881588141394a72055413c0ab29c81568941404a72055a2504f032481587d413c0a720561c504f02dca75
  | 4, 0, 3 => 0x871413f8a72055a2504bc234815855413c0a72055a2654f429c815689553c0a720564a6fd412f0b756e9413c0a72055a2504f02d8a757ed683c0a72055e3504f029c815881bf504b729d5b9504fe29c815689413c0c72055a26750a29c81580dbf654a72055a23c0bf29c815
  | 4, 0, 4 => 0x6cd413c0a72055f2504f029c8157a9413c0bc2055a2570a72348159b620654a720561c6114129c815929bf570b729d5a2654b729c8d5791413c0a72055a24e8f029c815881413c09d2055a2504f02e88158719529c8d20561c3c0a72042b56c1413c0b729d5a25c8f029c815
  | 4, 0, 5 => 0x6898d3c0a72055a2504a72388156894137ca72055ef504f029c8156b1953c0a72055b76551129c815661953c0a7205620654a72648158812f3c0a72055ea570f029c815665413c0a72055fb5050a29c8158ed283c0a72055a24e0f029c815865413c0a7205620654a7258815
  | 4, 0, 6 => 0x6dd3e3c0a720561c504f029c8156d5953c0a720565d8a59529c815581413c0a720561c4c4f029c8158820c654a72055b9504f029c8157fd413c0a7205620504e429c815529413c0a72056205a0f029c8156c19529c8d2055f8654f029c8157a941444a720563b58cf029c815
  | 4, 0, 7 => 0x579413c0a72056205050a29c815689413c09e2055a25a0f0340815688f029c852055a25bcf031c815002205cca72051a25050229c815688f02f4a72055a2655412dca75504f029c810d55a2670f029c815689413c0b729d620654a72047958816c3c0a720562f5050429c815
  | 4, 0, 8 => 0x688f029c810ad5a2654e529c815789953c0a72055a2504fe29c815929bf654b729d5a2538f029c8156c1413c0a72055683c0a7260815689823c0a720564a815952dca7588195370a72055a261d2f29c8156b1413c0c72056025ccf029c815689413c0972055b6504f029c815
  | 4, 0, 9 => 0x7a9953c0a72055bf689952dca758821c654a720564a6fd7d2dca7568984504a72056315050429c81568941428d02055f6504f029c815869413c0a72055a2574f029c8156b13a3c0a72055f25bcf029c815689413c0d62055a2654a72348156894139ca72055413c0cb29c815
  | 4, 0, 10 => 0x6b9953c0a72055fb504f0340815881a25cca72055f15050429c8156892d3c0a72055b75050a29c815504f0340ca20562c504fe29c815875413c0a7205541428a72608155f9413c0a72055e2564f029c8158716b3c0a72055a25051429c8158819529c811cd64a8817329c815
  | 4, 0, 11 => 0x6fd9a504a72055a2648f029c8156894129c8113963b6114129c8158819529c811c56205050429c8158d5a2654a7205602654f029c81592a29640a72055a2504f029c815688f029c811414008819529c8146696d504a72056484a0f029c815841413c0a7205620620f029c815
  | 4, 0, 12 => 0x881413c0d020564a8a5952dca7583d412cca72055a251cf029c8156891e3c0a7205639504f02708158819529c9c2055a2504a7204205505233c0a7205584504a72047458ed813c0a7205620504f02f0815504ca2cca72055a2654e429c8155f15e3c0a72055b8504f029c815
  | 4, 0, 13 => 0x68995428a72056205ccf029c815688f029c810b14006898729c81492a20654a72056205051129c81598220654a72055a2500f029c815689573c0a72055f3504f029c8158815c3c0a720562c504f029c8156fd6d410a72055413c0d329c815689593c0d92056346fd9529c815
  | 4, 0, 14 => 0x8edbf610a7205620504f329c8156895c3c0bc2055283c0a72047b56894129c8f2055a25a8f029c815595413c0a72055413c0a72188158312f3c0a72055a2504f031481574d413c0a7205616504f029c815689845f0a72055a6504f029c8159ae20654a720559a5bd4129c815
  | 4, 0, 15 => 0x88141378a7205622504f029c81588195610a72055ee504f029c8158819529c810355b7504f02f0815881412cca72055b74c0f029c815654f0328a72055a2505112f08156dd41410a72055e3504f03648156ed413c0a72055c9504f029c815881a2654a7205620504f829c815
  | 4, 1, 0 => 0x6b1413c0a72055a25050d29c815661413c0a72055a2504bc2cc815689703c0a7205620654a7204315695413c0a720564a6898729c8156dd5c3c0a7205620504a7258815689373c0a72055aa504f029c8159ba20654a72055f24bcf029c815504f0340982055a25711129c815
  | 4, 1, 1 => 0x6892c3c0a720563b4d4f029c81500220504b729d1b5504f029c815689203c0a72054f0328bf29c81500203654a720523b8819529c815789413f8a72055a2558f029c815689413c0c229d5f8504f029c815689413e8a7205620654a72047656dd733c0a72055a2534f029c815
  | 4, 1, 2 => 0x921813c0a720562967d4129c815689413c0d52055a2504f02e481568995410a7205541490f029c81588195384a7205621504f029c815689423c0a72055a256cf029c8156dd412cca72055413c0af29c8158819529c811d15a3504f029c81588195654a7205620654f029c815
  | 4, 1, 3 => 0x689953c0d02055d2504f029c8156c93a3c0a72056205050b29c8156895a3c0a72055f4504f029c8156893c3c0a72056206819529c8158819529c81065620504f129c8155a15e3c0a7205620564f029c815689953c0bc2055a2504f029c3a56892e3c0a7205620504a72041f5
  | 4, 1, 4 => 0x731413c0a72055a261cf029c815881413c0c72055a24a10429c8156a1413c0a72055a2504fe364815880f02fca72055a24e50429c81568995444a72055e2504f029c81580d733c0a7205620504a7240815881954a0a7205620644f029c815881954e4a72055a2504f02d4a75
  | 4, 1, 5 => 0x88195380a72055a2504b729c6d599e295cca72055a2504f02044a58813a3c0a72055a25050529c815689433c0a7205620689412dca75689953e0a72055df504f029c8157a9413c0a72055e9504f02f081568941410c72056036899529c8156dd953c0a72055a2630f029c815
  | 4, 1, 6 => 0x6b5413c0a72055a25f4b329c8157c941410a72055b1504f029c8158817329c8d2055a4504f029c815688f029c810b55a2654de29c8156b9413c0a72055b7564f029c815751413c0a72055a2654b329c8157a55c3c0a72055bf5b4f031c8157ad413c0a72055a2504f0274815
  | 4, 1, 7 => 0x921353c0a72056488819529c815689683c0a7205400881952043f4688f02b8a72055b7504f031c8156890429c932055b73c0bf29c81579d413c0a72055a24bcf029c815689503c0a72054008819529c544688f029c81111620654a724c81553d413c0a7205606504f029c815
  | 4, 1, 8 => 0x6894129c8117d5a25051d444d956dd413c0d120563b3c0a7244815689413c0b8205620504b729c8150022029c810691a25b0f029c81568941474b729d5a2674f029c8158b5413c0a7205620504f02dca75001a2654b729d1a22fcb329c81568995468a7205603654f029c815
  | 4, 1, 9 => 0x8e620654a7205620504fe29c8156695e504a72055a260cf029c8156899542ca72055b7624f029c815689953c0c92055dd504f029c815689943c0a720563b4bcf029c81599e29654a720555e3c0a72047158819529c810916205cd4129c81568941428a72055953c0a72042e5
  | 4, 1, 10 => 0x855953c0a7205620504a72044c56898429c811c563c4a4f029c81578d953c0a72056206114129c815689733c0b729d5a2654f031c8150019a504a7205231504f029c8156899529c9020552f3c0a72047458819529c8d2055413c0ca29c8157a5953c0a72056203c0a72042b5
  | 4, 1, 11 => 0x68941430a72055a24a0f031c8155a1283c0a72055a24e4f031c815689883c0a72055f2654f029c81578d593c0a72055a2504b72cca7588141454a72055a2504f02044956899529c81055541488f029c8156898a3c0a720560c504f027081588195604a72055a2514f029c815
  | 4, 1, 12 => 0x8819529c81151400654a72040d4881fb654a72055a25050429c815689903c0a72055413c0c029c8157a94129c8d2056358819529c81588195504a7205600504f029c8150023b610a72051a23c0c72fc815881413c0a72055a23c0a72045b5689973f8a72055a2504f02d0a75
  | 4, 1, 13 => 0x689413c0d020563b578f029c815689953c0b729d5a2504f729c81596e20654a72056206814129c8156899529c9c205603504f02dca7550528428a720562050511364a75504f029c811155f24a0f029c815689413c0bc2055a2504f529c8156899a504a72055a2504e629c815
  | 4, 1, 14 => 0x88220654a72055a2504f0310815689443c0a72056678a5412dca7590d283c0a72055a265cf029c81568987504a72055a2654f025c815688f031c932055a25ccf029c8156dd313c0a7205595578f029c8158819529c810695a2570f029c815689952dca72055f2504f031c815
  | 4, 1, 15 => 0x6897c3c0962055413c0a7204585689412cca7205620504b729c8d5881954d4a72055413c0a72045c58eda2610a72055a2654fe29c815688f029c94205620654a72046d5759413c0a7205603654a7234815504f029c811855a24acf029c815841412cca72055fb6898729c815
  | 4, 2, 0 => 0x688f029c811815a25bd0429c815881955f0a72055a2684f02588156899529c811315a2564fe29c8158819529c811a15a2518f029c8153c0a72042e0ad6206556f29c815881373c0a720564a6fd8729c815669413c0a72055a2504f629c81568995610a72055f23c0a724c815
  | 4, 2, 1 => 0x881a1654a7205620654d929c8158819529c982055de504f029c815689533c0a72055a2504f02044b5
  | 5, 0, 0 => 0x1a2504f01503f56fd413c0a72045966dda2504f029c816855413c0dc29c816689413c0a7204646929bf5711129c81600203504f029c81592a294c4f029c816881bf6899529c816689a1504f029c816689413c0d929c816689413c0a72045568ee20504f029c816689413c0a72608168e9a2504f029c816689413c0e329c816
  | 5, 0, 1 => 0x6c9414e4f029c81692a29504f029c816689413c0a72043f6959e6504f029c816871413c0a7264816939a2504f029c816689414d8f029c816881413c0f029c816689413c0a7220816929bd654f029c816001a2654f029c815971bf504f029c816905a2504f029c816929a2504b329c816001413ccf029c8156c9413c0a7284816
  | 5, 0, 2 => 0x6894141cf029c81668941410f029c816881413c0e129c81699dbf654a7234816929bf504bc2cc816689413c0a720463699dbf3c0a72042b6689413c0a72046e6929bf560f029c81699dbf504fe29c816929d5504f029c816881413c0a72047469c5b7504f029c81668941474f029c81688195504f029c81682dbf654f029c816
  | 5, 0, 3 => 0x901a2504f029c816689413c0d729c816001a2564f029c8158a5a2504f029c81692a28504f029c8169b9b7504f029c816929d7504f029c8166dd413c0a7204756001413c0a72042e59a1bf504fe29c8166898e504f029c816929bf504fa29c816929bf534f029c816689953c0a7204716689413c0a7204486689413c0a7280816
  | 5, 0, 4 => 0x7e9bf654f029c816929bf4b0f029c8166dd413c0a72047666fd413c0a720433699db2504f029c816881413c0a7284816929bf480f029c816965ac504f029c8166fdac504f029c8166fd955b4f029c816881413c0a72041966fd413c0b029c8166dd413c0a7204316929413c0a7204466689413c0a72045a698dbf504f029c816
  | 5, 0, 5 => 0x8ed413c0a7260816975a2504f029c816689413c0a729881668975504f029c816881414a0f029c81692a03504f029c8169a9a2504f029c816929af4e8f029c816929413c0c129c816689413c0a7204146689413c0d0204746881414e4f029c81600220504a7234815689413c0a829c816001a2644f029c815001e9504f029c815
  | 5, 0, 6 => 0x809413c0a7234816929413c0d429c816001a2504f031c815929f7504f029c816929a2654f029c816871413c0a720417668941444f029c816929bf6550429c816871413c0a726c816981a2654f029c816001a23c0bf29c8150021c3c0a7204245929bf508f029c816929bf56cf029c816689413c0a7204226689413c0a72043e6
  | 5, 0, 7 => 0x689413c0a7224816689413c0a72047f6001e3504f029c8156897a504f029c8169ada2654f029c8166fd9e504f029c816689413c0aa29c8166fdb5504f029c816689413c0a7204286689413c0a72040a6689283c0a7204716965bf654f029c816689393c0a7204716929b4504f029c816689955051129c816689413c0a7204386
  | 5, 0, 8 => 0x6dd95504f029c81680da2504f029c81600215504f029c815689413c0db29c816929bf654f02f0816929bf504f029c3a6689413c0ce29c8166dd413c0f029c816504f029c98204746929bf4b8f029c816001a23d0f029c815769bf504f029c816881bf654f029c81699dbf4c4f029c816871413c0dc29c81699e05504f029c816
  | 5, 0, 9 => 0x92a23504f029c8166dd413c0e129c816929bf4f0f029c816689413c0c329c816689a2654f029c816929c1504f029c816909bf504f029c816689413e0f029c816929413c0a72042e6929c4504f029c816689413ccf029c816689883c0e029c81693229504f029c816689413c0c72047166897c5bcf029c816959bf654f029c816
  | 5, 0, 10 => 0x689413c0a7204666001f2504f029c815689413c0a72047e6689413c0b329c816929f0504f029c81699e18504f029c816881413c0e029c8169a1bf504f029c816941a2504f029c816935bf504f029c8166dd413c0a728c816689413c0a72043c6929a2564f029c81699e20504f029c816839fa504f029c816001a24e8f029c815
  | 5, 0, 11 => 0x92a20504a7234816929a2644f029c816929e9504f029c8168721c504f029c816689413c0a7204126689414ccf029c816689413c0de29c816959bf564f029c816929bf504fe3648169b5a2504f029c816689413c0a72042e6929bf4e50429c816929bf6551129c81692dbf504f029c81692a11504f029c816975bf5ccf029c816
  | 5, 0, 12 => 0x689413c0a72047768f1b7504f029c8167c9413c0a7204716929a23c0bf29c816689413c0a72046f6689413c0a7258816689413c0a72045e6911a2504f029c8160021c504a7204315001953c0a7204195689413c0a72448166fd4135cb329c8160023b4a0f029c8159b9a2654f029c81699dbe504f029c8168820e504f029c816
  | 5, 0, 13 => 0x689413c0a7208816689413c0a720429600220504f029c545929bf654f829c8166fda26551129c8166fd4b504f029c816965bf504f031c816689953c0a7204316881413c0a724c816789bf504f029c81692a325050429c816929ed504f029c816929a2504f031c816929e8504f029c8166dd414e4f029c816929bf5050431c816
  | 5, 0, 14 => 0x9a5b7504f029c816929bf504b729c6d692a15504f029c816688f029c93204716929bf4f8f029c81692a1e504f029c816929bf504f02044a6999bf504f029c816929bf5050529c816689953c0a7204766929bf50cf029c816881a2504a7234816689414bcf029c81699d413c0cc29c816689413c0a7264816929e3504f029c816
  | 5, 0, 15 => 0x7a9bf504f029c816831a2504f029c8167b5a2504f029c816835a2504f029c816689413c0d829c816929bf654b329c8167eda24bcf029c816735bf504f029c81668968504f029c8166894129c8d2046d6689413c0a72047266fd51504f029c8166fd413c0a72043666fdb7654f029c81692220504f029c81600220504f02043f5
  | 5, 1, 0 => 0x99db7504f029c816745a2504f029c816001a2504f02dca7568941468f029c816929bf62cf029c8166fd3a3c0a72047d678da2504f029c816965bf4e8f029c816929bf654de29c8160021c504f029c8158eda2654f029c816939bf654f029c8166894144cf029c816929a24e8f029c816001a229c810c4245504f029c810c42e6
  | 5, 1, 1 => 0x92a2e504f029c81692a2a504f029c81692a24504f029c816689413c0a7204796689953c0a720474668995654f029c816689413c0bc29c8167a9413c0a72046d6689953c0f029c816929f2504f029c8166dd413c0ea29c816689413c0d229c816929bf504f0290816929bf5f4b329c816855a2504f029c816929bf504ed29c816
  | 5, 1, 2 => 0x8f9fa504f029c816929bf410a724c816995a2504f029c816689413c0a727c8166fd953c0d729c8160015e504f029c815945a2504f029c816929bc504f029c81692a3b4a0f029c816929bf4bcf029c816689953c0e129c816929bf3c0a7204446989a2504f029c816871413c0a7204716789413c0a7204686001a229c810c42b5
  | 5, 1, 3 => 0x689413c0dc29c8166dd413c0a724c81699e296554129c8168eda24e4f029c81699e29504f029c816881413c0a7204246929a2624f029c816919bf504f029c81681602504f029c8167c9a2504f029c816001a23c0a7204245689413c0a72041f6929bf5a0f029c816839b7504f029c816929bf3c0ae29c816689413c0d029c816
  | 5, 1, 4 => 0x8fa20504f029c816689953c0a7284816689413c0a7204416975bf654f029c8168ddbf504f029c816809bf504f029c816689413c0a7204116689a0654f029c816001b7504f029c545689953c0a7204196985bf504b329c816001b0504f029c815689413c4f029c816689413c0a72043068eda24a0f029c8166fda24bcf029c816
  | 5, 1, 5 => 0x689413c0ad29c816881413c0a7234816929bf5051d2dca76689954e4f029c816001b7504f02043f58e620504f029c816001a2654a7234815001a23c0a72042b56fda25a0f029c8166fda9504f029c8166894142cf029c816001a2504fe29c8150024a6fd952dca75689413c0a7204026929bf2fcb329c816689413c0a7204536
  | 5, 1, 6 => 0x929f55050429c816979a2504f029c816929a2504f02dca76001a26114129c8159ae1c504f029c816959a9504f029c816929bf504f02e0816969bf504f029c8167f1bf504f029c81668941474a723481668978504f029c816689413c0a724081692a296551129c816689954a0f029c81692a1c504f029c816689413c0a72046b6
  | 5, 1, 7 => 0x68969504f029c81692966504f029c8169295e504f029c8166fcf035cbf29c816689413c0a7228816929bf5050a29c8168ce1c504f029c816929bf504a72045f6965f5504f029c816929bf5051d444d9692a26654f029c8167f5a2504f029c8166fd413c0cd29c81690da2504f029c8169295f504f029c8166dd413c0a7204186
  | 5, 1, 8 => 0x689413c0a7204156689413c0d9204686929bf60cf029c816929bf6550b29c81699da2654f029c816925a2654f029c816929bf654f032481692a17504f029c816929c3504f029c816689413c0e929c816929af504f029c816929bf650f029c816929c5504f029c816689413c0a7204736001a2504a7204315689413c0a7204396
  | 5, 1, 9 => 0x6bda2504f029c816929a2504fe29c8166dd414a8f029c8166dd413c0a7204246929953c0a72042f699e296fd9529c8166895e504f029c816689413c0a72040e6929bf654a72408168e9414a8f029c8168da1c504f029c8166897c504f0364816955bf504f029c816689953c0e029c81693dbf504f029c8166fda25050a29c816
  | 5, 1, 10 => 0x929bd504f029c8166fd413c0ca29c816001a2504f029c815831414a0f029c81692a26644f029c81692a25504f029c816689733c0a723481682dfe504f029c81668988504f029c816929a2654a72348168eda23c0a724c816929a23c0a72042b6689413c0a7230816929bf5ccf02dca76929bf654f031c816000008819529c814
  | 5, 1, 11 => 0x68941474f03648165855e504f029c8166894143cf029c816001a2654f029c545871413c0a7204766929bf5050329c816915bf654f029c816929a7504f029c8168d620504f029c816929bf514f029c81682dbf504f029c816689953c0a724c816689413c0a72040066dd413c0a7234816959bf504fe29c816929a26114129c816
  | 5, 1, 12 => 0x8de29504f029c816504f029c810bc2e6929bf504b72cca76851bf504f029c8166fd413c0a72045d6871413c0a72047a699dbf6154129c816000f029c81090195689913c0ea29c816921a2654f029c816001a2654f02043f5689413c0a7204716881413c0a7204546001413c0a72040d594da2504f029c816881fb504f029c816
  | 5, 1, 13 => 0x929bf3c0a72045b6929bf65cfe29c81696e20504f029c816929ab504f029c8166fd6d504f029c816689413c0ec29c816929bf504f02d0a7686214504f029c816989bf654f029c816689413c0a72708167c5bf504f029c81668941470f029c81692a3b4a8f029c816929bf4e4f031c816929bf620f029c81699ded504f029c816
  | 5, 1, 14 => 0x981a2504f029c8166fda2620f029c816929bf640f029c816688f029c810c42b66895c504f029c8166898f504f029c816689413c0a72042a6689413c0e829c816689413c0b729c8160024a8819529c815001a23c0a72041a5504f0330ca29c816002205051129c815929bf3c0c72fc816929a24c4f029c81699dbf4f8f029c816
  | 5, 1, 15 => 0x689413c0a720465699dbf504f0290816881bf504f029c8169ada2504f029c816689413c0a7268816929c8504f029c81668973504f029c816689413c0a72041066d5413c0dc29c816689413c0a7204036965bf504f029c816951bf504f029c816929a2504f029c816929bf504f02ec816929bf5050429c816991bf504f029c816
  | 5, 2, 0 => 0x929bf654ec29c8166fda25050429c816975bf504f02dca76689413c0c729c816959bf504f029c8160014129c810c419588220504f029c816929bf504f02f0816929bf504f529c816871413c0a7284816881413c0a72047d6881bf6554129c816504f0364ca29c81668941448f029c816002206899529c815689953c0a7204246
  | 5, 2, 1 => 0x929bf64cf029c8169c5a2504f029c816929bf570f029c816929bf654b729c816689413c0a7204806689413c0dd29c816689953c0a7234816881414d4f029c816929bf504f03408166dd413c0a7204546689413f8f029c816929bf654f02dca76881413c0a72046d680d413c0a723481699dbc504f029c816689a2504f029c816
  | 5, 2, 2 => 0x96db7504f029c8169b9a2504f029c816929bf654f025c81692a205051129c8166fd413c0ac29c816929bf504f0318816929bf3c0c724c816929bf5ccf029c816689413c0a724881668984504f029c8168d9a2504f029c816871bf654f029c816689413c0a72040d6689413c0a72041c66fda2504f02f08166fd41494f029c816
  | 5, 2, 3 => 0x949bf504f029c816849a2504f029c816001ac504f029c8156fd7f504f029c816504f029c810c02f69261c504f029c816689413c0a72044c66fda2570f029c816929bf65cf029c816881413c0a7204686689413c0a7204376689413c0bc2046d668961504f029c8168816f504f029c816001413c0a72041956fda2504f0340816
  | 5, 2, 4 => 0x6895c3c0a72046d6881a25051129c816929bf654fe29c816975bf654a72348166fda25ccf029c8167f9b7504f029c8166896f3c0a7204716689413c0a7204316689413c0a720470668995604f029c81689a1c504f029c81699e29504a72348168e9fe504f029c8168817c504f029c816689413e4f029c81699e1c504f029c816
  | 5, 2, 5 => 0x929bf504b329c8168720e504f029c816881413c0d929c81668941444a72046d6689413c0a72888166f5413c0a7284816881413c0a7260816689413c0a7204256761a2504f029c8166b1413c0a720471668941454f029c816929c0504f029c81668941464f029c816929bf5c4f029c816689413c0a7204766741bf504f029c816
  | 5, 2, 6 => 0x6fd7c5b4f029c816689845052829c8166fd413c0a721c816831a2504f03648166fd67504f029c81699daf504f029c81600220654f029c815929bf504f629c8168eda2504f029c816689413c0a7204266939bf504f029c8168a56d504f029c816001b5504f029c815881b7504f029c8166894146cf029c816929bf5f0f0258816
  | 5, 2, 7 => 0x92a295050429c816689413c0a7204816929bf5bd0429c816689413c0a7204746929bf684f025881668995504f029c816689413c0a72041d6929bf504fc29c816929bf654a72044c6689413c0a7204096689413c0f029c816929bf564fe29c81688141474f029c8166dd413c0a72046d6881413c0a72043f6799a2504f029c816
  | 5, 2, 8 => 0x689413c0ef29c81692a29504f02f08166dd6f504f029c816689413c0a7204326689413c0a728c816689953c0a720454668964504f029c816929bf54cf029c8167eda2654f029c8166fd413c0d729c81696629504f029c81668941418f029c816689413c0e129c81676da2504f029c816929bf504f02044b6929bf3c0a7204606
  | 5, 2, 9 => 0x6897b504f029c816689a0504f029c816689413c0a7204196929ec504f029c81695ded504f029c81668959504f029c816001a23c0a715024568941444f0364a7684da2504f029c8166dd7c504f029c816928f029c810bc2b699dbd504f029c81695a29504f029c81697605504f029c816929ca504f029c8166dd413c0a7204686
  | 5, 2, 10 => 0x6dd413c0d929c816689414a0f029c8168a61c654f029c816929bf5d0f029c81688141444f029c816689414e4f029c816825a2504f029c816001a26551129c815689413c0a7204576929bf654f029c816001e2504f029c815001a23c0810fc24592a29570f029c81696da2654f029c816975bf504f029c816771a2504f029c816
  | 5, 2, 11 => 0x92a26504f029c8166fd9f504f029c81668963504f029c816929e1504f029c816689413c0bf29c816504f035ccc29c816929bf5f4f029c816001b7654f029c815929bf3c0be29c816881413c0a72040a6689413c0a720c81692a295ccf029c816689413c0a72041b6689414751129c816689953c0a72041a668991504f029c816
  | 5, 2, 12 => 0x68941364b329c816831fb504f029c816689413d0f029c816929bf65511364a76881a2654f029c816929bf564f029c8168fa1c504f029c81692a0e4c4f029c816929bf3c0c829c8168fdbf504f029c8166dd41474f029c816001ea504f029c815001413c0a7204185689413c0a72040566dd413c0a72043f69a5a2504f029c816
  | 5, 2, 13 => 0x93a29504f029c8168eda25bcf029c816689413c0a72044f6929bf644f029c816689413c0e029c81692a29504b329c816689413c0a72043d6689414e8f029c816689413c0b729c8d6929f9654f029c816001a2504a7150315689413c0a7204676929bf504f0324816689953c0a72046d668948504f029c81668941400f029c816
  | 5, 2, 14 => 0x689955f0f029c816929bf554f029c8168ed414a0f029c816001a24bcf029c815929bf504f02d8a76689953c0a7204686689955bcf029c81668949504f029c81692a27504f029c81692a32504f029c816929bf504f031c816871413c0a72040c6929bf3c0bf29c8169bda2504f029c816929413c0a72042f6001a2504810fc315
  | 5, 2, 15 => 0x689413c0b229c816929bf654b729c8d6505283c0a7204746689413c0a729c816689413c0a7204086929bf4e8f029c8167a5413c0a72046d6689413fcf029c81696da24e8f029c816001a25a0f029c815001a2504f029c545915bf504f029c816689413c0a724c816929bf504bc2348166dd41444f029c816929bf654f429c816
  | 5, 3, 0 => 0x92a29654f029c816689953c0a72043f67a9a2504f029c8166fd413c0cf29c81668980504f029c816689593c0a7204686929bf570a7234816929ed504f02f0816689a1654f029c816689953c0d929c8169adbf4e8f029c816689953c0a7260816921a2504f029c8168820c504f029c816001a2504f02043f59cda2504f029c816
  | 5, 3, 1 => 0x6dd414a4f029c816001a25050a29c8159c1a2504f029c81668995638f029c81668952504f029c816961bf504f029c816929bf504df29c81698a18504f029c8166897c4a0f029c8166897c4e4f029c816929ed570f029c816881413c0a720479668995474f029c81692a01504f029c816689413c0a7204696989bf504f029c816
  | 5, 3, 2 => 0x689413c0a7204166688f0364bf29c81692a07504f029c816001413c0ca29c815689413c0a7204246881413c0dc29c81668941458f029c81692a29564f029c81678d413c0a7204686689413c0a72041e692a02504f029c816002678a59529c815689413c0a722c816002203c0a7204245689413c0a7204046739a2504f029c816
  | 5, 3, 3 => 0x929bf3c0a7214816929bf5bcf031c81692a293c0bf29c81668995504a7234816689413c0a72042b6689413c0a720413668995444f029c816689413c0a7234816689413c0a7204346929bf655412dca768e5a2504f029c816929bf504f02dca76689413c0a720401692a29644f029c81692a29504f229c816831413c0a7260816
  | 5, 3, 4 => 0x68981504f029c816001413c0a715019599e295051129c8166897c3c0a724c816689413c0e229c81695dab504f029c8167d5a2504f029c81600220504a7204315929bf504f025c816689413c0a7204476871bf504f029c8168e21c504f029c816689413c0a72047b66fd9e654f029c816689953c0a72040a692a29504f031c816
  | 5, 3, 5 => 0x929e5504f029c816929bf574f029c816689413c0da29c8166bd413c0a72047d6001a2620f029c815929bf654a723481699e26504f029c816929bf3c0a72042b6001413c0810fc195929bf504fe29c8166fd413c0a72046266dd413c0a7204176689413c0a72047c6929bf538f029c81668941460f029c816689413c0a7204436
  | 5, 3, 6 => 0x68941504f029c81699dbf644f029c816001a25050429c8156fd41498f029c816689413c0b129c81699dbf5050b29c816929c2504f029c81668979504f029c81668954504f029c816929ed654f029c816002206554129c815689413c0a7204426689413c0a720451600220504f029c815689953c0a7258816929bf6114129c816
  | 5, 3, 7 => 0x831a2654f029c816001a2504f02f0815689413c0a7204546689413c0e429c816689683c0a72047467eda2504f029c81668941420f029c816689413c0a72046a699d413c0a72042f682da2504f029c8165bd5e504f029c816689414c8f029c816881413c0a7204716689414fcf029c8168d5a2504f029c816689413c0ca29c816
  | 5, 3, 8 => 0x689413c0a72041a6821bf504f029c816001a25ccf029c815929bf504f029c8166fd6d3c0a720471696da2504f029c816689413f8a7204686001a2570f029c81592a29504f02dca76001a2504f0340815881413c0a7270816871414d8f029c81668941410a7204716689413c0a72108166894c504f029c816689413c0a7204216
  | 5, 3, 9 => 0x1a2504b329c815689413c0a72046d6689413c0a7204276929bf564f0364816689413c0a72040f68edfb504f029c816881a26554129c816929bf478f029c816881a2504f029c8165b561504f029c816689953c0dc29c81699e29654f029c81668941428a7204746689413c0a725481668941428f029c816929bf504a72044e6
  | 5, 3, 10 => 0x881413c0a7204316689413c0a7204686929bf570f02f08169c9a2504f029c816689953c0a7204736001a2654a72043156896f504f029c816929bf504a723c8166894149cf029c8169ba20504f029c8167ed413c0a7204746929bf3c0a72042c668977504f029c816881413c0a72040d6929bf500f029c816689414d4f029c816
  | 5, 3, 11 => 0x689413c0a72043b60014129c810c42e5689413c0a72040b6929bf505112f08166897c504f029c81692a206fd9529c816
  | 6, 0, 0 => 0x929bf504f029c92205dbf689a2504f029c8176fd6f5b5413c0a7205e676fd413c0dc29c817929bf505103c0a7205e4a8d9bf504f029c81700000689953c0a720564a6fd413c0a72041c7001bf504f029c81025a4a689413c0a72046d799dbf504f029c8105de71929bf504f029c817001a2504f0364a720580099dbf3c0a7204246001a2504f029c98205a4a6fd413c0a7204807
  | 6, 0, 1 => 0x929a25bd413c0a7205e4a6fd6f3c0a7204717929bf504f029c810c5e4a6fd413c0a7204707929bf504f93c0a7205e4a7f9413c0a7204767929bf504f029c81131e4a6fd413c0a7204377929bf504f02f0811b5e4a6fd61504f029c81792a0e5052a3c0a7205e4a6fd413c0eb29c8179ba4a6fd413c0a7205c0068941474f029c8160024a8a5413c0a7205800689413c0a72043f6
  | 6, 0, 2 => 0x6fda2504f029c810c5e566fd413c0a7204687929bf5051b3c0a7205e4a6fd41444a72046d7929bf504f029ca2205e4a6fd413c0a7204257929bf505153c0a7205e4a6fd41464f029c817001bf504f029c81065a4a6897c504f029c8179b9bf689413c0a7205e4a6fd413c0a7204767929bf570f029c811b5c008a5a2504f029c816929a2504f029c811a1e4a8a5413c0a7204717
  | 6, 0, 3 => 0x9824a8a5413c0a7205e4a6fd413c0a7204747929bf655413c0a7205e4a6fd413c0a72045270024a689953c0a720580068941444f029c816929bf504f029c81075e4a6fd413c0a7204097929bf504f03c0a7205dbf689413c0a7204767929a2504f0364a7205e4a799bf504f029c817929a2504f029c98205c0099dbf504a720431692a3b6fd413c0a7205e4a6fd413c0a72047a7
  | 6, 0, 4 => 0x92a136fd413c0a7205dbf689413c0a72047476fda2655413c0a7205e4a6fd413c0ef29c817929bf504f029c810c9e4a6fd413c0a728c817929bf654f029c81151e6b92a29504f029c817929bf591413c0a7205c00928f029c81090176929bf504f0384a7205e3b6fda2504f029c817929a25051d3c0a7205c00689413c0a72040a6929a2504f029c810fde4a6fd413c0a7204817
  | 6, 0, 5 => 0x24a6fcf02043f091a7192a29504f029c81792a3e5052a3c0a7205e4a6fd413c0a728481796e4a6fd953c0a7205e4a771bf504f029c817929bf5ed413c0a7205e606fd413c0a7284817929bf681413c0a7205e4a6fd413c0a72041976fda2504f0384a7205e676fd414f4f029c817929bf565413c0a7205c00929bf3c0a7150246929bf505113c0d929de4a8a5a2504f029c817
  | 6, 0, 6 => 0x24a7b5413c0a7205a4a68941444f029c8176fda2504f029ca1205e4a6fd413c0bf29c8176fda2504f029c81065e6e92a29504f029c817929bf504f029c8106de4a6fd414751129c817929bf654f029c81069e4a8da29504f029c817929bf645413c0a7205e4a6fd414a0f029c817929c66fd413c0a7205e4a6fd414e4f029c8179adbf504f029ca1205c00929bf6551129c816
  | 6, 0, 7 => 0x929bf654f029c811b5e4a8a5413c0a7204767929bf521413c0a7205e4a6fd41400f029c817929bf504d92cca7205e4a6fd413d0f029c817929bf5053b3c0a7205dbf689414a0f029c81792a29504f029c810c5c00689413c0a7264816929bf654f029c811f5dbf689414e4f029c817929a2504f029c81029c009294129c810c4176929bf504f029c81015e69929bf504f029c817
  | 6, 0, 8 => 0x92a29504f029c811e9e4a839fe504f029c8179ae676fd413c0a7205e4a6fd413c0a72044f700000871413c0a720564a6fd413c0e029c81799dbf504f029c8100de4a6fd414e8f029c817929bf504f02dca7235c00831a2504f029c8160024a6fd4129c540c5a4a899bf504f029c81799e4a6fd413c0a7205e4a6fd413c0a720467799e606fd413c0a7205e4a925bf504f029c817
  | 6, 0, 9 => 0x92a29504f0384a7205e4a6fd955f0f029c817929bf505093c0a7205e4a6fd413c0a72948176fda2504f0380a7205e4a6fd953c0a720468792a29655413c0a7205dbf689413c0ea29c817929bf6556f3c0a7205e4a8a5413c0f029c8176fd413c0d935ca7205e4a839bf504f029c8170024a504f029c8105d80099db7504f029c8169be4a6fd413c0a7205c00929bf504810fc316
  | 6, 0, 10 => 0x1a2504f0370a7205800719413c0a72040a60024a6fd413c0810fda73929bf504f029c817002678a5413c0a7205a4a6fd413c0b229c817929bf504f029ca7205e4a6fd413c0a7204087839bf689413c0a7205c00929413c8f029c816929bf504ff3c0a7205e5b929bf4e8f029c81700000688f029c81091400929bf504f029c546929bf504f029c810bde4a6fd413c0a724c817
  | 6, 0, 11 => 0x99dbf504f029c811d9c006fda2504f02043f692a29505393c0a7205e4a6fd95474f029c817929bf504f029c811a5c0092a1c504f029c816001bf654f029c81029a4a6fd953c0a72043f792a0c689413c0a7205e4a8a5413c0a7284817001bf689413c0a7151a4a6fd80504f029c8176fda2504f029c93205e4a6fd593c0a7204687929bf685953c0a7205e4a6fd953c0d929c817
  | 6, 0, 12 => 0x929bf504f029c81091c00929a23c0a720424692a3e7f9413c0a7205c00929af504f029c816929413c0a7264811d9c00001a2504a7204315929bf504f029c81079e4a8a5bf654f029c817929bf504f029c81011e4a6fd413c0a72044079c24a6fd413c0a7205e4a6fd95638f029c817929bf549413c0a7205e4a6fd7c4e4f029c817929bf504f02a4a7205e67929b7504f029c817
  | 6, 0, 13 => 0x929bf655113c0a7205e4a6fd413c0a7234817929bf504f0394a7205e676fd413c0a728c817929bf504f029c81005e4a6fcf0364bf29c817929a2504f0370a7205e4a8f9bf504f029c81792a29504f03a8a7205e4a719413c0a72040a797e4a6fd413c0a7205e6792a29504f029c81792a05504f029c8d205e4a6fd413c0a720456792a498a5413c0a7205e4a689413c0a7204177
  | 6, 0, 14 => 0x92a29504f029c93205e4a7d5bf504f029c81792a0a6fd413c0a7205e676fd413c0a72848170020b6fd413c0a7205a4a6fd413c0a72044778f9bf689413c0a7205c00929bd504f029c81600000689413c0a720566c929bf504f029c817929bf615413c0a7205e4a6fd953c0a72040a76fda25052a3c0a7205dbf689413c0a7204247929bf6554129c8d205e4a6fd413c0a72042b7
  | 6, 0, 15 => 0x9b64a6fd953c0a7205e6999dbf504f029c81795e4a6fd413c0a7205e4a6fd413c0a72047c70024a8a5413c0810fda4a6fd6e504f029c817929bf504f029c8110dc00929a2504a7204316001a2504f029c811c5a4a6fd7c3c0a724c817929bf5050e3c0a7205e676fd414e4f029c8170024a8a5413c0a7151a4a6fd413c0a72040676fda2504f029c8d205e4a6fd413c0a72040c7
  | 6, 1, 0 => 0x92a0b6fd413c0a7205e4a6fd414fcf029c817002596fd413c0a7205a4a6fd413c0ee29c817929bf505413c0a7205c00929a2504f029c8160024a6fd41410a7205a4a6fd953c0a726481700260689413c0a7205a4a6fd413c0b129c81799e676fd413c0a7205e4a6fd79504f029c817929bf551413c0a7205e4a8f5bf504f029c817929bf654f029c96205c006fd6d504f029c816
  | 6, 1, 1 => 0x929cf6fd413c0a7205e596fd413c0a7204717001a2689413c0a7205a4a689413c0a7204717929bf5050429c811c5e4a6fd413c0a7210817929bf531413c0a7205e4a8a5413c0a7204247002566fd413c0a7205800929bf504f02f0816929bf504f029c81151c0099d413c0a7204176929fb6fd413c0a7205c00881bf504f029c8169ae4a6f5413c0a7205c009ada2504f029c816
  | 6, 1, 2 => 0x96dbf689413c0a7205e4a6fd413c0a725481700000504f029c810654009b9a2504f029c81692a056fd413c0a7205e4a6fd413c0a72041a7929fa6fd413c0a7205c00929bf5ccf029c816929bf504f029c8108de4a6fd413c0a720478792a29504f029c8d205dbf689413c0a720454796e4a6fd413c0a7205e4a6fd413f8a72046877edbf689413c0a7205c00929bf570f029c816
  | 6, 1, 3 => 0x929bf505273c0a7205e206fda2504f029c8176fda2504f029c811f5c008eda2504f029c8160024e6fd413c0a7205800929bf504b329c816929bf504f029c811b5e4a6fd413c0a720427792a186fd413c0a7205dfe6fda2504f029c817001a2504f029c811d9a4a881bf504f029c817001a2504f029c810c5a4a6fdbf504f029c817929bf654f0370a7205e4a929a2504f029c817
  | 6, 1, 4 => 0x929bf504f029c8101de4a6fd76504f029c8170024a504f02043f05da4a8a5413c0a7204547929bf5f1413c0a7205c006fd413c0d729c816929bf504f0330a7205c00689413c0e129c8160024a504f029c5405da4a6fd413c0a72046879ca4a6fd413c0a7205e4a6fd953c0a72047370024a6fd9529c810c5a4a6fd6f504f029c817001a2504f029c811d180068995504f029c816
  | 6, 1, 5 => 0x1a2505393c0a7205a4a6fd413c0a722081796e4a8a5413c0a7205c00929bf654f029c8160024a6fd413c0540fda4a6fdb7504f029c817929bf504f029c81191c00975bf504f029c816001a2504f029c81065a4a6fda1504f029c817929bf504f0364a7205e4a6fd413c0a726081792a3a6fd413c0a7205e4a6fd413c0a72043b7929bf505173c0a7205e4a6fd413c0a72046c7
  | 6, 1, 6 => 0x929bf504f029c81169c00929bf564f029c816989bf504f0370a7205e4a6fd8e504f029c8170024a899413c0a7205a4a6fd953c0a72047170024a504a7204310bda4a6fd413c0a7204487929bf505043c0a7205e4a8a5fe504f029c817929bf504f029c8118de4a6fd413c0a72046e7929bf5051d3c0a7205c00689414a0f029c816929bf504f029c810fde4a6fd414d8f029c817
  | 6, 1, 7 => 0x929bf504f029c81029e4a6fd393c0a7204717929bf65541444a7205e4a6fd413c0a72043870024a6fd413c0c7205a4a6fd41444f029c8179824a6fd953c0a7205c00929bf3c0bf29c816929bf504f029c810f9e4a689413c0a72848170024a504f029c810bda4a6fd413c0a72988178a5bf689413c0a7205c00929bf644f029c816001a2504f0380a7205a4a8a5413c0a72046d7
  | 6, 1, 8 => 0x929bf689953c0a7205e4a6fd413e0f029c81792a295f1413c0a7205e4a6fd413c0c720471700000689413c0a715164a6fd7c5bcf029c817001a2504f029c93205a4a6fd413c0db29c81792a29504f029c811a1c00929bf3d0f029c8166fd414e4f029c811f5e4a8a56f504f029c81783a0b6fd413c0a7205e4a6fd413c0a72248179ae4a6fd953c0a7205e4a6fd413c0a7204287
  | 6, 1, 9 => 0x92a0e689413c0a7205e4a6fd413c0a725881792a295051d3c0a7205e4a6fd413c0a72045e792a446fd413c0a7205e4a8a5413c0a72043f79ba4a6fd953c0a7205c00989bf504f029c8160024a8a5953c0a7205a4a6fd413c0de29c81792a29504f0364a7205e4a6fd413c0b329c81700000689413c0810fd64a6fd413c0a72043c70024a6fd3a3c0a7205a4a6fd413c0c329c817
  | 6, 1, 10 => 0x24a504f029c81031a4a6fd953c0f029c817929bf504f0348a7205e4a7b5413c0a72046d70024a6fd413c0b729da4a6fd4144cf029c8170024a6fca720431091a4a831bf504f029c817929bf504f0360a7205c00689413c0a7204246929bf504a7234811b5e4a6fd413c0a7204727929bf3c0a724c811c5e4a6fd413c0a7208817929bf504f029c810a5e4a6fd953c0a7204317
  | 6, 1, 11 => 0x929bf504f029c81009e4a6fda0654f029c817929bf504f13c0a7205e4a6fd413c0dc29c8170024a6fcf029c81091a4a6fd413c0a72041f799dbf6dd413c0a7205e4a504f029c810c42f79464a6fd413c0a7205c00871bf504f029c816929bf654f0384a7205c00929bf29c810c42b692a29505113c0a7205e4a6fd95654f029c817929bf504f02f0a7205c00689413c0a7234816
  | 6, 1, 12 => 0x1fb689413c0a7205a4a6fd413c0a72047370024a6fd4129c810c5a4a6fd413c0a720439796e4a6bd413c0a7205e4a6fd413c0a7228817929fd6fd413c0a7205c0000220504f029c81592a3e689413c0a7205e4a6fd41474a7234817929bf504f029c90205e4a6fd413c0ad29c817929bf655393c0a7205c00929bf654a72348160024a6fcf029c810ad800929bf504fe29c816
  | 6, 1, 13 => 0x94e4a6fd413c0a7205e4a6fd41474f03648170024a6fd953c0a7151a4a6fd953c0a724c817929bf504f029c81001c00929bf504f029c816001413c0a72041702980096da2504f029c816929bf5ccf029c8d205e4a899413c0ea29c817929bf504f029c8c205e4a6fd413c0a72040e7929bf5f1413c0d9205e676fd413c0a72040a7929bf504f0364811a1c00689413c0a7204546
  | 6, 1, 14 => 0x929bf505123c0a7205e4a6fd953c0a7204247929bf504f029c81195c00689413c0a7204686929bf5cd413c0a7205c006896f504f029c816929bf3c0a7204310ade4a6fd5c504f029c817929bf504f029c810a9e4a6fd413c0b729c8170024a6fcf029c81069800689413c0a72046d600220689413c0a7205a4a6fd913c0ea29c8170024a6fd953c0810fda4a6fd413c0a7204717
  | 6, 1, 15 => 0x929bf504f0374a7205e4a6fd953c0a7234817929bf504fe3c0a7205e4a6fda2504f029c817929bf504f031ca7205c006897c504f029c816
  | 7, 0, 0 => 0x24a8f9bf504f029c8170024a6fd413c0a720424700000929bf504f02043f600000929bf504f029c5460024a6fd413c0a724c8170024a839bf504f029c81700000929413c0a720417600267929bf504f029c8170024a6fd414e4f029c8170024a6fd413c0a72848170024a6fd413c0e129c8170024a6fd95504f029c8170024a6fd413c0a72047670024a6fd413c0a72043170026e929bf504f029c8170000092a29504f029c816
  | 7, 0, 1 => 0x929bf3c0a72042460024a6fd413c0a72040a70024a6fd41444f029c8170024a6fd41474f029c8170024a6fd413c0a72043f700000929bf654f029c8160024a6fd413c0d929c8170024a6fd7c504f029c8170024a6fd413c0a72046870024a6fd6f504f029c8170024a6fd413c0a72046d70025b929bf504f029c8170024a6fd413c0a720454700000929a2504f029c81600000001a2504f029c8150024a6fd413c0a7234817
  | 7, 0, 2 => 0x24a6fda2504f029c8170024a6fd413c0a720471700000929bf504f029c81600000929bf504a72043160024a6fd413c0dc29c817
  | 8, 0, 0 => 0x929bf504f029c816
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
private theorem z3_24 : span (Z 3) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_48 : span (Z 3) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_72 : span (Z 3) 16 72 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 72 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 24) z3_a1 z3_48

private theorem z3_a3 : span (Z 3) 88 0 = true :=
  span_join (f := Z 3) (a := 72) (o := 0) (b := 16) z3_a2 z3_72

private theorem z3 : span (Z 3) 88 0 = true := z3_a3

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
private theorem z4_288 : span (Z 4) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_312 : span (Z 4) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_336 : span (Z 4) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_360 : span (Z 4) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_384 : span (Z 4) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_408 : span (Z 4) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_432 : span (Z 4) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_456 : span (Z 4) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_480 : span (Z 4) 24 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_504 : span (Z 4) 24 504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4_528 : span (Z 4) 6 528 = true := by decide +kernel

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

private theorem z4_a12 : span (Z 4) 312 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 24) z4_a11 z4_288

private theorem z4_a13 : span (Z 4) 336 0 = true :=
  span_join (f := Z 4) (a := 312) (o := 0) (b := 24) z4_a12 z4_312

private theorem z4_a14 : span (Z 4) 360 0 = true :=
  span_join (f := Z 4) (a := 336) (o := 0) (b := 24) z4_a13 z4_336

private theorem z4_a15 : span (Z 4) 384 0 = true :=
  span_join (f := Z 4) (a := 360) (o := 0) (b := 24) z4_a14 z4_360

private theorem z4_a16 : span (Z 4) 408 0 = true :=
  span_join (f := Z 4) (a := 384) (o := 0) (b := 24) z4_a15 z4_384

private theorem z4_a17 : span (Z 4) 432 0 = true :=
  span_join (f := Z 4) (a := 408) (o := 0) (b := 24) z4_a16 z4_408

private theorem z4_a18 : span (Z 4) 456 0 = true :=
  span_join (f := Z 4) (a := 432) (o := 0) (b := 24) z4_a17 z4_432

private theorem z4_a19 : span (Z 4) 480 0 = true :=
  span_join (f := Z 4) (a := 456) (o := 0) (b := 24) z4_a18 z4_456

private theorem z4_a20 : span (Z 4) 504 0 = true :=
  span_join (f := Z 4) (a := 480) (o := 0) (b := 24) z4_a19 z4_480

private theorem z4_a21 : span (Z 4) 528 0 = true :=
  span_join (f := Z 4) (a := 504) (o := 0) (b := 24) z4_a20 z4_504

private theorem z4_a22 : span (Z 4) 534 0 = true :=
  span_join (f := Z 4) (a := 528) (o := 0) (b := 6) z4_a21 z4_528

private theorem z4 : span (Z 4) 534 0 = true := z4_a22

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
private theorem z5_720 : span (Z 5) 24 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_744 : span (Z 5) 24 744 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_768 : span (Z 5) 24 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_792 : span (Z 5) 24 792 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_816 : span (Z 5) 24 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_840 : span (Z 5) 24 840 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_864 : span (Z 5) 24 864 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_888 : span (Z 5) 24 888 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_912 : span (Z 5) 24 912 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_936 : span (Z 5) 14 936 = true := by decide +kernel

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

private theorem z5_a30 : span (Z 5) 744 0 = true :=
  span_join (f := Z 5) (a := 720) (o := 0) (b := 24) z5_a29 z5_720

private theorem z5_a31 : span (Z 5) 768 0 = true :=
  span_join (f := Z 5) (a := 744) (o := 0) (b := 24) z5_a30 z5_744

private theorem z5_a32 : span (Z 5) 792 0 = true :=
  span_join (f := Z 5) (a := 768) (o := 0) (b := 24) z5_a31 z5_768

private theorem z5_a33 : span (Z 5) 816 0 = true :=
  span_join (f := Z 5) (a := 792) (o := 0) (b := 24) z5_a32 z5_792

private theorem z5_a34 : span (Z 5) 840 0 = true :=
  span_join (f := Z 5) (a := 816) (o := 0) (b := 24) z5_a33 z5_816

private theorem z5_a35 : span (Z 5) 864 0 = true :=
  span_join (f := Z 5) (a := 840) (o := 0) (b := 24) z5_a34 z5_840

private theorem z5_a36 : span (Z 5) 888 0 = true :=
  span_join (f := Z 5) (a := 864) (o := 0) (b := 24) z5_a35 z5_864

private theorem z5_a37 : span (Z 5) 912 0 = true :=
  span_join (f := Z 5) (a := 888) (o := 0) (b := 24) z5_a36 z5_888

private theorem z5_a38 : span (Z 5) 936 0 = true :=
  span_join (f := Z 5) (a := 912) (o := 0) (b := 24) z5_a37 z5_912

private theorem z5_a39 : span (Z 5) 950 0 = true :=
  span_join (f := Z 5) (a := 936) (o := 0) (b := 14) z5_a38 z5_936

private theorem z5 : span (Z 5) 950 0 = true := z5_a39

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
private theorem z6_456 : span (Z 6) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_480 : span (Z 6) 22 480 = true := by decide +kernel

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

private theorem z6_a19 : span (Z 6) 480 0 = true :=
  span_join (f := Z 6) (a := 456) (o := 0) (b := 24) z6_a18 z6_456

private theorem z6_a20 : span (Z 6) 502 0 = true :=
  span_join (f := Z 6) (a := 480) (o := 0) (b := 22) z6_a19 z6_480

private theorem z6 : span (Z 6) 502 0 = true := z6_a20

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

def CG : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12577

theorem PEqualNP.Outside.L_meta_12577 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12577.mainG PEqualNP.Outside.L_meta_12577.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12577.CG, PEqualNP.Outside.L_meta_12577.CG_mono, by
      have : PEqualNP.Outside.L_meta_12577.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12577.CG_eval⟩
