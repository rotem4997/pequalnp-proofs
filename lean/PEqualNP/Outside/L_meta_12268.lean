import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- NOT gates save nothing on this six-input function: an AND/OR circuit with 10 gates is given, and a
-- table of live-wire states, checked by the kernel, shows that no AND/OR/NOT circuit has 9 gates or
-- fewer. The checker (Run, exists_run, next, covers, bar, moves) is copied from the merged
-- PEqualNP/Outside/L_meta_8493.lean; the rows are all pairs of a zero row and a one row, and the
-- tables hold 64-bit truth tables that expand to those pairs.
namespace PEqualNP.Outside.L_meta_12268

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 0, 56, 0, 0, 0, 0, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 27, 28, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 25, 25, 41, 42, 43, 44, 45, 46, 47, 25, 25, 25, 25, 25, 25, 25, 55, 25, 57, 58, 59, 60, 61, 62, 63, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 25, 26, 27, 28, 29, 30, 31, 26, 26, 26, 26, 26, 26, 26, 26, 26, 41, 42, 43, 44, 45, 46, 47, 26, 26, 26, 26, 26, 26, 26, 55, 26, 57, 58, 59, 60, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 25, 26, 27, 28, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 27, 27, 41, 42, 43, 44, 45, 46, 47, 27, 27, 27, 27, 27, 27, 27, 55, 27, 57, 58, 59, 60, 61, 62, 63, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 25, 26, 27, 28, 29, 30, 31, 28, 28, 28, 28, 28, 28, 28, 28, 28, 41, 42, 43, 44, 45, 46, 47, 28, 28, 28, 28, 28, 28, 28, 55, 28, 57, 58, 59, 60, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 25, 26, 27, 28, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 29, 29, 41, 42, 43, 44, 45, 46, 47, 29, 29, 29, 29, 29, 29, 29, 55, 29, 57, 58, 59, 60, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 25, 26, 27, 28, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 30, 30, 41, 42, 43, 44, 45, 46, 47, 30, 30, 30, 30, 30, 30, 30, 55, 30, 57, 58, 59, 60, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 25, 26, 27, 28, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 41, 42, 43, 44, 45, 46, 47, 31, 31, 31, 31, 31, 31, 31, 55, 31, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 25, 26, 27, 28, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 43, 44, 45, 46, 47, 41, 41, 41, 41, 41, 41, 41, 55, 41, 57, 58, 59, 60, 61, 62, 63, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 25, 26, 27, 28, 29, 30, 31, 42, 42, 42, 42, 42, 42, 42, 42, 42, 41, 42, 43, 44, 45, 46, 47, 42, 42, 42, 42, 42, 42, 42, 55, 42, 57, 58, 59, 60, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 25, 26, 27, 28, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 43, 43, 41, 42, 43, 44, 45, 46, 47, 43, 43, 43, 43, 43, 43, 43, 55, 43, 57, 58, 59, 60, 61, 62, 63, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 25, 26, 27, 28, 29, 30, 31, 44, 44, 44, 44, 44, 44, 44, 44, 44, 41, 42, 43, 44, 45, 46, 47, 44, 44, 44, 44, 44, 44, 44, 55, 44, 57, 58, 59, 60, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 25, 26, 27, 28, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 45, 45, 41, 42, 43, 44, 45, 46, 47, 45, 45, 45, 45, 45, 45, 45, 55, 45, 57, 58, 59, 60, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 25, 26, 27, 28, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 46, 46, 41, 42, 43, 44, 45, 46, 47, 46, 46, 46, 46, 46, 46, 46, 55, 46, 57, 58, 59, 60, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 25, 26, 27, 28, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 47, 47, 41, 42, 43, 44, 45, 46, 47, 47, 47, 47, 47, 47, 47, 47, 55, 47, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 25, 26, 27, 28, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 55, 55, 41, 42, 43, 44, 45, 46, 47, 55, 55, 55, 55, 55, 55, 55, 55, 55, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 25, 26, 27, 28, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 57, 57, 41, 42, 43, 44, 45, 46, 47, 57, 57, 57, 57, 57, 57, 57, 55, 57, 57, 58, 59, 60, 61, 62, 63, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 25, 26, 27, 28, 29, 30, 31, 58, 58, 58, 58, 58, 58, 58, 58, 58, 41, 42, 43, 44, 45, 46, 47, 58, 58, 58, 58, 58, 58, 58, 55, 58, 57, 58, 59, 60, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 25, 26, 27, 28, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 59, 59, 41, 42, 43, 44, 45, 46, 47, 59, 59, 59, 59, 59, 59, 59, 55, 59, 57, 58, 59, 60, 61, 62, 63, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 25, 26, 27, 28, 29, 30, 31, 60, 60, 60, 60, 60, 60, 60, 60, 60, 41, 42, 43, 44, 45, 46, 47, 60, 60, 60, 60, 60, 60, 60, 55, 60, 57, 58, 59, 60, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 25, 26, 27, 28, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 61, 61, 41, 42, 43, 44, 45, 46, 47, 61, 61, 61, 61, 61, 61, 61, 55, 61, 57, 58, 59, 60, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 25, 26, 27, 28, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 62, 62, 41, 42, 43, 44, 45, 46, 47, 62, 62, 62, 62, 62, 62, 62, 55, 62, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 25, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 41, 42, 43, 44, 45, 46, 47, 63, 63, 63, 63, 63, 63, 63, 55, 63, 57, 58, 59, 60, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x17f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff0000000000000000017f01ff01ffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xfe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe0000000000000000000000fe80fe00fe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xfe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000fe80fe00fe000000

def cMZZ : Nat := 0x17f01ff01ffffff0000000000000000017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff017f01ff01ffffff

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
theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 4096) (goal 4096) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)
theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 4096) (goal 4096) s xsG) :
    ¬ HasCircuitSize 6 fG 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 9 h
  have hr : NatRun (mask 4096) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 6 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 2 => 1
  | 3 => 41
  | 4 => 304
  | 5 => 1295
  | 6 => 1839
  | 7 => 622
  | 8 => 20
  | 9 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xae567c3
  | 3, 0 => 0xd998d02ea1dc851f9b4bbdb99af493ae913a3e9d8a46aa3189a958cd878511db7c1e32c36ef62f476dfe204065d108495cbce1ec4d7554284c4b9ed849e1607f44638c39434772184212507a3de88be93231f3832e24a5572b55d7ab2b07f06627bad6ee25ebe75f25d76e8e255618131e7f58841e7de7cc1d2bcd9e17ccdda717a52b8f16f0ae03168b633b155cf30b128e9f6511eba0b80ec5123206146cd802f3cc82
  | 4, 0 => 0xf8ef7b10f04745e0ec132990e8b89210ddf24f30db0287a0d89ea710d676dbb0d6114b00d42b1780d0bbfd00ce081380cb546b50ca294a90c7890bd0bad57010b8be6290b672ec20b53d3d10ae88e440aa492b40a8a0d770a83ad750a6d51940a4bec8e0a464ec50a027467095314b2091675c408fc2a3c08aeb634072539c907141c8f0707ff1e06db410f06d3e014068ad91a0640492f0636235105eaaeef05e79e7b0585642705804576056f20c204b60f7c04b0f09504690a64042f362d040a391a03548286030ed58a02bfb5de028f34cd028058770271c96b01e1369e019fe02300b5cbba0098bfff00852e600082e80e007bbb850073b775006190b1
  | 4, 1 => 0x2574b65c24dafc68247287b3244f1d4a23cd63a723bbbdae23879d602355fae4233f1d7122927a62219bbbf821452f52212bf46f1f8712c51f06dd081ec8179e1e97f3541e23ae441e1ee0cf1de27dc41dc0d71b1db254c71d790e821d2fa8041d1af8111ca82d761c7ba5241c168fad1bf7d9c61b41d11f1b2a4b8f1ae1eda21a1a2bd719e8f4e619387d0b18e5faa418cf2e9b18a5b5261850be08182ca1981804583017e365bf17c555341776b7af16fc8fd81691bdeb167bbb3715f666fd15d1652c15ab5a3a1519f9ad14d16f7a1443015d14334db113cd611e1336f12f12883d771264fd32124336cf11ec02161122d62c1108687610053c0e0feab107
  | 4, 2 => 0x3b8609ec3b0622eb3af927203ae882ab39d45d2e399848dc3950c0ee3937ee6e38d2d5bc3819b16e37eaa4fb372eaee035b0e73d35ad282134dda39e34c4383834ae88d03455e5ef341b269f335e8fa5335ad14b334f4c5832a31ab032417304319f9409316ba95d30d26fe83095af032f857efd2f4f03d32ed5a1602e47e3af2e0804882d8ad5dc2d7f7b6f2c0fe23c2c01ae112bcb637b2b9cb0072b6f1abe2b30dc502aa19efc2a8c0a132a83b7ec2a5e12b729c1662f2992ec9929529e96290e819128fbb91228dfeeee28b2bfbf288a9248281d9d0e28165969280ece7c27e06da927cab17726696215260725fd25f95a1c25f0a7cb25d0109825c70528
  | 4, 3 => 0x612295515d778aa85cd8c7455cc41bb45be66e545b870dbd5af3f46c5a8519c559cadb465918514d587127c65740c85556f2125556ec3619569db0fc568487a055bd5abd523e8b4a50b5258c4fff23aa4ec771564e9cf4244e7e548c4d6f56844d3a04314cbed7cf4c480a6d4bc932904b63870e4b637e7a4a041ff849507a1c46db879c466687fe45791346451e3a0944e93d7b44d4a9884470b215446db94f446a24b544638c3943f74d3343edac2e43772d2043088eb642fdc82941dd22b941cb221b41716f9e40bc42223fb8e99d3faf059e3f1f27a63efde7e93ed0141b3e32ed533defd5533d9c69413d5ab46e3d27935c3cbaf2003bba5bab3b97f869
  | 4, 4 => 0xf9a2d9eef68323e1f636bfc8ed81f330d8814867d3f2b072c25e0477bf8a41deb95f74a8af413a1faad7c88aa9c5c393a87e54329e20c1b79d6e40329b4bbdb9996b27649729d43e8cfa2d978c262e028b3242798a45bea589359d0988beec3c87e1331a86c7115785a13e7782eb2771813e37677fb791ee7cef5f3e78c0279a77fccf4f767f12c77594b9186f28b2706da5de586d504cd76a53618e69e21eac6960ecdf6881ad1867f6673966b55fc0650612f764e52488620c5b9761ff8232
  | 5, 0 => 0x31e88bd02fa4cb802f3f13702d8e04c02d37b8802bfb5de02bf6a6302bc83d902ab844c0292c273026c25eb0261222c024a9c1a024369e50230f21b0215897c0211bf3c020c8b3501cc799f01a88e85019bc16201888f3901868caa017cdb5f0178359d0176e7d401713d61016c913601671694015efe1e01597de401438150013ca7340138571a01360e650134f6d0012a5d580109ad4a0104dd2400e570ae00ce7a1100ca7f5c00c64bed00b49c0400ac7f0200a7b89800a76b7900a27b790086f1d60083bbca00737e430071ac3c006d1ee6006953d200593a370058d9d2003470eb003085ec002663f6002392a1001cd718001c75e00010795100026962
  | 5, 1 => 0x6716ac30670b89b066407a5065962e0065929270650d7bd064b919206472ec006391dfc062b4a120618e3a90617d577060a5e930604d4fb05f9974805e2f3ab05d8c9d105b76bf605a27e21058f07ab058cedd50583887b057b22a30575bc23055bd0c005426b2b053883b70531daf7052c384a052b41dd051e582a0512567404fcfcb504f067e904dfd63f04d8e1fc04d7a5f704d16b8404b9091f04b37c5e04a83bf604a55b260492d40f04926e200489053b04824cdb047688f304624dce04402c000438949904256b93042305630420b755041f0a850407e09103ef9f6103eec7ce03e554d903d3945a03b855fb039cb3ec0390a78c037836b1032d4e9d
  | 5, 2 => 0x9b24ee7098e24ca098c9b18097ffd1c0955b196093b321308f6f28a08ebfa2708e8711508e2252f08d879bc08cf041a08bf44c208bda2e708b933e008aeb634089942a308957939088fc845087ff597087b49a1086bf5a8085c8b6f085c4a75084d17ab08455436083fb97c0836632508283bc2081afd50081904ce08143b44080f0fe307fd681b07fbac3b07e3870307d50b2107ced2cf07bf786b07bb6f4b07b3b97d07b0cb3b07a0118a079fb612079db9c4079bfef2079a5b2407840138077847b2076f4c2a07602702074ded8b073bddd706fd38ac06f6698706eb049f06d8d9c206b7396406ae990506a5420606a2b5a7069aceb4067d985306722dc8
  | 5, 3 => 0xdf10f1e0de78d840db18a000da436f50da1f1330d98ad770d9526d60d7bcef20d5eff330d5347bf0d42b1780d2a41440d298e580d291e2d0d2444840d1b0d5b0d18e1bb0d183eed0d109dbc0cebac720cd778650ccbef6f0cc998580cbad8070cb8a1b50cb3ecec0c95dca80c909f160c8a97580c730d3b0c71df350c41491b0c0366340be1f8550bd35f690bc872ce0bc4a6ee0bb9024d0baab15b0ba6c1270b8440830b6d6ce60b5428690b34059e0b26c3d80b2553f40b1ca9e70af1dab20ae8989f0ae4f9450ac7209a0a74d2800a7094720a594ae80a4fdbea0a44c0790a3c7a530a3bd20b0a201ea50a1651b30a02746709d54ed609c37b0c09b3eda0
  | 5, 4 => 0x11f8fc8711ec9a4a11e8585e11bca647119e31011181da48116b5bdb1163939411601959115497e1114318a1111cdd21111c40c11116fa6110f6eef310f337c710ec566410dd9f5310d7185e10ca09e4109f2783108cb80c1089d3c3107aba241073e8af10694da310635c40105c862e1057482d1055620e10413487102371c51017b5761007273b0fd024250fbe511a0faa8e010f92adf50f91bee60f7e2d450f6eb8120f5bac670f5783ec0f56ad450f5410710ef9045d0eef1d640eda70430ed807bf0ea030fb0e9e4ce30e8ba6130e88ea530e6b60970e62afc50e5255eb0e3dd7650e2758380e273fe80e2479f30e1374470e0af81f0e00ddf40dfa8e03
  | 5, 5 => 0x16693f3e165de1131629cb5f162843b415fbdc2f15f3fdd815c5ecdd15b3330d15ab5a3a158eaa0f1581fcff15798739155da968153ddffa153480f61505606a1502baa3150126e914e21b2614dc133d14c5abfb14be764f14be643414acccae149d035114710288145de89c14411c70143c18311431d265142d56f4141c343114165dd313f8d43113eb7c6313e7fe5813e044e513dab0ac13c51f5513aaa2ae13a1c8de138f55221372788b1357fa241353e5d4133fb536133c4f111329e23a131da47712f15ddf12f016cd12ecce1c12c7649312b438f3129fbeb0128d07741288af0c1282915912819e4c1272bc831245aecc12326ad21210c8911205afd8
  | 5, 6 => 0x1a2022141a1dae241a01a7fd19f1b4f319e324a419e2901e19dd021619c55fef19ba86fe19b743c519ad92f519a2254a199afe15195dbacc195813a31956e9271940c159193d9539192c584a1918318f1914083b1901102918ffc17118e2494118d38d2618cdc60f18c9b6d218b179eb18ac6e96188ced85188400e018805e38187d8e881879975e186d3e14186cf1de1864084d1848a149184590db1843b1d1180955101808827d17f5b9fe17f51bf917ed4c1a17d9489817b7b86617a6c5e1179f0e67177057581766d11f175edd2c175a3d951724ccff17178cfb1706e9491704b6d716de883716c641ba16c4455416b4a6e4169bf737169a2da016872a6f
  | 5, 7 => 0x1f8687a91f6eef891f67a2a51f3e21601f386b6f1f34e3ba1f233f1f1f18b2891ec584b51ea87c6e1e971a331e5f25db1e4904bf1e3c0eed1e32f78a1dcebeb11db2b0331d953ca01d6d3fcb1d3682c21d3160d51d2bdf7d1d212cf11d031e061cd52cba1cc232561cbbec401caa778b1ca82d761ca209071c83f4901c6cc0e21c6acb571c60469b1c548f111c4863b11c2e1cdb1bf7c3041bf0c0271bcf2bc21bcb96d81bbb2ab11baf11321b9d92111b9598ff1b6e6ed51b373cc71b2e67031b09e3281b0740d11afbaefd1ae7eed11ae709441ae3eb141ac595761ac166b71ab15f291aa2cb9f1a9b73921a96df401a96b0f31a899c171a5bb91f1a2c27b4
  | 5, 8 => 0x24aae82924a7290d2493d4a0248afcf1247975302476e9e4246b6239246aba072406824f23ef8c1f23e318fb23d2245b23c637eb2355fae4234fe6db2349bb242344e46a232c03802319fc592315278b230ea03b229b9e122274703c22666a03225fe289225bdf422254d23722418be52232e3a121d1eb6621bd460621af5cf1219f38bf219b283c21968f5a21929948218c2c26217153b6216a7970215cab39213684f12130f59f2128b61121036e6220f0544220ba18a0209994f5208b79242065a1272042481a203ec25b201a86302009baee2003c0e82003a9a52002065a1fff97801ff8c2a51fe468871fd29c431fcc70d41fb4d0151f8fd4d71f8712c5
  | 5, 9 => 0x2a92ab972a8c0a132a800ad82a7798ea2a664f7c2a55f5b92a38e42529f9d18529c1662f29baaf43297d8185297408f3292d8a2e291e502c2905e7a228fa2c3228edfac928dc29fb28b7d56a28a176bc289249c828887f3028826108286e1cfb2840fa592831ef5a2831454627eb788427d79c9a27ccd6a827a2e88a279ebce4277e9e18277a32c727701883275d9d07272a669c272519672724c3ec270b775f2707b59526ca832726a118b42686bc9b2679da8a267266f126395ca82625e8b52612848226110a14260725fd25f95a1c25e6347a25e4b65225a8fd87258f35372580394e255af5b82553baa5250d26532501c67124ecd82d24dba2ca24ce4f8e
  | 5, 10 => 0x3022e72c2fe982542fe3b7092fc982032fc254df2fb6430e2fa699ea2f5234b32f50513c2f4f03d32f4612522f3b26ee2ed11cf82ec7c99c2ec73a922eb2ea892ea9068a2ea210522e9f79c62e92a0422e5ee8be2e5da6bf2e5803532e4967de2e2aee2a2dfb25262dc9a34c2dc6bc082dbdcd142dbb8ae12d7d58c42d6224422d4e6bcc2d3152362d2cee3f2d1ad5022d0b1ae32d0530d62c953d632c5dec932c5d44c72c58f30d2c54b55a2c48a12c2c45e0f62c3f8fd32c3771902c05f07f2be3d5b72bcaac8a2bb4871e2b90b9132b528faf2b4a131c2b3540a72b2b38422b2821092b14121c2b117d032adb4ecc2ac40a0a2abd01c02ab45c972a9a639a
  | 5, 11 => 0x345ad830345481d83450ba87344508d2343cf810341bfe1834183af53400dffd33ff816f33d6886033b4e31f337d750f3365f262335930903357c1cb33509f7133437806333dc7d432f14e1f32e7ad1a32d552a232d51a6432cad14032bf927132b1602732aa4f7732a8ec253291688c32712e0c323c29a03234d3873233e99b3229d15a322407d13203dc0c31fb81bf31f1a4dd31d8ea1331ce8b0b31ad2a4231a75b7631694ba23168250b316550da311fa8ab311879ba310ed38f310c013530fa99f930eaa8aa30deb3c930d4044b30c2340630b8aea830a545c630a38d7430a111ca30a09350309d35683095af033073f8ae3073ad8a30690c5a302e35c6
  | 5, 12 => 0x3b63029b3b3cdda93b2de3813b187e183b0f02a03b0e01f73b0a88dd3a8350953a7526523a708db63a69866b3a4aebb13a35f62f3a0017ec39e7c75539dd5b2e39a35790399ba5d139628eef393660a0391041343901b2bf387d7143384f5f73384a7b083836e48337e44d8a37c0e82c37a636c337a4284537a36e41371b6b7e370c479836ecb2fe36b16b6d36a11a16369c7fd236879d6c3680b2fd366629bd3653894a364220183639be97363402a5362b9690361bb8ab3615f4ea36151b0a36087e9135fa9d2d35f4545b35dea11035db544135c49ba335a6d97d359829e8359199db35883526354b208f34f54f7a34ae88d034a9e9783473143234667c36
  | 5, 13 => 0x430cb3fa42e8048a4287479d4283b50942083d2441f8c72f415ed50741576657411e0fb641053c4c40fcadbb40b2e9a3409fa392409667ae407040754040e8b1402e738e3ffc70ee3fcf49133fcb13293fc832013faf26783f76fa333f3079c83f25cef83ef817c03ed0d3683ed0141b3eaac77e3e900e173e8e37733e6e3d3e3e4d37863e45438e3e3a09f83e17efad3e06ea263df562e63dc304ee3d96f5103d7fdbe33d5e990c3d5b40fd3d1969e93cf497c33ce57e473cc60c153c9ddf533c8214f33c7e44883c55588a3c4dc0e53c47b56d3c1452473c14397e3c0854a33bf811e43bc67b963bb5614a3bad5da03b97f8693b93aeb63b92cc903b775306
  | 5, 14 => 0x4be91e6f4bd2c8314bbe1ca04ba4dbca4b992cef4b829d484b2987e94b0400204af82de94ace47a94acda4d94a810ea94a668a0b4a52d2004a45d2db4a047be849e2641449b65753496129fd4930274a48fe840348cfc45048a5dd8f484529ed47f33e074781b328478098ac474a59884740f574472fbfd447298fac47291ea7471c773747107255470694c54702141846f87ae446b85758463af4e2462453f345ec134145c9d68e45c65c9c4597b1e8457b20ff455a1f0e4553412a45264e76451e3a09451cda9d450e02d744b75ba944a897ec44a4beff4473bd95446540d8445f0c28445028ba4381488f437653ac435e11a2434df2ed43407e4b43378bea
  | 5, 15 => 0x5530c1f654f3d23254f0239654e6881f54abd92154650f76545242f4542702f0540013e353f62f8653d623fc53c3cf9553ad4794537752ee531b379f52f95fba52eb1dde52d2aed652b0802b52af7a9852a7bfff52a78ba9528d0505525b7e92524acdd151ed28b551ddd0a051d14bca512d34725108cbec50f78b7d50f7098750ea5d1c50d2443f50b9b65350864f7a507014ea502357c74fff5df34fd314f64f9e05b54f952ed04ed368d04ecb8f0d4ec594b84ec560bc4ec402954eb46ba24ead99f54e77b52c4db113be4d8e22724d4f5aff4d3595bc4d084f5c4cbe7e934c75d1f84c718b944c64fbcb4c56d3a24c53159e4c436eb24c22897a4c11e795
  | 5, 16 => 0x5fa7ef0c5f93f03a5f814dfd5f7eb5a55f7c93645f3c13b65eaa5d655e90d5c55e5a93615e527d285ddf7efa5d6975b55cbaf2845c9fdf445c7d8cd05c78329a5c52c1615c4a4dc35c202cff5bcda83a5b7d97ef5b3884005b190cdb5af290a45a7258815a60a9515a48e05759f08d1e59e4a17b59dc0b2a59d9715459d7f46e59cb712459cadb4659c7165359c6ab8159b46f6a59b2057959a6392559961f685963b770593509f0592d08af590f2aea58fc91d558fbfa2458f3e1a458ebcfd1584043ea57f33be257d3089157d0e0b157b4e13a57a7be62577bae0456f2125556f0682556b63cb256a2517a55d58dbd55ab25b05582e52a5574cb15555c9c55
  | 5, 17 => 0x700bd0956f9aa75a6f589b016f37eba86f206f6f6e54b51a6da5de586d1f0df66d100d026c20324a6be9602a6be250976bca06146bae46a46b4fbd836b14ba456ad7dc1f6ac641be6a80535b6a600cf06a4c7c096a457df26a00a71569f6dfc86994a74a691d93a6685145df683feb3e682b787f680e11c367f1ecd067db16f567507c8f674e1eb46732ae256700e14266a7b460665ec23d661b8a2a65c088c965bf4a8e6579a4b36547a52965262662650612f764b54291649838a6648eba04648493c564638e396444db936357ba816345a93c6237a3c961e784ad61bb3679619d4c6b619a52b5619844ec6171db24615b7eea611caaa860cdc19660039506
  | 5, 18 => 0x86de55e785e5ae3085debe8a85c8f0c58533af70851a080a84f781f08486a953840623f783d23a8d82d16c5f82961c97827e2cde821ae20b81b9e100813c93c1812ed8da8028bb5a7fd3ebd07eeca55b7ea144d07e10aed87d9dbee37cae4a3e7c3bd5747c2348047bef72fb7bbb2c957b261fc37ad98a567ac7abc07a133d697947039e7922b9177868cf8577e96db6779ad3c67724b243770f404b75784f7d75496f8e7545ef8c7528a5d974b1337a74a0d34674438dd67410611773e3080b7398903b737ffc21737c7be27360da9372b29d49728f7ba7727fd6e3727ce723722c4ffa71660677711b2d9870e3e49670e2efe4707ae256703838537024f889
  | 5, 19 => 0xb5e53667b3d83162b37c12d8af413a1faef8a44dae747906ad920de9aad7c88aaa5f3920a8597594a7c9066ca69c2801a643d7b5a54c2da2a2f4637fa2bbb27ba20a3355a099b766a08dd5319f70ffdc9d1364159ca712a09c9ae4099bec11c59b8db89c9a2ed02e99db10c799d1c97699b9c19c99a785be999f698598bfc47f9818971c979fc3aa9778551e9731ca1c96f542d0962c4b199606177893fa4a1b92c124ef927728d4921de30f90ecdeaa901b960c8fc8826e8fa82fc58eeea6118e9f007c8e1ede9f8e1415b98de305ab8d7b6a4b8d1c93868cdb94188cb494f78c804e498c68411e8c1281fb8bc2a79f8aea435d89d34fbc89359d0989033c88
  | 5, 20 => 0xfa7f64cced179384ebbc4e99eb87dba7e6a461bae25ec97cd3f2b072ce83c66aca5b8501c21ba614c0ca87c4bf0ef385bb280b75bb05f3a3b7421724
  | 6, 0 => 0x2d8e04c02d788c802d09b5602cfd24702cd829c02cbca9902b2538d02b1074002a6d9fc0293c99f02718e3c0262058c025f62bf024de56302474830024369e5023f6dfc0237c8880222e834021de34b0217a563020e7d7302090bfa01fa8d3701ea17b901d6e30b01c9f94701c4357f01b7fe6a01a81ba4019610bb0191ddf501888f390178db86016fd7d0015cd17601597de40147bc1c012d3a34012a5d58012184a4011f72ac011ae777011855e10111d1a100ec2c0300d3bb5a00b3a2bc00963400008ecaef007da070007bdb34007807700071ac3c006953d200676979004e98cd004a1840003df6c5003b527b0038b0db001adc4800107951000936af
  | 6, 1 => 0x5d8c9d105b144ed059c3c550590749f058cdd95057b6f85056c96fb0569ccef056771560564d59c055b54b30548a98b053e93fb053e8aeb053cc01d0528413305192305050ac0b504f96c8c04d16b8404c0690404b621b404a55b2604a09edf04a05f47049bfeeb04926e200489053b047ce1530471f8a50462abf804588d100457fae604432e65043db1300433b870042e81e2042aec320423f3ce041b3b9003febff703f7cca603f19c0c03e554d903d1157003d0ce6503cbf76203c56dbb03bc7ac503bc58a403af18a003a9030b03a2129c037d70c1037898340374c03103723bfc035d5c760341977e033bf58403158c4c030eb56602e57d4f02e0976a
  | 6, 2 => 0x8959826088fc845088042fc0874b551085f9505085c8b6f084ef55808350af80832f377082723d30812a3c20806e66d07f8a05907e09f1607d1e36207ce71b307c84d7707c3b7be07a9807f07a66f82079fb6120798db9007936044078702e607861bbb07824f2e0781a741077d0e44075c207e0748f418073ffdb9073f91c7073ce922071ecb7b0713c4ad06f1fe5206eb049f06e73bfe06e68eaf06e5fc8506d34c0206c5566306b9d4f506b71a6f06ae990506a90b3406a82a21069588be068d3c6b068b19f4067b405506557be6064158910640cec5063dc579062579740606484c0603bb370602806006019b8f05fee8c405feb7c305ebddc605e6b3b2
  | 6, 3 => 0xb2553f40b1c77800b04d84d0af87e370aec1a760aeac1130ae2d6740ae06c630ab231550ab11b500aafa8b00aaf05c50a8860110a7a88130a74d2800a73c6a10a6d0acd0a686fc10a6236df0a58dadb0a4797ea0a2e12540a2da6ac0a27af4a0a201fb00a1cce6a0a174d780a1651b30a11e0e70a0b2c3109fa105309ebe9fa09d7476409c6434d09b63d9609b3f76a09ab601509a0e4110998a8730995747e09839d03097fbe4909629c300960336b095768780955458a09532497094447cb0940a31d093e045409335560092d4401092a9cba092628a00922068c0913c0c6090032f408fab75108f8acc008f2bbd508e8711508d6a72508bf44c208a75e7b
  | 6, 4 => 0xe4c8c480e4aac790e326c5b0e2354960e1d53040e1374470e1047770dfe5e500df839710dce92680dbe6d210d9d8d040d7d98ee0d6cee5a0d6b74d80d616daa0d5e437a0d4cb15a0d44d06a0d43d7bf0d3fff490d360fd90d313ae80d2152ad0d20fed30d20223f0d109dbc0d0654220cfbd4d60cebcd9c0cdec6690cdcf9dc0cacb11f0ca746830c9175400c90b84b0c9067a30c7430cc0c6b62bd0c69e5850c4f72bc0c34afa60c299d100c1e87430c151fb70c12341e0bff7ccf0bf89d7e0bdc20650bd538b60bb8cafb0baae74a0ba849b20ba7a07a0ba1c2650b8d06640b8440830b64da8c0b64cc430b57fa6e0b39f1a40b394ae20b31fc1c0b28fbff
  | 6, 5 => 0x119db2921184b632116dd53d1163ae0b115a63aa112e3f341126bc74111cf33510fc007d10f69c0910f3e56c10f2a4d610ef38a110ec9f8910eaeb6410def32610dde78f10cbec5210c5248b10c519c610bf3e64109f2783109939ab108c9a3410775be71073cc5a10714a53105bb912103d50591023470c101f483e101ca68710177432100599120fed07070fe91db40fe86bea0fd4fc530fcd726d0fc87e640fc668ef0fa931c90fa365d10f81aed00f79e5b80f75b7730f6eb8120f5dad830f4ac2840f4311500f2f3f390f1c003b0f05c7cb0f0329ba0f01d4930efea2ce0ef9045d0ee6f1a10ec8fad60ec055780ea421d10e9983b60e5bc0540e594481
  | 6, 6 => 0x1455a42b1445cbc71443e26a143c55da143a4745142d17ae1421d6021420ddd414166d8d140de9d414029b7313f5017313f3233713f22fcd13f1afaa13ec35b413e6d91913c9bf2e13c2450413b0db7513adfbe7139df6021397bd4f136a1c811369c707135980a71357fa241354f3be13421f8d1337e24b133796dc132b1955132a589c1329c396131da6be13076afe12f51d0c12f15ddf12c85ac112b70e5a12b30e4612a4a0cc12938d0e127716641272f3671272bc83126b19b91240e89a1203b91211fd81cb11f9400711f0d90c11ed00c811ec9a4a11ebd2c811de33a511dcd26611d3adf411d1c4b411c460a811b8148511af26df11ad056011a45c3f
  | 6, 7 => 0x17d7769417c85bd3178d61981789785a177b9c671776a96317692184173dfb1d1736de7e172b4224170112d616fdd77e16f7939716f75a9516ed4d2f16e3797416bca9b216b1945216a3873b169deff21696c58c168823b7167d5059167d1edb1668d2ea165de113163f2b181638250d1629cb5f1621ddb5161a710e16093037160868941601653815fdeb4615fbdc2f15d133a615d10f2015cf5c3d15c0742615bb9d4115abc8c215963e87159093361577dbfe156274e3155da96815447801153a0bfa153480f61515084315050e8e150126e914ff073914e4c21914e0836714ca004714c5abfb14c5641c14c5555f14c4cbe8148c2781147137121461d315
  | 6, 8 => 0x1b380e2e1b373cc71b30f55e1b1a09851af92d5e1acc57421ac1b2ab1ab59f621a81a61b1a7f7f571a7c903a1a5bb91f1a55fc7f1a3768481a3752ae1a36ee531a3620d81a2022141a006aa619f1b4f319d0384919cbb0f019c475c619b743c519923a6b1980ac9e197ca3d01971053819564c08194062cb193fe778193ecf49193041ca192517a5192321c7191605ad1905976e18fce87818d152d518cd059518cceeb218bca6f618ba73e118a6b26f18a021871881b13e187d8e881862ae30185dcc8d184d3deb184a24321840d88418333b00183338171832db6c1820d18e181b7f251816d672180984f4180821af17f6232817f5a70f17e7fac017d94898
  | 6, 9 => 0x1e2900b21e08997b1dfbd5f91df91e641de80ae71dcebeb11dc665231dab4e731daae27a1da405961da255751da071211d9951bd1d90fd711d8a21711d6b4ddb1d63d0ae1d553c6c1d46a7661d4368ca1d2db9b51d1a1d951d0dc9be1d05ad711d0346f11cfa42bf1ce30ae91cdb384d1cdabcc71cd804591cd116751cc7b7b01cc232561cbf62101ca5bfb31ca3c40d1c91ad8b1c7e4d2a1c7a41361c5ec6f41c54d4901c4fb8631c4e62c41c48f6171c38c0a61c26dda71c0dc6fe1c060caf1c04d9121bcb96d81bbe0cc11bbc96611b93f1b81b7ebdf81b7e5d101b724bcd1b71081b1b6d5a321b606b3e1b57f81e1b52170a1b4b50251b431d8d1b40a478
  | 6, 10 => 0x215281f6213ea448213b7815213b6ca721362a8c213412ce2125ccc4211a4ca22104928d2103445120e3092620daf00220d1384220aaee9820aa843220a06b46209a2bd620915e50206bbc04206a27e7206806582067612d205db4d82041ebac2041914c203c9e09202e11ad202da747202d03f5202cdd2120289d1c200f84fb1ffb06331fe736af1fe0eee51fcfb7541fbdc7f11fa32ad91f7cc5771f6c0aa71f6b8b4b1f61026e1f41a81d1f2b0f4a1f21b2fa1f18caed1ef3306d1eef2d801eeafeff1ec584b51ec33dc51ec09a0a1ea914411ea09ad61e9ef6981e9a0ec21e97fca31e8665201e82088c1e74e3ef1e6cb1781e67e77a1e520e771e42af9c
  | 6, 11 => 0x251db44e2513064a250ff5d6250d6f1124fbd22224f49e1924f3b69324e6f5ec24ce4f8e24af67c2249fb806248285ab2480236c2479753024679d46245d13f9245782c72454f65d2425cb862420e3c4241b4ba5240f038323ef506623e2398023d590e323b38d5e238f4138238eeb59238d095d237a6fcf2364da53235e13892353a1a8232a75202329d176231a7b1222f9825b22f2339122ba158322b97a2522ae877e229d9b842275c641225ca301225569c3224e5db02245a694223e35cd2230558422270bd92216525022088f4721fe5a1821fd117421efeeea21e5858021c7ee6b21b9c4a221af15a0219b283c21956393219299482176e06c21762a9e
  | 6, 12 => 0x293de43a292bc126291522b12912d93028f927cc28f1266a28dd84f728cdd94828cb32e128a7fb8628a1c44f289c04ff289501e828887f30287eec972879b8cb285dba30285a2431282c71a2280b6f1f27e7cf2127bbb9a227aca44a277c068c273c33e32712541a2711eb02270e250b270942d52706f12926f033cb26e7c35426e0543926d3313526d253cf26c965e326c83a9726b659cd26a1bf162692f8d02684670e267b18912679da8a2656de8a264a243d26379cac26363d9e26343b802625e8b52609b48b25fbc9c425f6150c25d884dd25cb7fbe25a538b325a3533c25a1d9f4259f34dd2594e014257641122566b478255af5b8255299072528d48d
  | 6, 13 => 0x2e2ae5ad2e2434c52e21d84a2dd470b52dd2957d2dd1736c2dca9cca2db699da2db14dd02d90c8d62d8140962d7d58c42d5bb51a2d560f052d5547bb2d2d8b582d2959262d122ddb2d04e6d22cf1eb602cd99ed22cd192c12cab1bf62ca773eb2c9934842c953d632c93293a2c65da752c4bc9d92c49db372c3d13872c3c48512bee98af2bdf7f332bd59f162b7a63082b6e395d2b605c502b4a131c2b41b6592b24c0dc2af997662af945462ae109462ad1a0962ab8c4a72a7c44cd2a664f7c2a57ef202a4580022a19cb902a03b28129ec4cdc29df127e29cecc2a29cce0cc29c7bc4d29baaf4329aa5f4f29aa1e1529a545d1297408f32946638e294432d3
  | 6, 14 => 0x3277f9e032732994325ef5a6325c3bce3253b76c32515b113247ad07323cd6a432304ebd322d7fb73229041131e9a92231e0fd7731d8a19631d2032131bf8f4231a16835319ccd9a319405db318d58a1318148893174959e3168250b313bbe7f31293fe4311e6bdc311df60f3108bcc730d5a33030cdc37f30c6e2db30af37f2308478623080c2c53064e1d23055452830516dd630485424301f07c9301a2ba630132ac9300c594e2fdf2dd72fc101612fc015492fb8c0442fb890ef2f6d4c932f6be4c82f6a41612f5aab222f408fda2f3a9f232f31c9182f2dcf812f0f5bf22efd25862ee330ae2eda7a202ecc10fa2ec7c99c2e8e6f072e4d171c2e4967de
  | 6, 15 => 0x363f8df53632df4536317515362de016361bc3b13614350d36097109360310ea36007f5435fece8135fc150435f5ad0d35e1f2f835dea11035db544135cca22e35bd691935aa102235a98adb35a73500359829e8358ee5453576a9f53563bc05351dde17351b6a3f351825d5351505723503fbd934caf0df34c1c93234c0f57534b1547834a17b043463c0e1345643e23452b7f93450ba873445ff0c34429ca734249fa53420f30e34183af533fc5d3b33d6886033d4ec0533d3b85e33b4e31f335eb5c8335dbc65335ae6873357c1cb335340a533524149333d9b3b330fb5e6330d44c332ed7d7032c5623032b312ee32a9b840329cf60832904aee32874992
  | 6, 16 => 0x3bca0c0c3ba3aa0c3b712c743b67fdf73b6764f93b3d6f9e3b2463713afade1f3ae9281d3ae34b763a83fa303a77c2b23a6975543a61bcda3a4dc5833a07c51639f8103139f4944039ed8e9f39d5e8d439c3612f39a46b9a39851618394cd2ec393d7236393d2ebc393ad237391f226538ff54f938f1ecfc38e6e4c838cd2c20389a6d6238974e1d388b0709387b8148386d3b863862bed1384f5f733836e483382f1d4b381acb4d38099ae737f884ef37f6ded937e53e9d37e4ec5937e2d5da37af605337a74db53783852f3782256e3776a8ad37662cad375adbd8374f386437442a8636fc613d36ed3c0436a8bfaa36a3eab536a027dd367b11f036469a04
  | 6, 17 => 0x41b79cbc412c487241282229411e0fb6410d799140c8f77e4093e64c40890461407b29834057f04e402e738e4004286f3ffdfde43fd902993fd50f883fcc452b3f9166b23f8c997c3f55d8453f51ba6d3f48acca3f313fb33f1d58b33f1918803f18041d3f071f7b3efa5fd73efa24ef3ef393e93ef355a43ef274ad3ea6a75f3e9571c93e58725e3e370bba3e0edd903e05354e3dd4be0c3dd44c673dcc57703dbcc9873dae6c8e3d9bea6a3d96864a3d71b6183d54ac4e3d3504d03d1703c23d13882c3d019bde3cf3da113ccd2abc3cbf1fc43caff6f93c7e44883c712c6c3c55588a3c5034cf3c46c4ff3c3eeca13c0c9f1a3bf550d53be9302f3bdf8beb
  | 6, 18 => 0x472b494a4723638a472343ec472107aa470a8ebc46c3558c46b6053f46b5bcc946b342a146b1484b46afb3ed46af906c46af20d946a2166446a03df846958a39466635aa464f1708464af8244631cb1145ec134145ddc874459e98514556c9f1453b2ed04533a473452a1da9451bd966451a725a450fea54450736ea449a77bc446540d844648bd344569d414434a0d544302fce442225514405b71743e4add243e20e3e43cdf89a439c6dee4392a11c438a80cc4381ad29437653ac436f132d436056cb435cbe3043416bbf4323d9e642dee5fc42994357428c08b2428a5885424df875424cede242255bd7420e36aa420be3e841f0f83d41c3e4da41c34130
  | 6, 19 => 0x4da4d9bc4d54ec694d1a66ae4d0f3e084cd97fe64cce998d4cce095a4cbdb6ba4cbb68fe4cae252c4ca26e884c9f5c684c9d306f4c56d3a24c483e984c1af0a54c18caca4c0300484bfe0dd24bfd2c274bb77b954bb625cd4bb2ae384b7d8d534b5e88414b1a2deb4b0ea5514ae0d73b4ac315a24a8b18774a7d39444a5af5524a4b71f94a3e388b4a1a4ea64a0fdeaf4a047be849ec919049d0b01f49b7165b49935b824986881f495cffff491d6c3149056cda48e7bc3d48c1173f48b2996f48a12477489d4b03488ac00e486f05e84865099348473962484529ed481b7493481a387647f6882c47c3324b47a20aac4799875d4794e74c477fc7c8474ccc02
  | 6, 20 => 0x53e2e35b53d968f153d1f0c0538f04ce53596b2c53536a5553316b025300f40a52f86aaa52f85bc552ed9a3c52dfb6a952d0803752ba82c95269e6925261f96052183374520f29c951cdf57e51a9bfd151704f295131a4b5512d3472511660bb50f966f250dc5fee50cef44c50b73b9c50b5376550a8839250a7da2650a01d85509e78ff5083d065507f457d50726a8a5057674a503aa185502f600e502357c750209d26500c0dac500b1cc94fe85f7f4fce9aa34faad24c4f92974d4f71272b4f4f8c064f2bd1db4f2b29fd4f0ed8494efe92894eeb82634ee387f14eda3f424ed368d04ec142ef4ebf29674eb6caf94e3614a24ded04b24dc743b14dc37f51
  | 6, 21 => 0x5b4b082f5b30861a5b1a33365af61f3d5ac616a65a89e6ce5a5a5c8c5a2720ef59f8f60059e821ef59d9715459c71653598e3cfb5981c2cd597d7503596ccb1f5966b2bd593509f0590f2aea5905ce9e586d956458635b465832e4615802949f57cae52c57b4523b57572d9357232eb0570da82456fe794b56f2125556e3d98356d9977756b365a7569a454b567f9aa3566050d0564f1db655fae22e55e783b155be4e14558a3a9c55899ceb5566dec9555dc9d9555cc88e554884685545e53654f84dfa54e6ce5054df5ed854c3667f54ba89b55487c4745475f9d854532151544fd38a5432e45154023870540013e3540005ee53f20ea953eeda7a53ed5016
  | 6, 22 => 0x61d2246361b1cf33619d4c6b619a35b8619345696192b1c96179fa3d616a99b661380ea66128d5d56111996d60d9717360a5376b607d179b60600763605e38376056e3f760284eab600395065fdde5825fd782345fc0d0e05faf1f275fa4d18d5f9602485f8d22ca5f8a530b5efce0325ef885fc5ef530fd5ed78a7d5e96b9a65e952bc45e8b05095e7815435e5bb63d5e532ab35e529bed5e2a11df5e04ba105df388c55ddfb19b5dc71ed55dc506925da15cd35d8420dc5d61abe25d48e4705cc84f625cc234255cc1736d5cb90e5d5cac91505c9da2b55c8d0e975c78329a5c4f69445c4d35335c202cff5c040c4c5b7d97ef5b74e26a5b6958865b64a82e
  | 6, 23 => 0x6b5531166b4d78466b3ba4a56b1ce2266ae973e76ad7aa5f6a5a7c2a6a34d2bb6a3374da69d5e540697a2bb2693ae16c6918ceec6907cdfa68f08e28688bc58d687fda5f68516424682c30006824771b6817ccf667ff314a67b47d856795c36f6756b7c9671daafa671a2bac6700e142669924036671577e666ecf8f661b8a2a65ee40fb65e9cd0065df4d4a65a8f8906579a4b3655f7a36652009f96517c48364c92790648d1d77648181f7647ff1866442820e643ff07864329eb8642315bd63f64e2963d9a72d63d401f363c97d7a63c5bfaa639ce39d6358c69863587edc631e9559630a62036306b05862eab656629c46016273ff0b6236fc2e621d2f39
  | 6, 24 => 0x74b8c10d74b1337a746d7d0d7433c45e7422754a7413bb9573f8e97273ccba9b73a16b5173a11b947382503873616ab473168b8b72f7793372b2df70727f2b43726ac709721d2e43717fb457715f23ee715bb48a711b2d9870fd26db70fb379870f7d95670ef723570eb3f0870e8ea3c70db1d7270d261e770d0c237705f7c96702c48307024f8896ffdcf9a6fb3b9716f9f2cb86f46b2f76f3798bb6f01dc8e6ef933a76ee0955f6ec5bb4b6eabeefb6e1198856e04ef726df188636dee49966d95cfd56d72b7346d428a936d32c6c86d0324eb6cf541806ceea87a6cae2a666cae15426c8d61c66c4b34176bd4cf7a6bd1c5d26bcd1aa46b8f554d6b82d937
  | 6, 25 => 0x80ba8a2c809ade708052f8187fa83b3c7fa1a8527f9f03df7f672d517f2f58c57ef808227eeca55b7ee825c97edb8c757e7b974b7e47268c7e4112597e3194c57dace8da7d8eb9e17d2872517d1d12c37d0e16a57ce82a657cd065c07c756b377c58a3487c08f7857bae90157b41d1e97b3ab8577b301ae77ac39d767a88228c79f4e61779eb8c4179e4444979ce324479c7a97e79a72ff279a067397908ec3c78f7d74f78ed3c8d78be0fda78884714785d7b60784d49c378354e7277e2aec777bceeae779119df770f404b770cf3e87702d108769fc62f769b47b37696e9ba765f6a10762edb8a75ffcdcf758cd245756f6a3074fca95974ed73e774dfaf1c
  | 6, 26 => 0x94dab59593d6e75c92c124ef92ab55f5921de30f9213fa7791d83ee791b5b36791433e1a90a8cc218fd2b68d8fc3c5fc8fc2c8b68fa82fc58f1e5ece8f152e238ee77b7a8e9f007c8e5a219a8e51df958e08b47c8d904e8d8d76a8a48d2778258cdb87548cb494f78cadfdb48ca156d98c681e338c4c6ea58c2534c98bb38c428b693d7a8b532d3d8adc114289b9d7608983105188b3c288888f3c5487f830a187aafef687477ebf8739bbdb86f52a9786df341186b777fb86ab55e18651cb2185e967cc85debe8a8538e35c85383cf884c3ed4e84b5204d845d7b01841182bb840623f783130d1982e4319982e2e3648270adf7824fa80d821ae20b820513a1
  | 6, 27 => 0xae3db647ad64ff98ad127672acb2f730ac75cb2aac47d0e2ac304800ac22cbb0abf99382a9b43162a9894334a83d1d8da8114f3aa791fc22a78dd8baa789732aa746fbeda6c58ceba6101f55a5a2dbf3a4e84059a44ffe4ba40501a0a3e42892a39dcbc8a2d2324ea20a3355a09ea5c9a09c8b48a00e3c86a00a4d6d9fd090cb9fbde2b39fb00df99fad09e29f69ee319d5440989d1364159cc268a79cbebcb49ba94d339a2cce33999f6985992c98679909a3149906f4db9877954e9847c89e983a1e8d977a5290975260ef974709009742ddb6970f042796f395ff96e27b6696d9044c96adde2f9697af1d9625d0d795cc60c995aefb8d959628ed952799cd
  | 6, 28 => 0xfd5468cafc9bf21afa7f64ccf69a1271f557874cf45f96b6f3e12d75ee915297ebbc4e99e97965b8e88a7360e79a1558e71acdf8e6a461bae08493a4e06dde6cdc119470d2ab2c90d1a6e627cdffed15cd7d5252ccdea62ecccdf350cc15d1a7cb0c1925c91ec3b4c8e8df77c835e892c6a6c971c3529761c2deba9cc1aab52ac18f1a45c155a865c14002aac0f980b5be69547cbd00c1eebbc0abd9babba4a4b778cedab54022eab479a8dbb27c6fdbb206d80cb115a700ae8b0da6
  | 7, 0 => 0x8e53e8408c980a908b049630874b5510845f656080a442407d1e36207acd06906f3fbc406e5fc8506df3f5106c897c706ae990506a287d8068d3c6b06557be605ebddc605eaf41105b242c805b144ed059ca1ac0581f44f0577f275050a748b04f7ec3204d16b8404b91ad604b7902d0457fae6042e81e204279c42041b942503941f9b036b37fe0363083d030eb566030dc27902d788c8027c45a6026f44a602583c560254e73b0240ad41023f6dfc023a75830222e834021b2d0602005bb101f2248c01de086901a81ba40191ddf501597de4014be587012d3a34011ae777011855e100f31ec200ef749300d2b93700a8e69f009634000063d3b7004ab83e
  | 7, 1 => 0x128c20a41272f367126b19b91251403c1250e5381203b91211f71c1011b8148511ae964a11a8c3d611a1425e11945993113fc45810c5fe0c108c9a341065818a101cd13b0fbe956f0f5e38d60f2787c00f24fac60ee6f1a10ec055780e9983b60e7c09940e76c6630e4e8e670e4c8c480e1098e80d9876700d313ae80d20223f0d04813c0d02ce600cd49d460c4f72bc0c48cffe0c37f27b0c1918090c0694670bff7ccf0bfc90440bfbbf870ba1c2650b5d14ee0b52f3f40b49b94f0b39a6c80b343c490b19b0ad0a8b3fe70a8860110a4b1eaa0a37347b0a0c4c650a0b2c3109c4cc8a09ae1ed809ab9c2a09a22855098ccffb0980968f0957b91f09329cd9
  | 7, 2 => 0x1ca5bfb31c730cdd1c5f81681c30ef231bcb96d81bc297e81bc23dd11bac13421ba54e471b964af61b7e5d101b724bcd1b6f0d841b6bd3831b606b3e1b45c24d1b30f55e1b1a09851b1049b31b05ee9c1af92d5e1a8f3c1d1a8806411a54e7f719dcd5cd19dc016a19d9603119d74626198e6644198bf6b8198225541955c3cf1953a073191ebc7d191605ad1907d0c118be85fa18a4603b18a404d5181c598d1816ddec17be215117a6970d177e64eb171af63116f7939716f3739516b194521685f19d164698f916361dbd15cf5c3d14739bc7146c219713f3233713f1afaa13b256b3135536171344aa8f1317c18013031c2712c85ac112c4c9cd12b043f8
  | 7, 3 => 0x2a507e2c2a4508e32a3d06b729e3c31b29e32909294432d32906fa0628f927cc28dd84f7289501e828726d11285dba3028408805282c71a228137e282808977c27d300562735ff88270e250b26f033cb26d517a3262c5473259394a62578af0b2575aa6124c0ca312491452b2444beba23b38d5e232464bd23054db922d959b622bdb6e122bb7797228c51202282ceae2273157922668792225569c321845bb8215c823d20ee56f5209b6921205c85d22002bdb31fd9b0d91fcfb7541fbd0bf61f9d23c01f7ac3b11f5bc5591f23f05e1f1208921ed79f621e9702731e797a8f1e74f0191e2ee1541dc665231dafd3ab1d4368ca1d2db9b51d29fa1d1cdb384d
  | 7, 4 => 0x385df45337f5320537e611f937dbbeb337b8376437a9881a37a284a737a0fb953783852f37662cad3758d4b2372c968836d7c58636a3eab5369791f4363f8df5362a935f3622e7a035f5ad0d35d0b6ad351dde17351b6a3f34c1c155349bda93347b7b523460370d3452b7f934429ca733f7555b3361979a32fe698632c08eb932788f0f3253b76c324d6d7031465e97311df60f310106b7309f230b3049479b300f8bfd2fdf2dd72fd5def72f3c25f42ee330ae2ec7c99c2ea242362ea1db4d2e751b632dbe97e32d7215f72ce6eeb42cd192c12cb7890a2cab1bf62c9e1ae42c19cce82be35d2b2bb288f52b47096a2ae32e4b2ab7197a2a9001312a74a757
  | 7, 5 => 0x4a3e388b4a0fdeaf4a047be849fe26c649eb2f8249bd0cc5492119db48de789d48d502ef484529ed47d2151a474ccc02473969af461e3db145ec13414566551144dadea3449a77bc445c4da5444df8be4425bd55438a80cc4323d9e642c3c5c9428c08b2426536614245147d41aa63754135445040fff74c40c4450440b11e5940ad304c4093e64c3f96b8b53f7b37ef3f64ff5d3f1d58b33ef274ad3ee0d9663ebf3e4d3e9571c93e7613453e370bba3d3504d03cfbe67e3cf376ba3bcc9f1e3b423f843add61ab3a918ff63a3b30ab3a1008e039d5e8d4398b5f58396474b33957e3e23957a073394c3e5338ff54f938ce382738cab10b3875a3b3386d3b86
  | 7, 6 => 0x5c1f3f765beeaadc5b92011d5b7d97ef5b6958865af30db35ae75dfb5ad828185aa7b71e5a98e9d85a8956395936803f5887440a57c6009f57b4523b576452c657032b90562ad2e255fae22e55cce6455548846854e8688754c4031954a2f97c54986ee9547599c65471023c545cc7ab5445cd165411f9ac53f332ad53f20ea953c7c31752ee49a152ed9a3c52d57d3952c5375852adaa6d52420cad5222edba51cdf57e51948425517e630d5158b23d5157feee514ca4fe5095bcf6507f457d503aa1854fe77f4e4f955a6e4f92974d4f6a5e204f2b4f914e3e505a4df659564d92628e4d1268ff4d05ae984c3301874c1af0a54c0b85b14b38ddb84a442e86
  | 7, 7 => 0x753438a374b8c10d74259d7673bdee3a72cefbe2720ac07371a6247c717fb45770fd26db70e8ea3c70d0c2376f1da9db6f039e0e6e8830116d95cfd56d2c8a856cf9cf256cdd5b786c8c0f956bf70b016bc747326b4a99c96ac91c266a53aab4699c9f80696304106921e85668f1ddb367b47d8567a114046777e857675f43a7663a46996585a91664b694ab6486d331647ff186647a0aaf6414de7663fe379b63f5e4b86397e0d9626d63e561cbeb0c61b1cf336115c0a660e49bc860dbab61605924da601c59335ff0527e5f08667c5edee2eb5ed2ddca5e8c49fd5e12fecd5da487935d8420dc5d6a9c2c5d0f82ff5c9caa415c6c7b735c6b0eed5c638d53
  | 7, 8 => 0x9cbebcb49b1ccc9c9a7ed7b398d3d2979877954e9847c89e9832e49a980141c2975260ef95f00226952799cd94a6244093ebc30a92c124ef9227fa8892114550900a21eb8fc2c8b68f573cb78ee77b7a8ed6559f8de6bd178d9924fb8d76a8a48c5a046b8c4c6ea58adabc7d8aa314c58a726eb289a2faa08926cf1f88eff8e288af16e386ed26d786b777fb86a4fdcb8651cb21862ca08f8628f9d585f53603845d7b0183c7b539836b648882e2e3647fa1a8527f3fb22b7e5dc0747e4112597dec7d7d7deb2cac7d5d98cd7c08f7857ba3a1747ba3277e7a2e98037a05fdc179baf2ba797884a678be0fda7775f31d7737f90c770f404b762684887588d735
  | 7, 9 => 0xfe26ca86fd5468cafa7f64ccf557874cec4e69b6e97965b8e88a7360e6a461bae35997a2e26aa54ae08493a4e06dde6cda64c58ed52bc6d5cede2b26ccdea62ecc15d1a7c756d1d9c46cb09cc1aab52ac18f1a45bce82da9bb6f4c2fba90780ab9a2df3db8aa910cb4af5e44b30d9a21b2739a21b1031a81b08b50f1b03a0396ae45ebcaad64ff98acd56c2aa9c5da39a8761d29a80aeda0a7453182a7059d89a672cfc6a39dcbc8a373a9c7a2b65bf5a09ea5c99d544098
  | 8, 0 => 0xe97965b8e6a461bae08493a4ad64ff98a09ea5c99847c89e70e8ea3c61b1cf335d8420dc57b4523b386d3b8637662cad35f5ad0d28dd84f7270e250b1dc665231ca5bfb30ba1c2650874b55100963400
  | 9, 0 => 0xe6a461ba
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300000000000030303030000000000f0fffff000000000f0f0f0f000000000f000f0000000000030303030000000000ffffff0000000000ff00ff0000000000f000f00000000000550055000000000000ffff000000000000ff00000000000000cccc000000000000555500000000000000ff0000000000000000
  | 0, 1 => 0xff00000000000000cc000000cc0000000f0000000f00000000ffffffff00000000ffffcccc00000000ffffaaaa00000000ffff000000000000ff00ff0000000000fcfcfcfc00000000cccccccc00000000aaaaaaaa00000000aaaa000000000000aa00aa0000000000888888880000000055ff55ff0000000033333333
  | 0, 2 => 0xf0f00000f0f00000cccccccccccc0000cccc0000cccc0000aaaa0000aaaa0000aaaa000000000000888800008888000077770000777700005555ffffffff00005500000055000000505000005050000033333333333300003333000033330000111100001111000000ffffffffff000000ff00ff00ff000000ff000000ff
  | 0, 3 => 0xf000fffffffff000f000f000f000f000f000f00000000000a000a000a000a0000ffffffffffff0000ffffffff00000000ffff00ffffff0000ffff0000ffff0000ffff0000ff000000ffff0000f0f00000ffff000000000000fff00000fff00000ffcc0000ffcc0000ff00ff00ff000000ff000000ff000000ff0000000000
  | 0, 4 => 0xaaaaaa00aaaaaa00aa00aaaaaaaaaa00aa00aa00aa00aa00aa00aa0000000000aa000000aa00000088008800880088005f005f005f005f0055ffff0055ffff005500550055005500550000005500000033ffff0033ffff0033333300333333003300ff003300ff003300330033003300220022002200220011001100110011
  | 0, 5 => 0xffffff0000000000ff0fff00ff0fff00ff00ffffffffff00ff00ff00ffffff00ff00ff00ff00ff00ff00ff00ff000000ff00ff00f000f000ff00ff0000000000ff00cc00ff00cc00ff0000ffff000000ff000000ff000000ff00000000000000f000f0f0f0f0f000f000f000f000f000ee00ee00ee00ee00c000c000c000c0
  | 0, 6 => 0xa0a00000a0a0000050f050f050f050f05055555050555550505050555555555050505050f0f0f0f0505050505050505040404040404040403ff03ff03ff03ff0333033303330333030f030f030f030f0303030300000000030003000300030002aa02aa02aa02aa010101010101010100ffffffffffffff00ffffff00ffffff
  | 0, 7 => 0xf0fffff000000000f0f5f5f0f0f5f5f0f0f0f0fffffffff0f0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0a0f0a0f0a0f0a0f000f000f000f000f000f00000000000ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0aaaaaaa0aaaaaaa0aaa0aaa0aaa0aaa0a0a0a0a0a0a0a0a
  | 0, 8 => 0x3030303030303030300030003000300022aa22aaaaaaaaaa22aa22aa22aa22aa22222222222222221f1f1f1f1f1f1f1f1515151515151515113311331133113311111111ffffffff111111111111111111110000111100000fff0fff0fff0fff0fff0fff000000000fff0000ffff00000fff00000fff00000f5f0f5f0f5f0f5f
  | 0, 9 => 0x3f003f003f003f003c3c3c3c3c3c3c3c33ff33ff33ff33ff33773377337733773333ffffffffffff3333ffff3333ffff333333ff333333ff333333333333ffff33333333333333333333333333003300333333330000000033330000333300003322332233223322323232323232323230f030f0f0f0f0f030f030f030f030f0
  | 0, 10 => 0x5555555500000000555555005555550055555050555550505555000055550000555500000000000055005500ff00ff005500550055005500545454545454545450f050f050f050f050505050505050504ccc4ccc4ccc4ccc4c4c4c4c4c4c4c4c44cc44cc44cc44cc444444444444444444444444000000004040404040404040
  | 0, 11 => 0x77777777ffffffff77777777777777775f5f5f5f5f5f5f5f5f5f00005f5f000055ffffff55ffffff55ffffff0000000055ff55ffffffffff55ff55ff55ff55ff5555ffff5555ffff555555ff555555ff55555555777777775555555555ff55ff555555555555ffff555555555555555555555555555500005555555550505050
  | 0, 12 => 0x888888888080808088888888000000008888880088888800888880808888808088880000ffff0000888800008888000088880000000000008880888088808880880088008800880080808080808080808080808000000000808000008080000080008000800080007f7f7f7f7f7f7f7f77ff77ff77ff77ff7777ffff7777ffff
  | 0, 13 => 0xa0a0a0a000000000a0a0a000a0a0a000a0a00000ffff0000a0a00000a0a00000a0a0000000000000a080a080a080a080a000a000a000a00090909090909090908e8e8e8e8e8e8e8e8ccc8ccc8ccc8ccc8c8c8c8c8c8c8c8c8a8a8a8a8a8a8a8a8888aaaa8888aaaa88888888ffffffff88888888888888888888888888008800
  | 0, 14 => 0xaa00aa00aa00aa00aa00aa00aa000000aa00aa0000000000aa00a000aa00a000aa000000aa000000a8a8a8a8a8a8a8a8a8a8a8a800000000a5a5a5a5a5a5a5a5a2a2aaaaa2a2aaaaa2a2a2a2a2a2a2a2a0a0ffffa0a0ffffa0a0ffff00000000a0a0a0a0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a000a000
  | 0, 15 => 0xaaaa000000000000aaa8aaa8aaa8aaa8aaa2aaa2aaa2aaa2aaa0aaa0aaa0aaa0aaa0aaa0aa00aa00aaa0aaa000000000aaa0aa00aaa0aa00aaa00000aaa00000aa88aa88aa88aa88aa88aa88aa00aa00aa88aa88aa000000aa88aa00aa88aa00aa888888aa888888aa880000aa880000aa80aa80aa80aa80aa80aa80aa00aa00
  | 1, 0 => 0xaaaaa2a2aaaaa2a2aaaaa0a0aaaaa0a0aaaaa0a000000000aaaa8888aaaa8888aaaa888888888888aaaa8080aaaa8080aaaa2222aaaa2222aaaa0aaaaaaa0aaaaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0aaaaa0202aaaa0202aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aa000000aaaa0000a0a00000aaaa000088880000
  | 1, 1 => 0xaaaaaaaa88880000aaaaaaaa22222222aaaaaaaa22002200aaaaaaaa0a0aaaaaaaaaaaaa0a0a0a0aaaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaaa0aaa0aaa0aaaaaa88aaaaaa88aaaaaa00aaaaaa00aaaaaa00aaaaa000aaaaaa00aaaa0000aaaaaa00aaa0aa00aaaaaa00aa00aa00aaaaaa00aa000000aaaaaa0000000000
  | 1, 2 => 0xaaaaaaaaaaaaaaffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaaa000aaaaaaaaaaaa8888aaaaaaaaaaaa8800aaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa88aa88aaaaaaaaaa888888aaaaaaaaaa00aaaaaaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa0a0a0a0aaaaaaaa8a8a8a8aaaaaaaaa88888888
  | 1, 3 => 0xaaaaffff0000ffffaaaaffff00000000aaaafafafafafafaaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaababaaaaababaaaaaaaffaaaaaaffaaaaaafaaaaaaafaaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaeaeaeaeaaaaaaaaaaaffffffaaaaaaaaaaffaaffaaaaaaaaaaaaffffaaaaaaaaaaaafafaaaaaaaaaaaaaafaf
  | 1, 4 => 0xafafafafafafafafafaaafaaafaaafaaaf00af00af00af00aeaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaaaeaaaeaaaeaaaaffffffaaffffffaaffaaffaaffaaffaaffaaff00ff00ffaabfaabfaabfaabfaabbaaffaabbaaffaabbaabbaabbaabbaaafaaafaaafaaafaaafaaaaaaafaaaaaaaaffffaaaaffffaaaaffffaaaaaaaa
  | 1, 5 => 0xc0c08080c0c08080c0c00000c0c00000c0c0000000000000c080c080c080c080c000c000c000c000c000c00000000000c0000000c0000000bebebebebebebebebbbbbbbbbbbbbbbbbbbbbbbb33333333babababababababababaaaaababaaaaabab0bab0bab0bab0b3b3b3b3b3b3b3b3b0b0b0b0b0b0b0b0b0b0b0b030303030
  | 1, 6 => 0xc8c88888c8c88888c888c888c888c888c4c4c4c4c4c4c4c4c4c44444c4c44444c4c0c4c0c4c0c4c0c0ffc0ffc0ffc0ffc0ccc0ccc0ccc0ccc0c0f0f0c0c0f0f0c0c0ccccc0c0ccccc0c0c0c0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000c0c0c000c0c0c000
  | 1, 7 => 0xcc88cc88cc00cc00cc88cc8888888888cc88cc00cc880000cc88cc00cc00cc00cc880000cc880000cc80cc80cc80cc80cc00cccccc00cccccc00cc00ff00ff00cc00cc00cc00cc00cc00cc00cc000000cc00cc0000000000cc008800cc008800cc000000cc000000cc00000000000000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0
  | 1, 8 => 0xcccc000000000000ccc8ccc8ccc8ccc8ccc8ccc8cc00cc00ccc4ccc4ccc4ccc4ccc0ccc0ccccccccccc0ccc0ccc0ccc0ccc0ccc0ccc0c0c0ccc0ccc0cc80cc80ccc0ccc0cc00cc00ccc0ccc000000000ccc0cc00ccc0cc00ccc0cc00cc000000ccc00000ccc00000cc88cc88cccccccccc88cc88cc88cc88cc88cc88cc888888
  | 1, 9 => 0xcccccc00cccc0000cccccc00cc00cc00cccccc00cc000000cccccc0000000000ccccc0c0ccccc0c0ccccc000ccccc000cccc8888cccc8888cccc4444cccc4444cccc4444cccc0000cccc444444444444cccc0c0ccccc0c0ccccc0c0ccccc0000cccc0c0c0c0c0c0ccccc0000ffff0000cccc0000cccc0000cccc0000cc000000
  | 1, 10 => 0xcccccccc88888888cccccccc88008800cccccccc44444444cccccccc0ccc0ccccccccccc0c0c0c0ccccccccc00000000ccccccc0ccccccc0ccccccc0cccccc00ccccccc0ccccc0c0cccccc88cccccc88cccccc88cc88cc88cccccc88cc00cc00cccccc80cccccc80cccccc0ccccccc0ccccccc00cccccccccccccc00cccccc00
  | 1, 11 => 0xcccccccccccc8080cccccccccccc4444cccccccccccc00cccccccccccccc0000ccccccccccc8ccc8ccccccccccc0ccc0cccccccccc88cc88cccccccccc88cc00cccccccccc888888cccccccccc880000cccccccccc00cc00cccccccccc00c000cccccccccc008800cccccccccc000000ccccccccc8c8c8c8ccccccccc0c0c0c0
  | 1, 12 => 0xccccccccffccffccccccccccfefefefeccccccccfcfccccccccccccceeeeeeeecccccccceecceeccccccccccccffccffccccccccccffcccccccccccccccfcccfccccccccccccffffccccccccccccffccccccccccccccccccccccccccccccccc0cccccccccccccc00ccccccccccccc8c8ccccccccccccc0c0cccccccccccc8888
  | 1, 13 => 0xccddccccccddcccccccfcccfcccfcccfcccdcccdcccdcccdccccffffccccffffccccffff0000ffffccccffff00000000ccccffcc00000000ccccfcfcccccfcfcccccfcfccccccccccccceeeecccceeeeccccececccccececccccccffccffccffccccccffccccffffccccccffccccccffccccccffccccccccccccccccffffffff
  | 1, 14 => 0xdddddddd00000000ddddccccddddccccdd00dd00dd00dd00dcdcdcdcdcdcdcdcd5d5d5d5d5d5d5d5d0d0d0d0d0d0d0d0cfcfcfcfcfcfcfcfcfcf0000cfcf0000cececececececececcffffff00000000ccffccffffffffffccffccffccffccffccffccff00000000ccfcccfcccfcccfcccddccddccddccddccddccddcccccccc
  | 1, 15 => 0xecececec00000000ececccccececcccceccceccceccceccceccccccceccccccceca0eca0eca0eca0eaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeac0c0eaeac0c0eaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0e0e000000000e0a0e0a0e0a0e0a0e000e000e000e000ddddffff00000000dddddddddddddddd
  | 2, 0 => 0xeeaaeeeeeeaaeeeeeeaaeeaaeeeeeeeeeeaaeeaaeeaaeeaaeeaaeeaaeeaacc00eeaaeeaaeeaaaaaaeeaaeeaaaaaaaaaaeeaaee00eeaaee00eeaaaaaaeeaaaaaaee88ee88ee88ee88ee88ee88ee00ee00ee88ee00ee88ee00ee80ee80ee80ee80ee00ee00ee00ee00ee00ee0000000000ee00aa00ee00aa00ecececececececec
  | 2, 1 => 0xeeeecccccccccccceeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeee0000eeee0000eeee0000cccc0000eeee000000000000eeceeeceeeceeeceeecceecceecceecceecceecceecccccceecceeccee00ee00eecceecccccccccceecceeccaa00aa00eecceecc00000000eecceccceecceccceecccccceecccccceeccaa00eeccaa00
  | 2, 2 => 0xf000f00000000000f000c000f000c000efefefefefefefefeeffeeffeeffeeffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeeeecceecceeeeeeeeeeaaeeaaeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeecccceeeecccc
  | 2, 3 => 0xf0c0f0c0f000f000f0c0f000f0c0f000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f000f0a0f0a0f0a0a0a0f0a0f0a0f000f000f0a0f0a0a0a0a0a0f0a0f000f0a0f000f0a0f000f000f000f0a00000f0a00000f080f080f080f080f050f050f050f050f000fffff000fffff000f000f0f0f0f0f000f000f000f000f000f000f0000000
  | 2, 4 => 0xf0f0505050505050f0f03030f0f03030f0f000f0f0f000f0f0f00000ffff0000f0f00000f0f0f0f0f0f00000f0f00000f0f00000f0000000f0f0000000000000f0e0f0e0f0e0f0e0f0e0f0e0f0c0f0c0f0e0f0a0f0e0f0a0f0c0f0f0f0c0f0f0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f000f0c0f0c0f0c00000f0c0f0c0f080f080
  | 2, 5 => 0xf0f0f0f030300000f0f0f0f000000000f0f0f0c0f0f0f0c0f0f0f0c0f0f0c0c0f0f0f0a0f0f0f0a0f0f0f0a0f0f0a0a0f0f0f0a0f000f000f0f0f000f0f0f000f0f0f000f0f00000f0f0f000f000f000f0f0f000f0000000f0f0f00000000000f0f0d0d0f0f0d0d0f0f0c0c0f0f00000f0f0a0a0f0f0a0a0f0f07070f0f07070
  | 2, 6 => 0xf0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0f0c0c0c0f0f0f0f0f0a0f0a0f0f0f0f0f0a0a0a0f0f0f0f0f0a00000f0f0f0f0f050f050f0f0f0f0f000f0f0f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0c0c0c0c0f0f0f0f0b0b0b0b0f0f0f0f0a0a0a0a0f0f0f0f050505050f0f0f0f03030f0f0f0f0f0f030303030
  | 2, 7 => 0xf0f0f0f0fffffffff0f0f0f0fcfcfcfcf0f0f0f0fafafafaf0f0f0f0f3f3f3f3f0f0f0f0f0fffffff0f0f0f0f0fff0fff0f0f0f0f0fff0f0f0f0f0f0f0fcf0fcf0f0f0f0f0faf0faf0f0f0f0f0f3f0f3f0f0f0f0f0f0fffff0f0f0f0f0f0fcfcf0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0c0c0f0f0f0f0f0f0a0a0
  | 2, 8 => 0xf1f1f1f1f1f1f1f1f0fff0fff0fff0fff0fff0fff0f0f0f0f0fff0ff00000000f0fff0f0f0fff0f0f0fcf0fcf0fcf0fcf0f3f0f3f0f3f0f3f0f2f0f2f0f2f0f2f0f0fffffffffffff0f0fffff0f0fffff0f0ffff00000000f0f0fafafafafafaf0f0fafaf0f0fafaf0f0f3f3f0f0f3f3f0f0f0fff0f0f0fff0f0f0f3f0f0f0f3
  | 2, 9 => 0xf8f0f8f0f8f0f8f0f8f0f8f0f0f0f0f0f888f888f888f888f800f800f800f800f7f7f7f7f7f7f7f7f5fff5fff5fff5fff5f5fffff5f5fffff5f5f5f5f5f5f5f5f5f5f5f555555555f555f555f555f555f4f4f4f4f4f4f4f4f3f3f3f3f3f3f3f3f3f3f3f3f0f0f0f0f333f333f333f333f2f2fafaf2f2fafaf2f2f2f2f2f2f2f2
  | 2, 10 => 0xfafa0000fafa0000faf8faf8faf8faf8faf0faf0faf0faf0faf0faf0f0f0f0f0faf0f0f0faf0f0f0faf0f0f0f0f0f0f0fac8fac8fac8fac8faaafaaafaaafaaafaaafaaafaaaaaaafaaafaaaaaaaaaaafaaaaaaafaaaaaaafaa0faa0faa0faa0fa00fa00fa00fa00fa00fa00aa00aa00fa000000fa000000f8f8f8f8f8f8f8f8
  | 2, 11 => 0xfafafffffafafffffafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafaaafaaafafafafafa00fa00fafafafaf8f8f8f8fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafafaaafafafaaafafafa00fafafa00fafaf0f0fafaf0f0fafaf0f0aaaa0000fafaaaaafafaaaaafafa0000ffff0000
  | 2, 12 => 0xfcf0f0f0fcf0f0f0fcf00000fcf00000fcecfcecfcecfcecfcccfcfcfcccfcfcfcccfcccfcccfcccfcccfcccfcccccccfcccfcccccccccccfcccfccc00000000fcccfc00fcccfc00fcccccccfcccccccfcc0fcc0fcc0fcc0fcc0fc00fcc0fc00fca8fca8fca8fca8fca0fca0fca0fca0fc88fc88fc88fc88fc00fc00fc00fc00
  | 2, 13 => 0xfcfcfcfca8a8a8a8fcfcfcfc00000000fcfcfcccfcfcfcccfcfcfc00fcfcfc00fcfcf8f8fcfcf8f8fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcfc0000cccc0000fcfc000000000000fcf0fcf0fcf0fcf0fcf0fcf0fcf0f0f0fcf0fcf0fcf00000fcf0fcf0fc00fc00fcf0fcf0f0f0f0f0fcf0f8f0fcf0f8f0
  | 2, 14 => 0xfec00000fec00000feaafeaafeaafeaafeaafeaa00000000feaa0000feaa0000fea0fea0fea0fea0fe80fe80fe80fe80fe80fe8000000000fe00fe00fe00fe00fcfffcfffcfffcfffcfcfcfcfcfcfcfcfcfcfcfcfcfcf0f0fcfcfcfcfcf0fcf0fcfcfcfcfcccfcccfcfcfcfcfc00fc00fcfcfcfcf0f0f0f0fcfcfcfccccccccc
  | 2, 15 => 0xfefcfefcfefcfefcfefafefafefafefafefafefa00000000fefa0000fefa0000fef0fef0fef0fef0fef0fef0f0f0f0f0fef0fef000000000fef00000fef00000feeefeeefeeefeeefeeefeee00000000feccfeccfeccfeccfeccfecceecceeccfecceeccfecceeccfeccccccfeccccccfecc0000fecc0000fec0fec000000000
  | 3, 0 => 0xff00ee00ff00ee00ff00cc00ff00cc00ff00cc00ff000000ff00aa00ff00aa00ff00aa00aa00aa00ff00aa0000000000ff000f00ff000f00ff000000ff000000ff000000cc000000ff00000000000000fefefefefefefefefefefefefafafafafefefefef0f0f0f0fefefefe00000000fefeeeeefefeeeeefefe0000fefe0000
  | 3, 1 => 0xff00ff00ff00fc00ff00ff00ff00f000ff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff008800ff00ff00ff003300ff00ff00ff000000ff00ff00fe00fe00ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00aa00aa00ff00ff0088008800ff00ff000f000f00ff00ff000000ff00ff00ff0000000000ff00f000ff00f000
  | 3, 2 => 0xff03ff03ff03ff03ff01ff01ff01ff01ff00ffffffffffffff00ffffff00ffffff00ffffff00ff00ff00ffff0000ffffff00ffff00000000ff00ffccff00ffccff00ff0fff00ff0fff00ff00ffffffffff00ff00ffccffccff00ff00ff33ff33ff00ff00ff00ffffff00ff00ff00fff0ff00ff00ff00ff55ff00ff00ff00ff00
  | 3, 3 => 0xff88ff88ff00ff00ff88ff8800000000ff88ff0000000000ff880000ff880000ff80ff80ff80ff80ff80ff8000000000ff800000ff800000ff55ff55ffffffffff55ff55ff55ff55ff55ff5555555555ff44ff44ff44ff44ff3fff3fff3fff3fff33ff33ff33ff33ff33ff3300000000ff0fff0fff0fff0fff0fff0fff00ff00
  | 3, 4 => 0xffaaff0000000000ffaafaaaffaafaaaffaaf0a0ffaaf0a0ffaaaaaaffaaaaaaffaa0000ffff0000ffaa0000ffaa0000ffaa0000ff000000ffaa000000000000ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00ffa0ffa0a0a0a0a0ffa0ffa000000000ffa0ff0000000000ffa0a0a0ffa0a0a0ffa00000ffa00000ff88ff88ff88ff88
  | 3, 5 => 0xffc0c0c0ffc0c0c0ffc00000ffc00000ffafffafffafffafffafffaf00000000ffaaffffffaaffffffaaffff00000000ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaaaaaaffaaffaaffa0ffa0ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ffaa0000ffaaff00ff00ff00
  | 3, 6 => 0xffccffcc00000000ffccff88ffccff88ffccff00ffccff00ffccff00ff00ff00ffccff00ff000000ffccff0000000000ffccccccffccccccffccccccccccccccffcccccc00000000ffcc0000ffcc0000ffcc0000ff000000ffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ffc0c0c0c0c0ffc0ffc000000000ffc0ff0000000000
  | 3, 7 => 0xffeeffccffeeffccffeeffaaffeeffaaffeeaaaaffeeaaaaffee0000ffee0000ffee0000ff000000ffecffec00000000ffeaffeaffeaffeaffe0ffe0ffe0ffe0ffe00000ffe00000ffcfffcfffcfffcfffcfffcf00000000ffccffccffccffccffccffccffccccccffccffccffcc0000ffccffccff00ff00ffccffcccccccccc
  | 3, 8 => 0xfff0fff0aaa0aaa0fff0fff000000000fff0ffa000000000fff0ff00fff0ff00fff0ff00ff000000fff0ff0000000000fff0f0f0fff0f0f0fff0f0f0ff000000fff0ccc0fff0ccc0fff00000fff00000fff00000ffc00000fff00000ff000000fff0000000000000ffeeffeeffeeffeeffeeffeeff00ff00ffeeffee00000000
  | 3, 9 => 0xfffafffafffafffafffafffaaaaaaaaafffafffa00000000fffafff000000000fffaaaaafffaaaaafffa0000fffa0000fff80000fff80000fff50000fff50000fff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff00000fff0fff0ff00ff00fff0fff0ff000000fff0fff0faf0faf0fff0fff0f0f0f0f0
  | 3, 10 => 0xffff0000aaaa0000ffff0000aa000000ffff000033330000ffff00000f0f0000ffff000000ff0000ffff00000000ffffffff000000000000fffefffefffefffefffe0000fffe0000fffcfffcfffcfffcfffcfffcffccffccfffcfffcfcfcfcfcfffcfffcf0f0f0f0fffcfffc00000000fffcffcc00000000fffc0000fffc0000
  | 3, 11 => 0xffff0000ffffffffffff0000ffff5555ffff0000ffff00ffffff0000ffff00ccffff0000ffff0055ffff0000ffff0000ffff0000fffc0000ffff0000fff00000ffff0000ffcc0000ffff0000ffaa0000ffff0000ff550000ffff0000ff000000ffff0000fefe0000ffff0000fcfc0000ffff0000f0f00000ffff0000cccc0000
  | 3, 12 => 0xffff0f0f00000000ffff0c0cffff0c0cffff0a0affff0000ffff0505ffff0505ffff0303ffff0303ffff0303ffff0000ffff00ffffff00ffffff00ffffff0000ffff00ff00ff00ffffff00f0ffff00f0ffff0055ffff0055ffff0033ffff00ffffff0033ffff0033ffff0030ffff0030ffff000fffff000fffff0005ffff0005
  | 3, 13 => 0xffffa0a0a0a0a0a0ffff8888ffff8888ffff8888ffff0000ffff5f5fffff5f5fffff5f5fffff0000ffff55ffffff55ffffff5555ffff5555ffff5555ffff0000ffff555500000000ffff5050ffff5050ffff3333ffff3333ffff3333ffff0000ffff333333333333ffff0f0fffff0f0fffff0f0fffff0000ffff0f0f0f0f0f0f
  | 3, 14 => 0xffffaaaaffffaaaaffffaaaaffff0000ffffaaaaffaaaaaaffffaaaaff00aa00ffffaaaafafaaaaaffffaaaaeeeeaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffaa00aa00aa00ffffaa00aa000000ffffaa0000000000ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffffa0a0ffff0000
  | 3, 15 => 0xfffff00000000000ffffeeeeffffeeeeffffeeeeffffccccffffeeccffffeeccffffeeaaffffeeaaffffee00ffff0000ffffccffffffccffffffccccffffccccffffccccffffcc00ffffccccffff0000ffffccccccccccccffffcc00ffffcc00ffffcc00ffff0000ffffcc0000000000ffffc0c000000000ffffc000ffffc000
  | 4, 0 => 0xfffffafaaaaaaaaafffffaaafffffaaafffff8f8fffff8f8fffff5f5fffff5f5fffff3f3fffff3f3fffff0f0fffffffffffff0f0fffff0f0fffff0f0fffff000fffff0f0ffffc0c0fffff0f0ffff0000fffff0f0aaaaa0a0fffff0f000000000fffff0c0fffff0c0fffff000fffff000fffff000ffff0000fffff000f000f000
  | 4, 1 => 0xffffff00ffffff00ffffff00fffff000ffffff00ffffaa00ffffff00ffff0000ffffff00fff0ff00ffffff00ff00ff00ffffff00ff000000ffffff00aaaaaa00ffffff0000000000fffffcfcfffffcfcfffffcfcffff0000fffffcfc00000000fffffcf0fffffcf0fffffcccfffffcccfffffafafffffafafffffafafafafafa
  | 4, 2 => 0xffffffccffffffccffffffccffffccccffffffccffccffccffffffccccccccccffffffcc00000000ffffffc000000000ffffffaaffffffaaffffffaaffffff00ffffffaaffffaaaaffffffaaffff0000ffffffaa00000000ffffffa000000000ffffff88ffffff88ffffff55ffffff55ffffff0fffff0000ffffff00ffffffff
  | 4, 3 => 0xffffffff00330033ffffffff000f000fffffffff000f0000ffffffff00030003ffffffff0000ffffffffffff0000ff00ffffffff0000aaaaffffffff00000f0fffffffff000000ffffffffff00000033ffffffff00000000fffffffafffffffafffffff0fffffff0fffffff0ff00ff00fffffff000000000ffffffee00000000
  | 4, 4 => 0xffffffff44440000ffffffff3333ffffffffffff33333333ffffffff33330000ffffffff0f0f0f0fffffffff0f0f0000ffffffff0f000f00ffffffff0f000000ffffffff05050000ffffffff01010101ffffffff00ffffffffffffff00ff00ffffffffff00cc00ccffffffff005f005fffffffff00550055ffffffff00500050
  | 4, 5 => 0xffffffffc0000000ffffffffbbbbbbbbffffffffafafafafffffffffaaffaaffffffffffaaaaaaaaffffffffaaaaaa00ffffffffaaaa0000ffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffff88888888ffffffff88008800ffffffff80808080ffffffff55ff55ffffffffff55555555ffffffff55550000
  | 4, 6 => 0xfffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeeeeccccffffffffeeaaeeaaffffffffee000000ffffffffececececffffffffccccffffffffffffccccccccffffffffcccccc00ffffffffcccc0000ffffffffcc88cc88ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0
  | 4, 7 => 0xffffffffffaa0000ffffffffffa0ffa0ffffffffff33ff33ffffffffff00ff00ffffffffff000000fffffffffefefefefffffffffcfcfcfcfffffffffafafafafffffffffafaaaaafffffffffafa0000fffffffffaaafaaafffffffffa00fa00fffffffff5f5f5f5fffffffff3f3f3f3fffffffff0f0f0f0fffffffff0f0a0a0
  | 4, 8 => 0xffffffffffffccccffffffffffffcc00ffffffffffffaaaaffffffffffffa0a0ffffffffffff5555ffffffffffff00ffffffffffffff0000fffffffffffcfffcfffffffffff0fff0fffffffffff0f0f0fffffffffff00000ffffffffffccffccffffffffffcc0000ffffffffffaaffaaffffffffffaaff00ffffffffffaaaaaa
  | 4, 9 => 0xfffffffffffffffffffffffffffffff0ffffffffffffff00fffffffffffff0f0ffffffffffffeeee
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0xee974ae83
  | 3, 0, 0 => 0x774d4d7416546329bce29124774e39740d1486aee9740da486ac01740c6486abbd7412e4774bc17412e486ad05902f54632b2d2412e4632b98ae92e46329ccc212e46329ccde111463295cd912e4632960e292346329cccf1294632954e29114
  | 3, 0, 1 => 0x86aee9902ea4640bb576165486abe1740d14632998cf92e463295ce2924486aee9740f14774bb574165486aee9740c64632ab4e28ff463295cda92e46329bcce92e46329cce290646329cd0598f4774cf9902fb4632b50c792e4632960d912e4
  | 3, 0, 2 => 0x774ce990305486aee9740c54632954e292e486ad797412e486aee9752e84640c09800c64774d11741c546329ccc992e4774dbd740e24
  | 4, 0, 0 => 0x86aee9902a42f4aee9a9b2055a6055d4b194ce714972bba6dec8139a0d5774dbd9029525caee9b03205cc4b95dd38e640b2d542c35774ba0710d1586ac653999e25cb0d5dd340640bed60cb204e6678972c35774c817b8da58f6c813998525cac653324a38a4b95dd3194e67147aac35774ba1730c65
  | 4, 0, 1 => 0x774bb57427338ab065902733644b960e3204e661c972c35774ba1398f7586ad299029038aaee9c73205963f161abba640bed03ac89640b2d2412e5832c81339c525cb225902e62ba4b95dd353640bd539ac35678c816a92e5752c65399c725caee9a232057c5e95dd361640b14972ba96329ccd912e5
  | 4, 0, 2 => 0x632b79251c525caee9a1b2057c71558ca7338a674972bba71cba0e292e57aec65399c525cb0d5dd2e847a71561abba640b547a2c35774c817a8df586aee97416125cac6539a5e38a45158ca7338a63c972c356ccc817d92e586ac65399c51e8b0d5dd32046a8355dd38e640b2c972c1c64099cda92e5
  | 4, 0, 3 => 0x86aee9902c425cae2d8ca7338a4b9644b2046e714972b616bcc817312e586ac817aaf11c4ac652c25438a4b961abba5803bc632ba9632a9d399c55752c653998a25caee98ca7336a4b961abba5d09cc632c356ccc816292e586acf19027341ab0d5dd3205aa3d960e3194cc714972bba6dec81828e25
  | 4, 0, 4 => 0x86aee9741c51b8ac65399aa3224b958ca7331e5d8972c896409bce2912586aee9742732dcb0d58ca5838a4a561abba6409cd02ab194b0714d512e5838c81339c5248ac6537a4838a4b95da3194e66c8972c1c6409cce29235768c65339c525cb0d58ca6f38a45963db204e6714892c35774ba0b28ea5
  | 4, 0, 5 => 0x86ad29902ad430b1ed902cb4944b95dd344640c14e2ac7c6329cccf92e5774c815f1c51c8aee98ca7338a49163db204e68a8652b194cc714c892e586ac653997d25caee9b0b205964b958ca7333e4b88d2b194e68a8c792e5774c65379c5246b0d5dd3204e635d5d4b194e6604972c1a6329cce29295
  | 4, 0, 6 => 0x86ad05902ad38aaee99d3204e68a958ca73340670972c35774c81730f056329cce292e220b0719026038a4b961ab41640a8ce2ac35774ba1658e2586ac8139a2a196b0d5a532055a71561abba640becc0abba632a9d2f1c556329cce299025caeb58ca7338a4b95dd320550a14e2ac7b640960e29165
  | 4, 0, 7 => 0x86ad999024341ab0d5dd3205963e560e3204e6678972c35774c8162aa85632ad9399c5206ac81379aa3224a561ab194e671483ac35774ba1398d1586aee9acae82cab1ed9027343040d63db204e6654972c356329cd0b9035912c81399c520cb0d5dd3205ea38958ca734bc680972c7b6409cccf92e5
  | 4, 0, 8 => 0x82ec65379c525cac65399c524840960cb204e671494ac35774c8148181586aee9902ad40eb0d5dd32058a3f163db204e6674972c356329cccf914586ad05902a438ab05d8ca7333e4b961abba640bdc632ba96329cce29295912c813999e25cb0d5a532054871561ab005d0594972c1c6329cce29235
  | 4, 0, 9 => 0x838c81399c51ecaea58ca3b38a4b95dd3446409cd0c2b194e6870d512e5632b612f1c525cb2259025633c4b95d73194e6714972ba963295ce292e5640bb57627338aaea58caca4e64b961abba640b14972c356bcc818292e5632af9251c5234b0719026738a4b958ca7338a4688b2c356329bce29145
  | 4, 0, 10 => 0x86ad79902e625caea58ca7336a4b95da3194e671494ac35774c8182a355774c65399bc248b0d5dd3205f633963db194e667c972c89640ab4e28ff563299d251c525cb0d5dd32060a3155dd31957c7146fac7b6409cce29165838c812b9b525cb0d58ca5738a4b961abba640834f52c1964095ce292e5
  | 4, 0, 11 => 0x6329cd0d1c525cb071902e62c24b95dd3194aa714972c1c64095ce29245912c653999e25cb05d8ca7338a4595dd319594978972bba6329cce28fb56329ccde11a206b0719026238a4b95b5b204e6714972c196409ccda92e5774c652b1c525cb0d58caad38a40d63db204e671488ac35672c8139a2a5
  | 4, 0, 12 => 0x86aee97aae81c4aee9902cb50a4b95d4b194e66f094aba96329cce29245632af92f1c5206aee98ca6638a48d61abba640a90c52c35774c81569815774c656a9aa25cb0d5dd32038a54d60e3194ce714972bba6329ccd592e5774da9902d525cb0658ca7338a4a55b53194e6714972c35774c81658fc5
  | 4, 0, 13 => 0x912c812c1b525cadbda53204e68a95dd3194e6834d52c35632960e292e57c8c65399c525caee9b7b204e681d63db194e67148b2bba6d4c8139a0d5640c652a9c525ca0021abba5d03191f1b194e6714972c35632b98af12e56329cce295d25cac818130038a38963e3194e67148a2b194e67148d1145
  | 4, 0, 14 => 0x752c657316525cb2259025838a4915d4b195509cce2ac35774ba1250d1586ad99903051c4b0d58ca733404595dd3205aa768972c35692c81569c5586aee9902fe2f4b0d5c33205cc3dd60e32055a7148d2c7b640960e2923586aee9902fb18cb0d57c2e838a4b961ab194ae6f0972b194ce714c892e5
  | 4, 0, 15 => 0x86aee9902f51b4aea58ca733804b958ca6f38a63c972ba9632958e292e586aee990273408ae0d8ca7338a4b961abba6409cd032c35774c81150d85832c81399c525cb0d5dd2e84bc34561ab3c6408d5152b8e70cc81541c55752c65399c525cb0d58ca4e38a4b958ca733404b88d2bba6dec81730fc5
  | 4, 1, 0 => 0x86aee9902182a2b225902733264b95e9b194e6714972c35774c817f15c5832c65399c525caea58ca7238a4b961abba640b2c78ac35774c81759c5586aee9740d118cac65379aa3224b958ca48462714972b8e6ccc817312e5768c65399c525cb0659025538a4b95d4b194aa714972bba640c15810c65
  | 4, 1, 1 => 0x6329cce2914220b07d8ca6638a4b95dd38a640b2c972c35774bad741c55774c09741c51c4b2259025538a4b95dd344640af8e2ac1c640954e292e5774dbd7427325cb0d5a53204868a961abba640594ac2c35774c818295c586ac655424a38aaea59026f3784a55dd3194e67148dac19632954e292e5
  | 4, 1, 2 => 0x86aee9902a32f4b0d5dd33b640c1561abba60aba0632c35774c81740c65774c81331b2246b0d5dd32060a31961abba680ba139ab194cc924e292e5774c65339b525cb0d5dd32046a8a95dd3194cc714972b8a6329cce292e586ac652c1c522cb2258ca5538a4b958ca7338a4b82a2800632954e292e4
  | 5, 0, 0 => 0x774e399027338a3f9a1abba6409ccef143686aee990273314459a1abba640b2d54273686aee99027338a18da1abba6409cd150ce686aee9902733504b9a1ab86640af8e291a686aee9902cb4c64b99dd38e640b98c312e6774dbd902e625c389a1abba640ab4c08ef6912ed19026738a4b9a1abba640b70b292e6752c818ca7338a4b9a44c356409bce29166
  | 5, 0, 1 => 0x86aee9902c53144b9a1abba640aa8e292e6774dbd902e64864b9a1ab1955e9cce292e68f6ee99027338a48da1abba640a40e2957686aee98ca733804b9a1ab1161095ce292e6856ee9902733404b9a1abba6409cd0c14f686aee99027330a3e5a0bc016409cce292e68aeed19027338a4b9a1abba6b2c8156981669ed299027338a4b9a1abba640a44e292e6
  | 5, 0, 2 => 0x86aded9027338a4b9a1abba640aa0e29616774c8188a3a38a4b9a1abba640c15150c6686aee9902733ce345a1abc56409cce292e686b07d8ca733784b9a1abba6408e0e28ef6752c65399c525c25da1ab866408c4e28fc686ad05902732f44b9a1abba6409cd079c5686aee99023e3404b9a44b204de920e292e686aee9902733784b9a1abba6409cce29256
  | 5, 0, 3 => 0x838c81399aa3224b9a1abba640b2c970526774c65399c525c491a1abba6409ccf612e686aee9acb205ea9cd8003ba6dec8139a0d58f6ee9902d538a4b9a1abba6408f515191686aee9742a84e6715a1abba6409cd110d1686aee9902f24e64b9a1ab206109cce28f9686af059027338a3f1a1abba6409cd0c0f76912c812c1c53544b98003a94e67149705c5
  | 5, 0, 4 => 0x86aee9902cb4e63f19dd3204e6978de129686aee9902fb38a3899dd38e6409bce292e6700df19027338a4b9a1abba6409cce2908686aee9902733c04b99b7b66640b993992e686aee99026a38a4b9a1ab866408c4e292e686aef59027a38a4b9a1ab4a6409ccdb12e686aee9902e62ca3dda1ab195cc9ccc892e686ae59c3320550715a44c35640960e29296
  | 5, 0, 5 => 0x82ef259027338a4b9a44c1a6409cce2929686aee9902734303c9a1abba64094ce292e6774e39ba3205cc4b9a1abba6409cce28f7686af059027338a4b99dd3b46329cce292e686ac81842e62bc4b9a44b204e66a8c892e686ac81399c525c209a1abb46409cce292468c2ee99027338a4b9a1abba640b552192e686aee9902cb4863dda1abba698c81569c56
  | 5, 0, 6 => 0x86ac818425838a4b9a1abba640b54c392e6774d65a9b2055a715a1abba640a18e293c686b0098ca7338a4b99dd320622aa12f1c5686aee59027338a4b9a44ba96409ccc092e686aee9902f74e6345a1ab86640b98c512e6838c813999f25c469a253ba6409cce292e686aee990305354389a3db206109cce29166774d4d902ad38a3bda1ab204b0714970196
  | 5, 0, 7 => 0x86aee991a733784b9a44b204e68a8c792e686aee9902d541a645a1abba640a8d3998168f90719027333e4b9a18bba6409cce28fc6774d119023d38a4b9a1abba640b98e28f168f6c81399b23204b9a1abba6409cce692e6838ee99027338a491a1abb4640960e292e686aee9902352ee4b99dd36f640b653992e686aee99023d4307159dd39c6409cce292e6
  | 5, 0, 8 => 0x86aee9902ad4e6605a253d26409cce292e686aee9a2b2057c715a1ab204e68a8e2904686ad99902d54e64b9a1abba640914e292e686ad29902ad38a4b9a1abba6409cce291968dcee98ca7338a4b9a1abba640ab5069c5686aee9902cb4e64b9a1abc26409cce292e686aee99025938a4b9a1abba6e2c8139a0d6774d4d9027331c4b9a3dc1f6409ccd912e6
  | 5, 0, 9 => 0x86ac8157a733784b9a25c1c6409cce292e686aee99029e38a4b9a1abba640af8e28e36774d4d9027341a605a1ac1c6409ccc092e686aee99025038a4b9a1abb46408f4e292e686aee9742e62ca4b9a44b2057c920e292e6752c658327338a4b9a44bba6409cce2924686aee99026838a4b9a1abba640a40e28e6686ae199026738a4b9a1abba640970e292e6
  | 5, 0, 10 => 0x86aee9902733ba4b99fc3a96329cce292e686aee99026f38a4a5a3141c6409cce292e686aee99027343031998ca7338a4b88d103686ac8139a4c38a4b9a1abba640714a812e686aee98ea6f38a4b99dd36f6409cc97073686aee99027538a4c9a27bba6409cce292e686aee99027338a4c5a1bbba640960e292e686aee99027638a4b99a9b4a6409ccc092e6
  | 5, 0, 11 => 0x86aee9c9b20550715a1abba6409ccc091668f8c65399c525c40da1abba640b313992e686aee99027345433da1abba6409cd1517e686aee990273430431a1ab205cc9ccc912e686aee97427338a4b9a1ab206009cd150d1682eee99027333c4b99dd36f640ab4e292e6862ee99027338a4b9a1abba6409ccdf12e6774e75902733144b98003ba71cc816592e5
  | 5, 0, 12 => 0x86aee99027338a499a1abba640bd52192e686aedd9026738a4b99dd38e640af8e292e686aed19026e38a4b9a1abba640af92518168deee99026738a4b9a3db4a6409cce292e686aee9902733464b9a44bad6409cce292e686aee9902734223dda1abba640af91e9c56000c65399c531e4b961abba640bd4970e2686acf1902732ee4b9a1ab66640a24e292e6
  | 5, 0, 13 => 0x8f6ee99327338a4b9a1abba6409cce2930686aee9902e6454319a1abba6409cd21a0d686aee9902734543cda28c1c6409cce292e686aee9902e32c64b9a1abba6409cd150d3686aee98f27338a4b9a1abd56329cce292e6774d4d902a34e6715a0e3204e671497110686aee9902e22ca4b99da3206229cce292e686aee9902734403dda44b204e6714c812e6
  | 5, 0, 14 => 0x912c81399a03384b9a1aba064090ce292e686aee9902a8494715a1abba640b54d012e6912c65399c531e4b99dd33e640af9399c56838d4d9027338a4b9a44b204e671497110686aee9902e647c4b9a1abba64095ccf92e6774e899027338a3f9a1ab86640af8e2903686aee9902733bc3f19dd353640ab5399c5686ac818027338a4699dd38d6409cce292e6
  | 5, 0, 15 => 0x86aee99023d448715a1ab986409cce292e6774d11902e638a4b9a1abba5d09cc970d16834ea58ca7338a4b9a1ac066409ccd012e686aee990273374491a1abba640c10e28e2686aee99027338a515a0cbba6329cce292e6000ee98ca7336a4b961abba640b293792e686aee99027338a551a1ab205f8b54e292e686af299027338a4b9a1abba640aa12d9c56
  | 5, 1, 0 => 0x86aee9902732ee3d1a1fbc36409cce292e686aee9b1b205cc4b9a1abb56409cce292e6774d4d9027338a459a1abba6a6c81569c5686aee990243454345a1abba6409cceb14168f6ee19027338a4b9a0bbba64099ce292e686aee9901c525c2459da3206329cce292e686aee990273414715a1abba6409cce29056912c8139a5e3404b9a1abba640b48e292e6
  | 5, 1, 1 => 0x912ee98ca7336a4b99dd37a6409cce292e686aee99027338a4b1a0e3204e6714970df686aee99027838a4b9a203ba6409cce292e687aee99027338a4b9a1ab866409ccc50fc68f6c81399c525c40da1abba640b3d041c5686ac8184273340459a1abba6409dce292e6774d4d902be494715a1abba6409ccef12e68f6ea59026638a4b9a1abba640998d912e6
  | 5, 1, 2 => 0x752c6588a7338a4b9a1abba6329c8e292e6838c8139a5438a4b9a1abba640928e2955686aee99027338a4cda1abba632af8e28e26774dbd902733c84b9a0d4196409cce292e686af999027338a4a5a1abba6408f4f092e686aee9902734303c5a1abba640a40e28e2686aee99027338a1c99d4b194e671497129686aee9902a338a37d9dd38e6408c4c512e6
  | 5, 1, 3 => 0x86aee99027325c295a1ab866409ccc512e686aee98ca733004b9a1abba640b98b28f1686ace59027338a4b9a1ac1a6329cce292e686aeed9027338a4b9a1ab86640ae0e292e686aee9902ad38a37d9dd3a96329ccde12e6774cf59027338a4b9a1abba6409cc970d6686ad9990273454345a1abba6409cce288d686aee9902732ee3d9a1ab4a6409cce28706
  | 5, 1, 4 => 0x8f8ee98ca6738a4b9a1abba6409cce28f16752c657327338a4b9a1ab966ccc817312e6912c815b27338a40da1ab846408c4e292e686aee9902733ce469a1abba640928ec12e68f6ee99027338a4d1a1abba6409cce290f69130d59027338a41da1abba6408e8e292e686aee9902734543dda1ab65640b993992e686aee99027331a4b9a1ac1c6409cce992e6
  | 5, 1, 5 => 0x86ad2990273406715a1abba6409cce29186752c658ca7338a4b9a1abba640988d692e686aee99027338a4a9a1abba640bd13992e6832c8188a7338a4b9a1abba6404b8538a3686aee9b23205aa4b9a1abba6409cce293a686aee9902be4bc605a1abba64096ce292e686aee9902ee4e66a9a1abba6409cce592e68f705d9027338a4b9a1abba640af8e295c6
  | 5, 1, 6 => 0x838c8188a7336a4b9a44ba96409cce2929686aee9902734543c9a1abba580594970ef686aee990273410715a44ba963a9cce292e6774d699027338a4b99dd38e6409cce2916686aee9902d52ee3dda1ab4a6409ccd012e686aee9742732ca4b9a1abba6409ccd092e686aee9902734303fda1abba6409cd069a0686aee9902d53a04b9a1abba6409ccda12e6
  | 5, 1, 7 => 0x86ae119026738a4b9a0e3204e6714d512e686aee9902a84bc715a1ac216409cce292e686aee99023d454715a1abba640c14b28d1686aee9902733704b9a1abba6409ccda92d6000c65399aa3224b961abb4640aa1399c5686b0719027333e451a1abba64090ce28fe686aee9902be38a371a0e4176409cccf92e686aee98ca733784b9a3dbba6329cce29236
  | 5, 1, 8 => 0x774dbd9027342a4b99dd36f640c153992e686aee9902be378389a1abba6409cce2913686b0719027338a4a5a1abba68ec81519c5686b0718ea7338a4b9a1abba640b2cfb12e66329cce299131e4b9a1abba6409bcda92e686aee9902733284b9a0cb206329cce292e686ac458425838a4b9a1abee6409cce2916686aee9a132057c715a1abba6409cce29466
  | 5, 1, 9 => 0x86aee990273454319a0bbba6409ccc512e6774d4d902be4bc715a1abba640bcd3992e68c2ee98ca7338a4b9a1ab206109cccc12e6752c65399c525c3bda1abba68ec81569c5686ad79902733144b9a44c176409bce292e6912c81399c5248409a1abba640b9cb292e6774d119027338a3f19dd3204e67149705f686aee9902723784b9a1ab20610938e292e6
  | 5, 1, 10 => 0x86aee9741f638a4b9a1abb46409cd0c12e686aee9902e42ca4b9a1abba6409ccbe12e686aee990258454345a1abba6409ccd612e68f6ee99026738a4b9a0e3a964095ce292e6898ee99025f38a4b99dd3206229cce29126752d658ca7338a4b99dd33e6409cd151c5686aee98ca7338a3dda44b204e67148d116686aee9902732d84b9a44b194e66a8c892e6
  | 5, 1, 11 => 0x8f6ee9902733644b9a1abba640b54970c8686af25902733404b9a1abba6409ccc292e68390119027338a4b9a1ab4a640b54e292e686aee99027338a471a1abba6409ece292e686aee99026938a4b9a1fbba6409cce292e69131f19027338a459a1ab205eabc53992e6774e019024338a4b9a1abba640b81398f76912c815f24a38a469a213ba6409cce292e6
  | 5, 1, 12 => 0x912c8139a1c3544b9a1ab866409ccc092e6912c816c25e38a4b9a1abba6c8c8139a0d6774c81399f138a4b9a3db204e6714971166752c818ca733784b99dd32060ac08e28e2686ac65399c525c371a1abba6409cd0b12e683ec6539a5e38a4b9a1abb4640b98b292e6912eb99027338a4b9a1abba632b2d3992e6774d119027338a4b99dd3194e6714b092e6
  | 5, 1, 13 => 0x86aee98ca6f38a4a5a1abba640974e292e6700d999027338a4b9a1abc3640a24e292e686aee9902733544d9a1abba64099cc392e6000ea58c9c525c1ed61ab666409bce292e686aed19027338a4b99dd36f640b54e292e68f6c815f24a38a4b9a1abba640b1d3992e686aee99027338a4859dd3194de714d512e686aee9901c525c241a1abba6409d0e292e6
  | 5, 1, 14 => 0x752ea58ca7338a4b9a1abba640ab4c50fc6774cf990273454345a1abba6409cce712e686aee918a0338a389a1abba640908e292e686aee9902733744a1a3dbb4640998e292e6912f3d9027338a4b9a1ac1c64095ce292e686aee9902cb57c389a1abba640b4ce292e60010d5a532055a71561abba640aa11b1c5686aee9902673944b99dd38a6409cce28f96
  | 5, 1, 15 => 0x86aee9902733783dda1ab194e6714818ee6912ea99027338a4b9a30bba6409ccde12e686ac6539a4a38a4a5a1ab86640a80e292e6774c8188a73430469a1abba6409cd061c5686aee990273430345a1abba718c81541c5686ad29902be38a595a1abba640b55068d169130d59025738a4b998ca73494714d512e686aee9902ad2ee345a1bbba6409cce292e6
  | 5, 2, 0 => 0x86aee9902734543c5a1abba6409c4e29296774d719027338a4b9a1abba640628970a6686aee99025b34c4b9a1abba640918e292e686aee9902ad3144b99c33536409cce292e686aee98ea7138a4b9a1abba6409cd03a036774e299025838a4b9a1abba640ab8e28da6912ee9902be38a37da1abba6409cd1516e66a6d299027338a3bd800435774c817a8e25
  | 5, 2, 1 => 0x774c657325e38a4b99dd36f640b993992e6912ea59027538a4b9a1aba96329cce292e686aee9a3b20548715a1abba6408f5151656774dbd9027338a49da1abba6409cce2871686aee98da7338a4b9a1abba6409cd0695c686ad299027341a715a1abba640b08e292e68feea59027338a4b9a0e3716409cce292e6912c8133a4a38a4b9a0cba96409cce292e6
  | 5, 2, 2 => 0x86aee99026f3784a5a1abba64099cd012e686af359027338a4b9a44bb46409cce29296774c8188a7338a46da1abba640960e292d686aee9903014e6345a1abba6409ccde92e686aee9902733743f1a0e3556409cce292e6912ee990273378491a1abba6409bce29246774d1da232057c7159dd3936329cce292e686aee990273430329a3dbba6409ace292e6
  | 5, 2, 3 => 0x912ee99025638a4b9a44c35640ab4e2903686aee9902b747a7159d4b946409cce292e686aee9902733c24b9a0e3204bc8c4e292e686b0659027338a4b9a0bb084e671497038686aee9902733664b9a1ab86640b2d1892e686b071902c94e64b9a0e3204e68a8d512e68f6d499027338a4b9800435774ba1398d15912ea59027336a4b9a3db194e6714971036
  | 5, 2, 4 => 0x86ac8139a4a3784a5a1abba6e8c8139a076000ea58ca7338a4a54004896409cccf12e586aee9902cb25c3f1a1abba640b98970c5686b0719027336a4b9a1abba6e8c813994c686aee9902733184b9a1abba640a8ce28e2686aee9902733403d1a1abba640bd554273686aee99027a38a4cd9dd3194e671497058686aee9902cb4e63dda1abba6409ccdd12e6
  | 5, 2, 5 => 0x86aee9902f7550595a1abba640b98970c4686aee9a332057c715a0bb206109ccd012e686ad299026c38a4b9a3dbaf6409cce292e686aee99016d25c299a0e4176409cce2916686af019027338a4b9a12bba640960e292e686aee9902be38a3e5a1abba640984e292e686aee9902ad38a389a1abba640aa0e28c6686aee98f2733784b99c73866409cce292e6
  | 5, 2, 6 => 0x774e29902e638a4b9a44ba96329cce2929686aee99024f38a4b9a1abba640b2d150e2691305d9027338a4599d4b116109cce292e686ae19902ab38a4b9a12bba6408f4e292e68f70d5902733404b9a44bba6409cce28fb686aee99024138a4b9a1abba640b50e292e686aee9902e646a4b9a44b204e66f08d103686add1a53204e68a9a1ab866407149708f6
  | 5, 2, 7 => 0x86ae199027338a4a5800435774c816292e5912c8139a1a38a4b9a1abba6408e0e292e686aee99028338a4b9a1abba640bed398d16838c65399c53544b9a1ab656408fce292e60010719026738a4b961abba6409cce293c686aee9902673864b9a1abba6409cce29126838da99027338a4b9a1abba640ab4c092e6862ee99027338a465a1abba6409ccec13c6
  | 5, 2, 8 => 0x86aee9901ea2ee4b99dd320622b2d2f12e686aee9902c32ca4b9a1ab3c640b993992e686aee9902733a84b9a1abba640bd53992e686b0718ca7338a4a5a1abba640aa1399fd68daee9902a54e6715a1abba6409ccb592e6860ee99027338a4b9a1abba5d08a8e28e2686aee99027338a4bda1abba6409cd000f76912da99027338a4b9a2cbba64099ce292e6
  | 5, 2, 9 => 0x86aee99023c38a4a5a23bba6409cce292e6912ee9902d53544b9a1abba640b2d5424a686aee99027341a81da1ab205d89cce292e686aee99027338a4c9a1abba6409ccfe12e686aee99027e38a4b9a1ab666409cce29166912ee9902733564b9a1aba0640b98b292e686aee9c3320550715a1abba6409cd0912e6890ee99027338a4b9a1abba6409cce28e76
  | 5, 2, 10 => 0x912c815f25e38a40da0bbee6409cce292e6832ed19027338a4b9a42b836409cce292e686aee99024338a45da1ab416408c4e292e686ad999027345440d9dd3194e6978e292e686aee9902c14e64b9a3dbba6329ccd912e686aee9902ad38a3a9a1abba640aa0e295e686aee9902be4e65fda1abba640bdcb292e686ae819027338a4b99dd3756409cce292e6
  | 5, 2, 11 => 0x86ad299026738a4b9a1abba6409cce291d686aee99026741a715a1abba6409cd0c11a686aee9902a438a389a44ba96409ccde129686aed18ca7338a4b9a1abbc6409cce292e6838c81399c523445180043563295ce292e586aee99025638a449a1abba640a7d150d16752c81399c525c0e9a1abba6409cd150d1687ce199027338a4b9a44ba96409cce29246
  | 5, 2, 12 => 0x8beee99027338a4b9a1abba640af8c50d16774c81399c527c3bda1abba6409cce412e686addd9027338a4b9a1abba640bb96a9c5686aee9902e64e63d1a1abf36409ccd012e68f6efd9027338a4b9a44c356409cce28f9686b0718ca5738a4b980047b6409cce29165774c817ea7338a4b99dd3a16409cce292e6774d11902be38a389a1abb46409e8e292e6
  | 5, 2, 13 => 0x86aed19027238a4b9a44c3563295ce292e6854ee99027338a4b99dd36f64099ce292e686aee99027938a4b9a1abb4640af8e28e26774e39902ad38a3f1a1abba6469cce2932686aee9902734324b9a1abba6409ccee13b686aee9902733fa4b9a1abba6409cce2938682eee99027338a4a5a1ab666409cce29176774c81339c525c0d5a1ac1c6409cce29246
  | 5, 2, 14 => 0x8f6c816c27338a4b9a1abba640aa1379c56912f8d9027338a4b9a44c35640b98af12e686aee99027344c341a1abba6409cce492e686ad299024738a4b9a1abba640a8d1e9c5686aee9902733104b9a30bba6409cd041c5686aee99028838a4b9a1ac1c640960e292e6912c81399c52ba4b99f7ba96329cce292e6744e199027338a4b9a283204e6714971036
  | 5, 2, 15 => 0x86aee9902a64e6715a0e41a6409cce292e686aee99025838a459a1abb66409b0e292e6774e39902ad38a4b9a1abb864099ce292e69130d59025838a4b9a1abba640becc892e6812ea58ca7338a4b9a1abba6409cce612e686aee99027338a46da1abba6409cc778d5686ad459027338a4b9a1abba6409ccc492e686aee9902cb4944b9a1abba6409cd0c0fe6
  | 5, 3, 0 => 0x86aee99027334a4b9a26bba6329cce292e686aee99023d38a459a1abba6409cce28fe69130699027338a4b99d4b194e68c0e292e686afe99027338a4b99dd38a6409cce292e686aee97424a38a4b9a1abba640b98c312e686acf19023538a4b99dd3194e67149491a60010d5af3205cc4b961abba640b98b28fe6912ee99027341a6a9a0cba96329cce292e6
  | 5, 3, 1 => 0x86aee99026f38a3f1a1abba6409bd0c12e686aee99027338a4799dd3204e6798e292e6768c458427338a4b9a0bbba64095ce292e686aed1902733784b9a1abba640a50e2955686ae159027338a4b99dd36f6409cce28f6686aee99027334e4b9a1abba640b2d5425e686aee990273450345a1abba6409cd108cd68f8ee98ca7338a4a5a1abf3640b54e292e6
  | 5, 3, 2 => 0x86aee9902734545fd9da3196109cce292e6774dbd9023f38a4b9a1ab206009ccd512e686aee99025838a45da1abba6409cce2915686ae199028e38a4b9a1abba6409cce292d6912c81339c53224b9a1abba6409cccf92e687eee99027338a3dda1abba6e8c81730fc686aee990273422469a1abba6408c506965686aee9b4b205aa4b9a1abba6409ccef92e6
  | 5, 3, 3 => 0x86aee9902733a04d9a1ab4a6409cd1517b686aee990273298355a1ab8664090ce292e68f6ee99027336e4b9a1abba676c8139a2a686aee99027332a4b99dd38e6409ccc392e686ad29902733144b99dd3616409ccbb92e686aee99027338a4f59dd34f6409cce28ef686aee99027341a6299dd3806409cce292e68f6ee9902ab38a4b9a1abba640900e292e6
  | 5, 3, 4 => 0x86af6d9027338a4b9a12bba6409cce292e686aee9902a54e67159dd36f6409ccc512e686aea58ca733784b9a1ab4b6409cce292e686b0719025a38a4b9a1ab86640b68e292e68f6ee99027338a4a5a1abba632b50e292e68f6ee98ea7338a4b9a44c1a640958e292e60010d5dd3205963f15dd3536409ccd012e68d2ee99027338a4b99b0b5e6409cce292e6
  | 5, 3, 5 => 0x86aee9902be38a369a1abb764090ce292e6774e759023d38a4b9a1abba6409cd150cc686aee9902a338a371a1abba6a8c8139a18686aee9902a84e61d5a44c356409ccd011668f6c813324a38a4b9a1abba640b54cd92e686afcd9027341a715a1abba640af8e29526876ee98ca7338a4b99dd3194e67148d0ef686ae699027331c4b9a1abba5469ccbb8d16
  | 5, 3, 6 => 0x86aee9902432ee4b9a133a96409cce292e686aee98fa7338a4b9a1abba6409cd039776774dbd902e64e63dda44ba9640aa1399c5686aee9902bc38a385a1abba6409ccd212e686aee9902ad38a371a1abba640960e912e686af99902734304b9800435774c8156981586aee97425e38a4b9a1abba6b2c8156a18686ad29902b14e6715a1abb86409ccc512e6
  | 5, 3, 7 => 0x86aee9902313143f1a1ab666409ccbb92e6774c65399aa2ee4b9a1abba640ab0e2903686b071902a84e6715a1ab20610aa1251c5686af999027338a4b9a1abba640bd55f0e2686aee9acb2055a7159dd353640b54e292e686aee99016525c279a1abba6409cce294a686aee9902733a24b9a1abba640b40e292e686aee98ca7338a4c9a1abba6409cce29356
  | 5, 3, 8 => 0x10d58ca5838a4b961ab86640acce292e686aee9cb320550629a44ba9640b98b292e686ae199030538a4b9a1abba6409cd0699b6774c652f23038a4b9a0e3a96409cce292e682ed999027338a4b9a1ab66640b992192e68f707d9025838a4b9a1abba640aa0e29656912ea5902734304b9a1abba640910e292e686ad99902e625c3899dd32057ca14e292e6
  | 5, 3, 9 => 0x86aee9902a8490715a1ac1c640b98b292e68f6c81399c531e4b99f43ba6329cce292e686aee9902ad36a4b9a44c7c6409ccd012e6912c81399c533c4b9a1abba6409ccd01296912ea59027338a4b9a1ab86640960e292e686aed19027338a4cda44b204e66809711a686aee9902313144b9a1abba6409cd150c9686af99902ac38a4b9a1abba5d0af9398d16
  | 5, 3, 10 => 0x86aee9902a438a3bda44c1a6329cce292e686aee99027332c4b9a1abba64099cc512e6774c6539a5e3784b9a1abba640b98b2916686aee99024325c1cda1ac1c6409cce292e69130d58ca5838a4b9a1abba640b98c192e6774c817ca7338a4b9a1abba6409ccde132686ad458ca7338a4b9a1abba640714b2955686aee9902733164b99dd38e640b54e292e6
  | 5, 3, 11 => 0x86ad99902ad38a4b9a44b204de714c792e6912ea59025638a4b9a1abba6408d4c092e686aee9902733764b9a1abba64071471092682eee99027338a4e5a44ba96469cce292e6774d91b0b205cc4b9a1abba6409cce28f0686aee9902c538a4b9a44b836409cce292e686aee9acb205487159dd3194e6714970ff686ac81842be38a371a1abba6409cce29166
  | 5, 3, 12 => 0x86aee99027238a4b59f4ba96329cce292e686aee9902e63d44b9a1abba5eaba13992e686aedd9026e38a4b9a1abba6409cce212e686ae199027338a50da1ab205609cce292e686aee9902733864a5a44ba96409cce012e686ae19902e638a3f1a0bbba640960e292e686aecd9027338a4b99d4b194e6928e292e686aee9902cd2ca4b9a1abba6329cccf92e6
  | 5, 3, 13 => 0x86aee9902433c84b99d4b194e67149705b6838c81399c525c491a1abba6409cce294b68daee99026638a4b9a1ab194e6928e292e66f8dbd9027338a4b9a3dbba6329cce292969130d59025638a4b9a1abba6409ccfe8f7686ae19902e638a4b99903026009cce292e6774dd1a9b204e68a9a1abba72cc81730f7686aee99027338a45da47ba96329cce292e6
  | 5, 3, 14 => 0x86aee99027341a6bd9dd3204e6768bb92e686aee99026d38a4b9a3db204e66a8c892e686aee99e3204e68a99dc38e6409cce292e686aee9c33205964b9a1abba640ab4e2924686aee9902673024b9a1abba680c8182a736774d11902be4e6715a1abba640be8e292e686aee99027138a4b9a1abba640af8e28e8686aee98c27338a4b99dd320622998e292e6
  | 5, 3, 15 => 0x8f6c81331c53224b99dd36f6409cce2929686ad79902e638a4b9a123ba6409cce292e686aee9902733a44b9a1abba640b2d53273686aee99027038a4a5a3db204e6644bb92e6912ed19027338a4b99dd320632998e292e686aee9a232057c7159903194e6714970ff686aee98ea7338a4ada1abba640a40e292e686ad299027338a4a5a1abba640ae0c512e6
  | 5, 4, 0 => 0x838ea58ca7338a4b9a1abba640bd52512e686aee99027338c4b9a1abba640c152192e686aee9902c65509cda1abba6409bce28f76912c81379aa3224b98003a96329cce292e5912c812423138a4b9a1abba6409ccd31166774d4d9023d3024b9a0bbba6409ccd0116686aee9902733444b9a1ab206329cccf92e686aee9902fe3e67159d4b194e6978e292e6
  | 5, 4, 1 => 0x86b0059025738a4b98004196409cce292e5912ea58ca7338a4b9a1abba640b84c512e6774e399023138a4b9a1abba640b3cd512e6708c8188a7338a4b9a1abba640b98b192e686ad99902733404b9a3dc1f6409cce292e686aee99026438a4b9a1ab866409cce28fc6774c817b2a84e6715a3db204e6714c812e686aee9902cb5284b9a1abba64099cda9246
  | 5, 4, 2 => 0x86aee99028038a4b9a44ba96409c8e292e686b0718ca7338a4b9a0bbba640aa1399c5686ae199027338a4b9a0bbba6589cce292e68390659027338a4b99dd3194bc928e292e687eee99028938a4b9a1abba6409cd148d1686ae19902e62ca4b9a1abba640bf939981686aee9902d536a4b9a1abba640a04e29166774c81399c527c4b9a1abd86409cccb92e6
  | 5, 4, 3 => 0x898ee99027338a4b9a1abba6409ccda927686aee99023d38a1c19dd32062299cda92e682eee9902734304b99dd3194e6920e292e686aedd9027338a4b9a1aba76409cce292e686aee98f26f38a4b9a1ac1c640af8e28e2686aee98ca7338a4599dd38e64099ce292e686aee9902be3f6715a44c196409cce292e686cee99027338a4b9a1abba6409cc970d56
  | 5, 4, 4 => 0x86ad999027338a49d9903194bc928e292e686aee99027337e4b9a1abba640ab5541c56774d3d9027338a4b9a0fc176329cce292e686aee9902ad38a4a1a1ab8c6329cce292e686aee99026638a4b9a1ab5e6409cce292e6912f959027338a4b99dd3206049ccc892e686aee9902583404b9a1abba72cc81828d16774d4d902733f4715a1abba6409cce28d46
  | 5, 4, 5 => 0x86ac818ca7338a459a1abc46409cce292e6774e39902b838a4b9a3e3ba6329cce292e686ac8184273454329a1ab196229cccf92e686aee9902733824b9a1abb06329cce292e686aee9902734543499dd36f64090ce292e686aee9902d538a491a1abba6409cd018c66000ed18ca7338a4b961ab66640b993992e686aee9902ad4303f1a44bd36409cce292e6
  | 5, 4, 6 => 0x86aee9902cb58a4b99dd3926409cce292e6714c818427338a4b9a18c1c6409cce292e686ae119027338a4b99dd3206229cce2923686aee9902f5546389a1abba68ec815f17a686aee9902ad38a4b9a1abba6e8ba13992e686aee9902d141a715a1ab20610b2d2512e6752dcd8ca7338a4b9a1abba6409cce112e6838c81399c52c24b9a44bb46329cce292e6
  | 5, 4, 7 => 0x86aee990273412715a1ac01640960e292e686ae198ca7338a4b9a1abba640c14b88e268f6f499027338a4b9a1ac1c64095ccf92e60010658ca7338a4b961ab206109cccf92e68f707d8ca7338a4b9a1ab194e6714949036912ee99027338a46da1abba6409c4de12e682efd99027338a4b9a3dbba640b98b292e686aee99028438a4b9a1ab86640af8c512e6
  | 5, 4, 8 => 0x8f6c8157a7338a4b99dd3194e6998e292e6774c81812e62ca4b9a1abba640ab4e29206838c81399c525c161a1abba6409b0e2924686ae659027338a4b9a1abba6409cce28fd686aee99027338a5099d4b194e6714970ff686aee9b23205cc4b99d4b194e67149701c686aee9902be38a385a44c196329cce292e69130d5902a8494715a1abba64099cda92e6
  | 5, 4, 9 => 0x8c8ed19027338a4b9a1abba6409cceb92e682eee99027238a4b9a1abba6409cd1aa2a686aee99030538a37da1abba6409ccc112e686aee9902733404b9a1abba632998e292e66f8d4d9027338a4b9a1ab194e6714970ff686aee9902e61f83219dd3206049cce292e686aee9902733403f1a0e3204e6714970ce686ac65399c52063bda1abc9640960e292e6
  | 5, 4, 10 => 0x86eee99027338a459a1abba640b99218f76774c81399c525c2e9a1ab206109cce29166774e498ca7338a4b9a1abba640b98fd0c66912c8139a4838a4a5a1abba64090cc512e6622c21399c525c3fda3dbba640998e29236752c65399c525c345a1abba6349cce292e686aee9903051c4319a1abba6409cd071c56786dbd9027338a4b9a1abba640a38c512e6
  | 5, 4, 11 => 0x838c81399c5228441a1ab194bc928e292e6774dbd9027338a4b9a1abba64090cc092e686aee9902ad4303dd9dd32063299ce292e686aee9902d94e63dda1abba640c15398ce686ad299027338a4b9a1ab866409ccef12e686ad29902e62ca4b9a1abba640ab4e290e686ac81399c525c3759dd32062299ce292e686aee9902ff38a389a1abba640b54970d16
  | 5, 4, 12 => 0x86aee9cb320550715a1abba640b98e28e668f8ea58ca7338a4b9a1abba6409ccea92e6752c65399c525c015a1abba640af8d00e26622c212f24a38a4b9a1abba640c14e28e2686aee9902ad38a505a44b204e6714970546912db19027338a4b9a1abba6409c0e012e686aee98ca733404b99dd3204e6764e292e6000ee9a232057c71561abba6408f4c512e6
  | 5, 4, 13 => 0x838c81399c525c3fda1abba65c9cce292e69130d59025838a459a0bbb46409cce292e6774c097427338a4b9a0bb204e671497019686aee990273454129a1abba640af9398d5686aee99026738a4b99dd32050a8c4e292e686aee99023d3024b9a3e4196409cce292e686aee990a7338a4b9a1ab116109cce291668a0ee99027338a4b9a1abba640af8e28e56
  | 5, 4, 14 => 0x8f6ed19027338a4b9a44c7c640960e292e686aee9902e64e63dda1abba640b98778c6686aee9902733144b9a1abba6409cd150cd686aee9903054e63199dd36f640af8e28e2686aef59026738a4b9a1e3ba6409cce292e686aee9903052c24b9a44bba640998e292e6774dbd8ca7338a4b9a1ab866409ccdd12e6912c81399c525c3fda44b8a6409cce292e6
  | 5, 4, 15 => 0x8f6ed18ca7338a4b99d4b194e67149703b688cee99027338a4b9800435774c811aa2a586aee982ae838a3899dd3194e6714971236774c458426738a4b98003ba632998e292e586aee9902be548715a44bba64099cda92e686ae19902d53144b9a1abba63299ce292e686aee9902e838a389a1abb464099cda92e6774e39902733524b998ca7338a6a8c792e6
  | 5, 5, 0 => 0x21abba6329cce292e6000c65399c525c0ed61abba6469cce292e6914ea59027338a4b9a1abba6409cce292e68f70718ca7338a4b9800435774c81828c658f70719027338a4b9a1abba6449cce292e6924ea58ca7338a4b9a1ab194e6714971146752c65399c525c171a1abc16409ccc512e6768dbd9027338a4b99da32062299ce292e6
  | 6, 0, 0 => 0x86aee99027338a4b80e3c35774c8165a7325c16dc00435640ab4e292e070d2261ac1a6409cce292e786aee9902a84bc71497380086aee9902cb5509cd800435774c8139a2a19cd0d5fc3ba6409cce29177912ee9d4b204e66f0973c35774c811ea2a38a4b9e1abba6409cce291a116f0d5dd3a96409bce292e786aee9c53204e6714973c7c86ad999027338a4b9c003a9640c65399c525cc0021abba6406549707b6
  | 6, 0, 1 => 0x10d5e2b204e6714973435774c815d27338a4b9e1abba640c35399c525cf0d5dd3204e67149704e70010d5dd3204e66f0973435774d799027338a4b9e1abba6409cce292e0eee0023dbba6409cce2923686afb5da3204e6714973c35774c81399c525c201e1abba6409cd1519125cf0d5dd3204e6714970ff7774c8188a5e494714973bba6dec81399c525c2c9e1abba640b8d339c525cf0d5dd3204e67149706b7
  | 6, 0, 2 => 0x86b071903114e6714973c35774c815f2a84e6715e1abba6409cd379c525cf0d5dd36d6409cce28f479131f1dd3204ce714973800774e39399c525c16da1abba6409cce292e1c2f0d5dd32057c98ce292e7912ea5902e64e6714973c35774d519027338a3bde1abba6409cd0c21825cf0d5dd3204e66a897073782eee9dd3204e671497380086aee99027316425da1abba6409cce292e022f0d5dd3205289cce292e7
  | 6, 0, 3 => 0x10d5dd3204e67b0973435774dd1902e64e64b9e1abf8774c81389c525cf0d5f83ba6409cce292e786aee99027338a4b806bc35774c8139a2a25c319e1abe66409cce292e1def0d5c33204e6714970e2786aee9ba3204e671493bc35774c81399ef38a4b9e1abba6b2c81569c51def0d5dd3204e67149706d786aee9cb32057c7148d3c35774c81569c53544b9e1abfe774c8139a2a1a2e0021abba6409cd0c0f76
  | 6, 0, 4 => 0x8f6ee9c4b204e6714973c35774e7d902733144b9e1abb46409cce292e072f0d5dd3716409ccbb92e786aee99027338a660973c35774e599023138a3f1e1ac29774c81399a625cf2421abba6409cce292e786aee9902d53225dc973c35774c8184273454345e1ab9a640af9399c525cf0d5dd3204e6978e28f778b6ee9c73204e6714973c3583eee9902733404b9e44ba9640c65399c525cf0d5dd3206069cce292e7
  | 6, 0, 5 => 0x86aee990273430714973c35838c817327338a4b9e1abba6e8c8139a0d38af0d5903085cc928e292e79130d5dd3204e66f0973c35774c816ba7338a4b9e1abba6409cce2948234f0d61abba6409bce292e786aee9903114e67148b3c8286aee99027338a491e1abba640b55069c525ce0021ab866408c4e292e686aee990267462714973c35774d659027331c4b9c0047b6409cce292e070d0d5dd32055a714bb92e7
  | 6, 0, 6 => 0x86aee9902cb4e6978973800774c81399c5252071a1abba6409cce292e10ee0021abba6409cce28f7686aee9902be38a4b8293c35774c81399a025c1edc004896409ccd519125cd0d5dd3806409cce292e786aee99027338a4fc973c3570cc819027338a4b9c00435768c81399c5248c00230bba6409cce292e686add1a53204e6714973c7186aee99027336a4b9e1abba6ccc817327325cf0d5dd3204e68610992e7
  | 6, 0, 7 => 0x10d5903084b0714973435774c81731c52ca4b9e3dbba6409cce29aa25cf0d5dd3205269cce292e786b0b5dd3204e6714973c35774c81659c525c389e1abba6409cce2924234f0d5dd3204e6714970c0786ad65a53204e6604973c35774c815427338a345ddd3206229cd241c525cf19a26bba6409cce292e786b071903194e6714973c35774c816427338a4b9e1ac03774c81219c525cf0d5dd3596409cd069817
  | 6, 0, 8 => 0x8f90d5dd3204e6714923c35774c8165a4338a4b9c004357749cce29290b6cee9ba36f6409cce292e786aee99027336a4b881bc35774c815927338a4b9e1abba67ec81399c525cf0d5dd3204e6760e292e786aee9902be4e67147e3c3570cc81399c525c25de1abba640b99399c522cf0d5dd3204e671492038786aee9903074e6714973c896409cce299131e4b9e1abba72cc81189c525cf0d5dd32057c9cd0c12e7
  | 6, 0, 9 => 0x86aee99027338a4b8283c3584aee99027338a4b9e3dbba6409cce297725cf0d5dd3204b07149711a70010d5dd3204e67148cb47086aee99027338a4b9e1abba6409cd099c525cf0d5dd3204e6714e292e786aee9902874e671497380086aee9902d525c25da1abba750c81399c525cf0d5dd3204e689ce292e70010d5dd3205969cc97347186aee99024338a4b9e42435774c81399c51eef0d5dd3204e6714970537
  | 6, 0, 10 => 0x86aee9902734547d868bc89752d659027338a4b9e39435774c81399c525cf2261abba6409cce28f77001225dd3204e6714923435774c814527338a4b9e1abba640a35399c525cf0d5dd3204b071497038786aee9902674ce714973c5b86aee99027338a4a5e1abba6329cce299125cf0d5dd3204e6834f99c578c50d5dd3205aa714973c35774e59902e63144b9e1abba640b995f16525cf225d4b204e6714970ef7
  | 6, 0, 11 => 0x86aee99023d38a4b88d380086aee99026f38a4a5a1ac1f774c816a9c525cf0d5dd32057c9cce292e786aee99027338a55897380086ac8139a4c38a4b9a1abba640b69399aa25cf0d5dd36e6409cce292e786aee9902e04e6644973c35774c815727338a3dde3e435774c812c1c525cf0d5dd3206029cce292e786aee99024338a4b8213bba6ded999027338a4b9c004356409cc97097070c0021abba6409ccd00b26
  | 6, 0, 12 => 0x86aee99027338a57c973c17774c81399c525c389e1abba6409cce28fc1a2f0d60fc066409cce292e786aee99023d38a4b81c3c89774c81399c52c24b9e1ab4c694c81399c525cf0d5dd3204e6860970d1786aee9903174e6714973c35774c8182a2a2ca4b9e1abba6409cd199c525cf0d5dd3204e6714970b570010d5dd2e84e6714973435774c8139a432ee4b9c00431774c81399c525cd0d5dd359640a8d399c57
  | 6, 0, 13 => 0x86aee990273454714c0bc35774d65902ad4e6715e3e435774c811e9c525cf0d5dd32057c714c88e279130d59027338a4b86e3c35774e599026738a4b9e1ac1c6409cce292e1def2260fb204e6978e292e79130d5dd3205969cc973c35774d759027338a4b9e38c356ccc81399c525cf0d60fbba6409cce192e786aee9902e6490714973c35774c8166a7338a4b9e1abba6409ccbd12e1c4f0d5dd3204e6714bc92e7
  | 6, 0, 14 => 0x86aee9902e62ca4b868bc89774c81379c53544b9dacb53694c81399c525cf185dd3204e6714b992e786aee99027338a4b8763c4c774c81399c525c25de1abba6409cce292e078f0d5dd3205aa7149707b786aee990273454578973c35838d659027338a4b9e27435774c81399c525ce0021abba640af91e9c5686afbddd3204e68a868bc35774c8139a1c38a4b9e1abba640a60e292e14cf0d5dd3204e6680970cd7
  | 6, 0, 15 => 0xed1903114e67149734357b2c81399c525c2b1e1abba746c81399c525cf0d5dd3205eeb2d3992e786b07d903084e67148b3800912ea5901c525c1ed800435774c80e292e0ccd191dd3a96409cce292e786ad999027338a4b8213c3581eee99027338a4b9e1abba6409cd291c525cf0d5dd32057c928e28dc786aee99027338a4b8043c35774c81399c525c0a1c003ba71cc815f1c525ccee9903115cc9ccd512e7
  | 6, 1, 0 => 0x86aee9acb204e67148b3c35812ee990273454345e1abba6e6c65399c525cf0d5dd3204e671497071786aee9902733ac714973c35774c813998a25c0f9e1abba6409cce292e1a2f2361abba6389cce292e70010d5dd31e4e6714973435774c815f1c51c4319e44c35774c81379c5252f0d5dd3204e67148b0ef786aee99027338a4b811bc35774c81399e338a4b9e1ab666409cce292e206f05ddd3206409cce292e7
  | 6, 1, 1 => 0x912ea5d4b204e6714973c35774d65902be494715e1abba6409cce292e21af05ddd3204e67149709778f6ee9dd3204e6714973c35774c81399c529c4b9e3e435774c81371c525cf165dd3204e67148d103786aee990273448714973c35774c8139a1138a4b9e1abba640ab4e292e170f0d5dd3205509cce2965786aee99029f38a4b868bc35774c81399c528e4b9ddd3206229cce292e234f0d5dd3204e6714970347
  | 6, 1, 2 => 0x86aee9902733544b80b3c35774c81399c51ee3dde1abba6408c4e28ef1c4e0021ac1c6407149707b60010d5dd3205aa7145934896409cd251c53544b9e1abba6409cd101c525cf0d5dd3204e66049709c786afe1c33204e6714973c7c774c8188a7338a4b9c00435774c815424a38ad0d5dd3205ba960e292e786aee9902bf4e6714973c35774c81399c525c1d1e1abce774c81399c525cf0d5dd3204e6714c912e7
  | 6, 1, 3 => 0x10d59027338a2c81c300086ad299027325c25da44c356409cd251c5252f0d5dd3204e68c4c512e786aee9902a84e68a8e2b80086aee990273414715a1abba640c21379c525cf0d602bba6409cce292e70010d5902733404b81c3435774c81339c525c2c9e2bbba6409cce292e206f0d5dd3204e6714a012e786af89dd3204e6714973c35774c81399c525c00de1abba6409cce29c025cf0d5dd3204e6714970137
  | 6, 1, 4 => 0x86aee9902cb4e64b833bc35774c8139a4a30a4b9e1ab656409cce29aa25cf0d5efbba6409cce292e786b071d4b204e671497380086aee9901c522c1eda1abba6409cce292e092eee9903194e67149711a70010d5dd3204e6778973435822ee99027338a4b9e1abba6409ccf41c525cf1921abba6409cce292e786aee99027338a6b8973c35774c81399c525c329e1abba6409ccde19125cf2261abba63c9cce292e7
  | 6, 1, 5 => 0x86ac8139a4a38a4b80cbc3583ed299027338a4b9e1abba6409cce29651f8f0d5dd3204e67147b8f2786aee9902fb4e6714973c7186aee99027338a491e1abba6409cd0c16525cf0d5dd3204e66a8d012e786b07ddd3204e6834e2bc35774c81519c525c389e1abba694c811e9c525cf0d5dd3204e67149700e7774c81399da38a4b81c3c35774c8139a1825c31dc0047b6409cce292e206d19e1abba6409cce292e7
  | 6, 1, 6 => 0x86ac8184273494714973c89774e4d9027338a4b9e1abba6aec81399c525cf0d5dd3a96409cce2916786aee99027338a4b855b80086aee99027338a4cda44bba640b992f1c525cf2261aba96409cce292e786aee99027338a52026bc35774c81399ee38a4b9e3d435774c81399c525cf0d5dd3204e6714a4103786aee99027338a4b86db800774dbd9027325c25da3e3ba640c65399c525cf0d5dd3786409cce292e7
  | 6, 1, 7 => 0x86aee99027338a4b8033c35774e59902733143f1e1abba6409cd069c50f6f0d5dd3204e6860970eb78e30d5dd3204b0714973c35774dd199a7338a4b9e1abba640b98b296525cf0d5da3204e6928e292e7000ee93992e12e16c0e300086aee99026025c25da1abba64ec81399c525cf0d5903194e6714c892e786aee9903054e66a8973c35774d9d9027338a4b9e1abba640c2152a7338af0d5dd32038a4b8710a67
  | 6, 1, 8 => 0x86aee99027338a4b863bc35774c81399c52ec4b9e1abba736c81399c525cf19a1abba6409cd150d1786aee9902734404b868b80086ae19902733144b9a1abba6409cd151c51f8f07ddd36f6409cce292e790d1eddd3204e6714973c35774c81399c53223ddddd39f6a6c81399c525cf0d5dd3204e671497027786aee99025e494714973bba640c455b27338a4b9e1ab4a6409cce292e0f6f0d5dd3204e6714921037
  | 6, 1, 9 => 0x86aee99027338a4b8553c35774c812c1c525c40de2f435774c81399c525cf0d5dd3204e67149708a786afdddd3204e66d497380086aee99027338a3c5a1abba6409ccf49c525cf05ddd3204e6714d012e786aee99032055a714973c35774c8139a1b38a4b9e1abba6409cce292e126f0d5dd32053e714970c7786aee9b83204e671497380086aee99023a38a4b9a1abba6409cce292e16ef0d5dd32057c9cce29207
  | 6, 1, 10 => 0x912ee99027338a4b82c3bba6e8dbd902734544b9e1abba6409cce292e224f0d5dd3205969ccc892e782efe1dd3204e6714973c35774c81399c525c305e1abba6409cce29a625cf0d5dd396640ae0e292e70010d5902d538a4b81c3000774c81399b525c071800435774c812d9c525cd0d5deb204e671497008786aee98b3084e6714973c35774dd19026738a4b9c003204e671497104038d0d5a9b4a6409cce292e7
  | 6, 1, 11 => 0x10d5dd32052a714593435864ee99027338a4b9e1abba6409cce292e014f0d5dd3203e07a8e292e786aee9a93204e671477bc35774c815127338a4b9ddd39d6b2c81399c525cf0d5dd3205189cce292e78f6ee99027338a4b8713c35774da19027338a4b9e1abba6409cce292e086f0d5dd3204e6714818ed786aee9cb3204e6628973c357b4ee99027338a4b9e1abba6409cce292e1d6f0d5ea3204e6714970957
  | 6, 1, 12 => 0x86aee9902d538a6a897380086aee98ca733784b9a1abba6409cce292e150f111dd3204e67149711a7001225d4b204e671494b417774c8139a5838a4b9e1abba6409cd1012e194f0d60a3ba6409cce292e70010d5dd27336a4b82db00086aee990273410715a1abba640af9399c519ce0021ab4a6409cce28b2686afbddd3204de714973c35774c813992e1081d5e1abba6329cce292e038f0d5dd3204e6714d592e7
  | 6, 1, 13 => 0x86aee99027338a4b885bc7b774c819027338a4b9e1abba6329cd379c525ce0021abba6408f5151c5686afa9dd3204e6714973c5b86aee99027336a4b9e46c35774c81399c525cf0d5dd359640af92f1c5786aee99028b4e6714973c35768c81399c525c16de1ac1f792c81399c525ce001dd3204867149701c686ae19903114e6714973c35774c8184a7338a4b9c00435774c815f1c51b8d0d5ee3ba6409cce292e7
  | 6, 1, 14 => 0x86aee9dd3204e6680973c35774c816a9c52ee4b9e1abba640af8e28e2038e001dd36f6409cce28b2686aee9902733fc714973c35812ee99026f38a4b9e1abba6409cce297f25cf0d5dd32057c714c512e786aee9902a84e67148d3800838c81399c53544b9a1abf1774c81399c525cf0d5dd3205ac9cce292e70010d5dd320550978e2b435774c812c1c52c04b9e1ac1c632c45399c525cf0d5dd3204e6714970267
  | 6, 1, 15 => 0x86afe5dd3204e6714973c257deee99027338a4b9e1abba6409cce2929166f1f21abba640aa1399c5786ae19902e64e67149738007749cce28b20b6071a3dbba6409cce292e12ef0d5dd3204e68c4c092e78b2ee99027338a6a8973c35774c81399c521225dc0043577490ce292e0b6d0d5dd3205509cce2838786aee99027338a4b85ebc3582eee99025838a4b9e1abba6409cce292e052f0d5dd3204e67149912e7
  | 6, 2, 0 => 0x86aee9bf3204e6714973c35774c8137a3038a4b9c003666409cce292e038d0d5dd3204e6714970bc78b30d5dd3204e671494bc35774c81399c525c105e1abba6409cce296225cf0d5dd3204e6628970b2786aee99027338a5bc973c35694c81399c52f64b9e44c35774c65399bc25cf16e1abba64090ce292e786aee9b23204e65dc973bba73ee399027338a4b9e1abba676c81399c525ce001dd3204e67149705f6
  | 6, 2, 1 => 0x86aee99027325c3bc51bc35774c814a9c525c289e40435774c81399c525cf0d5dd3204e68a8970d1786aee9902df4e6714973c356c8d799027338a4b9e1abba640b55671c525cf0d5dd32057c7d8e292e786aee9902d138a5d4973c35774cd59027338a4b9e0d417774c81399c525cf0d5dd3204e6880b292e786aee990273448714673c35774c81399d02ee4b9c00435774c8139a2a18cd0d619bba6409cce29197
  | 6, 2, 2 => 0x86aed1902734bc7149738008f6ee9902733644b9a1abba640a6d399c525ce0021abba6409ccc292e686aee99027338a4b8313c35774c81399c525c025e1abba74cc817316525ce0021fbba6409cce292e686aee990273400644973c35774c813ea7338a4b9e1abba6409cced9c525cf0d5da3204e6714da92e786aee9943204e6714973c35774c8139a1125c3ade1abba6a0c81399c525cf0d5dd3206089cce292e7
  | 6, 2, 3 => 0x86afe1dd32055a71497380086aee9901c525c241a41435774c81399c525cf0d5dd3205cc9ccd512e786aee9d33204e6714973c35774c81399c51f80e1e2dc356ccc81399c525cf0ea1abba6409cce292e7912ea5903084e6714973c35774c814127338a4b9e1abba6f2c81399c525ce001dd3446409cce292e686aee9c7b204e6714973c35774e59902e138a4b9e1abba6409cce291a1f8f0ce18bba6409cce292e7
  | 6, 2, 4 => 0x82eee9903114e671497380086aed19027338a4b9a1abba6409cd141c525cf071dd3204e6978e292e786aee99027338a4b8363c35774c818927338a4b9e1abba6409cce292e15ef0d5dd3205c09cce292e786aee9902e62ca4b88d3c35774c816a97725c345e1abba640c41399c525cf1f21abba6409cce28fc786aee9902733b84b816bc35774c81399bc25c071e1abba6409cd0012e18cf0d5dd3204e67149703f7
  | 6, 2, 5 => 0x10d60e3204ae714973435694c81399c53544b9e1abba6409cce292e234f19a1abba6409bce292e78f90d5dd3205cc594973c89774c81399c536a4b9e1abba6409ccec12e070f0d5e5bba6409cce292e791b0d5dd3204e6700973c35774c655f27338a4b9e1ab82694c81399c525cf0d5dd3206229cce29147774d4d90273462714973c35774c81311c525c2c9e1abba6409cd1512e194f0d5dd3205cc594970387
  | 6, 2, 6 => 0x90f0d5dc3204e6714973c3570cd659027338a4b9e1abc36409cce292e084f225dd3204e6978e292e786aee99027338a4b802bc35774c81399c525c179e1abba72cc813998125ce0021abba64099c97097686aee9afb204e6714973c3578eee99027338a4b9e1ab59694c81399c51def0d6033ba6409cce292e786b071903084e6714973c35774c8139a6f3784b9e1ab866409cce292e1dee001b7b204e6714970386
  | 6, 2, 7 => 0x86aee99027338a4b81bbc17774c817327338a4b9e1abba6409cce292e056f0d60ebba6409cce292e786aee99027340671471380086eee99027338a4b9a3e435774c81399c525ceee99027338a6a897035786b0719027338a4b876bc357acee99027338a4b9e42435768c81399c525ce001399c525c16c1c01c686aee9902be38a4686fbc7b774c818327338a4b9e1abba6e8c813998a25cf0d5dd3205349cce292e7
  | 6, 2, 8 => 0x86aee99027a38a4b804380086aee990273430345a1abba6409cce28f7038f0d60fbba64099ce292e786aee9902a64e6714973c8986aed19027338a4b9e1abba640960e292e22cf0d5dd3206109cce29167774dbd9027338a6a8973c7b7f0ee99027338a4b9e1abba640af95f1c51c4f0d5dd3204e6714b812e78930d5dd3204e6714973c35774c8139a1e38a345e1abba6409cce29221def0d5dd3204e6680970e27
  | 6, 2, 9 => 0x86aee99027338a6e4973c35774dc1902734544b9ddd38e6409cce292e07cf0d5dd3204e68a8b292e786aee9902924e6714973c35774c81399c52d44b9e1abba6329cce292e1a2f0d5dd3204e6714970ad786aee99027338a4b84c3c7186aee99027338a4a1e1abba640c2d399c525cf0d5dd3204e65b4970b2786aee99027338a5d0973c35774c81339c525c1f1e1ab47682c81399c525cf0d5f63ba6409cce292e7
  | 6, 2, 10 => 0x86aee9902ac38a4b88d3c4386aee99027338a4b9e1abba6409cce292e186f0d5dd3204e68b8e292e786aee99026738a4b83db8008a0ee99027338a2c9800435774c80e292e0f4c001dd3204b07149701c686aee99027343a714973c35774c8139a2a3d24b9e1abba640b813992e1a2f0d5dd3206409ccd012e70010d5dd27338a4902db435774c81399c525c3f9e1abba6b0c81399c5252eee9b7b204e6714bb92e7
  | 6, 2, 11 => 0x86aee99027338a4b83ebc35850ee99027338a4b9e1abba6409ccc092e164f0d5dd396640a80e292e7912fbdd4b204e6714973c5b86aee99027338a491e1abba6408c4e292e1bef0d59027338a4b82e856786aee9ba3205cc9cc7bbc35774c81399912ea4b9e49435774c81399c5252f0d5dd38c6409ccc292e78e30d5dd3205509cce2bc35774c8139a2a38a339e1abba66cc81399c525cf0d5dd3205969cc9701c7
  | 6, 2, 12 => 0x86aee951a7338a5dc973c35774c816a9772ca4b9e1abba640b793999125ceee9cb3536409cce292e786afb9dd3204e671494bc35774c81399d625c0e1e1abf4640c21399c525ce001dd32047a7149701c686aee990273410714c8bc35622c2139a4a38a4b9e1abba640af8e28e21a2e001dd36f640b993992e686aee9902733404b84bb80086aea58ca7338a4b9800435774c80970d50f6d0d5dd32057c9cce290e7
  | 6, 2, 13 => 0x86aee99027338a4b8173c35774c815f27f38a4b9e1abba640af9399bc25cf0d5dd3204e67b0e292e7913025d4b204e6714973c1f82ec818427338a4b9e1abba640b75399c525cf16e1abba640960e292e786aee99027345a714973c35774c81399c525c4b5e1ab8c640c21399c525ceee9c73204e68c4e292e786aee9902b64e6714973c356409cd261c525c071e1abba6469cce292e00af0d5d4b866409cce292e7
  | 6, 2, 14 => 0x86aee992b204e6714973c35774e399023138a4b9e1ab866409cd399c525cf0d5dd3204e67149706579110d5dd3204e6714973bba71cc81399c525c3e9e44bba6409cce2929234f05ddd3596409cce292e78f70d60fb204e6714973c35774d299027338a4b9e1ac1c7dec81399c525cf0d5dd320622ab4e292e786ad299027338a4b8243c35852ee99025b38a4b9e1abba6409cd269c525cf05ddd3204e6714970ef7
  | 6, 2, 15 => 0x86ac81399d038a648973c35774c81399c538a3dde44c7c774c81399c5252f0d5dd3204e67148b020786b005dd3204e6714973c8989aee99027338a4b9e37bba752c81399c525cf2259027338a6a8c892e70010d5dd3204e66e89733ba640c456f27338a4b9e38c35774c81399c51f8eee9ba36f6409cce28f778e30d5dd3204e686097380086aee9902733c24b9a44c35752c65399c525cf16e1abba6408f4e292e7
  | 6, 3, 0 => 0xe39c33204e6714973435774c81399cf38a4b9e31c35774c813998125cf0d5dd396640b2d1892e786aee98ca7338a5d8973c35774c81399c529a4b9e3a435774c81399c525cf0d5dd3416409cce292e786b00ddd3204e6714973c35774c81902d538a4b9e1abba6409cd081c525cf0d5dd371640b993992e786aee99027345434467380086aee9902a338a389a1ac1c812c81399c525cf0d5dd32057c9cce294f7
  | 6, 3, 1 => 0x86aee99027338a4b812bc3570ce0d9027338a4b9e1abba640945189c525cf0d5dd3204e68c4e2929786aee9b13204e6714973c35774c8139a2a1a2219e1abba640af9399c51eef1f21abbd6409cce292e7774c8182b024e6714973c35760c818427338a4b9c00435774c81569c51c4d0d5dd3204e66f0970d1786aee9902733e8714973c35840ee99027338a4b9ddd3536409cce292e164f0d5dd3916409cce292e7
  | 6, 3, 2 => 0x86aee99027338a4b8213c35774c8156a1825c3bdddd39671cc81399c525cf0d5dd3204e67c8e292e786aee99027338a4b8263c35774c81399a03404b9e1abba770c81399c525cf0d5dd32056a960e292e786af21dd3204e6714973c35774c81399c525c47de1ac09774c81399c522cf1c61abba6409cce292e700105ddd32038a4b83db435774c816a9c525c25de1abba640b2d399c525cf0d5dd3205c09ccb292e7
  | 6, 3, 3 => 0x86b08ddd3204e6714973c35774c81399c525c2ede44c66752c81399c525cf0d60fbba6409ccc512e786aee99027338a4b826bc35774c81379c52c84b9e1abba6409cce292e206f0d5da3204e6714c892e782eee9d4b204e6714973c35774c8139a2a1a216de44c3583ec81379c525cf0d6003ba6409cce292e786af79dd3204e6714973800752c458427338a4b9a1abba640b2d5f27325cf0d5dd32055a7147e0ef7
  | 6, 3, 4 => 0x86aee9902db4e6714973c35774c8139a6638a4b9e1abba640af8e296125cf0d5dd3204e6960d012e786aee99027338a4b83b3c35774c815e26f38a4b9e1abba6409cce28f71a2f0d5dd34d6409cce292e786af85dd3204e671497380086aee99027338a4f1a46c35774c65399c525ce0021ab204ce71497038686aee9cb32038a4b847b80086aee99027338a449a1abba640960e292e1bcf0d5e4bba6409cce292e7
  | 6, 3, 5 => 0x9130eddd3204e6714973c89774c81399c52343bde1abba6409cce296025cf0d5dd3204ce714d512e78cd0d60e3204e6714973c35774c815f27338a505c00435774c817aa7325cd2261aba96409ccde12e786aee9903134e6714973c35774c81399f838a4b9e1abba6409cce292e12af0d5dd320550a8d399c5786aee9aa3204e6714973c35774ba15f27338a4b9e1abeb774c81399c525ce0021abba640a0ce292e6
  | 6, 3, 6 => 0x86ad059027338a4b8713bba6dec81399c525c389e1abba640af8e28e217af0d5dd3204ce714bb92e786aee9902be4e6714633c35774c8139a0038a4b9e1ac17774c81399c525ce0021abb46229cce292e686aee9cb3204e671494b80086aee99027338a4c9a1abba6409cce812e02cf0d5dd3204e6850e292e786aee9adb204e6714973c35774c8139a313ee715e1abba6409ccbf92e234f0d5dd3116209cce292e7
  | 6, 3, 7 => 0x8b70d5dd31c4e6714973c357f0ee9902d538a4b9ddd36f6409cd219c525cf0d5dd3204e67149710070010d5dd3204e6628593435810ee99027338a4b9e3dc1f640c21399c525cf0d60e3116109cce292e786aee9c132048e714973bba640c455f25e38a4b9e1abba6409cce295125ce0021aba06409cce292e686aee99027345471487380086aee99027325c271a1abba640af9399c5218f19a1abba6409cce29167
  | 6, 3, 8 => 0x86aee99027343c7148d3c8986aee99027338a4c9e1abba640a61189c525ce0021abba64071497078686aee9902733bc714973c9286aee99027336a4b9e28c35774c81311c525cf0d5dd3204e68a8de12e7774dbd903204e6714973c35774c999027338a4b9c004356409cce292e072d0d5dd3204de928e292e70010d5dd3204e68a868b435762c818427338a4b9e1abba6409cd069c512ee001dd3194e6978e292e6
  | 6, 3, 9 => 0x91b0d5dd3204e66f0973c35774c65399c525c469ddd36f6409cce292e12ef0d5dd3a9640ab4e292e78f90d5da3204e66d4973c6b86aee99027338a4b9e1abba6409cce292e10af0d5dd36f64090ce292e786ae19903084e6714973c35774c81399c525c145e1abba6409cce292e058f0d5dd3204e6714d50f67774e41c73204e6714973800774c815427338a071a1abba748c81399c525cf0d5dd3205769cce292e7
  | 6, 3, 10 => 0x8f90d5dd3194e6714973c8986aee990273454345e1ab206109cce295e25cf0d5dd3204e6800970d17912ee9902733545dc973c35774dd190273454389c00435774c81399fd25cd0d5be3746409cce292e70010d5dd2a84e67142db489774c6539a5e38a4b9e1abba640a8d399c525cf0d5dd3194e671497005786aee9902733ea714973c3e774e599027338a4b9e1abba6409cce2929164eee9903025cc9cce292e7
  | 6, 3, 11 => 0x90f0d5dd3204e6628973c8986ac817324a38a4b9e1abba640c4539a1525cf0d5dd38e6409ccc512e786aee99027338a4b8533c35774c81602733544b9e1abba640a65399c525cf20e1ab666409cce292e78b70d5dd3205509cce2bc3583eee9902733024b9e3e435774c813d1c525cf0d5dd3205aa9ccc892e786aee99027338a4b830b80086aee99026238a2c9a1abba6409cce292e11cf0d5dd393640af8e292e7
  | 6, 3, 12 => 0x9131f1dd3204e66d4973c35820ee99027338a4b9e1abba6409bce292e0b6e0021abba640b2d2512e686af65903084e6714973c35774c8164a734624b9e1c435774c81399c525cf0d5dd32052e9cce292e786aee9902e64e6680973c5286aee99027338a4b9e1abba640a9939a5e38af0d5dd32057c7148d0e2786aee99027338a48081bc357ecc81399c525c40de1abba6409cce292e0fcf0d5dd3204e68a8e28f77
  | 6, 3, 13 => 0x86aee99027338a510973c35774c81399d625c0b1e1abbe774c81399c525cf19a1abba6409c4e292e786aee99027338a4b88b380086aee99025838a459a41435774c81399b925cf0d5dd3204e6714ba92e78f90d5dd3204e4714973c35774c81732de2ca4b9c0048986ac812c1c525cc0021ab204e66289703860010d5dd3204e6730973435774c813998125c1ede3e435774c815f1c51c4e0021abba6409cce291b6
  | 6, 3, 14 => 0x86aed19027338a4b80e3c35774c81399c53344b9e1abf8694c81399c525cf0d5dd3204e67148d10e7000ee9c53204e67149734356409cce292e2062b1e1abba640a3d399c525cf0d5dd3886409cce292e786aee9902be494714973c35774c81399c53324b9e1abba6409cd189b525cf0d6053ba6409cce292e786b07d8427338a4b81c3c35640c21399c52063bdddd36d6d4c81399c525ce001dd3205cc5949701c6
  | 6, 3, 15 => 0x86aee99023138a4b8713c35774c818426638a4b9c00435774b98b292e0b6d0d5b6b666409cce292e786aee99027338a4905a3c35774c818a27338a4b9e0e3206229cd2f1c525cf0d5903084e68a8c892e786ac818427338a4b87fbc5b86aee99027338a3f1e44be8774c81399c525ce001dd3204e67149701c686afeddd3204e6834e2b80086aee99027338a3f9800489834c81399c525cd0d5dd3204e66a8c512e7
  | 6, 4, 0 => 0x86b0d1dd3204e6714973c35774c81399c525c03de3dc35774c81399c525cefe1dd36f6409cce292e7774c458427338a4b88d380086aee9399c525c16da1abba6409ccde12e234f0d5dd3204868c4e292e786aee9902733145dc973c35774c81399c525c2b9c00435774c8139981164d0d5dd3b26409cce292e786aee99027338a4b80c3c17774c818427338a4b9e1abba640c456a9c525cf0d5dd34e6409cce292e7
  | 6, 4, 1 => 0x86aee9902be4e67147fbc7c774c458427338a4b9e1ac0970cc81399c525cf1f21abba6409ccde12e78b70d5dd3204e6714973c35774c81399a025c3bdc00435774c81399c525ac0021abba6409cccf92e686aee99027338a4b85cbc35774c81399e538a4b9e1abba6409f1399c525cf225dd3204e6978de12e786b07d903084e6680973c35774c8137a5e38a4b9c00435774c814b27338ad0d5dd3204e66f0970057
  | 6, 4, 2 => 0x86b09ddd3204e6714973c35774c81339c525c389e1abba640a71399c525cf0d5dd3336409cce292e786aee9b23205cc9cc973c35774c8139a3e38a4b9e1ac1c774c813999f25cf225dd3204e6714970ff786aee99027338a4b8503c35774e7d9023d38a4b9e1abba6409cd151c5218f1561abba6409cce292e78f10d5dd3204e6714973c357e6c81399c53544b9e1abba6b2c81399a025cf0d5dd3204e699cda92e7
  | 6, 4, 3 => 0x86aee99027345464468bc35774c8139a1e38a40de1abba6409cd0f9c525cf0d5dd3205ca9cce292e786b035dd3204e6714973c89752c8139a4a38a4b9e44c35774c81399c525af0d5dd3766409cce292e78e30d5dd3194e6714973c35774c814ea7338a4b9e1abba72cc81471c525cf0d5dd3204e671497068786afcd9027338a5dc973c7b774c81399c53644b9ddd3536a6c81399c525cf0d5f7bd96409cce292e7
  | 6, 4, 4 => 0x82eee99027338a4b8103c35774c81399c525c405e1abe0774c81399c525cf1361abba6409cce291e786aee9902e6354584973c35774c8165a7325c469c00425774c81399c525cd0d5dd3204e6714970b170010d5dd32054a9cce2b435774c81399bc3784b9e1abba6409cce297225cf0d60e3204e67149705d786aee99027338a4b874bc35774c815ca7338a4b9e1abba6409cce292e036f0d5dd32064099ce292e7
  | 6, 4, 5 => 0x9290d5dd3204e6714973c35774d65902d538a4b9e1abba640af92f1c525cf0d5dd396640b68e292e78b50d5dd3204e67148b3c35774c81399c525c231e1abba640b54e292e1def24e1abba6409cce292e786affddd3204e6714973c8f912ea59027338a4b9e1abb4640af9399c525cf0d60e3204e6928e292e7912fa5d4b204e6714973c177deee99027338a4b9e1abba6a4c81399c525ce0021ab204e6604970386
  | 6, 4, 6 => 0x86aee99027338a5048d3c35774c81399c525c191e1abba6409cd251c522cf0d5dd3206049cce292e786b005903114e6714973c35774c81399c525c12de44c356409cd251c525cf0e61abba6409cce292e782f025dd3204e6714973c35774c8139a1838a345e1abba640ab4e292e1daf0d5dd3204e6714970de7774e399027338a4b83dbc35640c2139a1c38a4b9e1abba6409ccee1c525cf19a1ab866409cce292e7
  | 6, 4, 7 => 0x8f6ee9da3204e6714973c8983ec81399c525c469e1abee6409cce291a206e0021abba6b2c81569c5686aee99027344a71481bc35768c81399c525c345e1abba75ec81399c525cf0d5dd3204e6714970e0786aee99027346271492380086aee9901c51c41a9800435774c812197725cd0d5a53205cc9cce292e70010d5dd3204e64a44bb3ba6dec8188a7338a4b9e1abe1774c815f1c51c4f225d4b204e67149705b7
  | 6, 4, 8 => 0x86aee99027338a4a43dbc5c86aee99027338a4b9e1abba752c816a9c525cf0d5dd32057c9cce28d1786aee9902be400714713c35774c81399c525c349c004356407149707b070d191dd3204e6978e292e7774e79c73204e6714973c898f907d9027338a4b9e1ac1c6409cce292e0b6f1961abba6409cce292e7000ee9c73204e6714593435774c8139a2b38a4b9e38c35774c813f9c525cf1c61abba6409ccde12e7
  | 6, 4, 9 => 0x1071d4b204e67149734357f0ee99026738a4b9e44ba96409cd2f1c525cf0d5dd3204e68a8b28c6786aee9902734ce714923c35834ee99027333c4b9ddd3596a6c81399c51def0d5dd3204e67148b05b7774d4d9027338a6a8973c3585eee99027338a459e1abba640995189c525cf0d5dd3204e66f097103786aee99027338a4b81dbc35640c21399c525c329c00435774c81541c52cad0d5fe3ba6409cce292e7
  | 6, 4, 10 => 0x86aee9a03205cc9cc973c35774c813f1c525c071e1abba72cc81399c5248f0d5dd3206409ccc512e7001225d4b204e67149734356b2d299027338a4b9e1abba6b2c8139a0d38af0d5dd3a56409cce292e78e30d5dd3204e67147bbc6682eee99027338a4b9e1abba6409cd161c525cf0d5dd3204e688cc892e786aee99027341a71477bc35774c81399c53744b9e1abba640714970b814ef0d5dd3204e6714970157
  | 6, 4, 11 => 0x86aee9902be546714713c35774e59902b338a4b9e1abf2774c81399c525cf0d5dd3204ce924e292e786aee99027338a40c7bbc35774c81399c52860f9e1abba6e8c81219c525cf0d5dd38c640af8e292e786aee99027338a4b8853c87774e399027338a4b9e1ac1c6409cd2f1c525cf0d5dd3204e6714b492e786aee9cb32060a714973c35812ee9902ad38a4b9e1ab20610979251c525ceee9c738e6409cce292e7
  | 6, 4, 12 => 0x8c10d5dd3205cc594973c35774c815ea7338a4a5e1abba690c81399c525cf0d5dd3204e6978e2916786aee99027338a4b827bc7b774da59027338a4b9c00435838c81399c525cd0d5dd3205c0928e292e786ae7dcd3204e6714973c35774c81399c52f04b9e1abba640b99251aa25cf0d5beb666409cce292e786aee9902733144b84bbc3581cee99027338a4b9e1abba6229cce292e030f0d5dd3204e6714971227
  | 6, 4, 13 => 0x8fd0d5dd3204e6714973c35774c81399c525c275e1ac15774c81399c525cf0d5dfbba6409cce292e70010d5dd3204e67148b3489774c812f24a38a4b9c003ba6329cce292e038d0d5dd3204e68a8d50e2786b0720e3204e6714973c3585d0719027338a4b9e1abc6774c81399c525cf0d5dd3ab6409cce292e786aee9993204e6714973c35774c8165a7325c40de44c89752c81399c525cf0d5dd32060ab98e28e27
  | 6, 4, 14 => 0x86aee9ba3596409cd153800774c815f1c51c4071a1abba640960e292e164f0d5e8bba6409cce292e786aee9c0b204e67149738007747149707b0b60719dd3a96409cce292e06af0d5dd3205ccb60b292e78f70d5dd3194e6714973c8986b0719027338a4b9e1abba6589cce292e062f0d5dd3204e65dcb092e7774c8188a734ce714973c35774c81709c525c389e1abba6409cce292e17ef0d5dd3204e6714970127
  | 6, 4, 15 => 0x86aee9902733c4714973c35774c81399c525c2d1e1abba640bd55f27325cf0d5dd3204e67149701e79130d5dd3204e67148b3c35774d4d9027338a3bde1abba6409cd15191234f19a1abba640ab4e292e786aee9903114ce71497380086aee99027338a2b98004356409cce2929070cee9d4b6f6409cce292e79190d5dd3204e671497380082eee99025838a4b9a2dc35774c65399c525cf0d5dd3204e67149706a7
  | 6, 5, 0 => 0x8fb0d5dd3204e6714973c35774e59902733524b9c003ba6409cce292e012d0d5dd3966409cce2943786aee9902b6494714973c35774c81189c525c371e31435774c81399b525cf0d5eebba6409cce292e70010d5c33205cc714973435774c81399c525c171e1abba640b99339c525cf0d5fc3ba6409ccc512e7912ee990273490714973c35774c919027338a4b9e1abba6409cd0c12e1b2f0d5dd3204e680cc892e7
  | 6, 5, 1 => 0x86aee9902d54e659497380086aee99024325c25da1abba6dec81399c525cf0d5dd37c6409cce292e786af25d4b204e6714973c35774c81399c525c091e44c357e8c81399c525ce0021ab194e6928e292e686aee9a032046a714973c7b8ccee99027338a4b9e1abba6409cd0c1c5234f20e1abba6409cce292e786aee99027336a640973c1f83905d9027338a4b9e1abba6409cce292e06af0d5dd3956409cce292e7
  | 6, 5, 2 => 0x86aee9902733404b8103c35774c81399a025c265e49435774c81399c525cf0d5dd3204e67f4e292e786aee9aca7338a3bc593c8983f05d9027338a4b9c00435774c81389c525cd0d5dd320610b54e292e7000ee99027316425c0e3435774c817325e3544b9e1ab866409cd251c525cf0d5dd3204e6714ac92e79130d5c63204e6714973c357a0ee99027338a4b9e1abba6409cce292e0b4e001dd3204e67149703f6
  | 6, 5, 3 => 0x86aee9902ad38a4b8973c35774db59027338a4b9e1ac1c640c453999f25cf0d5dd3296409cce292e786aee9902b44e6714973c1c774c81399c525c469e1abba640b54e298a25cf0d5dd3204e6714a607b786aed9acb204e6714973c8986ac6539a4a38a4b9e3e435768c81399c525cf0d5dd3204e671497045786aee99027338a4b862bc357ceee9902734304b9c004357749cc590970b6d0d5da3204e6714970387
  | 6, 5, 4 => 0x86b07db33204e6714973c35774c81399c525c051e1abba6409bce292e1c2f0d5dd3204e68d4e292e79130d5d83204e6714973c35774c8139a3938a4b9e1abba6c8c813998a25cf0d5dd386640af8e292e786aee9d63204e6714973c35774ea59027333c4b9e44c35774c81389c525ce00244bb46409cce292e686aee99023138a4b8293c35774c818627338a4b9e1abba70ec81399c525cf0d5dd3346409cce292e7
  | 6, 5, 5 => 0x9170d5dd3204e6714973c35774c81399c525c1a5e2dc35774c81399c51eef0d5dd3205cc8c4b292e786aee9902734547c0973c35774c81399c525c005e44c7c774c81399c525cf0d5dd3204e67149706f786aee9902734387148d3c35774c81399c52ae3bde1abba6409cce29b125cf0d5dd3ba6409cce2929786ae199027338a4b82dbc35774c8182a7338a389e1abe7774c81399c525cf0d5dd3204e68c4e28fc7
  | 6, 5, 6 => 0x86aee99027338a4b87d38008f707d9027338a4b980043570cc81399c51f8d0d5dd3204e68a8c8903786aee9c83205cc714973c35774c8139a0238a4b9e1abba640b98e28ef1c4f0d5dd3204e6890e291a786afbddd3205aa714973c35774c8139a3138a4b9e1abba6409cce292e088e0019027325c25c1c01c686aee9903114e662897380086aee99024338a2c9800000752c65399c525cb0d5ba3666409cd1512e7
  | 6, 5, 7 => 0x86aee9902be4de714973c5486aee99027338a4b9e44c356409cce2929206f0d5dd3966409cd0c12e786aee99027347a604973c89774c815b27338a4b9e1abba64cc21399c525cf0d5dd3204e68a8688c7786aee9901c525c38847bc3570cc8139a5e38a4b9c003ba6409cce293e25cc00244ba96329cce292e686b025dd3205aa714973c35774ea59026738a4b9e1abba670c81399c525cf21e1abba6409ccda92e7
  | 6, 5, 8 => 0x10d59027338a4b819b435774c81399c525c3e1e1abba6409ccda9aa25cf0d5dd3204e67149701a786aee9903054e6714753c6f774c8139a5e38a4b9e1abba6409cd1a1c525ce0021abba6409cc970d5686aee9cb3205cc594973c35774c81399c525c0a9c00435838c65399c525cd0d5e1b746409cce292e70010d5c33204e6714973435774c815427338a2c9e1abba6409cd339c525cf1aa1abba6409cd069c57
  | 6, 5, 9 => 0x86aee99031d4e6714973c35774c81399c525c165e1abba6409bce292e1a2f0d5dd3204e67149702179030d5dd3204e6714973c8986ae199027338a4b9c00435774c81399c5166d0d5da3204e671497103786aee9b7b204e68a8973c35774c81399c525c1c1e1abba640a8d251c525cf0d5dd369640b993992e786aee9902b74e671468bc35774e599027338a4b9e1ac35774c81339c525cf0d5dd3204e6714970a17
  | 6, 5, 10 => 0x896ee9903114e6714973c35774c8188a733024b9c00435774c81399c51a8d225d4b204e67149701c786aee99027338a4b805bc35774c818527338a4b9e1ab204e69290e1c525cf0d5dd3204e67148d0eb786aee99027338a4b83cbc17774c81399c53384b9e1abba6409cce292e07af0d5dd320494714970a6786aee99024338a6a8973c8986b0718ca7338a4b9e1ac18774c81399c525cf1ee1aba96409cce292e7
  | 6, 5, 11 => 0x86ae99d03204e6714973c35774c81399c525c2c9c00435774c81331c525cd0d5dd3204e6894d512e786b05d903084e6714973c8986af659027338a4b9e33435774c81399d025cf225d4b204e69bce292e786aee9902733da714973bef774dbd9027338a4b9e1abba6fec81399c525cf189dd3206229cce292e786aee990273496714973c35774c817316525c2c9e44ba96409cce292e1fef0d5dd3204e67149707f7
  | 6, 5, 12 => 0x86aee99027338a4580e3c35774c81399812b84b9e1abba752c813998a25cf0d5dd32057c9ccc712e786aee9901c525c3bc53bc35838ee99027338a451e0e417774c81399c525cf0d5dd3204e65dcb892e786aee99027338a4c802bc8986ac81399c52063bdc00435774c81399c5168d0d5dd3204e671497083786aee98ca7338a4b82e3c35774c81399c530c4b9e1ac1c6409cce292e038f0d5dd3204e6714ab88b7
  | 6, 5, 13 => 0x86af31dd3204e6714973c7c86aee990273454345e20c35774c81399c525cf24a1abba6329cce292e7000ee9b7b20486714973435774c81689c52ee4b9e1abba6409cce292e160f0d5dd3906409cce292e786aee99027345446868bc35774dd1902734304b9e1abc96409cce292e0aaf0d5dd3204e67149701079130d590273454644973c8986ac81399c525c3fde1abba6409cce292e044f0d5dd3204b0950e292e7
  | 6, 5, 14 => 0x86ae199027338a644973c357faee99027338a4b9e49435774c81391c525cf0d5dd3204e6714d51247774c8188a7338a4b86fbc35774c8156a5e38a4b9e1abf5774c81399c525cf0d5dd3b464099ce292e786aee9903084ce714973c35774dc59027336a4b9e1abf8774c75399c525ce0023e3ba6329cce292e686aee99027338a4b8233c7786aee99027338a4b9e1ac1f774c81399a022ce0021abba6409cce092e6
  | 6, 5, 15 => 0x10d5dd3204e68a85f3435774c811e9c53544b9e1abba6409ccda92e1c4e001da3204e67149701c6912ea59027338a4b868bc35774c81471c525c389e1abba6409ccf99c525cf0d5fb3204e6714c792e786aee9a03204e6604973c898f8ee98ca7338a4b9e1ac12774c81399c525cf0d5903084e671497116786aee99028938a4b8213c66774dbd9027338a4b9e44c35774c81399c125cf1edd4b206109cce292e7
  | 6, 6, 0 => 0x86aee9902733225dc973c35774c81219c525c389e1ac1c6409cce292e1a2f2261ab204e6870e292e70010d5dd32049c4b84bb435866e199027338a4b9e1abba752c813998125cf0d5dd3204e671497081786aee9902e64e658497380086aed1399c525c16d8004356409cce292e068d0d5dd32057c9cce2916786b07ddd32c4e6714973c35774c8151a7338a345e1abba6329cd189c525cf0d5dd3204e68a8b291a7
  | 6, 6, 1 => 0x86ad999027338a4b871380086aee99026736a4b9a1abba6629cce292e0eef0d5dd3206229cce2929786aee9902e625c388633c35774c813997725c319e1abba6409cce292e080f0d5dd3204e67148b0d170010d5dd3204e67145b3435774c81399c52b44b9e1abba6409ccd819125cf0d603bba6409cce292e786aee9902ee5809cce2bc35774c81399f938a4b9e1abba6409cce292e004f0d5dd3205cc644970e27
  | 6, 6, 2 => 0x86aee99027338a640973c356a4c818427338a4b9e31435774c81399c525cf0d5dd3966329cce292e786aee99027338a4b84db80086aee9b23205cc4b9a25c35774c81399c525cf0d5dd3204e68c8e292e786aee99027338a4b803bc35774c81399a025c16de1abba660c81399c525ce0021abba6409cc9709768b10d5dd3204e6714923c35858ee99027338a4b9e1abba6409cce292e0c0f0d5dd3205969cc970d97
  | 6, 6, 3 => 0x8a30d5dd3204e6714973800774c818127338a4b9a1abba6409cce298325cf0d5dd3204e671497110786aee9aab204e6714923c35838dc19027338a4b9e1abba640928e292e05ef0d5dd3205b29ccc892e786aee99027338a4b84fbc35774c81419c525c0b1e48c35774c81379c525cf0d5dd3204e671497057786aee9902e62ca4b83dbc35774d1d902e638a4b9e1abba640c65399c5252f0d6033204e6928e292e7
  | 6, 6, 4 => 0x888ee99027338a6a8973c35774d659027338a4a5c00435774c81399a025cd0d5dd3204e6714948ef786aee99030538a4b8713c7b768c818427338a4b9e1abba640ab4e291a1def0d5dd32055a714c892e78ed0d5dd3204e671497380086aee9902e62ca2c9a1abba6acc81399c525cf0d5dd3194e6714970b2786ae199027338a4b80e3c35774c81559c525c3bde1abba6409cce91c525cf2261ab204bc928e292e7
  | 6, 6, 5 => 0x774e39902734e6714973c35774dc99027338a4b9e44c35774c81399a025cf0d5dd3204e67fce292e786aee99023d38a4b8713c35774c8118a2a38a389c003a96409cce292e00ad0d5dd3204e6804e292e786aee9902be454594973c35774e59902a838a4b9e1abba6409cce292e1bef1d61abba6409cce292e786afbddd3204e6628973c5d86aee99027338a4b9e1abba65ec81399c525cf0d5fc3ba64090ce292e7
  | 6, 6, 6 => 0x86aee99027338a4b8183c35774e5d9027338a4b9e1abba6e8c815f1c51c4f14e1abba6409cce292e79131f1d4b204e6714973c59774c8139a5e38a4b9ddd320622979189c525cf225d4b204e67149700570010d5902e62ca4b81c348786aee99027338a4b9c003ba6409f8e292e038d1f2323ba6409cce292e786af0ddd3204e6714973bba6dec8139a4a38a4b9e1abba640c213998125cf0d5dd32061e9cce292e7
  | 6, 6, 7 => 0x86aee9902a94e6714973c35774c81399c522c0e1e1abba656c81399c525cf0bddd36f6409cce292e786aee9a3b204e6714973c31774e599027338a4b9e3e435838c81399c525cf0d5dd3204e67149706e786aefd903084e671497380086ac818427338a459a1abc96409cd251c525cf0d60e3204e67149703870010d59027338a4b81bb435774c8139a182ee4b9e1abba6409cce293725cf0d5dfb204e6714970197
  | 6, 6, 8 => 0x86aee9902e625c38868b800774dbd9027338a4b98003ba6404b84b87b038d0d5dd32060a9ccc892e70010d5dd3194e64b84bb435774c817f27338a4b9e1abba640929189c525cf0d5dd3204e6680c892e70010d5a53204e6714973435774c81399c525c291e1abf4774c816a9c525cf0d6023ba6409cce292e786ad29902734bc71497380086ac81399d625c0e18003ba640c45339c525cd0d5dd3204e6714d812e7
  | 6, 6, 9 => 0x86aee9902e64e6714923c35774c81399d03224b9e1abba640b993992e1eef0d5dd3716409cce292e786aee9902d538a644973c89774dbd9027338a4b9e1abd2774c81399c525cf0d5dd3204e6714a492e786b079dd3204e6714973c35774ca99027338a4b9e1abba640aa12f23138af24a1abb46409cce292e7774c81399c525c46857b8007749cce292e0b6071a1abba6409cd0c12e170f0d5dd3ba6409cce292e7
  | 6, 6, 10 => 0x86aee99027348671497380086aee9cb320550715a04bba71cc81399c525cf199dd3536409cce292e70010d5dd3204e64b84b346f774c8139a4838a4b9e1abba640979189c525cf1ee1ab204e6928e292e786aed19027346271497380086aee99030538a389a0d3ba640c45399c525cf0d5dd3204ce7149705b786aee9902a14e6714973c35774c814727338a4b9ddd3204e6979119c525ce001dd32038a2c83d81c6
  | 6, 6, 11 => 0x86aee991b204e6714973c35774c8168a7338a4b9c00435774c81339c525cd0d5da3966409cce292e70010d5dd32047a60497343570cc81399c525c0e1e1ac1f640c212c1c525cf2259027338a6a8c792e786b06ddd3204e6714973c35774c81399ca38a4b9e44c3582ec81399c525cf0d5dd3204e671497089786aee9903204e67149738008a0ee99027338a4b9a1abbd774c81399c525cf22a1abba6409cce292e7
  | 6, 6, 12 => 0x86aee99027338a598973c8986ac81399c525c459e1abba640c19399c525cf0d5dd3204e67ace292e786aee9903055cc594973c35774c81399c52ce4b9e1abba6409ccc512e0b6f0d5dd32057c714bb8e2786aed19027338a4b8593800912ea5399c525c16da1abba6409cce292e03af15e1abba6409cce292e78f90d5dbb204e6714973c35774d1d902be38a389e44c35774c81339c525cf0d5dd3204e6714970ea7
  | 6, 6, 13 => 0x774ea5903194e6714973c8e86aee99027338a4b9e1abba640a81251c525cf0d5dd320622b98b292e786b069dd3204e671497380086aee9902733144b9a1abba640b54e29c525ceee9d4b206229cce292e786aee99027338a4b8443c35774ee98ca7338a4b9c004896409cce292e1fed1f20bbba6409cce292e786aee99027338a4b871b80086b071399c525c16da1abba640c15399c525cf0d5fc3ba6409cce292e7
  | 6, 6, 14 => 0x8f90d5dd3204ce6d4973c3583ec81399c525c065c00435768c813992e12ec0021abba4e67149705c686b04ddd3204e6714973c35774c81399c52b84b9e3e47b774c81399c525cf2260fb204e6714d512e786aee9903194e6714973c89752c81399c525c0edc0047b768c81399c525cd0d5dd3206229cce292e786aee99027338a5a0973c35774c813998125c16de3dbba6409cce292e012eee9b7b204e67149701c7
  | 6, 6, 15 => 0x86b0719027338a4b88a3c35774ea59027338a4b9e1ac22774c81399c525cf0d5dd3204ce7149701c788b0d5dd3204e6714973c35774c81399c525c0d9e1abba752c817316525cf0d5fc3ba6329cce292e786aee99025838a4b8103c898c4ee99027338a4b9e1abba6409cce292e184f0d5dd3204e671497017782f05ddd3204e6714973c35768c81399c53204b9e1abba640c39399c525ce0021abba4e67149705a6
  | 6, 7, 0 => 0x10d5dd27325c25c2db435774c81399c525c155e34435774c81399c525cf0d5dd3a96329cce292e7912ea59027338a4b8593c35774c812423138a4b9e3e3ba6dec81399c525cf0d6063ba6409cce292e786aee982ae84e6714973c35774c658ca7338a4b9e39c35774c81399c525cf0d5dd3196229cce292e78f70d5dd3204cc714973c35774c817427338a4b9e49489752c81399c525cf0d619bba6409ccc512e7
  | 6, 7, 1 => 0x86b0bddd3204e6714973800912c81399c525c0eda1ac0b774c81399c525ceea5903116109cce292e786aee99027338a4b8023c35774c81399c525c07dc003204e671497038038d0d5dd3204e671497056786aee988b084e6714973bba640c45399c525c161e1abba4e68c4e292e0eef0d5dd3204e6714970327774ea588b084e671497380086aee9900b212e1eda1ac1c6409cce292e164f0d5dd32d6409cce292e7
  | 6, 7, 2 => 0x48986aee98ca7338a4b9e44c1a752c81399c525ce0021abba6329cce292e6912ea5903064e6714973c35774c81399c525c319e1abba6329cce292e0b6f0d5dd3204e67149705479130d5dd3234e671497380086aee991a7338a4b9a44c35774c81399c525cf0d5dd3204e67149700070010d5953204e6714973435640c45399c525c159c00435774c81399c525cd0d5dd3204e67149705b7
  | 7, 0, 0 => 0x86aee99027338a4b83d87b886afe1dd3204e67149702480000021abba6409cc5909760010d5dd3205289cce292e70000021abba6409ccde12e686aee9ba3204e6714bb92e80010d5dd3204e67149707770010d5dd3204e68a8c892e70010d5dd3204e6714970ff786aee990273494714970d188f919a1abba6409cce292e886aee9903204e68c4e292e886aee99027338a644c892e80010d5dd3204e67149701c78cd0d5dd3204e671497038886b07ddd3204e67149707b8
  | 7, 0, 1 => 0x12521abba6407149707b79130d5dd3204e67149701c80010d60fbba6409cce28b270010d60fbba6409ccd012e78b70d61abba6409cce292e80010d5dd374640b993992e786aee99027338a4b80e000886b009dd3204e68c4e292e88e30d5f7bba6409cce292e886aee9902be4e67149705b886aee99027338a4b8688ce80010d60e3206229cce292e786aee9902734627149709780010d5dd3204e69bce292e70010d5dd3204e64b84b894786aee9902984e6714970b28
  | 7, 0, 2 => 0x10d5dd3966408c4e292e786b025dd3204e67149710380010d5dd3204e64b84b88f70010d5dd3205cc714b292e70010d5fc3204e6714c892e786aee99027338a4b86885b80011461abba6409cce28b270010d5dd3204e67145907b79130d5dd3204e69bce292e80000021abba6409cce28f7686aee9902e14e6714d512e886aee9cb3204e6714970e280010d5dd3204e6860e292e70012261abba6409ccde12e786afbddd3204e67149710388e30d604bba6409cce292e8
  | 7, 0, 3 => 0x86aee99027338a4b8710b280010d5dd3204e655c97097786aee9902e65b09cce292e80010d5dd32057c9cce292e786aee99027341a714bb92e886aee9cb3204e67149709780000021ab204e64b84b838686aee990273494714b292e886aee99027338a4b89711a80010d5dd3204e6714e292e786aee9902be4e6978e292e886aee9903114e68bce292e80000021abba640b2d3992e686aee9cb3206409cce292e80011f21abba6409cce29247000ee9ba36f6409cce292e7
  | 7, 0, 4 => 0x10d59027338a4b83d83870010d5dd3204e65dc970977000ee9903084e67149701c70010d5dd3204e671497008786aee9d4b204e67149703b88e319a1abba6409cce292e886aee9902734bc714970d180010d5dd3204e6870e292e7000ee99027338a4b80e019786aee99027338a644af12e886aee9902734948a8e292e80010d5dd3204e66a89709770010d60fb204e671497038786b059dd3205cc9cce292e886afe1dd3204e68c4e292e80010d5dd27338a5209705b7
  | 7, 0, 5 => 0x86aee99027338a6a89707b88b70d5dd3206109cce292e886b07ddd3204e6714bb92e80010d5dd3204e6890e292e786aee99027345471497086886aee99027338a4b85909788f70d5dd3206109cce292e88cd0d5dd3204e6714971038000ee9903114e67149711a78d90d5dd3204e68a8e292e80010d5dd3084e67149705b70010d5dd3204e6714970d1786b07ddd3204e6714d512e886aee990273494920e292e89130d5dd32057c9cce292e886aee9902be4e6714b892e8
  | 7, 0, 6 => 0x10d5dd3204e6714d50b278e30d5dd3204e67149700c886aee9ba3204e690ce292e886afe1dd3966409cce292e886aee9cfb596409cce292e80010d608bba6409cce292e70011921abba6409cce292e70010d5dd3204e6714970ca786aee99027338a5dc9707b89130d5dd3204e6714970d1886aee9ba3204e6714970e280000021ab204e671459038686aee99027338a4b8590ac886aee99027338a6449701c80010d5dd3204e6880e292e70011f1dd3206229cce292e7
  | 7, 0, 7 => 0x86aee9902734947149703880010d5dd3706409cce292e70010d5dd3204e6714970b7786b07ddd3ba6409cce292e80010d5dd27338a4b82d85570010d5dd3204e6714970c7786aee9902734947149711a80010d5dd3204bc928e292e786aee9903114e68c4e292e886aee99027338a4b8778d9886aee9ba3204e67149709780010d5dd3204e6714bb8b27000fbddd3204e67149701c786aee9902734bc714b292e80012261aba96409cce292e786afbddd3204e6714cc92e8
  | 7, 0, 8 => 0x86aee99027338a4b88d05b80010d59027338a6a897038786af49dd3204e67149707b80012361abba6409cce292e70010d604bba4e67149705b786aee9902734bc920e292e80010d5dd3966409ccc512e70010d5dd3204e6714970eb786aee9902e64e68c4e292e886afe1dd3204e6714970b2886aee99027338a4b88d0ce88f90d5dd3204e6928e292e8001025dd3204e67149701c70010d5dd3204e67a4e292e786aee9902734bc8a8e292e80010d5f7bba4e67149705b7
  | 7, 0, 9 => 0xee99027f4e67149701c7001199dd3204e67149701c70010d5dd3204e68a8970d1786aee990273462714970ef886afe1dd3746409cce292e891b2261abba6409cce292e886aee99027338a644970d180010d5dd3204e64b871097786aee99027338a6a8d512e80010d59027338a5dc9703878f90d5dd3204e67149705b886aee9cb3206229cce292e886aee99027338a4b82d83880010d5dd3204e6714970bd786aee99027338a4b83d87380010d5dd3205aa714bb92e7
  | 7, 0, 10 => 0x120a1abba6409cce292e70010d5dd3205cc9ccd512e786aee9902734bc7149711a886aee99027338a5dcbb92e80010d5dd3a66409cce292e700119a1abba4e67149705b786aee99027338a4b80e01c886aee99027338a4b8688c6886aee9902e04e6978e292e886aee99027338a4b81c02d80010d5f7bba6409cce2903786b07ddd3204e6714970e2886aee99027338a6a8bb92e886aee9acb204e68c4e292e886aee9cb3205cc9cce292e80010d604b204e6928e292e7
  | 7, 0, 11 => 0x10d5dd3204e67149711a786aee99027338a594ad92e88e30d5dd3204e6928e292e88f90d5dd3204e6978e292e80000021abb46409cce292e68c90d5dd3204e6714c892e886b07ddd3206409cce292e886aee9903114e6714970b2886aee9902734bc7149703888cd16e1abba6409cce292e80010d5dd3204e6714970af70010d5dd3205c09cce292e70010d5dd3204e64b84b89778f90d5dd3204e6714da92e80010d5dd3206209cce292e786b019dd3204e6978e292e8
  | 7, 0, 12 => 0x9091f21abba6409cce292e89130d5dd3204e67149711a886aee9cb3596409cce292e886aee99027344a7149711a886aee9c83206229cce292e886aee9cb3204e6714970ef80010d5dd3204e6714710b278ad0d5dd3204e6714970e2886aee9d4b204e68c4e292e886aee9902734947149710380011f21abba6409cce292e786aee9902e64e6714970b28001225dd3204e6978e292e70010d5dd3204e671497005786b07ddd3204e67149709780010d6033ba6409cce292e7
  | 7, 0, 13 => 0x86aee99027338a4b88185b88b70d5dd3204e67149712e80010d5fc3ba6409cc9709770010d5dd3966407149707b786aee9b8b204e6714d512e886aee9902be4e67149701c80010d5dd32056c9cce292e70010d5eabba6409cc97097786aee990273454714c892e88e30d5dd3204e67149705b89131f21abba6409cce292e886aee9902734e68c4e292e89130d5dd3204e67149700580010d5963204e67149703870010d5dd3204e68a8b292e786aee9902734bc7149707d8
  | 7, 0, 14 => 0x8b70d5dd3204e6714d792e886aee9d4b204e6714c792e80011c61abba6409cce292e70010d5dd3205969cce292e786aee9a3b204e6714970e2886aee9cb3204e69cce292e886aee99027338a4b86881c88e30d5dd3204e6978e292e80010d5dd3964e68c4e292e70010d59027338a4b87103878b70d5dd32062a9cce292e886aee9d4b966409cce292e80010d5dd34a6409cce292e786af25dd3204e67149705b886aee99027338a4b8778b2886aee99027338a4b82d84d8
  | 7, 0, 15 => 0x8770d5dd3204e671497038886aee9902be57c9cce292e886aee99027338a64497038886aee99027338a6a89709789131c61abba6409cce292e80010d5e4bba6409cce292e70010d5fc3ba6409cce28b270010d5dd3204e67149704d70010d5dd3204e67149710370010d5ef3ba6409cce292e786aee9d4b204e6714970b280010d5dd3204e671497042786aee990273462714970848000ee9cb38e6409cce292e70010d59027338a4b84b838786aee99027338a5dc970e28
  | 7, 1, 0 => 0x86afd5dd3a96409cce292e88b70d5dd3204e6928e292e886aee9902be4e6714970d180010d5dd3205cc9cc9709770010d5dd3204e6800e292e70010d5dd2734947149705b70010d60bbba6409cce292e786b07ddd3206229cce292e80010d5dd3746407149707b786aee99027338a714970d189130d5dd3204e6714971038000ee9902734947149701c70010d5dd3206229cc97097786aee99027338a6449709a886b05a04bba6409cce292e886aee99027338a504970388
  | 7, 1, 1 => 0x86afe1dd3204e6714bb92e80010d5dd3204e6714970a678b70d5dd3204e67149705b80010d5dd27338a4b82d85b70010d5dd3205469cce292e786afe1dd3204e6714d512e886aee99027338a4b8688d1886aee9902e64e67149707b88d916e1abba6409cce292e80010d5dd3204e67149702c7000ee99027338a4b82d81c786afbddd3206189cce292e80010d5dd3266409cce292e70000021abba6409cd150d160011f21abba6229cce292e786b07ddd3205cc9cce292e8
  | 7, 1, 2 => 0x86aee9902be4e68a8e292e886aee9acb204e67149707b8000001dd3204e67149701c60010d5dd2734bc7149705b70010d5dd32057c928e292e70010d5dd3204e6714cc92e786b025dd3204e68c4e292e886aee990273454714e292e886b07ddd3596409cce292e8000ee9902734bc7149701c70010d5dd3204e67149711670010d5dd3204e6714ba92e786b07ddd3204e6714970ef80010d5dd3205cc9cce28b2786afbddd3204e68c4e292e80010d5dd3596409cc970977
  | 7, 1, 3 => 0x86aee99027338a4b871097886afe1dd3ba6409cce292e88f319a1abba6409cce292e8000ee99027338a4b80e00078f90d5dd3204e67149701c80010d5dd3a96409cc9709770010d60fbba6407149707b786aee9acb536409cce292e80011ee1abba6409cce292e70000021abba4e67149705b686aee99027338a594970d1886aee99027338a4b81c01c88b70d5dd3204e6978e292e80010d5dd3204e671497018786aee99027338a4b88d01c80010d5dd320462714970e27
  | 7, 1, 4 => 0x91316e1abba6409cce292e88cd0d5dd3204e68c4e292e886b025dd3966409cce292e80012261abba4e67149705b78e30d5dd3b16409cce292e80010d5dd3336409cce292e70010d5902e64e671497038786b07ddd3a96409cce292e886aee9903114e6714d512e886aee990273454714970d180010d5dd27338a4b82d80070011e21abba6409cce292e786afbddd3966409cce292e8001225dd3204e67149701c79290d5dd3204e67149705b800116e1abba6409cce292e7
  | 7, 1, 5 => 0x8cd0d5dd3966409cce292e80010d5dd3af6409cce292e78f90d5dd32057c9cce292e886afe1dd3204e6714970e280010d5acb204e67149703870012261ab204e6928e292e70010d5dd3204e6770e292e70010d59027338a4b877838786b025dd3204e6714970b280012521abba6409cce292e786aee9902be4e67149711a80010d5dd32057c978e292e70010d5dd3526409cce292e786afbddd3204e6714970b2886aee9902734e67149707b886aee99bb204e6714970b28
  | 7, 1, 6 => 0x8cd0d5dd3204e6714970b280010d5dd3204e67149701570010d5dd32038a6a89707b70010d5d4b204e671497038786aee9902be56c9cce292e80010d5dd3204e67149703b70010d5dd32057c9cce28d178f90d5dd3204e6714970d180000021ab2038a4b83d838686afbddd3746409cce292e800119a1abba6409ccd512e78f90d5dd3204e671497008886aee9acb204e6714d512e88e30d5dd3204e67149701c886aee9c13596409cce292e886aee99027338a6a8970ef8
  | 7, 1, 7 => 0x10d5dd3204e67149709d70010d5dfbba6409cce292e70000021abba6409cce2916686b0d5dd3204e6714d512e886afe1fc3ba6409cce292e886aee9903206229cce292e886aee99027338a4b8590a988e30d5dd32057c9cce292e886aee9933204e67149701c80000021ac1c6409cce292e686aee9903114e6714970e280010d5dd3204e671497122786b07ddd3206109cce292e886aee9d4b204e6714d512e800000244ba96409cce292e686aee9903084e6714970608
  | 7, 1, 8 => 0x10d5dd3204e6714970247000ee99027338a4b80e01c786afbddd3204e67149707b80010d5dd3204e671497035786aee99027344071497103886aee99027338a4b8778e2886aee9acb204e67149704780010d604bba6409cc97097786af79dd3204e6714970d1886aee9dd3a96409cce292e886aee9902734948c4e292e80010d5f7bba6409cc9709770010d5dd3204e67149706a78e30d5dd3204e6714970d1886aee9902734bc8bce292e88cd0d5dd3746409cce292e8
  | 7, 1, 9 => 0x8f90d5dd3204e67149711a886aee9902be5469cce292e80011f21abb46409cce292e786aee9cb3204e6928e292e88e30d5dd3204e6714b292e80010d5f7bba6409cce28b2786afe1dd3206229cce292e80010d5903084e671497038700124a1abba6409cce292e786aee9902734627149705b80010d5dd3376409cce28b2786b025dd3204e67149707b80010d5dd27338a4b82d81c786aee99031160c9cce292e886aee99027338a4b80e01880010d5dd36f6409cce292e7
  | 7, 1, 10 => 0x86aee990273494714970b2886aee99027338a4b8818eb80012263e3ba6409cce292e78cd0d60fbba6409cce292e80010d5f3bba6409cce292e78f91f21abba6409cce292e88e30d5dd3204e68a8e292e89252261abba6409cce292e886aee9d4b204e6714970e2886aee9903055cc9cce292e80010d604bba6409cce28b278f90d5dd3204e671497038886afe1dd3205cc9cce292e800119a1abba6409cc97097786aee9903084e6714d512e80010d5dd3206189cce292e7
  | 7, 1, 11 => 0x86afbddd3204e6714bb92e886aee9cb3204e6978e292e886aee99027338a4b85905b80000021ab866409cce292e60010d5dd3204e699ce292e7000ee99027338a4b86881c786aee9dd3206109cce292e80011c5dd3204e6978e292e786afbddd3204e6714d512e886aee9903116229cce292e89130d5dd3204e68c4e292e80010d5dd2be4e67149705b79290d5dd3204e67149701c8000ee9902be4e67149701c70010d5dd3204e68c4e292e786aee9cb3204e67149705b8
  | 7, 1, 12 => 0x9130d5dd3966409cce292e886aee9902734bc714970b2886b026023ba6409cce292e886afe1dd3a96409cce292e886aee99027338a4b88d10380010d5dd3204e6714590a9786aee99027338a4b80e015886aee9d4b2060c9cce292e88e30d5dd3204e67149703880010d5dd3966409cce292e78b70d5dd3204e6714970d188e30d5dd3204e67149711a886aee9903115cc9cce292e886aee9ba3204e6928e292e886b025dd3204e6714d512e80010d5dd27338a4b86885b7
  | 7, 1, 13 => 0x10d5dd3204e692897097786aee9ba3204e6978e292e886aee990273462714c892e89130d5dd3204e6714970b280010d5dd3204e671497010786aee9acb205cc9cce292e886b069dd3a96409cce292e88cd0d5dd3204e6714bb92e886aee9902e64e6714970ef886aee99027338a4b859000886aee9903084e6714970e2886aee990273462714ad92e80010d5dd3204e6714970b279231c61abba6409cce292e886b0bddd3746409cce292e886aee9b6b204e6714c892e8
  | 7, 1, 14 => 0x90516e1abba6409cce292e886afe1dd3206109cce292e8000ee99027338a4b81c01c7000ee99027338a4b88d01c786aff9fc3ba6409cce292e886aee9902e64e69cce292e80010d5dd3204e64b84b85b786aee9acb596409cce292e886aee9902734947149707b886aee9d4b205cc9cce292e886afbddd3204e6714970e289090d5dd3746409cce292e80010d5fabba6409cce292e70010d5dd3205cc7149707b78e31c61abba6409cce292e886aee9d4b206229cce292e8
  | 7, 1, 15 => 0x86aee9903116109cce292e80011461abba6409cce292e786aee9d4ba96409cce292e80012261abba6409cc9709770010d5dd3204e64b84b800786aee9cb3866409cce292e886aee9902734627149701c800118a1abba6409cce292e700112e1abba6409cce292e70000021abba6409cc9709760010d5dd3204e671497060786aee9cfb2057c9cce292e88b70d5dd3204e67149703880011f21abba4e67149705b70010d5dd3204e6644bb92e786aee99027338a4b8688be8
  | 7, 2, 0 => 0x86afbddd3205cc9cce292e80010d5dd3204e664497097786aee99027338a4b8778ed800121e1abba6409cce292e786aee99027338a4b85901c886aee9dd3204e6928e292e80010d59027338a4b81c02d70010d5e4bba4e67149705b70010d5dd27338a4b82d84d786af65dd3204e6714970b280010d5dd3204e6714970df786aee9cb3204e67149701c886aee9903085cc9cce292e80000021abba6409ccd012e686aee990273494714bb92e886aee9902733b8714970388
  | 7, 2, 1 => 0x86afbddd3a96409cce292e80010d5f7bba6407149707b7000001dd27338a4b82d81c686aee99027338a5dcb992e80010d5dd3ba6409cce292e786aee99028e4e67149705b886aee99027338a4b81c0358000ee99027338a4b80e01870010d5dd3204948c4e292e78cd0d5dd3206229cce292e886aee990273462714b292e80010d6023ba6409cce292e70010d5dd3476409cce292e786aee9902734bc714bb92e88cd0d5dd3204e6994e292e80010d5dd3204e67149b92e7
  | 7, 2, 2 => 0x91f0d5fc3ba6409cce292e80010d5dd3206409cce292e70012521abba4e67149705b70010d5dd3204e690ce292e78f90d5dd3204e68c4e292e8001251dd3204e67149701c786afe1dd3204e6928e292e80010d5dd3204bc8c4e292e786b025dd3204e69cce292e80010d5dd32051c9cce292e70010d5dd3204e64b84b81c70010ee1ab204e671497038786b025dd3a96409cce292e886aee9903204e67149705b89130d5dd3ba6409cce292e89251f21abba6409cce292e8
  | 7, 2, 3 => 0xee9d4b206229cce292e79130d5fc3ba6409cce292e886aee9903114e67149705b88f90d5dd3204e6714970b280010d5dd32060a9cce292e70010d5fc3ba6409cce292e786aee99027338a4dc9701c886aee9902a04e6714970d180010d5dd32060c9cce292e786aee9903114e6928e292e80010d5dd3204e6714970ea78f90d5dd3966409cce292e8000ee99027338a4b80e01570000021abba64099ce292e686afe1dd3204e67149705b886b0bdfc3ba6409cce292e8
  | 7, 2, 4 => 0x86aee9903084e6928e292e89130d5dd3a96409cce292e80010d5dd3964e67149705b70010d5dd3a96409cce292e7000ee9cb3204e67149701c78f90d60fbba6409cce292e80010d5dd2734627149705b70011f21abba6409cc97097786aee9d4b204e67149705b8000ee9902734627149701c79130d5dd3206329cce292e80010d5dd3206329cce292e79130d5dd3206229cce292e886aee9d4b204e6928e292e80010d5dd3206229cce292e70010d60d3ba6409cce292e7
  | 7, 2, 5 => 0x86afe1dd3204e67149703880000019027338a4b81c01c60010d5dd3116109cce292e786aee9d4b204e67149701c88b70d60fbba6409cce292e80000021abba4e64b84b85b60010d5dd3204e671497055786aee9dd3204e671497038886aee99027338a4b82d855886aee9903114e67149701c89290d5dd3204e6714970b2886b07e0bbba6409cce292e80011f21ab204e67149703878e30d60fbba6409cce292e80010d5dd27338a4b85905b7000ee99027338a4b85901c7
  | 7, 2, 6 => 0x10d5dd3a94e67149705b70012261abba6329cce292e70000021abba6329cce292e60010d5dd3204e6714970c679132261abba6409cce292e80012261abba6409cce292e70010d5dd3204e67149700070000021abba6409cce292e69130d5dd3204e67149705b886aee99027338a4b82d80080010d5dd3204e67149705b70010d617bba6409cce292e786aee99027338a4b82d85b886aee9903084e67149701c8
  | 8, 0, 0 => 0x21abba640c45399c525ce000004357f0ee99027338a4b9c000000010d5dd3204e64b84bb0000010d5dd3204e6714970b270000021abba72cc81399c525ce00000435774c8139a3138a4b9c000008b70d5dd3204e67149738000000021abba4e67149705b6000000003ba6409cce292e038c00000435774c81399c525c40dc000008e30d5dd3204e67149738000011f21abba6409cce292e70000021abba6409cce292e234e00000435774c81399c525c345c0000086aee9902be4e67149738000010d5dd3204e67149701c7
  | 8, 0, 1 => 0x244c35774c81399c525ce0000000086aee99027338a4b980000086aee99027338a4b82db8000010d5dd3a96409cce292e7
  | 9, 0, 0 => 0x21abba6409cce292e6
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 2 => 37
  | 3 => 48
  | 4 => 59
  | 5 => 70
  | 6 => 81
  | 7 => 92
  | 8 => 103
  | 9 => 114
  | _ => 0

def idWidth : Nat := 11
def wireAt (i : Nat) : Nat := expand (fld (dictB (i / 256) (i / 16 % 16)) 64 (i % 16))
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1024), (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 192), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, 64), (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]

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
private theorem z2_0 : span (Z 2) 1 0 = true := by decide +kernel

private theorem z2 : span (Z 2) 1 0 = true := z2_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : span (Z 3) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3_24 : span (Z 3) 17 24 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 41 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 17) z3_0 z3_24

private theorem z3 : span (Z 3) 41 0 = true := z3_a1

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
private theorem z4_288 : span (Z 4) 16 288 = true := by decide +kernel

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

private theorem z4_a12 : span (Z 4) 304 0 = true :=
  span_join (f := Z 4) (a := 288) (o := 0) (b := 16) z4_a11 z4_288

private theorem z4 : span (Z 4) 304 0 = true := z4_a12

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
private theorem z5_936 : span (Z 5) 24 936 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_960 : span (Z 5) 24 960 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_984 : span (Z 5) 24 984 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1008 : span (Z 5) 24 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1032 : span (Z 5) 24 1032 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1056 : span (Z 5) 24 1056 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1080 : span (Z 5) 24 1080 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1104 : span (Z 5) 24 1104 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1128 : span (Z 5) 24 1128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1152 : span (Z 5) 24 1152 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1176 : span (Z 5) 24 1176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1200 : span (Z 5) 24 1200 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1224 : span (Z 5) 24 1224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1248 : span (Z 5) 24 1248 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_1272 : span (Z 5) 23 1272 = true := by decide +kernel

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

private theorem z5_a39 : span (Z 5) 960 0 = true :=
  span_join (f := Z 5) (a := 936) (o := 0) (b := 24) z5_a38 z5_936

private theorem z5_a40 : span (Z 5) 984 0 = true :=
  span_join (f := Z 5) (a := 960) (o := 0) (b := 24) z5_a39 z5_960

private theorem z5_a41 : span (Z 5) 1008 0 = true :=
  span_join (f := Z 5) (a := 984) (o := 0) (b := 24) z5_a40 z5_984

private theorem z5_a42 : span (Z 5) 1032 0 = true :=
  span_join (f := Z 5) (a := 1008) (o := 0) (b := 24) z5_a41 z5_1008

private theorem z5_a43 : span (Z 5) 1056 0 = true :=
  span_join (f := Z 5) (a := 1032) (o := 0) (b := 24) z5_a42 z5_1032

private theorem z5_a44 : span (Z 5) 1080 0 = true :=
  span_join (f := Z 5) (a := 1056) (o := 0) (b := 24) z5_a43 z5_1056

private theorem z5_a45 : span (Z 5) 1104 0 = true :=
  span_join (f := Z 5) (a := 1080) (o := 0) (b := 24) z5_a44 z5_1080

private theorem z5_a46 : span (Z 5) 1128 0 = true :=
  span_join (f := Z 5) (a := 1104) (o := 0) (b := 24) z5_a45 z5_1104

private theorem z5_a47 : span (Z 5) 1152 0 = true :=
  span_join (f := Z 5) (a := 1128) (o := 0) (b := 24) z5_a46 z5_1128

private theorem z5_a48 : span (Z 5) 1176 0 = true :=
  span_join (f := Z 5) (a := 1152) (o := 0) (b := 24) z5_a47 z5_1152

private theorem z5_a49 : span (Z 5) 1200 0 = true :=
  span_join (f := Z 5) (a := 1176) (o := 0) (b := 24) z5_a48 z5_1176

private theorem z5_a50 : span (Z 5) 1224 0 = true :=
  span_join (f := Z 5) (a := 1200) (o := 0) (b := 24) z5_a49 z5_1200

private theorem z5_a51 : span (Z 5) 1248 0 = true :=
  span_join (f := Z 5) (a := 1224) (o := 0) (b := 24) z5_a50 z5_1224

private theorem z5_a52 : span (Z 5) 1272 0 = true :=
  span_join (f := Z 5) (a := 1248) (o := 0) (b := 24) z5_a51 z5_1248

private theorem z5_a53 : span (Z 5) 1295 0 = true :=
  span_join (f := Z 5) (a := 1272) (o := 0) (b := 23) z5_a52 z5_1272

private theorem z5 : span (Z 5) 1295 0 = true := z5_a53

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
private theorem z6_480 : span (Z 6) 24 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_504 : span (Z 6) 24 504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_528 : span (Z 6) 24 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_552 : span (Z 6) 24 552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_576 : span (Z 6) 24 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_600 : span (Z 6) 24 600 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_624 : span (Z 6) 24 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_648 : span (Z 6) 24 648 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_672 : span (Z 6) 24 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_696 : span (Z 6) 24 696 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_720 : span (Z 6) 24 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_744 : span (Z 6) 24 744 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_768 : span (Z 6) 24 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_792 : span (Z 6) 24 792 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_816 : span (Z 6) 24 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_840 : span (Z 6) 24 840 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_864 : span (Z 6) 24 864 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_888 : span (Z 6) 24 888 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_912 : span (Z 6) 24 912 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_936 : span (Z 6) 24 936 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_960 : span (Z 6) 24 960 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_984 : span (Z 6) 24 984 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1008 : span (Z 6) 24 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1032 : span (Z 6) 24 1032 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1056 : span (Z 6) 24 1056 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1080 : span (Z 6) 24 1080 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1104 : span (Z 6) 24 1104 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1128 : span (Z 6) 24 1128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1152 : span (Z 6) 24 1152 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1176 : span (Z 6) 24 1176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1200 : span (Z 6) 24 1200 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1224 : span (Z 6) 24 1224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1248 : span (Z 6) 24 1248 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1272 : span (Z 6) 24 1272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1296 : span (Z 6) 24 1296 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1320 : span (Z 6) 24 1320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1344 : span (Z 6) 24 1344 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1368 : span (Z 6) 24 1368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1392 : span (Z 6) 24 1392 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1416 : span (Z 6) 24 1416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1440 : span (Z 6) 24 1440 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1464 : span (Z 6) 24 1464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1488 : span (Z 6) 24 1488 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1512 : span (Z 6) 24 1512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1536 : span (Z 6) 24 1536 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1560 : span (Z 6) 24 1560 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1584 : span (Z 6) 24 1584 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1608 : span (Z 6) 24 1608 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1632 : span (Z 6) 24 1632 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1656 : span (Z 6) 24 1656 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1680 : span (Z 6) 24 1680 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1704 : span (Z 6) 24 1704 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1728 : span (Z 6) 24 1728 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1752 : span (Z 6) 24 1752 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1776 : span (Z 6) 24 1776 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1800 : span (Z 6) 24 1800 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_1824 : span (Z 6) 15 1824 = true := by decide +kernel

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

private theorem z6_a20 : span (Z 6) 504 0 = true :=
  span_join (f := Z 6) (a := 480) (o := 0) (b := 24) z6_a19 z6_480

private theorem z6_a21 : span (Z 6) 528 0 = true :=
  span_join (f := Z 6) (a := 504) (o := 0) (b := 24) z6_a20 z6_504

private theorem z6_a22 : span (Z 6) 552 0 = true :=
  span_join (f := Z 6) (a := 528) (o := 0) (b := 24) z6_a21 z6_528

private theorem z6_a23 : span (Z 6) 576 0 = true :=
  span_join (f := Z 6) (a := 552) (o := 0) (b := 24) z6_a22 z6_552

private theorem z6_a24 : span (Z 6) 600 0 = true :=
  span_join (f := Z 6) (a := 576) (o := 0) (b := 24) z6_a23 z6_576

private theorem z6_a25 : span (Z 6) 624 0 = true :=
  span_join (f := Z 6) (a := 600) (o := 0) (b := 24) z6_a24 z6_600

private theorem z6_a26 : span (Z 6) 648 0 = true :=
  span_join (f := Z 6) (a := 624) (o := 0) (b := 24) z6_a25 z6_624

private theorem z6_a27 : span (Z 6) 672 0 = true :=
  span_join (f := Z 6) (a := 648) (o := 0) (b := 24) z6_a26 z6_648

private theorem z6_a28 : span (Z 6) 696 0 = true :=
  span_join (f := Z 6) (a := 672) (o := 0) (b := 24) z6_a27 z6_672

private theorem z6_a29 : span (Z 6) 720 0 = true :=
  span_join (f := Z 6) (a := 696) (o := 0) (b := 24) z6_a28 z6_696

private theorem z6_a30 : span (Z 6) 744 0 = true :=
  span_join (f := Z 6) (a := 720) (o := 0) (b := 24) z6_a29 z6_720

private theorem z6_a31 : span (Z 6) 768 0 = true :=
  span_join (f := Z 6) (a := 744) (o := 0) (b := 24) z6_a30 z6_744

private theorem z6_a32 : span (Z 6) 792 0 = true :=
  span_join (f := Z 6) (a := 768) (o := 0) (b := 24) z6_a31 z6_768

private theorem z6_a33 : span (Z 6) 816 0 = true :=
  span_join (f := Z 6) (a := 792) (o := 0) (b := 24) z6_a32 z6_792

private theorem z6_a34 : span (Z 6) 840 0 = true :=
  span_join (f := Z 6) (a := 816) (o := 0) (b := 24) z6_a33 z6_816

private theorem z6_a35 : span (Z 6) 864 0 = true :=
  span_join (f := Z 6) (a := 840) (o := 0) (b := 24) z6_a34 z6_840

private theorem z6_a36 : span (Z 6) 888 0 = true :=
  span_join (f := Z 6) (a := 864) (o := 0) (b := 24) z6_a35 z6_864

private theorem z6_a37 : span (Z 6) 912 0 = true :=
  span_join (f := Z 6) (a := 888) (o := 0) (b := 24) z6_a36 z6_888

private theorem z6_a38 : span (Z 6) 936 0 = true :=
  span_join (f := Z 6) (a := 912) (o := 0) (b := 24) z6_a37 z6_912

private theorem z6_a39 : span (Z 6) 960 0 = true :=
  span_join (f := Z 6) (a := 936) (o := 0) (b := 24) z6_a38 z6_936

private theorem z6_a40 : span (Z 6) 984 0 = true :=
  span_join (f := Z 6) (a := 960) (o := 0) (b := 24) z6_a39 z6_960

private theorem z6_a41 : span (Z 6) 1008 0 = true :=
  span_join (f := Z 6) (a := 984) (o := 0) (b := 24) z6_a40 z6_984

private theorem z6_a42 : span (Z 6) 1032 0 = true :=
  span_join (f := Z 6) (a := 1008) (o := 0) (b := 24) z6_a41 z6_1008

private theorem z6_a43 : span (Z 6) 1056 0 = true :=
  span_join (f := Z 6) (a := 1032) (o := 0) (b := 24) z6_a42 z6_1032

private theorem z6_a44 : span (Z 6) 1080 0 = true :=
  span_join (f := Z 6) (a := 1056) (o := 0) (b := 24) z6_a43 z6_1056

private theorem z6_a45 : span (Z 6) 1104 0 = true :=
  span_join (f := Z 6) (a := 1080) (o := 0) (b := 24) z6_a44 z6_1080

private theorem z6_a46 : span (Z 6) 1128 0 = true :=
  span_join (f := Z 6) (a := 1104) (o := 0) (b := 24) z6_a45 z6_1104

private theorem z6_a47 : span (Z 6) 1152 0 = true :=
  span_join (f := Z 6) (a := 1128) (o := 0) (b := 24) z6_a46 z6_1128

private theorem z6_a48 : span (Z 6) 1176 0 = true :=
  span_join (f := Z 6) (a := 1152) (o := 0) (b := 24) z6_a47 z6_1152

private theorem z6_a49 : span (Z 6) 1200 0 = true :=
  span_join (f := Z 6) (a := 1176) (o := 0) (b := 24) z6_a48 z6_1176

private theorem z6_a50 : span (Z 6) 1224 0 = true :=
  span_join (f := Z 6) (a := 1200) (o := 0) (b := 24) z6_a49 z6_1200

private theorem z6_a51 : span (Z 6) 1248 0 = true :=
  span_join (f := Z 6) (a := 1224) (o := 0) (b := 24) z6_a50 z6_1224

private theorem z6_a52 : span (Z 6) 1272 0 = true :=
  span_join (f := Z 6) (a := 1248) (o := 0) (b := 24) z6_a51 z6_1248

private theorem z6_a53 : span (Z 6) 1296 0 = true :=
  span_join (f := Z 6) (a := 1272) (o := 0) (b := 24) z6_a52 z6_1272

private theorem z6_a54 : span (Z 6) 1320 0 = true :=
  span_join (f := Z 6) (a := 1296) (o := 0) (b := 24) z6_a53 z6_1296

private theorem z6_a55 : span (Z 6) 1344 0 = true :=
  span_join (f := Z 6) (a := 1320) (o := 0) (b := 24) z6_a54 z6_1320

private theorem z6_a56 : span (Z 6) 1368 0 = true :=
  span_join (f := Z 6) (a := 1344) (o := 0) (b := 24) z6_a55 z6_1344

private theorem z6_a57 : span (Z 6) 1392 0 = true :=
  span_join (f := Z 6) (a := 1368) (o := 0) (b := 24) z6_a56 z6_1368

private theorem z6_a58 : span (Z 6) 1416 0 = true :=
  span_join (f := Z 6) (a := 1392) (o := 0) (b := 24) z6_a57 z6_1392

private theorem z6_a59 : span (Z 6) 1440 0 = true :=
  span_join (f := Z 6) (a := 1416) (o := 0) (b := 24) z6_a58 z6_1416

private theorem z6_a60 : span (Z 6) 1464 0 = true :=
  span_join (f := Z 6) (a := 1440) (o := 0) (b := 24) z6_a59 z6_1440

private theorem z6_a61 : span (Z 6) 1488 0 = true :=
  span_join (f := Z 6) (a := 1464) (o := 0) (b := 24) z6_a60 z6_1464

private theorem z6_a62 : span (Z 6) 1512 0 = true :=
  span_join (f := Z 6) (a := 1488) (o := 0) (b := 24) z6_a61 z6_1488

private theorem z6_a63 : span (Z 6) 1536 0 = true :=
  span_join (f := Z 6) (a := 1512) (o := 0) (b := 24) z6_a62 z6_1512

private theorem z6_a64 : span (Z 6) 1560 0 = true :=
  span_join (f := Z 6) (a := 1536) (o := 0) (b := 24) z6_a63 z6_1536

private theorem z6_a65 : span (Z 6) 1584 0 = true :=
  span_join (f := Z 6) (a := 1560) (o := 0) (b := 24) z6_a64 z6_1560

private theorem z6_a66 : span (Z 6) 1608 0 = true :=
  span_join (f := Z 6) (a := 1584) (o := 0) (b := 24) z6_a65 z6_1584

private theorem z6_a67 : span (Z 6) 1632 0 = true :=
  span_join (f := Z 6) (a := 1608) (o := 0) (b := 24) z6_a66 z6_1608

private theorem z6_a68 : span (Z 6) 1656 0 = true :=
  span_join (f := Z 6) (a := 1632) (o := 0) (b := 24) z6_a67 z6_1632

private theorem z6_a69 : span (Z 6) 1680 0 = true :=
  span_join (f := Z 6) (a := 1656) (o := 0) (b := 24) z6_a68 z6_1656

private theorem z6_a70 : span (Z 6) 1704 0 = true :=
  span_join (f := Z 6) (a := 1680) (o := 0) (b := 24) z6_a69 z6_1680

private theorem z6_a71 : span (Z 6) 1728 0 = true :=
  span_join (f := Z 6) (a := 1704) (o := 0) (b := 24) z6_a70 z6_1704

private theorem z6_a72 : span (Z 6) 1752 0 = true :=
  span_join (f := Z 6) (a := 1728) (o := 0) (b := 24) z6_a71 z6_1728

private theorem z6_a73 : span (Z 6) 1776 0 = true :=
  span_join (f := Z 6) (a := 1752) (o := 0) (b := 24) z6_a72 z6_1752

private theorem z6_a74 : span (Z 6) 1800 0 = true :=
  span_join (f := Z 6) (a := 1776) (o := 0) (b := 24) z6_a73 z6_1776

private theorem z6_a75 : span (Z 6) 1824 0 = true :=
  span_join (f := Z 6) (a := 1800) (o := 0) (b := 24) z6_a74 z6_1800

private theorem z6_a76 : span (Z 6) 1839 0 = true :=
  span_join (f := Z 6) (a := 1824) (o := 0) (b := 15) z6_a75 z6_1824

private theorem z6 : span (Z 6) 1839 0 = true := z6_a76

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : span (Z 7) 24 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : span (Z 7) 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : span (Z 7) 24 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_72 : span (Z 7) 24 72 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : span (Z 7) 24 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_120 : span (Z 7) 24 120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : span (Z 7) 24 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_168 : span (Z 7) 24 168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : span (Z 7) 24 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_216 : span (Z 7) 24 216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : span (Z 7) 24 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_264 : span (Z 7) 24 264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : span (Z 7) 24 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_312 : span (Z 7) 24 312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : span (Z 7) 24 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_360 : span (Z 7) 24 360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : span (Z 7) 24 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_408 : span (Z 7) 24 408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : span (Z 7) 24 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_456 : span (Z 7) 24 456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : span (Z 7) 24 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_504 : span (Z 7) 24 504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_528 : span (Z 7) 24 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_552 : span (Z 7) 24 552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_576 : span (Z 7) 24 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_600 : span (Z 7) 22 600 = true := by decide +kernel

private theorem z7_a1 : span (Z 7) 48 0 = true :=
  span_join (f := Z 7) (a := 24) (o := 0) (b := 24) z7_0 z7_24

private theorem z7_a2 : span (Z 7) 72 0 = true :=
  span_join (f := Z 7) (a := 48) (o := 0) (b := 24) z7_a1 z7_48

private theorem z7_a3 : span (Z 7) 96 0 = true :=
  span_join (f := Z 7) (a := 72) (o := 0) (b := 24) z7_a2 z7_72

private theorem z7_a4 : span (Z 7) 120 0 = true :=
  span_join (f := Z 7) (a := 96) (o := 0) (b := 24) z7_a3 z7_96

private theorem z7_a5 : span (Z 7) 144 0 = true :=
  span_join (f := Z 7) (a := 120) (o := 0) (b := 24) z7_a4 z7_120

private theorem z7_a6 : span (Z 7) 168 0 = true :=
  span_join (f := Z 7) (a := 144) (o := 0) (b := 24) z7_a5 z7_144

private theorem z7_a7 : span (Z 7) 192 0 = true :=
  span_join (f := Z 7) (a := 168) (o := 0) (b := 24) z7_a6 z7_168

private theorem z7_a8 : span (Z 7) 216 0 = true :=
  span_join (f := Z 7) (a := 192) (o := 0) (b := 24) z7_a7 z7_192

private theorem z7_a9 : span (Z 7) 240 0 = true :=
  span_join (f := Z 7) (a := 216) (o := 0) (b := 24) z7_a8 z7_216

private theorem z7_a10 : span (Z 7) 264 0 = true :=
  span_join (f := Z 7) (a := 240) (o := 0) (b := 24) z7_a9 z7_240

private theorem z7_a11 : span (Z 7) 288 0 = true :=
  span_join (f := Z 7) (a := 264) (o := 0) (b := 24) z7_a10 z7_264

private theorem z7_a12 : span (Z 7) 312 0 = true :=
  span_join (f := Z 7) (a := 288) (o := 0) (b := 24) z7_a11 z7_288

private theorem z7_a13 : span (Z 7) 336 0 = true :=
  span_join (f := Z 7) (a := 312) (o := 0) (b := 24) z7_a12 z7_312

private theorem z7_a14 : span (Z 7) 360 0 = true :=
  span_join (f := Z 7) (a := 336) (o := 0) (b := 24) z7_a13 z7_336

private theorem z7_a15 : span (Z 7) 384 0 = true :=
  span_join (f := Z 7) (a := 360) (o := 0) (b := 24) z7_a14 z7_360

private theorem z7_a16 : span (Z 7) 408 0 = true :=
  span_join (f := Z 7) (a := 384) (o := 0) (b := 24) z7_a15 z7_384

private theorem z7_a17 : span (Z 7) 432 0 = true :=
  span_join (f := Z 7) (a := 408) (o := 0) (b := 24) z7_a16 z7_408

private theorem z7_a18 : span (Z 7) 456 0 = true :=
  span_join (f := Z 7) (a := 432) (o := 0) (b := 24) z7_a17 z7_432

private theorem z7_a19 : span (Z 7) 480 0 = true :=
  span_join (f := Z 7) (a := 456) (o := 0) (b := 24) z7_a18 z7_456

private theorem z7_a20 : span (Z 7) 504 0 = true :=
  span_join (f := Z 7) (a := 480) (o := 0) (b := 24) z7_a19 z7_480

private theorem z7_a21 : span (Z 7) 528 0 = true :=
  span_join (f := Z 7) (a := 504) (o := 0) (b := 24) z7_a20 z7_504

private theorem z7_a22 : span (Z 7) 552 0 = true :=
  span_join (f := Z 7) (a := 528) (o := 0) (b := 24) z7_a21 z7_528

private theorem z7_a23 : span (Z 7) 576 0 = true :=
  span_join (f := Z 7) (a := 552) (o := 0) (b := 24) z7_a22 z7_552

private theorem z7_a24 : span (Z 7) 600 0 = true :=
  span_join (f := Z 7) (a := 576) (o := 0) (b := 24) z7_a23 z7_576

private theorem z7_a25 : span (Z 7) 622 0 = true :=
  span_join (f := Z 7) (a := 600) (o := 0) (b := 22) z7_a24 z7_600

private theorem z7 : span (Z 7) 622 0 = true := z7_a25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : span (Z 8) 20 0 = true := by decide +kernel

private theorem z8 : span (Z 8) 20 0 = true := z8_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : span (Z 9) 1 0 = true := by decide +kernel

private theorem z9 : span (Z 9) 1 0 = true := z9_0

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 4096 s poolG xsG || found S NN idx s (ori xsG)
theorem rootChecked : span RootG 5 5 = true := by decide +kernel
theorem xsG_len : xsG.length = 6 := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 4096) (goal 4096) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h
    rw [xsG_len] at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

def CG : Circuit := ⟨[⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [10, 14]⟩], 15⟩
def vec (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool := fun i => [b0, b1, b2, b3, b4, b5].getD i.val false
theorem CG_mono : Monotone2 CG := by
  intro g hg
  simp only [CG, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem CG_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    CG.eval (List.ofFn (vec b0 b1 b2 b3 b4 b5)) = fG (vec b0 b1 b2 b3 b4 b5) := by decide +kernel
theorem CG_eval (x : Fin 6 → Bool) : CG.eval (List.ofFn x) = fG x := by
  have hx : x = vec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext ⟨i, hi⟩
    interval_cases i <;> rfl
  rw [hx]
  exact CG_vec _ _ _ _ _ _

end PEqualNP.Outside.L_meta_12268

theorem PEqualNP.Outside.L_meta_12268 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 9
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12268.mainG PEqualNP.Outside.L_meta_12268.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12268.CG, PEqualNP.Outside.L_meta_12268.CG_mono, by
      have : PEqualNP.Outside.L_meta_12268.CG.size = 10 := rfl
      omega, PEqualNP.Outside.L_meta_12268.CG_eval⟩
