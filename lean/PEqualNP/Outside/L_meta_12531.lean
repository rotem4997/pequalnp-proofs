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
namespace PEqualNP.Outside.L_meta_12531

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 8, 9, 10, 11, 12, 13, 0, 0, 16, 17, 18, 19, 20, 21, 0, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 0, 36, 0, 0, 0, 40, 41, 42, 0, 44, 0, 0, 0, 48, 49, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 6, 6, 6, 6, 6, 6, 6, 7, 6, 6, 6, 6, 6, 6, 14, 15, 6, 6, 6, 6, 6, 6, 22, 23, 6, 25, 6, 27, 6, 29, 30, 31, 6, 6, 6, 35, 6, 37, 38, 39, 6, 6, 6, 43, 6, 45, 46, 47, 6, 6, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 7, 7, 7, 14, 15, 7, 7, 7, 7, 7, 7, 22, 23, 7, 25, 7, 27, 7, 29, 30, 31, 7, 7, 7, 35, 7, 37, 38, 39, 7, 7, 7, 43, 7, 45, 46, 47, 7, 7, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 14, 14, 14, 14, 14, 14, 6, 7, 14, 14, 14, 14, 14, 14, 14, 15, 14, 14, 14, 14, 14, 14, 22, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 35, 14, 37, 38, 39, 14, 14, 14, 43, 14, 45, 46, 47, 14, 14, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 6, 7, 15, 15, 15, 15, 15, 15, 14, 15, 15, 15, 15, 15, 15, 15, 22, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 35, 15, 37, 38, 39, 15, 15, 15, 43, 15, 45, 46, 47, 15, 15, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 22, 22, 22, 22, 22, 22, 6, 7, 22, 22, 22, 22, 22, 22, 14, 15, 22, 22, 22, 22, 22, 22, 22, 23, 22, 25, 22, 27, 22, 29, 30, 31, 22, 22, 22, 35, 22, 37, 38, 39, 22, 22, 22, 43, 22, 45, 46, 47, 22, 22, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 23, 23, 23, 6, 7, 23, 23, 23, 23, 23, 23, 14, 15, 23, 23, 23, 23, 23, 23, 22, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 35, 23, 37, 38, 39, 23, 23, 23, 43, 23, 45, 46, 47, 23, 23, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 6, 7, 25, 25, 25, 25, 25, 25, 14, 15, 25, 25, 25, 25, 25, 25, 22, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 35, 25, 37, 38, 39, 25, 25, 25, 43, 25, 45, 46, 47, 25, 25, 25, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 6, 7, 27, 27, 27, 27, 27, 27, 14, 15, 27, 27, 27, 27, 27, 27, 22, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 35, 27, 37, 38, 39, 27, 27, 27, 43, 27, 45, 46, 47, 27, 27, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 6, 7, 29, 29, 29, 29, 29, 29, 14, 15, 29, 29, 29, 29, 29, 29, 22, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 35, 29, 37, 38, 39, 29, 29, 29, 43, 29, 45, 46, 47, 29, 29, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 6, 7, 30, 30, 30, 30, 30, 30, 14, 15, 30, 30, 30, 30, 30, 30, 22, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 35, 30, 37, 38, 39, 30, 30, 30, 43, 30, 45, 46, 47, 30, 30, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 6, 7, 31, 31, 31, 31, 31, 31, 14, 15, 31, 31, 31, 31, 31, 31, 22, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 35, 31, 37, 38, 39, 31, 31, 31, 43, 31, 45, 46, 47, 31, 31, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 35, 35, 35, 6, 7, 35, 35, 35, 35, 35, 35, 14, 15, 35, 35, 35, 35, 35, 35, 22, 23, 35, 25, 35, 27, 35, 29, 30, 31, 35, 35, 35, 35, 35, 37, 38, 39, 35, 35, 35, 43, 35, 45, 46, 47, 35, 35, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 37, 37, 37, 6, 7, 37, 37, 37, 37, 37, 37, 14, 15, 37, 37, 37, 37, 37, 37, 22, 23, 37, 25, 37, 27, 37, 29, 30, 31, 37, 37, 37, 35, 37, 37, 38, 39, 37, 37, 37, 43, 37, 45, 46, 47, 37, 37, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 38, 38, 38, 6, 7, 38, 38, 38, 38, 38, 38, 14, 15, 38, 38, 38, 38, 38, 38, 22, 23, 38, 25, 38, 27, 38, 29, 30, 31, 38, 38, 38, 35, 38, 37, 38, 39, 38, 38, 38, 43, 38, 45, 46, 47, 38, 38, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 39, 39, 39, 6, 7, 39, 39, 39, 39, 39, 39, 14, 15, 39, 39, 39, 39, 39, 39, 22, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 35, 39, 37, 38, 39, 39, 39, 39, 43, 39, 45, 46, 47, 39, 39, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 6, 7, 43, 43, 43, 43, 43, 43, 14, 15, 43, 43, 43, 43, 43, 43, 22, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 35, 43, 37, 38, 39, 43, 43, 43, 43, 43, 45, 46, 47, 43, 43, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 6, 7, 45, 45, 45, 45, 45, 45, 14, 15, 45, 45, 45, 45, 45, 45, 22, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 35, 45, 37, 38, 39, 45, 45, 45, 43, 45, 45, 46, 47, 45, 45, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 6, 7, 46, 46, 46, 46, 46, 46, 14, 15, 46, 46, 46, 46, 46, 46, 22, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 35, 46, 37, 38, 39, 46, 46, 46, 43, 46, 45, 46, 47, 46, 46, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 6, 7, 47, 47, 47, 47, 47, 47, 14, 15, 47, 47, 47, 47, 47, 47, 22, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 35, 47, 37, 38, 39, 47, 47, 47, 43, 47, 45, 46, 47, 47, 47, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 6, 7, 51, 51, 51, 51, 51, 51, 14, 15, 51, 51, 51, 51, 51, 51, 22, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 35, 51, 37, 38, 39, 51, 51, 51, 43, 51, 45, 46, 47, 51, 51, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 6, 7, 53, 53, 53, 53, 53, 53, 14, 15, 53, 53, 53, 53, 53, 53, 22, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 35, 53, 37, 38, 39, 53, 53, 53, 43, 53, 45, 46, 47, 53, 53, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 6, 7, 54, 54, 54, 54, 54, 54, 14, 15, 54, 54, 54, 54, 54, 54, 22, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 35, 54, 37, 38, 39, 54, 54, 54, 43, 54, 45, 46, 47, 54, 54, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 6, 7, 55, 55, 55, 55, 55, 55, 14, 15, 55, 55, 55, 55, 55, 55, 22, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 35, 55, 37, 38, 39, 55, 55, 55, 43, 55, 45, 46, 47, 55, 55, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 6, 7, 57, 57, 57, 57, 57, 57, 14, 15, 57, 57, 57, 57, 57, 57, 22, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 35, 57, 37, 38, 39, 57, 57, 57, 43, 57, 45, 46, 47, 57, 57, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 58, 58, 58, 6, 7, 58, 58, 58, 58, 58, 58, 14, 15, 58, 58, 58, 58, 58, 58, 22, 23, 58, 25, 58, 27, 58, 29, 30, 31, 58, 58, 58, 35, 58, 37, 38, 39, 58, 58, 58, 43, 58, 45, 46, 47, 58, 58, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 59, 59, 59, 6, 7, 59, 59, 59, 59, 59, 59, 14, 15, 59, 59, 59, 59, 59, 59, 22, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 35, 59, 37, 38, 39, 59, 59, 59, 43, 59, 45, 46, 47, 59, 59, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 6, 7, 61, 61, 61, 61, 61, 61, 14, 15, 61, 61, 61, 61, 61, 61, 22, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 35, 61, 37, 38, 39, 61, 61, 61, 43, 61, 45, 46, 47, 61, 61, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 6, 7, 62, 62, 62, 62, 62, 62, 14, 15, 62, 62, 62, 62, 62, 62, 22, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 35, 62, 37, 38, 39, 62, 62, 62, 43, 62, 45, 46, 47, 62, 62, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 6, 7, 63, 63, 63, 63, 63, 63, 14, 15, 63, 63, 63, 63, 63, 63, 22, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 35, 63, 37, 38, 39, 63, 63, 63, 43, 63, 45, 46, 47, 63, 63, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x11171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f000000000000000011171717153f3f3f000000000000000011171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011171717153f3f3f11171717153f3f3f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011171717153f3f3f11171717153f3f3f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c00000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eee8e8e8eac0c0c0eee8e8e8eac0c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0eee8e8e8eac0c0c0

def cMZZ : Nat := 0x11171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f00000000000000000000000000000000000000000000000011171717153f3f3f000000000000000011171717153f3f3f000000000000000011171717153f3f3f0000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f0000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f0000000000000000000000000000000011171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f11171717153f3f3f

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
  | 3 => 17
  | 4 => 175
  | 5 => 535
  | 6 => 371
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xd3d1d0fb8d75d8d607993c66
  | 3, 0 => 0xfe7dfbe6fe05417ef87c2a86ef844720d71f9b32ca3dd618c5cee20ab3242f3db08e63d4604c45f545dba5783900cbb230a8dbf52e95d3322ac3abe82547d1c91d4085cc
  | 4, 0 => 0x51fc819f51f360814e51e4034a0fc93f466cdf4e4553bc2344c90aae438d5769405910ca3d5719bc3c47aa953c44601b3bff7e7c39c6633134fc24b232afded232acf9dc30fd19dc30f23bf22fa4cd322f0176f02d4a3d942beb13762b5f0fff2b230f9f2714e11221ab689c212fb10520cee3072037a3011d0335321bf777801ad4e1b31aa7780618fcb23a17df411316749c5d165acd6915f53e0d15e80c5715b26da11218c26411c3e5c81069462d100efc8d0fcb25ca0dfe10dd0de235370cd2645d0cd1f4140c4f90920bf733360ba597d90b14513409c35fa808cc02620861fa3006b78f63064bb03403c21b8002d2d56e0141e6b1012803e600b542d4
  | 4, 1 => 0xb5f8b195b1a05c6bb0503cdcaed5e4a3ac4ce9b3abaca73ca990345aa92db97fa88ea7a7a868b758a515a344a39f04eba330a3aa9f858f3d9f7a136a9bcbc2f698f695ac971f1821963912c4955b42949483f0629305686891b3df18905f8ce78fc033eb8f7cb6d58f26dac68dd2d10d8ba819fb8b2a1cd689d1d02c86375a968479b7b6841e61c484071f4a811bdf908103e3c37e019afb7a9570bd79c19844799c5b93793087677884a7b87873d72977b5fe97706622da704ec73f6d3e177b6c922e276c7733586bb04934676a12d76768fd0f66e34848614629375ec17dae5dc0a8d25d7068035bf8c88558ce73b956a2f3a3562aaed2556fd6d3552aec92
  | 4, 2 => 0xffb83642fd5da6a4fd4aa12cfcf138f5fb42d3d4fad012c2f774175af3a6aab9f18b2a45f166984ff13a9311ed8e06bee9466cb8e64a6199e005c58fd7e40c5dd6ffddb9d68bbfb3d4313015d31d3a95d2084cf4d0d2c4a0d0a6bf62cfeb8f4ace67904bce46696cccff3347cad81f38c956c87fc8cb78a3c89f7365c7e092c4c7612b32c5585cfec3b15a3fc0fa2bc8c0eea520c0b65b52c03c9448bf856a90bce649d0bc8f47ddbc3c00fcbb9d6da2b7b65475b781644bb6376927
  | 5, 0 => 0x1455a50413bdbfac13bb4cf113524d3e11f01bb611deefd711114d1310e717fd10b3ed061069462d101fbb80100803b210029f950f73829d0f567db80ee9f0dd0eac62030e6660df0db0b64a0d95df5c0d8001fb0d1411650cd1f4140c5767cf0c3401600b605ed80b1451340b1040b40ae467ce0aded29a0a8555410a591dd30a2017f409fd323609e1a60709c35fa809c20ccf0977e2320967ee71094319810861fa300861b82107cec1f807ce4c6a065671d305dbbf440572db74054db8080523531404d22a6a04596695042d6157042aecba02f173b7021591e2018efb8e017c41cd0134f248012803e6010980bb00fc1c7c0035ff78001b0998000ed45f
  | 5, 1 => 0x329cb051325984b831abfcb431630a0f3148a69830fd19dc301843592fabdc8e2fa7c8942fa4cd322f1def862d4a3d942d3d2b0c2cb8de162bc343392b2ba2c62b0e4aa42ad371e32aa67d932a8b9d9d2987276a28338dc82792035f277cf4d527691ef926632a3426040cb225e9ab8625a6ee3f25517e8624f0209c2479b94e22d69e0722c0f1f622695ed721f69ee921e3ca2c21cdfa2a216ee2ce21284f3a1eea1ced1ede9f401ebcdb3d1e87e1651e7191fb1de918181d376dcf1d12311e1ca65cf21c350cf41bd273eb19a60d86192719e1187e6ad018264fd017de288317dd29c217ca10b617c1ef8e171a8ad2165acd691561356b14d738f314726767
  | 5, 2 => 0x46a941a746a67935461b113e45b3cab045362d5a445255f743efe81d43ebca7e436db114430fb6fe42eb48c042a0700141a53ec4416e083a416abe174169dbe1414fd2b8413f05164099f5b34055004a3fa587cd3f857d643f66a6d23f4198813f0271823edd68763e4edddd3e38d5c23df26fc93d44cea23cfcd2323c9777ba3b7febc13b4b26c73b2588e93a9e1af03a7f50183a6ebe9039c1d44d399524b439735867394ffb303900eab438e45c7438d1181f37cbc43537c8589d371cbc193706f30636704a3e3623a33d35ef435e35d8763a35a96a94357f0e59357a7584356ab1893529b4a335268ec134df4a9d3435f66933d562723390a82e33662187
  | 5, 3 => 0x614fa0fa60969702605c1f5b60051d685fb1d6875f16901a5e2f6feb5dc0baf75c231b125ba944c75b4f4a8e5af739d659da734a59ad3eb2590a859d581fdfdd581ee28857a541b456f4548556edd85b56337a8555f042e05553fb7d5539874955123c9054ad71fc5432d32d53c61267533e8ef951f3608151c97bb1518e0e4d50ea917850b0d4c0504b78ac5012f4794fc2bf3e4f4164704f2c922d4ec6e7ba4e8d88204e6efaad4e0a5e7e4debc2e34d01a8cb4cc9276d4ca38f0a4c75e5564c4cbb9e4c449e584b43635e4b14e58b4ae750fb4ac1ae424a8fa6de4a6682b449d21407498214cc48f82d2848ec00c5486d31ae47bfb9e74787564a475e814c
  | 5, 4 => 0x7eb31e8a7ea40ea57e019afb7cad57247c1767947b9e0fd57a5dcbc9799c5b937991b1e37934a7b3790dcf98790325e1789b0e86789a09a97758014076931020762bfd1d7594cb35753227bb752d2fc175220a237514a5a874835d49736164d5725b277971f1f0167181836d7176ffe6709ac302709782896fe8e0f86fbcbe3e6f726a0f6f289b5f6e57a72c6e4df4c36d93367c6d90a5686d7a91f36c414e2e6c1548f06c11d94e6bd635ab6b443cdc6ad700bd68967e416896109b686acfdf67bd450466f5c4ff66834719661bd7e264ed813e64dd4f5e64c4fd15648a48746465234263b269d3632de66762fb401b627c71bf61c25c03619656c5615ff5e7
  | 5, 5 => 0xa5123b46a4b7bc37a49dd96ca48d33c9a330a3aaa158dd8ba149b450a05485efa040721da03ffb1c9f5dd4f79efaacc49e9bac8d9e6d51549d5addd89cf7aafc9bd3d5f59b8862ff9b872ef49b81a8619b4a1c3d9b045a749946b794991f44d6991506bb981c076197f5c60897adc8ee971f18219694609095d784ef9564c3dd9408a3929286725e926908aa91f0c64a90d20f3d9048bbfb8ff8b04d8f5a6a468f4d4f998cf10b4c8cbc42438c9779fb8b67e7658adfa5828ac50a2e89efd4cd89753a39892e10c1888710238859ff428811aa7c87f90789872d8bb88640cd0a861d87f78548fe3b84558f0383ae957182622572825e84cd80b1ce14806fec8b
  | 5, 6 => 0xc444b88dc407a23dc3ad7887c2d0020cc23548a0c2019b4fc1e5c040c1b9bb02c172ff2ec146f9f0c0fa2bc8c03c9448bf6d4d06bf2f803cbf01ad6dbdfd1e2ebde0d3a7bdd73392bd9a7d94bd81d568bc8f47ddbbc4621bbb95e124bb7ca3f4bb551699ba9aaf02ba5adf96b9d0a2efb96d4109b95de1ddb846962db781644bb752dc62b7063561b65a751eb647cf0bb646487ab603d3ebb575efbeb4f2c606b340fb50b3071cb7b2eaa36db254e939b1c6a7c9b173e663b04a85a1b047c99ab0321869af6d08bcae8a26baad969e7cacfe9a4fac6632deac4ce9b3abd7cfb6aa4107b8a8a0643aa7fb62c6a78054a0a750fb9fa71898e4a6a24568a5daf23c
  | 5, 7 => 0xee9b9b7bee5fff61edfaf321edd3969ced8b55c3ed2dcd13ec960ba4ebf234c0eaee4f10e83ee034e7d29d6ce7a6982ee698ea02e6515f79e3cee650e1e257d7e1dbaf37e00c1f2ddea4e91ede9c8a48de3fb765de23d3f2dd3c38b7dc74f11ddc04510bdaabf0e6d7ff0299d634d72fd622cf62d5034c3bd4e255eed472ef62d3328ec2d31d3a95d31aa2b8d2774c76d1e2fb12d1126320d0c0131ad0565e76cfc779e7cfa8a44bcebf0cbcce98e525ce50117acdc3e117cb190992caf14ececad81f38ca5e30e3ca00d600c99ddfb5c8ff0c61c86a363ec852b190c81115c1c7f5ee93c7e1a17cc77d1ac7c6328d00c59ffef1c52d3ddfc5243aacc4edfc95
  | 5, 8 => 0xff082f92fec6241bfebb8891fe6a09f2fde04c3afd8ed1b0fc44493ffb42d3d4fa52e7dafa18c929f9a08458f937266bf749128cf6ea23f8f662732ff5693607f3fd7ebef1c7b989f1b89797f199d205f150e7a4f09992b0eef09b42
  | 6, 0 => 0x1c2ca32f1bc8deba1b3ee1461b2371b11acdd6cb1ac9e06019d7088b19b4662c199a4dca1973b5cf190aa0c018f7709318ed938d1897dfae188a7b331800244a17dd29c21760772615f7df181567c5a114ecd57114e2c12514aaf8a61455a504140d5814135eb683133293c912e83f9a129e70ea11cd7cb711090c0711067af310db26dc101fbb800ffaf5bd0f73829d0e4445900c6b4eea0c0be6260be0a56a0bcf46160b331a8f0a8555410a5858960991ad6d09431981086356c9085324e90810c7a808001dff07daf8cd074035fd06a3bbf205cf9b33054db80805425df40538318e050c2c5004c5768503c7319a028c65a5018efb8e010980bb00543103
  | 6, 1 => 0x3cd41fb73b91dcec3b75c4a73b42e5eb3b2588e93b239e793a5e8a3d394d5a7a38e45c7438da99683836ba96377e791d36808ede35fc47e935dede3535560e9e3455dba733be91863383237b336e85d832c53c4731abfcb43066e0d73047fe0e300d4f862f8b43f02e557b0d2e3adfb92d786f272ca3e64c2b8d443d2b8780072b6edd142b2eb4642a3eecd629fe5b1429c99a3729b6a29529935d8228d8b5fd288c0efc288ba9d527cb648e27691ef927246afc26632a3425d7fafd2409eb542387b4b6231eb94421fd7b4f21cdfa2a21aebe1020da193a209b6f0f20232caf1f8d3d1f1f13e5601de918181dd3a1541d12311e1d07876e1caa7d3e1c83a523
  | 6, 2 => 0x604d03c6601561775e2f6feb5e10848d5dd0b5215ce316945bbc6bb85af739d659bda49659bc1e0559b4129158ebc54958ae314858689b91567cf24256337a8555cabec455123c9054d4eb28542cae4154028d0053d2655653c05b2c520688d3510c740750746fda501826a54fec21674fdc08694fc2bf3e4f4164704f36fe9b4efd7e974db6dd434d0e67ac4d01a8cb4cfd1dea4cc9276d4c5402f94b7138514b2427444b14e58b4acdc4a74ac6d12a4a81fc844950c7c747bfb9e7471eded546bc5b184686227244ceb31644bf89db43efe81d43b647a8430fb6fe42beaebb428009f441e326df4199d55b40d0b363406d80873f49ab803efd047f3ebff1c8
  | 6, 3 => 0x8cf10b4c8cedeef68c9779fb8b67e7658ac50a2e8a0ebf8d892e10c1885a494b85582d6281482aba804986a47feac6a87f9fee767e56a63a7e21c6717da217757c05fd017a6b882179c325e779aaacba7929eec9790dcf98787921c676a8644d7693102075d7ec417594cb357558d09d748838ab73cc3401738c600c71ee51167139b6a26feb5b416fe8e0f86e57a72c6e4df4c36d76ab8b6d13b5406cf3b8136c74e1ec6bc8871b6bc0f4016b6bc41e6a461c9769a8628b686acfdf6863d220677d77c86683471965ab1e2b6561c94f655b95cb652f908d64e9066364e8d4b964d4edee64bccf7b64673d94627782f862183dc6614fa0fa6110531f60f7aaf3
  | 6, 4 => 0xbb53fe09bb52ff48b9d0a2efb59b8559b4872299b2e95823b2cc533eb1268bd0b089e6ebb047c99aae8a26baadfb2ac7ad37e255acedb7b8acddc3f7acb8ef07abd7cfb6a8e8b0faa8c38d8ea899289aa847fff0a7cf3c1ba7a336dda60f9022a58b6768a4f21753a47f5641a390df1ea35d79e2a27e051da23bf9a6a2315e1ca158dd8ba13ec4e3a104a73ba0d6501ea0253ea59da5e8fd9d5addd89cacfbf698b7bba19783de0e97757fe19773544995d784ef952e6d22950fa79094c6bd2f9431a6d9940f683b93801e68937c57ab926908aa9261174891f0c64a91d5d4ec91496c2791012b4e90a3a29e8fc161ee8f680a4b8f3be71b8ec1f8b08d3a95f7
  | 6, 5 => 0xff082f92febb8891fb94b80ef9a9500bf8af5ccff8881216f5693607f2b739f6ee8abb11edd3969ceafd2bd0e765bda3e6e3869ae6858c84e4e3ddc0e4e0939de4dfb167e40fcb39e2784708e168454fe0baa428e00d4d40de13f076dce92deddc5a31fadb4199bbda92919fd9e61fc4d99978c3d94e4bc0d8e0870fd89c6447d7abcbefd634d72fd521d23ad31d3a95d1e2fb12d0b30092ce84202ace1c5319ccfcfcf0cadef47fc957ef49c91cc3c5c8592b9ac64c738dc59ffef1c25ff273c1e5c040c1b9bb02bfde6314
  | 7, 0 => 0xf8881216f2b739f6ee8abb11e765bda3dc5a31fad31d3a95bb52ff48adfb2ac7a8c38d8ea47f5641a27e051da2315e1ca13ec4e3937c57ab91496c2779aaacba769310207558d09d655b95cb652f908d614fa0fa542cae4144ceb31640d0b363394d5a7a3066e0d7300d4f862e3adfb92387b4b621aebe10190aa0c0135eb68311cd7cb70be0a56a00543103
  | 8, 0 => 0x76931020
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000ff00000000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f0000000000ffffff0000000000ff00ff0000000000000000
  | 0, 1 => 0xcc00cc00cc00cc00aaaaaa00aaaaaa00aa00aa00aa00aa0055555500555555005500550055005500333333003333330033003300330033000f0f0f000f0f0f000f000f000f000f0000ffff0000ffff0000ffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa0000555500005555
  | 0, 2 => 0xf000000ff0000000f0000000f0000000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff000000ff000000f0f0f0f0f0f0f000f0f0f000f0f0f000cccccc00cccccc
  | 0, 3 => 0x3300330033003300330000003300000030303030303030302a2a2a2a2a2a2a2a222222222222222211111111111111110fffffff0fffffff0fffffff000000000fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0000ffff00000f0f00000f0f00000f000f000f000f00
  | 0, 4 => 0x5500550055005500550000005500000050f0f0f050f0f0f0505050505050505044cccccc44cccccc44444444444444443f3f3f3f3f3f3f3f3f3f3f3f000000003f003f003f003f003f0000003f00000033ffffff33ffffff33ff33ff33ff33ff33333333ffffffff333333333333333333333333000000003333000033330000
  | 0, 5 => 0xa0000000a000000088888888888888888888888800000000888800008888000088008800880088008800000088000000808080808080808077777777777777775f5f5f5f5f5f5f5f55ffffff55ffffff55ffffff0000000055ff55ff55ff55ff5555ffff5555ffff55555555ffffffff55555555555555555555555500000000
  | 0, 6 => 0xaaaaaa00aaaaaa00aaaaa8a8aaaaa8a8aaaa8888aaaa8888aaaa0000aaaa0000aaaa000000000000aaa8a8a8aaa8a8a8aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aa888888aa888888aa00aa00aa00aa00aa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000
  | 0, 7 => 0xaaaaaaaaaaffffffaaaaaaaaaaffaaffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaaa0a0a0aaaaaaaaaa888888aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000
  | 0, 8 => 0xcc000000cc000000cc00000000000000c8c8c8c8c8c8c8c8c0f0f0f0c0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c000000000c000c000c000c000c0000000c0000000bbbbbbbbbbbbbbbbafafafafafafafafafafafaf00000000af00af00af00af00af000000af000000aaffffffaaffffffaaffaaffaaffaaffaaaaaaaaffffffff
  | 0, 9 => 0xccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc00000000cccccc00cccccc00ccccc8c8ccccc8c8ccccc0c0ccccc0c0cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc8c8c8ccc8c8c8ccc0c0c0ccc0c0c0cc88cc88cc88cc88cc888888cc888888cc00cc00cc00cc00cc00cc0000000000
  | 0, 10 => 0xeaaaeaaaeaaaeaaaeaaaaaaaeaaaaaaae0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0ddddddddddddddddcfcfcfcfcfcfcfcfccffffffccffffffccffffff00000000ccffccffccffccffccccccccffffffffcccccccccfcfcfcfccccccccccccccccccccccccccccc0c0cccccccccccc0000ccccccccccc0c0c0cccccccccc000000
  | 0, 11 => 0xeeaaeeaaeeaaeeaaeeaaeeaa00000000eeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaeeaaaaaa00000000ee00ee00ee00ee00ee00aa00ee00aa00ee000000ee000000ee000000aa000000ececececececececececececccccccccecececec00000000eccccccceccccccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaaaaaeaeaaaaa
  | 0, 12 => 0xf0a0a0a0f0a0a0a0f000f000f000f000f000f00000000000f0000000f0000000f000000000000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000aaaa0000eecceecceecceecceecccccceecccccceecccccccccccccceecc0000eecc0000
  | 0, 13 => 0xf0f0f0f0f0f00000f0f0f0f0f0c0f0c0f0f0f0f0f0c0c0c0f0f0f0f0f0000000f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0a0a0f0f0a0a0f0f00000f0f00000f0f0000000000000f0e0e0e0f0e0e0e0f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0
  | 0, 14 => 0xfaaaaaaafaaaaaaafa000000fa000000f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f0f0f0f8f0f0f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f0f0f0f3f0f0f0f1f1f1f1f1f1f1f1f0fffffff0fffffff0fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0
  | 0, 15 => 0xfcf0f0f0fcf0f0f0fcf0f0f0f0f0f0f0fcccfcccfcccfcccfcccccccfcccccccfc00fc00fc00fc00fc000000fc000000fafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000faf0f0f0faf0f0f0faf0f0f0f0f0f0f0faaafaaafaaafaaa
  | 1, 0 => 0xff000000ee000000ff000000cc000000ff000000aa000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fe000000fe000000fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0
  | 1, 1 => 0xff00cc00ff00cc00ff00c000ff00c000ff00c000ff000000ff00aa00ff00aa00ff00a000ff00a000ff00a000ff000000ff008800ff008800ff005500ff005500ff001100ff001100ff000000ffffffffff000000ff555555ff000000ff550000ff000000ff00ff00ff000000ff000000ff000000fa000000ff000000f0000000
  | 1, 2 => 0xff00fff0ff00fff0ff00ffccff00ffccff00ffaaff00ffaaff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff000000ff00ff00fa00fa00ff00ff00ee00ee00ff00ff00aa00aa00ff00ff00aa000000ff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00f000ff00c000ff00f000ff000000
  | 1, 3 => 0xff880000ff000000ff808080ff808080ff800000ff800000ff555555ff555555ff50ff50ff50ff50ff505050ff505050ff500000ff500000ff33ff33ff33ff33ff333333ff333333ff330000ff330000ff11ff11ff11ff11ff111111ff111111ff0fff0fff0fff0fff0f0f0fff0f0f0fff0f0000ff0f0000ff00ffffff00ffff
  | 1, 4 => 0xffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaaaaaaff000000ffaaaaaaaaaaaaaaffaaaaaa00000000ffaa0000ffaa0000ffaa0000ff000000ffaa0000aaaa0000ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ffa0a0a0ff000000ff88ff88ff88ff88ff888888ff888888ff888888ff000000
  | 1, 5 => 0xffccffccff00ff00ffccffcc00000000ffccff00ffccff00ffccccccffccccccffccccccff000000ffccccccccccccccffcccccc00000000ffcc0000ffcc0000ffcc0000ff000000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0ffc0c0c0ff000000ffc00000ffc00000ffaaffaaffaaffaaffaaffaaff00ff00
  | 1, 6 => 0xfff0fff000000000fff0ff00fff0ff00fff0f0f0fff0f0f0fff0f0f0ffc0c0c0fff0f0f0ff000000fff0f0f0faf0f0f0fff0f0f0f0f0f0f0fff0f0f000000000fff00000fff00000fff00000ff000000ffeeffeeffeeffeeffeeffee00000000ffeeeeeeffeeeeeeffeeeeee00000000ffee0000ffee0000ffccffccffccffcc
  | 1, 7 => 0xffff0000ff000000ffff0000f0f00000ffff0000cccc0000ffff0000aaaa0000fffcfffcfffcfffcfffcfcfcfffcfcfcfffcfcfc00000000fffc0000fffc0000fffafffafffafffafffafffa00000000fffafafafffafafafffafafa00000000fff0fff0fff0fff0fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff0f0f0f0f0
  | 1, 8 => 0xffff8888ffff0000ffff8080ffff8080ffff5555ffff5555ffff3333ffff3333ffff0f0fffff0f0fffff00ffffff00ffffff00ffffff0000ffff0055ffff0055ffff0033ffff0033ffff000fffff000fffff0000ffffffffffff0000ffff5555ffff0000ffff00ffffff0000ffff0000ffff0000fff00000ffff0000ffcc0000
  | 1, 9 => 0xfffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000ffff0000ffffeeeeffffeeeeffffccccffffccccffffccccccccccccffffc0c0ffffc0c0ffffc0c0ffff0000ffffaaaaffffaaaaffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffa0a0ffff0000ffff8888ffff8888
  | 1, 10 => 0xffffffff00ff00ffffffffff00555555ffffffff0000ffffffffffff00005555ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffff0000ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffcfc00000000fffffafafffffafa
  | 1, 11 => 0xffffffffaaaaaaaaffffffffaaaa0000ffffffffaa000000ffffffffa0a0a0a0ffffffffa0000000ffffffff88888888ffffffff88000000ffffffff80808080ffffffff55555555ffffffff50505050ffffffff33333333ffffffff33000000ffffffff11111111ffffffff0f0f0f0fffffffff03030303ffffffff00ffffff
  | 1, 12 => 0xfffffffffcfcfcfcfffffffffafafafafffffffffa000000fffffffff0f0f0f0fffffffff0f00000fffffffff0c0c0c0fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffc000c000ffffffffc0000000
  | 1, 13 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffff0fff0fffffffffff0f0f0ffffffffffccccccffffffffffaaffaaffffffffffaaaaaaffffffffff00ff00ffffffffff000000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x16a521cced89e3e1db53c733
  | 3, 0, 0 => 0xe85b53c7c470add48704b4a90e0654892d1167c4e85a9487c470aed48654e65b548734e15b1487c4892b1387c4893853c734e65b1487c4b4c4948734b5a71167c486b8548734b5b853c7c4893693c7c4
  | 3, 0, 1 => 0xdeda9487c4
  | 4, 0, 0 => 0xd5c5dc2a43e2eae24e1592917571470a90f8bab8938562a45d5c49c2a4352f0a24e1521f17572070a90f8babb4a90f8655d5c49b4a43e2eae7ee1521f17572270a90f0b8295ab1387c5d5c49487c26aeae24e1521b97576989290f8b6989290f8705
  | 4, 0, 1 => 0xd5c69c2a43e2eadc2a43e1197731270a90f8b1282291167c5ba449c2a43e2eae24e14f1f1756b856a90f8b1270a78f8705d5c49c2953e2eae24a4461f1756e15ba90f8babb5b85487c5d5c85c2a43e2eae24e7521f1757126b290f8bab8ab85487c5
  | 4, 0, 2 => 0xd5c49d8a43e2eae24e1521cd7851e70a90f8bab89385847c5d5c496c8b3e2ef624e1521f1757126f290f8bab88b85487c58931d5aa43e2f42d312521f17571270a90eebd086b85487c589429c2a43e2eae24e15a9f17571270a68f8b1270a90f8485
  | 4, 0, 3 => 0x95b8588a4382eae24ad521f17851270a78f8bab893855ea45d5d01c2a43e2eae42da521f17851270ac948bab70a90f82f5e1449b4a43e2d8a24e1521f17a11270a78f8bab89384f84b5d5c49487c112d9224e1521f17573470a90f8bab8f38564a45
  | 4, 0, 4 => 0xd5c49b6a43e2c49c2a43e0e17571270b04f8b0c70a90e0655d9c49c2a43e2dda24e1521f179b1270a90f8bae89385487c5d5db1c2a43e2eaed6a4459f17576a89290f8bc6893853c7c58938548853e2c49c2c8521c177b0d70a90f8bab89385487d5
  | 4, 0, 5 => 0xe15b624a43e2eaed50d521f17571270a94f8bab8eb85487c5d5c49c2a43daeaea8e1521f17052b5a22cf8bab89385467c5a7449c2a43e2c49c2b4521f17573a70a90f8b1270a90f8555d5c49d6a43e2eae86e1521f15c2c75c290f8bc189385487c5
  | 4, 0, 6 => 0xd5ce5c2a43e2eadc2b8521f17571270a84f8bac89385487c5d5c49a4a43e2eaed8da521f176d1270a90f8bab89389487c5d5db6249e3e2eae24e1599f17571256290f8bab893853e7c5d5c4964ad522ef624e1521cd77b1270b08f8babb6c4964a45
  | 4, 0, 7 => 0xe1551c2a43e2eae24e1521fd7711270a90f8bab893a1487c5893858ea43e2eae24e1521d57a1ccb6a90f8b1270af9487c589431c2a439aeae24e1572916491270a90e6bab9f385487c5d5c49e4a43e2f2a24e1521f17570870a90f8ba789385487c5
  | 4, 0, 8 => 0xa4b85487c32aeae24e1521e577f1270a90e6bab70af548655d5d49c2a43e2eae24dd521f17052b6d278f8b4989385487c589361388b3e2ec624e1521f17911270a90f8ba189385487c58938550a43e2eaea8e1592917571270a90f0b1270b613c7c5
  | 4, 0, 9 => 0xd5db5c2a439ac49c2bb521f17576d70b08f8bbdb6b85487c5d5c49c2a43e2eae24fe521f17996b70a90f8b6b70a91387c589385929c3e2eae24e15e2917575370a90f8bab9eb85487c589411c2a43e2eae24f1521f1799126d290f8b126d291387c5
  | 4, 0, 10 => 0x6ae24f2611f177b1279290f8bab70a91067c5ddc49c2a43e2eae1ae1521f161ae1521f0e0bb489385487c5d5b8584b83e2eae1ee1521f17991270a90e6b1270a9138735d5c49c2a43b2eae24e1520f17811270a90f8b7989385487c5
  | 5, 0, 0 => 0xe66ae24e14f1f1b571270a71167c6e671a24e1521f1b8d1270a91387c6d5e1624e1521f1b572b84b85487c6d5e8e24e1521f1b578a95b85487c6d5eae24e1521f1bb5ab89385487c6006aed312521f17571270a90f8706d5c49c2a4481f1b61ab89385487c6d5c49c2a4449f1b571270a90e06c6
  | 5, 0, 1 => 0xd5c49c2a43e039b578395b85487c6d5e7224e1521f1801ab90385487c5d5c49ece1521f1b571270a90f8416d5c49c2a43e0cdb574c89385487c6006ae24da521f17571270b3d487c6c153a24e1521f1b571270a90f8116d5db624f9521f1b57828db85487c6d5c49c2a44f1f1b571270a91167c6
  | 5, 0, 2 => 0xd5e1256e1521f1b57a489385487c6d5d1624e1521f1b571270a90f83e6d5e7e3ee1521f1ba3ab8938548746006ae24e1592917578293b85487c6d5e0aa8e1521f1b56e15d2e1487c60070a24e1521f175782b9385487c6d5c49c2a43e03db678295b85487c600449c2a43e0317057695b85487c6
  | 5, 0, 3 => 0xd5e5e56e1521f1b578095b85487c6e1eae24e1521f1b57829ab85487c6d5c49c8e1521f1b578695b85487c6e76ae24e1521f1b574c70a90f8656e0e0a56e1521f1801abb5b85487c5d5e0ae2e1521f1b578295b6d487c6d5e3e56e1521f1b575c89385487c6d5c49f2e165291aa34e89385487c6
  | 5, 0, 4 => 0xc14adc2b4521f1b578292b85487c6d5cad8aad521f1b27828e385487c6d5d8656e1521f1ba9ab89385487c6d5e0a56e158291b571270a90f82b6d5c49c2a43e145b573695b85487c6d5c49c2a43e06db579b95b85487c6006ae24e14f1f17abab89385487c6d5c9a24e1521f1b278289385487c6
  | 5, 0, 5 => 0xd5c49c2a43e10db571689385487c6d5c49c2a4491f1b57a289385487c6d5e5eace1521f1b57828fb85487c6d5cc224e1521f1b574870a90f8666d5c4a0ea4459f1b572b892b5487c6d5c49c2c2521f1b574f89385487c6d5c49e0e1521f1b578270ae9487c6d5e0a56e1519f1b054e95b85487c6
  | 5, 0, 6 => 0xee6ae24e1521f1b571270a90f81a6006ae24e1289097571273385487c6d5e6224e1521f1801ab521f068285d5e4224e1521f1b578295b854a7c6e86ae24e1521f1b571270a90f8256d5e0a5ce1521f1b578295b852c7c6d5c49c2b2521f1b578270ae1487c6d5e5e3ce1521f1b578295b85487b6
  | 5, 0, 7 => 0xd5e0a56ac521f1b56e1652e1487c6d5db624e1521f1b5782893c9487c6d5e0a56e14f9f1801ab8938548735d5de256e1521f1b571270a90f8376d5c49c2bf521f1801ab89385847c5d5e0a56b256a91801bd89385487c5d5c49c2a43e1c5b578295b85487e6d5e09c2a4421f1b571e70a91167c6
  | 5, 0, 8 => 0xd5c49c2a43e0498011270a90a20c500449c27c210317052470a90e0666d5c49c2df521f1b575489385487c6d5e0a5ee1521f1b578270ae5487c6e7eae24e1521f1b6d8295b85487c6d5d7e24e1521f1b571270a90f8646d5c49c6e1521f1b578295b89487c6d5c49c2a43e091b571270a90f8536
  | 5, 0, 9 => 0xd5c49c2d3521f1b99abb6c49487c6ebeae24e1521f1b571270a99487c6c1449c2c7521f1b577c93385487c6d5c89c2a43e1b1b577189385487c6e16ae24e1521f1b576d70a90f8656d5c49c2a43e085b571270a90f80c6d660a56e1521f1b571270a90f80d6d5e2656e1521f1b571270ab5487c6
  | 5, 0, 10 => 0xd7eae24e1521f1bb1ab89385487c6d5c49c2a43e1c9b5782b9369487c6e4449c2cc521f1b5782aab85487c6d5e0656e1521f1b4f8295b85487c6d5c49c2b25222db579eb8b85487c6d5d1224e1521f1b577fb9b85487c6d5c49c2a43e175b851270a91167c6d5c9a1ae1521f1b57127c385487c6
  | 5, 0, 11 => 0xd5e7e56e1521e1b578295bc9487c6d5c4a02e1521f1b57828938548786d5c4a00e1521f1b56e162ae9487c6e36ae24e1521f1b573389385487c6dbeae24e1521f1b571270a90f8286d5c49c2a43e101b571270a90f8096d5c49c2a43e029b75ab89385487c6d5c49c2a4451f1b571270a90f8066
  | 5, 0, 12 => 0xe165e56e1521f1b578289b85487c6d5c7e24e1521f1b571270a90f8626d5e6644e1521f1b918289385487c6d5dea24e1521f1b579d89385487c6d5c49c2a43e1cdb571270a90f85a6d5e0a46e1521f1b577f89385487c6e4eae24e1521f1b571270b39487c68938594c7521f1b571270ae9487c6
  | 5, 0, 13 => 0xd5c49fae1521f1b571270b71487c6d5e0a5ae1521f1b57a089385487c6c14adc2c7521f1b57a689385487c6d5e0aa4e1521f1b571270ae1487c6d5e3a56e1521f1b054989385487c6d5e5e56e159291b57829db85487c6d5e7e24e1521f1b571270a91307c6c14adc2be521f1b573889385487c6
  | 5, 0, 14 => 0xdaeae24e1521f1b577589385487c6e2eae24e1521f1b571270a90f8236d5c49c2cc521f1b571270a90f8296d5e4a24e1521f1b571282b85487c6d5c49c2a43e0d1b576589385487c6d5c49c2a43e0c1b718295b85487c6c1539c2a43e199801ab892b5487c5d5c49c2a43e171b571277385487c6
  | 5, 0, 15 => 0xd5e0a24e1521f1b575795b85487c6d8e0a56e1521f1b918295b85487c6d0e0a56e1521f1b577e89385487c6d5dfe56e1521f1b571270b2d487c6d5e0a56e0521f1b7bab89385487c6d5c49c2a44a1f1b578295b8548786d5c49c2a43e19db052b70b613c7c6c144a08e1521f1b576389385487c6
  | 5, 1, 0 => 0xd5c49dae1521f1b578795b85487c6d5e0a38e1521f1b571275385487c6d5d7624e1521f1b571270a90f83d6d5c49c2d0521f1b571270a91267c6d5c49c2a43e13db054995b85487c6edeae24e1521f1b052b6c271167c6d5c49e4a43e195b991270b61487c689385b0a44e1f1b571270a90f84e6
  | 5, 1, 1 => 0xd5c49c2c8521f1b571270a90f8266d5c49c2ca521f1b052b82385487c6d5c49c2a43e01db7dab89385487c6d5dfe56e1521d1b998295b69487c6c14adb4a44e1f1b578294385487c6d5c49c2a4501f1b572b70b11487c6d5e0a56e1521e5b57828c385487c6d5dba24e1521f1b575189385487c6
  | 5, 1, 2 => 0x95b858ec5521f1b572489385487c6d5e09c2a43e11db574695b85487c692449c2a43e1c1b578d89385487c6d5d0624e1521f1b052b70b25387c6d5e0a32e1521f1b571270a91327c6d5c49c2a43e115b57aa89385487c6d5e0a24e1521d1b57a989385487c6006ae24a43e0d17571270a90f86b6
  | 5, 1, 3 => 0xd5db624a4459f1b572b70a90f8326006aea8e1521f17576789385487c6d5c49c2c3521f1bb3ab89385487c6d5c49c2a44e9f18014e89385487c5d5c49c2a43e0b1b8dab89369487c6d5c4a18e1521f1b571270a91047c689431c2a43e1c1b5771b3385487c6d5c49c2a43e18db578295b85487c6
  | 5, 1, 4 => 0xd5e0a1ae1521f1b571270a911e7c6d5cadc2c0521f1b571279385487c6d5c49c2d5521f1b571270a90f8616d5e0a3ce1521f1b571270a91447c6d5c49c2a43e1b5ba1ab8938548736d5c49c2a4409f1b571270a90f8356d5c49c2a43e165b579195b85487c6d5c31c2a43e195b579695b85487c6
  | 5, 1, 5 => 0xd5c49c2d1521f1b571274b85487c6d5c49c2a43e195b576795b85487c6d5b85488f3e195b571270a90f8136d5c7224e1521f1b5782b4c49487c6d5c49f4e1521f1b57127cb85487c6d5e0a56e1520f1b571270a90f85e6006adc2a43e0a17571270a9d487c6d5c4a24e1521f1bafab91385487c6
  | 5, 1, 6 => 0x6ae24a4288d17578895b85487c6006ae247c210d17a12489385487c6d5c49c2a43e149b57828938564a46e160a24e1521f1b571270a90f8686d5e0a56e1521e9b57125222cf8626d5e0a40e1521f1b571270a910e7c6006adc2b8521f17578289369487c6dfeae24e1521f1b7f1270a90f8706
  | 5, 1, 7 => 0xd5d1e56e1521f1b578295b85486e6d5e0ad32b521f1b5782893853c7c6006ae24f2521f17571270b61487c6d5c49c2a43e0edb5782b3385487c6d5c49eae1521f1b571270aa5487c6d5c4a20e1521f1ba11286385487c6d5e0ad6e1521f1b571270b5d487c6d5d8224e1521f1b575089385487c6
  | 5, 1, 8 => 0xd5d51c2a4459f1b578295b8562a46e160a56e1521f1b575689385487c6d5c4a16e1521f1b57a889385487c600449c2c7521f17578295b69487c6d5c49c2a43e005b571270a90f8206d5d3a24e1521f1b571270a90e065600449487c1a0317576989431487c6d5c49c2a43e159b575e89385487c6
  | 5, 1, 9 => 0x6adc2a4288a1401ab709f084285d5db6b8e1521f1b8fab89385487c6d5c49c2a43e015b575a89385487c6d5c49c2a43e131b79ab89385487c6d5e0a56e7521f1b571279b85487c6d5c4a1ae1521f1b65ab89385487c6d5c49c2a43e009b578295b59487c6d5c49c2a43e111b578295b8564a46
  | 5, 1, 10 => 0xd5da224e1521f1b578289385847c6d5c49c2a43e1a5b571270a90f82a60072224e1521f17a1bf89385487c6d5d7224e1651f1b7b8289385487c6c14ae08a4459f1b571270a90f8506d5df624e1521f1b578295b853c7c6d5c49c2a43e0b5b052b70a78f8706d5c49c2e1521f1801ab8938548785
  | 5, 1, 11 => 0xc14ae14e1521f1b571270aa9487c6d5e0a56e15a9f1800e1521f0500c5d5c49c2a4521f1b571270a90f8396e66ae24e1521f1b571270a91387c6e6449c2a43e1c1a24e152270f8706006aea4e1521f14014989385487c5c14adc2a43e121b57828938548736d5c49c2a43e129b7fab86b85487c6
  | 5, 1, 12 => 0x44a08e1521f17573195b85487c6d5c4a0ce1521f1a250782385487c6d5c49c2a43e011b575989385487c6d5c49c2ab521f1b576b89385487c6d5c49c2a43e125b573c89385487c6d5cde24e1521f1b571270a90f8606d5df256e1521f1af92b70a90f8706d5c49fee1521f1b571270a911a7c6
  | 5, 1, 13 => 0xd5c49eee1521f1801ab89385487c5d5e0a56e1611f1b578295ad9167c6d5c4a0ee1521f1b571270ad9487c6dee0a56e1521f1b571270a90f8786d5c49c2a43e09db571270a911c7c6d5c49c2a43e079b052b63ab5487c6e86aedae1521f1b571270a90f8586d5c4a1ce1521f1b571270a91107c6
  | 5, 1, 14 => 0xd5d2e24e1521f1b571270a90f8186d5dadc2d8521f1b578295385487c6d5c49c2a43e17db571270a90f82e6c159256e1521f1b571270a91007c6d5d6e24e1521f1b571270b1d487c6d5c81c2d8521f1b571270a90f8666d5e0a56ec521f1b571270a90f8006d5c49c2bd521f1b578295b8548736
  | 5, 1, 15 => 0xd5d2624e1521f1b57126c291167c6d5cca24e1521f1b571270a90f8426d5c49c2da521f1b5712652b5487c6dec49c2a43e195b571270a90f87c6e46ae24e1521f1b858295b8564a46e873224e1521f1ba11270a91387c6d5c49c2a43e00db576989385487c6e160a56da521f1b571270a91367c6
  | 5, 2, 0 => 0x6ae1ae1521f1757127e385487c6c14adc2a4429f1b052b70b2148706d5c4a08e1521f1b571270a90f81c6e96ae24e1521f1a994989385487c6d5e0a56ad521f1b571270a90f8576e160a56e14f1f1b571270a910c7c6d5c49c2d9521f1b571270a90f86f6d5c49c2a43e0e9b571270b08f8656
  | 5, 2, 1 => 0x1ab8938548515d5c49c2c9521f1801ab89384f8425d5c49dee1521f1b574a89385487c6d5c49c2a43e021b8d8295b853c7c6
  | 6, 0, 0 => 0xebeae571270a90f8fabc14adc2a4499f1f578295b85487c27beaf051286385487c7edeaf052b70a90f8fab95c49c2a43e031c01ab89385488b3e372f578295b85487c7e660a56e16c290f8f8295b85b0a44e1f1f5782c14adc2a43e3eaf052489385487c7d5e0afd2b70a90f8e00d5e2a56e1521f1801ab89385487c3836af052b70a91227c7
  | 6, 0, 1 => 0xe36ae571270a90f8e00d5e0ae2e1521f1b572b89385487c143803575c89385487c6d5e0ae71270a90f8fabc1449c2a43e059f5782b74adc2a43e3eaf055195b85487c7d5e0a570370a90f8fabc14addae1521f1c000089385487c062eaf054295b85487c7d5e0a56ea70a90f8e00d5d3224e1521f1b5782aecadc2a43e3eaf052b70a90f83d7
  | 6, 0, 2 => 0x6ae24e1521f0a2dabc1449c2a4479f1fadabc14adc2a43e3eaf052b70a91327c7d5eab052b70a90f8e00d5cc1c2a43e059b572b893859ca43e3803579795b85487c6d5ea7052b70a90f8e00d5e0a56a43e0d1b578295b85487c35beaf052b70b21487c7d5e0a56e1521f04cfabc14adc2ca521f1f578295b85487c03befb578295b85487c7
  | 6, 0, 3 => 0xd5e9a571270a90f8fabc14adc2a43e02df5782bdcadc2a43e3eaf05127cb85487c7d5e0a56e1521f0c6fabc1449c2a43e179c01ab70a90f8250b36ae571270a91307c7006af04e1521f050dd7d5e0a52e1521f1f578295c91c2a43e3eaf051289385487c7d5e0a56fb70a90f8f8295c91c2a43e1c1f578dc14adc2a43e3eae571270a90f8627
  | 6, 0, 4 => 0xd5e0ae72b70a90f8fab95c49c2cc521f1f572b89385487c1a380357828fb85487c6d5e0a56e1521f02cfabc15cec0e1521f1f578289385487c32beaf056795b85487c7d5e0a56e161a90f8fd9d5e0a56e1521f1c01abc138574a43e36af052b70a913a7c70060a9d2b70a90f8dabc14adc2a43e0b1f8dabc14adb4a43e3eaf052b86385487c7
  | 6, 0, 5 => 0xd5e0a56e1521f0c2fabc14adc2c5521f1f5782b7cadc2a43e3eaf3f8291385487c7d5cae24e152244f8fabc14adc2a4511f1f578295b85487c36b803578270a90a2256006af04e13e1084adabcacadc2a43e1b1f578295b8548813e3803a1ab89385487c6d5e0a56e1521f06ae00d5c49c2a43e095b578295b85487c2cbeff578289385487c7
  | 6, 0, 6 => 0x609c2a43e09418dabc14adc2a43e04df579ec14adc2a43e3eaf052b8e385487c7d5e97052b70a90f8e00d5db624e1521f1b578295be5c2a43e3803572b521f068166d5e0a56e1521f0bcfabc1449c2d8521f1f578295b854ea43e3eaf052b89385487c7006af04e1521f046dabc14adc2a4479f1f5782b0449c2a43e3eaf052b70b55487c7
  | 6, 0, 7 => 0x6ae5712521f068dabc14ad488b3e189f5782b84adc2a43e3eae571270b29487c70075f571270a90f8dabc14adc2a4439f1f5babc14adc2a43e3eff578295b85487c7006ae24e1521f018dbfc14adc2a43e1c1f572b70b298aa43e3eaf052b70b45487c7d5e09c2a4489f0ccfabc14add2e1521f1f578295b85487c32beaea32b89385487c7
  | 6, 0, 8 => 0xd5e0a56e166a90f8fabcbcadc2a4459f1f578295b85b0a43e3eaf052b70a90f83b70071b571270a90f8dabc14adeae1521f1c01ab89385487c143713578295b85487c7d5cae491270a90f8fabc14adc2d7521f1f578295b85487c083eaf056095b85487c7d5e0aa12b70a90f8e00d5e0a56a4288d1801abc14acf8421a36af052b70a90f8527
  | 6, 0, 9 => 0xd5e0a570270a90f8fabc14adc2a43e005f578295b95c2a43e3803579f89385487c6d5dce571270a90f8e00d5c49c2a44c1f1b578295b85487c0fbeaf054e95b85487c7d5cae24e1521f02ce00d5c49c2a43e189b5799c147dc2a43e3803052b521f0680c6d5e0a56e1521f028fabc157a56e1521f1c01ab893859ca43e36af052b70a90f81d7
  | 6, 0, 10 => 0xd96af052b70a90f8e00d5c49c2a43e0d1b578a95b85487c12beaf052b70b51487c7d5e0ab12b70a90f8fabc15f256e1521f1f578295b85487c223e57278295b85487c7d5e0aad2b70a90f8fabc14ae16e1521f1f99abc1449c2a43e3eaf051270a91387c7d5ea3052b70a90f8e00c14adc2c7521f1801abd3449c2a43e36af052470a90f8667
  | 6, 0, 11 => 0xd5e0a56f470a90f8fabc144a0ee1521f1c01abbfcadc2a43e36af052b70a90f8507d5e0afb2b70a90f8fabc14adc2a43e0b5f578295b85c2a43e3803578295b8548786e3eaf052b70a90f8fabc14adc2a43e015f5782b9b85487c333eaf052b70a90f84c7d5e0a56e1521f062fbcd5e0a56e1521f1f578295bcdc2a43e3803571270b31487c6
  | 6, 0, 12 => 0xd5e0a56e155290f8e00d5e0a38e1521f1b578295b8548a43e3eaf178295b85487c7e66af052b70a90f8fabc14adc2a44e1f1f578295b85487c1b3f33052b70a90f8707d5e0a56e1521f02ef8295b85489c3e1c1f578289385487c333eaf052b70a90f84a7d5e53052b70a90f8e00d5e0a24e1521f1b578295b85487c34beaf052b70a90f82a7
  | 6, 0, 13 => 0xd5e0a56e1521f0b0fabc15de56e1521f1c0000d5c49487c1a2803571270b29487c60060a570470a90f8dabc14ae0ce1521f1f052b83c11c2a43e3eae572b89385487c7d5e0a56e1521f008fabc14adc2ab521f1f578295b85487c2dbeaf052b70a90f8497d5d82571270a90f8fabc14adc2a43e181c01aba8c49c2a43e36af052b70a911a7c7
  | 6, 0, 14 => 0xd5e0a24e1521f084fabc14adc2a43e151fa7abc14adc2a43e3eaf052b70a90f8667d5e0a24e1521f0d8e00d5c4a18e1521f1b578295b85487c003eaf052b7bb85487c7006af052b70a90f8dabc14adc2a43e055c01ab92449c2a43e36af052b83b85487c7d5e0a56e15b290f8fabc14adc2a43e1e1f579e95b85b0a43e3eaf052b70a912e7c7
  | 6, 0, 15 => 0x6ae24f970a90f8c00d5e0a24e13e109801ab89385487c2f300001ab70a90f8285006ae251270a90f8dabc14adc2a43e00dc01ab89385488f3e36ff577c95b85487c7d5e0a56e15226cf8fd1d5e0ae6e1521f1f5751a44adc2a43e3eaf052b70a91007c7d5e0a56e1521f07efabc14ae52e1521f1f578295b858ea43e3eae571270b51487c7
  | 6, 1, 0 => 0xd5e0a56e1521f032fabc14adc2a43e0e9f578289385488b3e3803572b70a90f8166006ae24e1521f0cadabc660a56e1521f1c01abb3cadc2a43e36af052b6c291167c7d5e0a56e1521f084fabc14adc2da521f1f578295b295aa43e3eaf158295b85487c7d5e0a56e1521f0f8fabc1449c2a43e1c1f578295b85487033380357828938548516
  | 6, 1, 1 => 0x6ae24e16c290f8dd1d5e0a56e1521f1f578295b85487c043eaf054d95b85487c7d5e0a592b70a90f8fabc157224e1521f1c01abb0449c2a43e36af052b82385487c70060a24e1521f018dabcd60a56e1521f1f5782a6449c2a43e3eaf052b70a90f8577006ff571270a90f8dabc14adc2a4431f1f578295b85b2a43e3eaf052b70a90f86f7
  | 6, 1, 2 => 0x6af052b6d290f8dabc14adc2a44f1f1f578295b85488b3e3f33578295b853c7c7d5e0a56e14e22cf8fcce360a56e1521f1f8d8295b85489c3e3eaf051270a90f8517d5e8f052b70a90f8fabd5e0a56e1521f1f578295b85487c383eaf052b70a91127c7d5e0a56e163290f8e00d5e0a56e152145b578295b8592a43e3803578295b84f8426
  | 6, 1, 3 => 0xd5e0a56e1521f056fabc14adc2a43e145c01abc14adc29e3e3743578289385487c7e76af052b70a90f8fabc157256e1521f1f578295be5c2ca523eaf054595b85487c7e8eaf052b70a90e8e00d5e0a56e159291801c2c14adc2a43e3003052b70a90f80c6d5e0a56f670a90f8fabc14adc2a43e105f578295b85487c19beaf054c95b85487c7
  | 6, 1, 4 => 0x3571270a90f8a00d5c4a0ee1521f1b578295b85487c38bf73578295b85487c7006af052b7094484dabcc60a56e1521f1fa1abc14adc2a43e3f5f578289385487c7d5e0a56e159290f8fabcacae24e1521f1f578295b85487c21b803577c95b85487c6d5e0a57075222cf8e00e66ae24e1521f1801ab89385489c3e36af056d89385487c7
  | 6, 1, 5 => 0xd5e0a56e1521f0bafc2c14adc2a4459f1f578295be1c2a43e3eaf052b70a99487c7e16af052b70a90f8fabc14adc2a43e031f578295b85487c06beaf052b70ab5487c70060a56e15214418c00c14adc27c21031b578295b85bea43e3f3f578295b85487c7d5e0abf2b70a90f8fabc14adc6e1521f1c01ab89385487c3336af056d95b85487c7
  | 6, 1, 6 => 0xd5e0a56e166290f8fabc14ae0ae1521f1f578295b85487c1a3803578295ab5487c6d5e9b052b70a90f8fabc14adc2a43e189c01ab89385487c21360a56e16531d487c7e36af052b70a90f8fb7d5e0a56e1521f1f578295b85487c143eeb578295b85487c7d5e0a56e152228f8fabc14adc2a43e019f578295b85487c393eaf052b70ac9488b7
  | 6, 1, 7 => 0x6ae24e15214540000d5c49c27c212ed7578295b85487c7
  | 7, 0, 0 => 0x6af052b70a91387c700003578289385487c6006af052b70b51487c7006af052b70b61487c7006af056095b85487c7006ff578295b85487c7006af052b7cb85487c7006af052b70a90f85e7006af052b89385487c7006af057395b85487c7006af052b70a90f8167006af052b92385487c700003578295a90f8346006af052b70b29487c7006af055195b85487c7006af052b70a91227c7
  | 7, 0, 1 => 0x71b578295b85487c7006af052b70a90f80c70000001ab89385487c5006af052b70a90f851700003052b70a90f80c6006af052b70a91167c7006af052b70a90f870700003578295b854851600003578295b84f842600747578295b85487c700003572b70a90f8166006af052b70a90f8427006af052b70a90f866700003578295b85487c6006af052b83b85487c700733578295b85487c7
  | 7, 0, 2 => 0x6af052b70a90f8347006af4d8295b85487c7006af052b70a90f8627
  | 8, 0, 0 => 0x3578295b85487c6
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 512), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]

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
private theorem z3_0 : span (Z 3) 17 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 17 0 = true := z3_0

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
private theorem z4_168 : span (Z 4) 7 168 = true := by decide +kernel

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

private theorem z4_a7 : span (Z 4) 175 0 = true :=
  span_join (f := Z 4) (a := 168) (o := 0) (b := 7) z4_a6 z4_168

private theorem z4 : span (Z 4) 175 0 = true := z4_a7

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
private theorem z5_528 : span (Z 5) 7 528 = true := by decide +kernel

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

private theorem z5_a22 : span (Z 5) 535 0 = true :=
  span_join (f := Z 5) (a := 528) (o := 0) (b := 7) z5_a21 z5_528

private theorem z5 : span (Z 5) 535 0 = true := z5_a22

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
private theorem z6_360 : span (Z 6) 11 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 371 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 11) z6_a14 z6_360

private theorem z6 : span (Z 6) 371 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12531

theorem PEqualNP.Outside.L_meta_12531 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12531.mainG PEqualNP.Outside.L_meta_12531.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12531.CG, PEqualNP.Outside.L_meta_12531.CG_mono, by
      have : PEqualNP.Outside.L_meta_12531.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12531.CG_eval⟩
