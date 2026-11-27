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
namespace PEqualNP.Outside.L_meta_12613

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008636138 * 2 ^ 32 + 4008373992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 0, 1, 2, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 18, 0, 20, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 0, 0, 44, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 3, 3, 3, 3, 3, 5, 6, 7, 3, 9, 10, 11, 3, 13, 14, 15, 3, 17, 3, 19, 3, 21, 22, 23, 3, 25, 26, 27, 3, 29, 30, 31, 3, 33, 3, 35, 3, 37, 38, 39, 3, 41, 42, 43, 3, 45, 46, 47, 3, 49, 50, 51, 3, 53, 54, 55, 3, 57, 58, 59, 3, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 5, 5, 5, 3, 5, 5, 6, 7, 5, 9, 10, 11, 5, 13, 14, 15, 5, 17, 5, 19, 5, 21, 22, 23, 5, 25, 26, 27, 5, 29, 30, 31, 5, 33, 5, 35, 5, 37, 38, 39, 5, 41, 42, 43, 5, 45, 46, 47, 5, 49, 50, 51, 5, 53, 54, 55, 5, 57, 58, 59, 5, 61, 62, 63, 6, 6, 6, 3, 6, 5, 6, 7, 6, 9, 10, 11, 6, 13, 14, 15, 6, 17, 6, 19, 6, 21, 22, 23, 6, 25, 26, 27, 6, 29, 30, 31, 6, 33, 6, 35, 6, 37, 38, 39, 6, 41, 42, 43, 6, 45, 46, 47, 6, 49, 50, 51, 6, 53, 54, 55, 6, 57, 58, 59, 6, 61, 62, 63, 7, 7, 7, 3, 7, 5, 6, 7, 7, 9, 10, 11, 7, 13, 14, 15, 7, 17, 7, 19, 7, 21, 22, 23, 7, 25, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 42, 43, 7, 45, 46, 47, 7, 49, 50, 51, 7, 53, 54, 55, 7, 57, 58, 59, 7, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 9, 9, 9, 3, 9, 5, 6, 7, 9, 9, 10, 11, 9, 13, 14, 15, 9, 17, 9, 19, 9, 21, 22, 23, 9, 25, 26, 27, 9, 29, 30, 31, 9, 33, 9, 35, 9, 37, 38, 39, 9, 41, 42, 43, 9, 45, 46, 47, 9, 49, 50, 51, 9, 53, 54, 55, 9, 57, 58, 59, 9, 61, 62, 63, 10, 10, 10, 3, 10, 5, 6, 7, 10, 9, 10, 11, 10, 13, 14, 15, 10, 17, 10, 19, 10, 21, 22, 23, 10, 25, 26, 27, 10, 29, 30, 31, 10, 33, 10, 35, 10, 37, 38, 39, 10, 41, 42, 43, 10, 45, 46, 47, 10, 49, 50, 51, 10, 53, 54, 55, 10, 57, 58, 59, 10, 61, 62, 63, 11, 11, 11, 3, 11, 5, 6, 7, 11, 9, 10, 11, 11, 13, 14, 15, 11, 17, 11, 19, 11, 21, 22, 23, 11, 25, 26, 27, 11, 29, 30, 31, 11, 33, 11, 35, 11, 37, 38, 39, 11, 41, 42, 43, 11, 45, 46, 47, 11, 49, 50, 51, 11, 53, 54, 55, 11, 57, 58, 59, 11, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 13, 13, 13, 3, 13, 5, 6, 7, 13, 9, 10, 11, 13, 13, 14, 15, 13, 17, 13, 19, 13, 21, 22, 23, 13, 25, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 42, 43, 13, 45, 46, 47, 13, 49, 50, 51, 13, 53, 54, 55, 13, 57, 58, 59, 13, 61, 62, 63, 14, 14, 14, 3, 14, 5, 6, 7, 14, 9, 10, 11, 14, 13, 14, 15, 14, 17, 14, 19, 14, 21, 22, 23, 14, 25, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 42, 43, 14, 45, 46, 47, 14, 49, 50, 51, 14, 53, 54, 55, 14, 57, 58, 59, 14, 61, 62, 63, 15, 15, 15, 3, 15, 5, 6, 7, 15, 9, 10, 11, 15, 13, 14, 15, 15, 17, 15, 19, 15, 21, 22, 23, 15, 25, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 42, 43, 15, 45, 46, 47, 15, 49, 50, 51, 15, 53, 54, 55, 15, 57, 58, 59, 15, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 17, 17, 17, 3, 17, 5, 6, 7, 17, 9, 10, 11, 17, 13, 14, 15, 17, 17, 17, 19, 17, 21, 22, 23, 17, 25, 26, 27, 17, 29, 30, 31, 17, 33, 17, 35, 17, 37, 38, 39, 17, 41, 42, 43, 17, 45, 46, 47, 17, 49, 50, 51, 17, 53, 54, 55, 17, 57, 58, 59, 17, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 19, 19, 19, 3, 19, 5, 6, 7, 19, 9, 10, 11, 19, 13, 14, 15, 19, 17, 19, 19, 19, 21, 22, 23, 19, 25, 26, 27, 19, 29, 30, 31, 19, 33, 19, 35, 19, 37, 38, 39, 19, 41, 42, 43, 19, 45, 46, 47, 19, 49, 50, 51, 19, 53, 54, 55, 19, 57, 58, 59, 19, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 21, 21, 21, 3, 21, 5, 6, 7, 21, 9, 10, 11, 21, 13, 14, 15, 21, 17, 21, 19, 21, 21, 22, 23, 21, 25, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 42, 43, 21, 45, 46, 47, 21, 49, 50, 51, 21, 53, 54, 55, 21, 57, 58, 59, 21, 61, 62, 63, 22, 22, 22, 3, 22, 5, 6, 7, 22, 9, 10, 11, 22, 13, 14, 15, 22, 17, 22, 19, 22, 21, 22, 23, 22, 25, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 42, 43, 22, 45, 46, 47, 22, 49, 50, 51, 22, 53, 54, 55, 22, 57, 58, 59, 22, 61, 62, 63, 23, 23, 23, 3, 23, 5, 6, 7, 23, 9, 10, 11, 23, 13, 14, 15, 23, 17, 23, 19, 23, 21, 22, 23, 23, 25, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 42, 43, 23, 45, 46, 47, 23, 49, 50, 51, 23, 53, 54, 55, 23, 57, 58, 59, 23, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 25, 25, 25, 3, 25, 5, 6, 7, 25, 9, 10, 11, 25, 13, 14, 15, 25, 17, 25, 19, 25, 21, 22, 23, 25, 25, 26, 27, 25, 29, 30, 31, 25, 33, 25, 35, 25, 37, 38, 39, 25, 41, 42, 43, 25, 45, 46, 47, 25, 49, 50, 51, 25, 53, 54, 55, 25, 57, 58, 59, 25, 61, 62, 63, 26, 26, 26, 3, 26, 5, 6, 7, 26, 9, 10, 11, 26, 13, 14, 15, 26, 17, 26, 19, 26, 21, 22, 23, 26, 25, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 42, 43, 26, 45, 46, 47, 26, 49, 50, 51, 26, 53, 54, 55, 26, 57, 58, 59, 26, 61, 62, 63, 27, 27, 27, 3, 27, 5, 6, 7, 27, 9, 10, 11, 27, 13, 14, 15, 27, 17, 27, 19, 27, 21, 22, 23, 27, 25, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 42, 43, 27, 45, 46, 47, 27, 49, 50, 51, 27, 53, 54, 55, 27, 57, 58, 59, 27, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 29, 29, 29, 3, 29, 5, 6, 7, 29, 9, 10, 11, 29, 13, 14, 15, 29, 17, 29, 19, 29, 21, 22, 23, 29, 25, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 42, 43, 29, 45, 46, 47, 29, 49, 50, 51, 29, 53, 54, 55, 29, 57, 58, 59, 29, 61, 62, 63, 30, 30, 30, 3, 30, 5, 6, 7, 30, 9, 10, 11, 30, 13, 14, 15, 30, 17, 30, 19, 30, 21, 22, 23, 30, 25, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 42, 43, 30, 45, 46, 47, 30, 49, 50, 51, 30, 53, 54, 55, 30, 57, 58, 59, 30, 61, 62, 63, 31, 31, 31, 3, 31, 5, 6, 7, 31, 9, 10, 11, 31, 13, 14, 15, 31, 17, 31, 19, 31, 21, 22, 23, 31, 25, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 42, 43, 31, 45, 46, 47, 31, 49, 50, 51, 31, 53, 54, 55, 31, 57, 58, 59, 31, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 33, 33, 33, 3, 33, 5, 6, 7, 33, 9, 10, 11, 33, 13, 14, 15, 33, 17, 33, 19, 33, 21, 22, 23, 33, 25, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 42, 43, 33, 45, 46, 47, 33, 49, 50, 51, 33, 53, 54, 55, 33, 57, 58, 59, 33, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 35, 35, 35, 3, 35, 5, 6, 7, 35, 9, 10, 11, 35, 13, 14, 15, 35, 17, 35, 19, 35, 21, 22, 23, 35, 25, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 42, 43, 35, 45, 46, 47, 35, 49, 50, 51, 35, 53, 54, 55, 35, 57, 58, 59, 35, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 37, 37, 37, 3, 37, 5, 6, 7, 37, 9, 10, 11, 37, 13, 14, 15, 37, 17, 37, 19, 37, 21, 22, 23, 37, 25, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 42, 43, 37, 45, 46, 47, 37, 49, 50, 51, 37, 53, 54, 55, 37, 57, 58, 59, 37, 61, 62, 63, 38, 38, 38, 3, 38, 5, 6, 7, 38, 9, 10, 11, 38, 13, 14, 15, 38, 17, 38, 19, 38, 21, 22, 23, 38, 25, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 42, 43, 38, 45, 46, 47, 38, 49, 50, 51, 38, 53, 54, 55, 38, 57, 58, 59, 38, 61, 62, 63, 39, 39, 39, 3, 39, 5, 6, 7, 39, 9, 10, 11, 39, 13, 14, 15, 39, 17, 39, 19, 39, 21, 22, 23, 39, 25, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 42, 43, 39, 45, 46, 47, 39, 49, 50, 51, 39, 53, 54, 55, 39, 57, 58, 59, 39, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 41, 41, 41, 3, 41, 5, 6, 7, 41, 9, 10, 11, 41, 13, 14, 15, 41, 17, 41, 19, 41, 21, 22, 23, 41, 25, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 42, 43, 41, 45, 46, 47, 41, 49, 50, 51, 41, 53, 54, 55, 41, 57, 58, 59, 41, 61, 62, 63, 42, 42, 42, 3, 42, 5, 6, 7, 42, 9, 10, 11, 42, 13, 14, 15, 42, 17, 42, 19, 42, 21, 22, 23, 42, 25, 26, 27, 42, 29, 30, 31, 42, 33, 42, 35, 42, 37, 38, 39, 42, 41, 42, 43, 42, 45, 46, 47, 42, 49, 50, 51, 42, 53, 54, 55, 42, 57, 58, 59, 42, 61, 62, 63, 43, 43, 43, 3, 43, 5, 6, 7, 43, 9, 10, 11, 43, 13, 14, 15, 43, 17, 43, 19, 43, 21, 22, 23, 43, 25, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 42, 43, 43, 45, 46, 47, 43, 49, 50, 51, 43, 53, 54, 55, 43, 57, 58, 59, 43, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 45, 45, 45, 3, 45, 5, 6, 7, 45, 9, 10, 11, 45, 13, 14, 15, 45, 17, 45, 19, 45, 21, 22, 23, 45, 25, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 42, 43, 45, 45, 46, 47, 45, 49, 50, 51, 45, 53, 54, 55, 45, 57, 58, 59, 45, 61, 62, 63, 46, 46, 46, 3, 46, 5, 6, 7, 46, 9, 10, 11, 46, 13, 14, 15, 46, 17, 46, 19, 46, 21, 22, 23, 46, 25, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 42, 43, 46, 45, 46, 47, 46, 49, 50, 51, 46, 53, 54, 55, 46, 57, 58, 59, 46, 61, 62, 63, 47, 47, 47, 3, 47, 5, 6, 7, 47, 9, 10, 11, 47, 13, 14, 15, 47, 17, 47, 19, 47, 21, 22, 23, 47, 25, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 42, 43, 47, 45, 46, 47, 47, 49, 50, 51, 47, 53, 54, 55, 47, 57, 58, 59, 47, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 49, 49, 49, 3, 49, 5, 6, 7, 49, 9, 10, 11, 49, 13, 14, 15, 49, 17, 49, 19, 49, 21, 22, 23, 49, 25, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 42, 43, 49, 45, 46, 47, 49, 49, 50, 51, 49, 53, 54, 55, 49, 57, 58, 59, 49, 61, 62, 63, 50, 50, 50, 3, 50, 5, 6, 7, 50, 9, 10, 11, 50, 13, 14, 15, 50, 17, 50, 19, 50, 21, 22, 23, 50, 25, 26, 27, 50, 29, 30, 31, 50, 33, 50, 35, 50, 37, 38, 39, 50, 41, 42, 43, 50, 45, 46, 47, 50, 49, 50, 51, 50, 53, 54, 55, 50, 57, 58, 59, 50, 61, 62, 63, 51, 51, 51, 3, 51, 5, 6, 7, 51, 9, 10, 11, 51, 13, 14, 15, 51, 17, 51, 19, 51, 21, 22, 23, 51, 25, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 42, 43, 51, 45, 46, 47, 51, 49, 50, 51, 51, 53, 54, 55, 51, 57, 58, 59, 51, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 53, 53, 53, 3, 53, 5, 6, 7, 53, 9, 10, 11, 53, 13, 14, 15, 53, 17, 53, 19, 53, 21, 22, 23, 53, 25, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 42, 43, 53, 45, 46, 47, 53, 49, 50, 51, 53, 53, 54, 55, 53, 57, 58, 59, 53, 61, 62, 63, 54, 54, 54, 3, 54, 5, 6, 7, 54, 9, 10, 11, 54, 13, 14, 15, 54, 17, 54, 19, 54, 21, 22, 23, 54, 25, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 42, 43, 54, 45, 46, 47, 54, 49, 50, 51, 54, 53, 54, 55, 54, 57, 58, 59, 54, 61, 62, 63, 55, 55, 55, 3, 55, 5, 6, 7, 55, 9, 10, 11, 55, 13, 14, 15, 55, 17, 55, 19, 55, 21, 22, 23, 55, 25, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 42, 43, 55, 45, 46, 47, 55, 49, 50, 51, 55, 53, 54, 55, 55, 57, 58, 59, 55, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 57, 57, 57, 3, 57, 5, 6, 7, 57, 9, 10, 11, 57, 13, 14, 15, 57, 17, 57, 19, 57, 21, 22, 23, 57, 25, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 42, 43, 57, 45, 46, 47, 57, 49, 50, 51, 57, 53, 54, 55, 57, 57, 58, 59, 57, 61, 62, 63, 58, 58, 58, 3, 58, 5, 6, 7, 58, 9, 10, 11, 58, 13, 14, 15, 58, 17, 58, 19, 58, 21, 22, 23, 58, 25, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 42, 43, 58, 45, 46, 47, 58, 49, 50, 51, 58, 53, 54, 55, 58, 57, 58, 59, 58, 61, 62, 63, 59, 59, 59, 3, 59, 5, 6, 7, 59, 9, 10, 11, 59, 13, 14, 15, 59, 17, 59, 19, 59, 21, 22, 23, 59, 25, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 42, 43, 59, 45, 46, 47, 59, 49, 50, 51, 59, 53, 54, 55, 59, 57, 58, 59, 59, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63, 61, 61, 61, 3, 61, 5, 6, 7, 61, 9, 10, 11, 61, 13, 14, 15, 61, 17, 61, 19, 61, 21, 22, 23, 61, 25, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 42, 43, 61, 45, 46, 47, 61, 49, 50, 51, 61, 53, 54, 55, 61, 57, 58, 59, 61, 61, 62, 63, 62, 62, 62, 3, 62, 5, 6, 7, 62, 9, 10, 11, 62, 13, 14, 15, 62, 17, 62, 19, 62, 21, 22, 23, 62, 25, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 42, 43, 62, 45, 46, 47, 62, 49, 50, 51, 62, 53, 54, 55, 62, 57, 58, 59, 62, 61, 62, 63, 63, 63, 63, 3, 63, 5, 6, 7, 63, 9, 10, 11, 63, 13, 14, 15, 63, 17, 63, 19, 63, 21, 22, 23, 63, 25, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 42, 43, 63, 45, 46, 47, 63, 49, 50, 51, 63, 53, 54, 55, 63, 57, 58, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1111111511151117111111151115111711111115111511170000000000000000111111151115111711111115111511171111111511151117000000000000000011111115111511171111111511151117111111151115111700000000000000001111111511151117111111151115111711111115111511170000000000000000111111151115111711111115111511171111111511151117000000000000000011111115111511171111111511151117111111151115111700000000000000001111111511151117111111151115111711111115111511170000000000000000111111151115111700000000000000001111111511151117000000000000000011111115111511171111111511151117111111151115111700000000000000001111111511151117111111151115111711111115111511170000000000000000111111151115111711111115111511171111111511151117000000000000000011111115111511170000000000000000111111151115111700000000000000001111111511151117111111151115111711111115111511170000000000000000111111151115111711111115111511171111111511151117000000000000000011111115111511171111111511151117111111151115111700000000000000001111111511151117000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee80000000000000000eeeeeeeaeeeaeee8000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8eeeeeeeaeeeaeee8

def cMZZ : Nat := 0x1111111511151117000000000000000000000000000000000000000000000000111111151115111700000000000000000000000000000000000000000000000011111115111511170000000000000000000000000000000000000000000000001111111511151117000000000000000000000000000000000000000000000000111111151115111700000000000000000000000000000000000000000000000011111115111511170000000000000000000000000000000000000000000000001111111511151117000000000000000011111115111511170000000000000000111111151115111700000000000000000000000000000000000000000000000011111115111511170000000000000000000000000000000000000000000000001111111511151117000000000000000000000000000000000000000000000000111111151115111700000000000000001111111511151117000000000000000011111115111511170000000000000000000000000000000000000000000000001111111511151117000000000000000000000000000000000000000000000000111111151115111700000000000000000000000000000000000000000000000011111115111511170000000000000000111111151115111711111115111511171111111511151117

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
  | 3 => 62
  | 4 => 457
  | 5 => 765
  | 6 => 354
  | 7 => 28
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xe7c4b3729a08713355b463ee
  | 3, 0 => 0xeea7f622ecae21d1e5512003e34a86b1df360d08d475c591cf7ee37cb64df145b302795ba621d21fa24e602494fbf82b91e4195d91b91a0e8f65ea088dc05eb688f0cb1d8577fb2285520c6a83aa34b27ae13ad1789251db71a4faec6fa2bc1d69c52a7865f8f3245e5b66895cc6fbcf5378dd114f1f32474ebed0d94d89554448d523c1486ef448480163cd430e42b740fc6a764027f71c3eb531eb3e2d67d33dacaf0d34b11f14290a927724d98a88249a7491202f474d1fbc1cca1e611d191ad089261a8456d0182e54ca1651d4cc13da9d7210670d8e0ff0fdf80fd1fd0d0deb7cf60c7a9d6609ce5ea4074da1a5068b7cea01edd507
  | 4, 0 => 0xdb8c98a0d3e67830cf563a30ca6622f0bcbe6f30bb340ce0b353cd40b31f8bf0b1feceb0b1fa63e0b0a063e0aed53760ab0a2510a85e7990a82b4900a6842ce0a3c64980a17a5f409ed363409e6157e098901f5096a0cf609642da2090a544e08fb45b708cd1ba908aa64f9088a9eff0882305a083fece607acefb40761049007287f1506cafc5f06b6367e06920f98063a8b770627d06305fc9d1f05de677705c8097d05c420520521676a04d477e604c6279403dab5d803d8e675033422c302dfe3ff02d5579b02965183029004a40279cd2e01ed85740196ccf101903d7a01331e4c00fe8aaa00f06bd200b224e600b021ca0082b2cb005136ee002ab112
  | 4, 1 => 0x2001073e1fe4584f1fe134e01fbc1cca1f696ef51e320ff71da7dcf01d52fb191d43967b1d4126921d0de5271cd20c091cd1b36c1cb23cf71c1329611bc5be1b1ba6d2151b5e44211b10d2451b04fa901a01a35c19f89a8919f4202719b6cbe619af90761959179b18b0ec5c182e54ca17d9f41417b4dc4217735f0016a7766f16560c9915768af31508c6be1498a324149779cd1477fc99145563af1447b010143f40e71412fc8313f9f91e1380a698134b968c131c8e0a1315b67212fdaa49127b0419124d128f11fd7eb611705058109018e71089cd29101b82150ffd61540fa00c850f807c420eeba9050ece3b460ec6fdc90e6fa3b40e3918660e1685f6
  | 4, 2 => 0x342727e03410c4c333ef13ae33bd724833a59561335a8208331ad3fa32c8f8ce32c78dce32a2ae2f32644c05323d1fa831e992ac31e3841531aef073315060fd3115f11d30c775d730c4c50c308533e9300a01313004875b2fc7d8b12fc19cce2ec702082e12b8e72ddda1ad2d8d6bec2d83a8d82cc33a492c5a6f332bba53892b5728ef2b2d223c2a91202929c73d802923c17d2908923a2885a5b22869a3e7283847da281607a127fc524c2795ad2d278acb582785f4b5274866d227333f5326c96f0126c783ec263ac75e2637347a250c532323e0fa072385a157235e04512325be2722d36ff22292fa6d2270d25121c4780621589a9520af531e202f1889
  | 4, 3 => 0x4cc8b0a44b5870904adfcda54a5ff63f499d278c495631c14923173e4893065e480163cd47fbf59d4733417947333b4c464fc22545db55a14547df9644c557b544ac793044ac3a5843fbfc554320dc9c42e6372842d377ab42853bed4275efd9416915cf4146f9d841407eb04102eaf840b269d540a094ac402bee464006f80b3f734c6f3eb3dddd3eb2e59e3e495a8d3deecd4c3d3425993cd543bb3cc003163c9d2ec13c1b07ba3bdedb513bdb57143bacb3c83a898ccc3a57effb3a57b8473a03b983396dc321393086d838710b12383f5ff137cf1d9937694d9c376762b937101390361e329735f6506b359c40ad3563da62353e05623480d81d344a85e7
  | 4, 4 => 0x6b3e291f6abaed106981de156938b4166923b70569195fac68393d8067da43d6679c77d8679b575d66f306bf65b949f565938709650e083e64b6759264a2d99c6401a837637f008f633871d9629463e96291a4ea62826e5061a0b22f616ab60460c4375560b84c4a608271816051cab05fbbb43c5f2961f55ea88f715e51311e5e33442e5d2945d85cae6f865c914dcb5be9f3255be69d6c5b83b1175a70fac95a5c1fc159ba1c3f59400810590c56f058295b0556cbb08655bbf26d55314dbf54ebb01054e990ab54cdc320542698b452ed8f78529a478f5288984c510549a250f86a0850f0e77f50b0df3e504e36424f7171c54ed311194e8d065f4cef7d9a
  | 4, 5 => 0x940076a093966e1c927a6fbc925424b3918040a68f1b77428ed47ed48d3f747d8d2e41b68cf256998bd318288af0d41e8a60ae3f89b1710888e5a7e18863bb9688439f7b86e06547821795ca80cdb4c98015f2417f9cd2227f37b2ff7eca093d7dfebb3b7d7fc8477d5bede17d57d8967af279b17ac3dcc07a3516f3797c0d9478f6264178b184227785a16276bf8cbd764ea3037549574e74d907ef741cc03c73f904de73f2578872bce68f724f8d237234fe59722e37a671c8b1c5717d4990715bbd1b70f3fc8d70ecf02070c21436706388e26f1d1abc6f0b36c06edce0256ec38be26e606cbe6d7068df6cfa36d76c900b736c4b8b7a6bff79836b61a843
  | 4, 6 => 0xe288bcb9e0f1fbdfe0ef13b4e03c6ea7e023dd9ddfb2bc44de766eefdd3a7732d8e3e33ad74c7d4ad66b4916d5237687d4374eadd087d29ed06cb411cef46d72c75d9b94c6fbe160c5f0ba9fc079a6ddbfb09187bcfdfc55b88d43d0b7fc1330b64df145b6461b1db56270cbb4b3bf2db44b48f0b3fa076fb2cebcabb0d98001aff110c2afdb84abaf0959fbacf2292aaa5063f3a944c380a4571241a4264a77a24f719ca19bdab9a15abf5ea129752ba07489559f5c51999f1c99b99ed1c1619e93841c9d857d6a9c35c6fb9b08d7629adc5eb9997d009d9936dce8989c1907983125969718acdf9653a6a696492cb8958c58f894fbf82b94f64876944f5867
  | 4, 7 => 0xfbeb1ecdf6f9dd45f48bc7c3ef69e5d0ed9acab5ea93c277e9a79ae5e742b3b9e2ba2c96
  | 5, 0 => 0x8373e950811619f07bb50ca07a664860740704b0721d48206badc5f069a738306735a5f06128bf905d208b2059bd7f30591b54305846ae50583084205719820056dc92d054c113a054683fd0522c109050a9e9304de949704cd671d0487a9ed04494946044495cd0421f358040b72dc03ebfeed03e4298d03bc5bf10388caac0384221803832cf3031bcc38031ad2be027c6aa5026e350d025fbbb70257fcf302391b56023005e702071bae01f9230401cb09db01c97d4501be1de501bd158501a8edb4014922d101396a59010861cc0100395000fbdc7600c9ad4300b021ca00a550ef00a344f3009dd543009d2c33007d97b4007af9900059e49e000badc2
  | 5, 1 => 0x12299abd122480b611ff8ecf11fd7eb611bc4f1311b96a011182933d10c38934109cd26e1099d7bd108755901051e5390fd04c9a0fb590400fb260110fb0c5c70f76c5680f4927b20f02c43e0edfc2e40ed5a77b0e28fb110dda9d840dd7913b0d728c050d6162b90d49aa9b0cfbd7ff0cf563a30cdd5ca40cd7495d0cce87850cb82a780ca684090ca66cc60c8fca300c7721b50c22129c0c17c1a90bf0954c0be102e70bb340ce0ba6e9030b96f9b90b89c7480b6c9cbc0b0807c90ad9a86f0ad60d140ac966c10a7c2a940a783ab00a70472e09fdd2cc09dc6ab109c1f5b909a6b288097b4e5509671bba0912e4290875427008707d2a085755800849c603
  | 5, 2 => 0x1a32c08f1a03e7f219f89a8919df63ea19d8947819c474e319543a4e191e45461914171f190df3b018cffd221898a74718665b4218551c1118456cea17fcd27a17f5f23417d3f0c617b99fa117a469b41795a2e91780b7a6174e95aa1738357016f291a816ec020116e79b3d16c7909b16bbb0df16a5f04816a468181692092c1650a46515beb13715a2e937159250f5158db88c1568cf871560296c1550d463154928db150c6a11150bf92414e66ec014c9657114b9fc1e148d4c4714577ea81456687414241b2b13e1aba213d3aa8b13af90ce13aeef0f139a565f138a321f1367fb8b134e536a1335b74513138c4e12e3fc7c12cc9cc812ca2a4b128b9eed
  | 5, 3 => 0x2297fdbd2294c9202293b606223a37f12229127f2218967221aaedf82174ba5821589a9520faf24420f3ddc520e6b0f020e638b420a581181fe5699d1f89cc3d1f55f2401f5198981f0d65c21ef94ebb1eeb91b31e93d7361e839a551e78cd591e723ab61e6b7d691e6402ef1e5feed41e5c06cb1e18af571dfff0391db2756d1daf71f91dad65b71d6043021d0de5271d01363d1cedc8041ccfbd9d1ccdcf251caed2541c99accc1c2c6faa1c13eda31c13b39e1bf00eee1bda1a1b1bd0896e1bb77eb41bb08eaa1b76c73e1b04fa901af7f3001ae8c6c21ae62dfb1adb61c61ac0efc41a9557901a737dca1a6754311a5a21c01a540a501a52924e1a41658f
  | 5, 4 => 0x2eb96bd22e68332b2df03a092de60d3e2de4f3612dcbafb22d40b95e2d402eb42d3c7a8b2cc8d3fc2c8e68242c2c0fc52be1d7ff2bd190b52b9852202ad72adb2aabdfac2a01abe629cb825729c23608299af15d294aeaab292d9070292c4cfe2924e769290b032a28d4426a28b8b30628294ca0281ff9ff281607a127cfe6f82757bae1272e148a2717093a26fa9d3c26eb85fd26a2f33e26729d68264fc42926365080261e339e25ebd21325e02ea825c3c1c125b8063a257b094425796eb12520fedd24d14af42464e182245e1304243083e424198353240ed26023f5898c23e39faf2365c2e923509d302338886923331d352306bc8022fdc1ff229ded93
  | 5, 5 => 0x3bacb3c83b775d613b74ff763b6713493b2e80213a7996533a77acf93a7590553a35e7253a054054396f29e0392c7a8338ea04a338dcd79938b971e5388f86e63887df9b385c0515382817a237f30b1437e6b9d237b434a537934d68375c35133712945436f223da36f0547736ab0dd035f54bab35d8dec4359a13103544f36d34bee6633499bbe03465283e3455ffd734197487340ff5a133f8bcb23350bbaf330ff08c32f37db432ca6660326844e4324c16b3323d1fa83228fdcd31e3841531cfdba031aef073313d444d31100f47308ed583307f262a2ff983c62fdbac542fc19cce2f76fc042f5e22792f24d7522f1d87482f1cb0ec2f0e6bbe2ee8f638
  | 5, 6 => 0x48eed53848d09060489055c9485f61744845208248160fda4807c36c47c8153d47b5d739475f9172472c5f8d465d907045ff011e45c7f19245bccfda45a2a04d4595913b4547df9645151de74492116b4484d275446f519c446e62b44454f15044020b1c43fbfc5543a9306042f8a161418db97a414fed7c414efdbc41407eb04137bb5940d48b2940a094ac409c57054084c470407f3733404436714041f3ad3fcf4a8d3fc4b15c3f3e5fd23ef9e0663ef27c933eac1b1b3dfa10643deecd4c3dc0fd353db51ddb3da8ef5b3d6c2f573d5e3dc03ccee9833cc0a2663cb54dd93ca04edd3c9d2ec13c47d98d3c451a8e3c2b77d23c1eff933bb86d923bb86a20
  | 5, 7 => 0x57685891570b4e3a56ec326b56df6faa56df0c3756ccd72b56c5b42455f438fb55314dbf54a5ef555486bfd85483499f547be70b5477526453e738c753d1ff2b53cbfd1553cb0367533e9205532ea56a52f1d037524d5d09523ec20351dafb2851969e7d517ad2a051605c3250f2e89550d2e866505338db4ff8194e4fcd87b04f8061c14f7e1b214f2658a84ec6bce34eb056024e9ff1524e3ce6584e28bcaa4e026fad4dd035e04dbdf11c4dac7a824cef7d9a4cb875aa4cabc4684c8578534c5aa54e4c2d4e494c152de44c0e182a4bd585a44b89f9444b7c27694b7a30f04b4640b54b30bf344abd65944a5ff63f49fc46d2499939834924f0214914374b
  | 5, 8 => 0x6b25f61e6ab61c436a1be05069b17dfe697c44346924529569196c42688210cc687b48646821817567d8699167a9fdc7675604a36711ed4a670a43eb66e4785b66a5cc3d6620645165b7f1a565868dcc650d93a2650100ae64ff048a64fcea4b64a61815645108dd6401a837637649cd6364e6ac635102e062a3b2e762991d85614a99d46148dddb61289e6960fe33a860f50faf60b65f425fcded115f71dd355f69d19b5f69371a5ed832c95ea88f715e0a55985dda94a85d5c42c85c914dcb5c7b4b425c38fb675af791515ae08b365ac5dd405a90431b5a812a6d5a0119ac59fb5074595235605941425358cf181d5825617757ed18cb57b230df579af559
  | 5, 9 => 0x891c1bfc88f8597188bccf9f88a0ef5287e021b58713e3a186dd4a79866c18dc8626103384295fea83551169828b60f1826d738381720c7f814381317fba73b87e8c41ec7e5621357e0a87e57dd9c01b7d6057367c1dd3ac7af279b17adceacf7a63b8a77a27fef9797d6717790fc73d78d00f5d7802ac9376a1fb87763ca20a762bde087626c130752393ab7309eebc72ea528c72e5ba09727bc5847254507a717d4990715da3b670cc228370cae6777016d5ed6ffca25c6feec59b6f13e5966ee55f236ee38fc06e9830196db3ec446d7e49b76d7068df6d49e3c06cc8edec6ca404e76c9fc5696c845e3b6c2de5606c1e3e406c079a576bff79836b61a843
  | 5, 10 => 0xaebe55dfadeac451ac33849caa97026daa19aac2a9c71b11a9c4b1e6a9ab63c7a9a7ddf1a8c0d70fa8287ef3a4d7af2ea2be124da299cea9a2836884a24adc9fa1a63ce3a16948caa142633fa129752ba11113eca10a7384a0748955a06e83ada00845149f5c51999ed1c1619e652b539d59a9449cf43bf79cce0f5b9c7dd78b9c5b0a489c5ac3f69ae3b9509a2d1c819935217198e9e4ff98e84af898de36a9988e5223985783669765187e960dd7e99600897e958695ba953c735492d4a4249240b974918ce33191689f2090e836ff904c06948dad7d138d9a75778d50f6218cd25e2c8c82324f8b6b28188aebde2b8aaa3b0d8a8cf5a58a3fdedd8968dc72
  | 5, 11 => 0xfc4f4739fb77eda5f9a07e04f74d61a3f6f9dd45f65b0f79f62bbaf1f55b9786f28b5b1cece91627ece746c4ea93c277e9c7c263e9c52da3e7b53502e742b3b9e5574f4fe5001942e2ba2c96e29e0ed9e254bfe1e1f20ecfdfb012bed611471cd44736d7d28ee1aad2529d09d19004bfd0ad52e9d051140dcf5924e4ce3f3d67cdc2d1cfccc0fe22cbeb5a8fc8c11c98c853414dc8354a13c7610f42c648d786c447381bc2b3bb84c1c43ffcc0f6295dc079a6ddbeac17d4bdf42a13bcc5fb07bbbbe8fbbaa57183b97b1465b88d43d0b7bc7176b64df145b3fa076fb3026b57b2c29d67b1af6f72b06bfbe8b01ebebaafff03cc
  | 6, 0 => 0x15d27537158db88c156bdfc41568cf871560296c154928db1528751a14f96ca9142905f913e846b6126ce789124f5273124630a8123b553f1227627011db8d4611cb003e1146c30c10db796c10c609f810a5997e10892609105b6b510fdb8afd0fa842180f4927b20f1417fe0f0d7e280f0baec50e4d31840e09757b0dc36b450cc366300bff8c570bf0954c0b96f9b90b89c7480b8351440af0b9f10a424b2709dc6ab1092a71a808d84cf608d0fcec08d0269008aa2fd1089c6bdc07b6307907a3afad078e8aab07125bfb06f60ad20585065903bc5bf1037bc31c02fe604f02dfc2a2027c6aa5013fbf16010b308500ae12e000a344f3009cc10500250c62
  | 6, 1 => 0x2d15e1872ca545db2c00d2ad2bedac372b1195c52aa65e3929cb825729bb8b75287a328728626c6127b5e551277166c0275baafc2757bae126a2f33e267de0802661a9f5265f3a0c260e1af225e0c3ed24f9b6592311e9d522c7acef21bb39102180e2c4217b8ae121589a95211307161f7b67361f70457e1e723ab61e45870f1db580c01daf71f91d489e011d01363d1b62d9081b16048c1b0273601af7f3001aeb30fd1a98961a1a540a501a03e7f219f89a8919f569511982c031195f690d18f1d57618876069185f90bf17ad8608177472d91711b36416f74ac616ec02011692092c16868af116825f271668c37d1653c4811650a4651648671a15deed76
  | 6, 2 => 0x49ca4b9149a23b3f497c22dd49332671485f61744851bd2d475f9172465cb91f46533b0d45d1b3e445bccfda45548de744d96bc24492116b43c9208042e5db1442d7c83942be4593428dc5a9427f2090422ebe0841d4f71941a3014941933e5c418bdf354137bb5941097a474097edff40492cbf4037d2b63f0399593ef9e0663eb27a2e3e598db93e1d0b973dfa10643db51ddb3c7a3e793c6f55e83bfda8503bb86d923ab1a94c3aa885533a1a6e99398162b5391069fd378e0a4c3611b11134db8ca5347952e433aec61833ad4ae83305ab0432f4b7f732b3cf4c316d8fae311bce352fe3618e2e409ff62e3a357c2de4f3612d8574cf2d7f72b92d2579e4
  | 6, 3 => 0x7104b83370b36c297063f1d16feec59b6fc295c96fc14d8d6fb3ff226f199ca56eefe8f86e9830196e855c6f6b4058d56b25f61e6b1c14c46b0f310d6a83c9706983f96e6924529567eeadee67d869916685d3d0651f123a651e9dbc64f43eab64b304a7645db0b1631c521662f9845962cf91a061b693b6619397595fcded115ddcd58e5d08870d5c3ed6955b2582235a3857a059fb5074587295b7583fb79055ba205d55314dbf54a5ef5553a9c63a51c36cdf51b6223751a822b151969e7d50c7834d505c39ad4fdf18124fda36d44ed7094f4eb056024e3009814d8a35bc4d442b864c992fad4c07c61e4b30bf344b15993f4b143e334a9101e049fff566
  | 6, 4 => 0xac42574eac0612adab437a63aa0489b1a7589ee5a5aadb3ca274923ca206b6f1a1fee481a1e8bfb7a11484e6a10a7384a0f9dd869ffc4d2a9f5c51999ee9fba99d59a9449c6e07489a2d1c8199b917e1998fb2fd97a79fb7967970ab9600897e932e8a0991f7690090e4b0058fc44fe98e082ab78dad7d138cb5e0fb8c76130b8b62e5168aaa3b0d898e43a088c2e8f28871cb8387e021b5866c18dc85dd7960838045af837a90b58378278a835b5395828b60f182744cb3824e42f47e8b24d27e84599a7b59b2877b4c0c547af5d8e37adceacf7abde9287a27fef9790fc73d77a97ce5770d1ee87580bc6f74972ef4732e0b2972e89715720af90a71c83edc
  | 6, 5 => 0xf825b055f4ab689ff09f77a0f06f267eece91627ece746c4e92a3b07e68abefce5947886e20acb1fe0445c4cdf367de1db7e7f7ad100d747d051140dd011c7b3cf0f0d2acdba9be0c8c11c98c69c8bcbc69abc68c648d786c37b3807c0393d74bf4a5e6db97b1465b9333f1fb8d4e429b5f56e81b2c29d67b144ecb4b0eaf18daecca7a2ad23f6ff
  | 7, 0 => 0xf825b055f09f77a0c69c8bcbc0393d74aa0489b19ffc4d2a9f5c51998c76130b87e021b57abde928790fc73d770d1ee86fb3ff2264b304a7645db0b149a23b3f485f617444d96bc242d7c839418bdf35398162b533aec618211307161f70457e1e45870f1aeb30fd18876069010b3085
  | 8, 0 => 0x790fc73d
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff000000ff000000f0f0f0f0f0f00000cccc0000cccc0000aaaa0000aaaa000033330000333300000f0f00000f0f000000ff000000ff0000000f0000000f00000000ffffffff00000000fff0fff000000000f0f0f0f00000000055555555000000000f0f0f0f00000000000f000f000000000000ffff0000000000000000
  | 0, 1 => 0xcc00cc00cc00cc0033003300330033000fffff000fffff000f000f000f000f000f000f00000000000f0000ffff0000000f0000000f0000000c000c000c000c000a000a000a000a000500050005000500030003000300030000ffffffffffff0000ffff0000ffff0000ffff000000000000fff0fff0fff00000fff00000fff0
  | 0, 2 => 0xf0f0f0f0f000f000f0f0f0f000000000f0f0f000f0f0f000f0f00000f0f00000f000f000f000f000a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ff00ff00ff00ff00ff00f000f000ff00ff0000000000ff000000ff000000f000f0f0f0f0f000f000f000f000f0
  | 0, 3 => 0x33ff33ff00000000333f333f333f333f333f333f0000000033333333ffffffff33333333333333333333000033330000333033303330333030303030303030302a2a2a2a2a2a2a2a222a222a222a222a222222222222222211111111111111110fff0fff0fff0fff0fff00000fff00000f0f0f0fffffffff0f0f0f0f0f0f0f0f
  | 0, 4 => 0x555555550000000055550000ffff0000555500005555000055505550fff0fff055505550555055505500ff005500ff00550055005500550050505050505050504c4c4c4c4c4c4c4c444c444c444c444c4444cccc4444cccc44444444444444443f3f3f3f3f3f3f3f3f3f00003f3f00003f003f003f003f0033ff33ff33ff33ff
  | 0, 5 => 0x88880000888800008880888088808880880088008800880077777777777777777777777700000000777077707770777070707070707070705f5f5f5f5f5f5f5f5f005f005f005f0055ff55ff55ff55ff55ff55ff0000000055ff000055ff0000555f555f555f555f555f0000555f00005555ffff5555ffff5555555555555555
  | 0, 6 => 0xaaaaa0a0aaaaa0a0aaaa0000aaaa0000aaaa000000000000aaa8aaa8aaa8aaa8aaa0aaa0aaa0aaa0aaa0aaa000000000aa88aa88aa88aa88aa00aa00aa00aa00a8a8a8a8a8a8a8a8a0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a000a000a000a00088888888888888888888888800000000
  | 0, 7 => 0xbbbbbbbbbbbbbbbbafafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaafaaafaaafaaafaaaf0000aaaf0000aaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaa0aaa0aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa00aaaaaa00
  | 0, 8 => 0xccccc0c0ccccc0c0cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc0ccc0fff0fff0ccc0ccc0ccc0ccc0ccc0ccc000000000cc88cc88cc88cc88cc00ff00cc00ff00cc00cc00cc00cc00cc000000cc000000c8c8c8c8c8c8c8c8c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0c00000c0c00000c000c000c000c000
  | 0, 9 => 0xcfcf0000cfcf0000ccffccffccffccffcccfcccfcccfcccfcccf0000cccf0000ccccffff00000000ccccccccffffffffcccccccccccccccccccccccccccc0000ccccccccccc8ccc8ccccccccccc0ccc0ccccccccc0c0c0c0cccccccc88888888cccccccc00000000ccccccc8ccccccc8ccccccc0ccccccc0cccccc00cccccc00
  | 0, 10 => 0xeeeccccceeeccccceeeaeeeaeeeaeeeaeeeaaaaaeeeaaaaaeee0eee0eee0eee0eecceecceecceecceecceecccccccccceeaaeeaaeeaaeeaaeeaaeeaaaaaaaaaaeeaaaaaaeeaaaaaaee00ee00ee00ee00ecececececececececcceccceccceccceaeaeaeaeaeaeaeaeaaaeaaaeaaaeaaae0e0e0e0e0e0e0e0dddddddddddddddd
  | 0, 11 => 0xeeeeeeeeececececeeeeeeeee0e0e0e0eeeeeeeecccccccceeeeeeee00000000eeeeeee0eeeeeee0eeeeeecceeeeeecceeeeee00eeeeee00eeeeececeeeeececeeeee0e0eeeee0e0eeeecccceeeecccceeeecccccccccccceeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeee0000eeee0000eeee0000aaaa0000eeeceeeceeeceeec
  | 0, 12 => 0xf0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f000f0f0f000f0f0f00000f0f00000f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f000f000f000f000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeceeeceeeeeeeeeee0eee0eeeeeeeeeecceecc
  | 0, 13 => 0xf7f0f7f0f7f0f7f0f5f0f5f0fff0fff0f5f0f5f0f5f0f5f0f3f3f3f3f3f3f3f3f0fff0fff0fff0fff0fff0fff0f0f0f0f0fff0f0f0fff0f0f0ff0000f0ff0000f0f0fffff0f0fffff0f0fff0fff0fff0f0f0fff0f0f0fff0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0
  | 0, 14 => 0xfcccfcccfcccfcccfc00fc00fc00fc00fafafafafafafafafafafafafafaf0f0fafafafafaf0faf0fafafafaf0f0f0f0fafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafaf0faf0faf0faf0faf0f0f0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0
  | 0, 15 => 0xff00ff00f000f000ff00ff0000000000ff00f000ff00f000ff00ee00ff00ee00ff00cc00ff00cc00ff000000ff000000ff00000000000000fefefafaf0f0f0f0fef0fef0fef0fef0fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcccccccccfcfcf0f0f0f0f0f0fcf8fcf8fcf8fcf8fcf0fff0fcf0fff0fcf0fcf0fcf0fcf0
  | 1, 0 => 0xffaaff00ffaaff00ffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff80ff80ff80ff80ff55ff55ff55ff55ff50ff50ff50ff50ff33ff33ff33ff33ff33ff00ff33ff00ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff00ff00ffffffffff00ff00ff00ff00ff00ff00ff000000
  | 1, 1 => 0xffccffccffccffccffccffccff00ff00ffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffccccccffccccccffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffa0ffa0ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffa0ffaaffa0ffaaff88ffaaff88
  | 1, 2 => 0xfff0fff0ccc0ccc0fff0fff000000000fff0ff00fff0ff00fff0ff00ff00ff00fff0fcf0fff0fcf0fff0f0f0fff0f0f0fff0ccc0fff0ccc0fff0aaa0fff0aaa0fff00000fff00000fff0000000000000ffeeffeeffeeffeeffeeffeeff00ff00ffeeffee00000000ffeeff00ffeeff00ffee0000ffee0000ffe0ffe0ffe0ffe0
  | 1, 3 => 0xfff5fff5fff5fff5fff3fff3fff3fff3fff3fff0fff3fff0fff1fff1fff1fff1fff0fffffff0fffffff0fff0fffffffffff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff00000fff0fff0ffe0ffe0fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff0fcf0fcf0fff0fff0faf0faf0fff0fff0f0f0f0f0fff0fff0eee0eee0
  | 1, 4 => 0xfffcfffcfff0fff0fffcfff0fffcfff0fffcfff0fff0fff0fffcccccfffcccccfffc0000fffc0000fffafffafffafffafffafffafffafff0fffafffafff0fff0fffafffaf0f0f0f0fffafffaaaaaaaaafffafffa00000000fffafff8fffafff8fffafff0fffafff0fffafff0fff0fff0fff8fff8fff8fff8fff8fff0fff8fff0
  | 1, 5 => 0xffff0000ffff0000ffff0000fffa0000ffff0000fff00000ffff0000ff000000ffff0000fafa0000ffff0000f0f00000ffff0000cccc0000ffff0000aaaa0000ffff000000ff0000ffff0000000f0000ffff000000000000fffefffefffefffefffefffe00000000fffefff0fffefff0fffefff0fffafff0fffcfffcfffcfffc
  | 1, 6 => 0xffff8888ffff8888ffff8880ffff8880ffff5550ffff5550ffff5500ffff5500ffff3333ffff3333ffff3333ffff0000ffff333300000000ffff3330ffff3330ffff3030ffff3030ffff1111ffff1111ffff0f0f00000000ffff0f00ffff0f00ffff000fffff000fffff0000fffff0f0ffff0000ffffccccffff0000ffff5555
  | 1, 7 => 0xffffc000ffffc000ffffaaaaffffaaaaffffaaaaffffaaa0ffffaaaaffff8888ffffaaaaffff0000ffffaaaafff0aaa0ffffaaaaf0f0a0a0ffffaaaaaaaaaaaaffffaaaaaaaa0000ffffaaaa00000000ffffaaa0ffffaaa0ffffaaa0ffff0000ffffaa88ffffaa88ffffaa00ffffaa00ffffa0a0ffffa0a0ffffa000ffffa000
  | 1, 8 => 0xfffff0f000000000fffff000fffff000ffffeeeeffffeeeeffffeeee00000000ffffeee0ffffeee0ffffee00ffffee00ffffe0e0ffffe0e0ffffccccffffccccffffccccffff0000ffffccccccccccccffffccc8ffffccc8ffffccc0ffffccc0ffffcc00ffffcc00ffffcc00ffff0000ffffc8c8ffffc8c8ffffc0c0ffffc0c0
  | 1, 9 => 0xfffffafafffffafafffffafafffff0f0fffffafafff0faf0fffffafaf0f0f0f0fffffafa00000000fffffaf0fffffaf0fffffa00fffffa00fffff8f8fffff8f8fffff0f0fffff0f0fffff0f0fffff000fffff0f0ffffc0c0fffff0f0ffff0000fffff0f0fffaf0f0fffff0f0fff0f0f0fffff0f0fafaf0f0fffff0f0f0f0f0f0
  | 1, 10 => 0xffffffaa00000000ffffffa0ffffffa0ffffff88ffffff88ffffff00ffffff00ffffff00fffff000ffffff00ffffaa00ffffff00ffff0000ffffff00fffaff00ffffff00ffaaff00ffffff00ff33ff00ffffff00ff00ff00ffffff00aaaaaa00fffffef0fffffef0fffffcfcfffffcfcfffffcf0fffffcf0fffffc00fffffc00
  | 1, 11 => 0xfffffff0ffffccc0fffffff0ffffaaa0fffffff0ffff0000fffffff0fffafff0fffffff0fff3fff0fffffff0fff0fff0fffffff0ff00ff00fffffff0f0f0f0f0fffffff000000000ffffffe0ffffffe0ffffffccffffffccffffffc0ffffffc0ffffffaaffffffaaffffffaaffffff00ffffffaaffaaff00ffffffaaff00ff00
  | 1, 12 => 0xffffffff0f000f00ffffffff00ff00ffffffffff00f000f0ffffffff0000ffffffffffff0000fff0ffffffff00000000fffffffcfffffffcfffffffafffffffafffffffafffffff0fffffffaffff0000fffffffafffafff0fffffffafff0fff0fffffff8fffffff8fffffff0fffffff0fffffff0ffffff00fffffff0fffff0f0
  | 1, 13 => 0xffffffffaaaaaa00ffffffffaaaaa0a0ffffffffaaaa0000ffffffffaaa8aaa8ffffffffaaa0aaa0ffffffffaa00aa00ffffffffa0a0a0a0ffffffffa0a00000ffffffff88888888ffffffff88880000ffffffff88008800ffffffff80808080ffffffff55555555ffffffff55505550ffffffff55005500ffffffff11111111
  | 1, 14 => 0xfffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffeee0eee0ffffffffe0e0e0e0ffffffffccccccccffffffffcccc0000ffffffffccc8ccc8ffffffffccc0ccc0ffffffffccc00000ffffffffcc00cc00ffffffffc0c0c0c0ffffffffc000c000ffffffffaaaaaaaaffffffffaaaaaaa0
  | 1, 15 => 0xffffffffffa0ffa0ffffffffff88ff88ffffffffff00ff00ffffffffff00cc00ffffffffff000000fffffffffef0fef0fffffffffcfcfcfcfffffffffcf0fcf0fffffffffafafafafffffffffafaf0f0fffffffffafa0000fffffffffaf0faf0fffffffff8f8f8f8fffffffff0f0f0f0fffffffff0f0f000fffffffff0f0c0c0
  | 2, 0 => 0xfffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffffcfffcfffffffffffafffafffffffffffafff0fffffffffff8fff8fffffffffff0fff0fffffffffff0ff00fffffffffff0ccc0fffffffffff00000ffffffffffccffccffffffffffc0ffc0ffffffffffaaff00ffffffffffaa0000
  | 2, 1 => 0xfffffffffffffffffffffffffffffff0ffffffffffffff00
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1ba30c783714991e0dbc2f4783
  | 3, 0, 0 => 0x729bc2647847ad8b2647846c4d32647845614826478481d842647847e9a326478481dc22a4994645012f47847f5972b8994729bb26478481dc22b899481d972a499481d52264784799c22b899481d972b89947e1c2264784
  | 3, 0, 1 => 0x76d5f2b899481d8b26478481dc22d878481dc3264784729c22b8994708c12647847295126478479dc22647846e97b26478469cea2647846f0991e0724841ba26478481d8824478481dc92447847117b26478471188264784
  | 3, 0, 2 => 0x5553930c78481d6d264784815c2264784821c326478481dc225c784825c2264784831c426478481dc2308784561392f47845dd392647847c9bc26478481d5f248784729ba2d87847ad5f2b89946410130c78464115264784
  | 3, 0, 3 => 0x839ba264784845ba2647846e8991e0774831392cc9947295f2c0ae4711c226478481dc22c078481dc2264784825bc264784711b22647848314d264784831ba26478481dc229478455549264784
  | 4, 0, 0 => 0x7c15f4e4991e15fd57d332647857c95f4e4b01e15d057d39264785729ab4e4991e15ca7092f26478581d584e4991e15ca701392647857f55f4e4b61e15fd57d43264785729ad504991e1607610d326478583190404991e15ca71d4826478575d5f504991e155f54d39264785
  | 4, 0, 1 => 0x81dac528991e15da57cd32a49957c997404bf1e15ca6b0dd26478581d944e4991e155f4e4be264785729554e4b61e15fd65c992287857295550c991e15ca6b0d32b89957c9ac460991e160c561392647857f55f354991e16077095526478581dc22648a1e15ca57d4a2c0785
  | 4, 0, 2 => 0x8315c4e4991e15fd610d32647857c9ba65c991e16074e4991e02c577d5f4e4991e15ca4e5212647857f5c134c991e15ca57939264785729a634c991e15975d93926478572939264781095ca691392647857295f508991e15ca6f0d32647856755f404991e1539264780b82c5
  | 4, 0, 3 => 0x73d6434c991e15fd7089922878578d97404991e160057d392647857c9a834c991e15ca6b0d32a49957b9ac4e4991e16076e95f2647857fdac34c991e15dd64501264785785ca6f0991e157a57d392647857c9974b4991e1597404991e02457c95f4e4a326560c69cd3264785
  | 4, 0, 4 => 0x81dc2574991e1558404ea2647857295f480991e15d957d182647857f5a734c991e15f657d4326478566d974e4991e15fd6b0d32d87857f5944e4991e160c641392647857296e4e4991e15ca57d50528c45729c2264961e160c6e95f2647857715f4e4991e15fd65939264785
  | 4, 0, 5 => 0x7295f394a92655fc6b0d326478582e07708991e15ca57d392bc7857f5ba57c991e160757d4e26478578dc2404991e15ca55d392647857295f510991e15ca6b1392e87857297f4e4991e15af57d392647857f539264780b15ca6293926478557d202f0991e15ca6e988264785
  | 4, 0, 6 => 0x81d754e4991e155f4e4991e02f565d392f0991e15ca6f5392647857117657c991e15ca65d392647857f5ac284991e15ca694d32d87857f5ac3c0991e15fd680d3264785728b22b0991e140081d842647847c997430991e15ca6b13928c9955d939264781b95fd57cf7264785
  | 4, 0, 7 => 0x7f55f3c0a92655ca57cde26478581d5f2647812d400729bc264784729974e4ab1e1607721c22647857c997450991e160f641012647857c9714e4991e15f260d392647857ed5f4e4991e15b0620d326478581d5f520991e15f865d01264785729a7644991e15e365d39264785
  | 4, 0, 8 => 0x729c24e4ab1e15ca57d392e078581dc2264781a15fd57d482647857f5754e4991e15e460d392647857295f4e4a72655c46c15f26478578dc24e4991e15f365d0126478572939264781515c24e4bc26478575d6f4e4991e15ca709392647857515f4e4991e15fe57d39264785
  | 4, 0, 9 => 0x7299e4e4991e15ca7115f2647857295f4e4aa1e160757d18264785799c257c991e15ca5ed482647857655f4e4a51e15ac671012647857298a34ca92655db57d39264785729564e4991e15fd6a53926478581d5f4e4c21e15d857d39264785775ac4e4991e15ca57c9922c785
  | 4, 0, 10 => 0x7455f4e4991e15f265d01294785729834e4a92655ca708d32b8995809b434c991e15ca709392f4785729734e4991e16077095f2647857a997404991e15e365d0128c99581dc2264781855ca6d92026478581de9708991e15f257cac26478581dc249c991e15ca60539264785
  | 4, 0, 11 => 0x7595f4e4991e15ca6fd392647857f597528991e15f265d13264785729c2404a326560757d412647857295f480a326560c6e1012647857f56434c991e160957d39264785729704e4991e15d757d3926478581dc2528991e15ca57d392d87857295f50c991e160757d3e264785
  | 4, 0, 12 => 0x819ac4e4991e15392647806c1957b55f4e4991e155f4e4991e05b57c939264780655ca60939264785831b74e4991e16075ed392647857295f4e4a22655eb57d392647857b9c24e4991e15ea57d2026478581dc2318991e160c46cd32647857f56c34c991e160757d3925c785
  | 4, 0, 13 => 0x7295f460a51e160c6e9a5264785729614e4991e1607708991e0305729c22648a1e15ca4e49f2647857f55f4ac991e15fd57d41264785831554e4991e15f2708992187856b1392647808d5fd488d3264785729584e4991e15ca709392c0785555013b0991e15ca57cae2b0995
  | 4, 0, 14 => 0x83d8f4e4991e15db57c9922878572939264780b15ca57d3c26478557d392647c1e1607708991e0715799844e4991e15ca7093928c9957295f264781315db57d392c0785729a734c991e15f257d392b899581d5f264780415f26b13926478557d39368991e15f26e597264785
  | 4, 0, 15 => 0x7295f3dcab1e1558404d32f478500207264780211ca6b0f026478573d5f4e4991e1577404d326478581d844e4991e15ca6f939264785001ca708ae26515f5209924c785729c22648c1e15ca6a93926478581dc22647802160757d2f264785729ba57c991e15ca5f139264785
  | 4, 1, 0 => 0x81e07708991e15ca57d3d26478581d6f4e4991e15ca57d402647857c9ac404a32655ca57d4d2647857f5844e4991e1590404991e07757757e4e4991e16076b0ed264785729bc4e4991e156957d392647857295f4e47811d6106490126478557d39264780f55d957d39264785
  | 4, 1, 1 => 0x7f56f4e4991e159e6710126478581dc2324991e15f2709012647857e1ac3c0991e15885d93926478581dc23d4991e159c404991e06e583990404991e160b57d3925878583d554e4991e15fd6b0d329478583207708991e15ca6653926478557d013e0991e15f265d01264785
  | 4, 1, 2 => 0x7c9974e4991e15fd6b0e12647856e95f264781c95dd57d392d87855ed39264931e16016b0d32647857295f4e4c21e15ea6250126478577dac4e4991e15ca7094a310995729a14e4991e157b5d939264785729674e4991e15f457d392647857995f4e4991e16077f5c2264785
  | 4, 1, 3 => 0x7f9ad34c991e15ca57d391e04557855f520991e15ca6b1202647857d19a404991e1555404d330c78577590404991e15ca4e4b62c87856315f4e4991e16075f5392647857c981404991e1607610992287857295f520bd1e15f26f539264785729c22b0991e16077295f2b8995
  | 4, 1, 4 => 0x7f4d32e4991e15ca4e4991e01a581dc2264780ed5cb57d392647858215f504991e15d757d3931078581d724e4991e155f4e49b2647857815f4e4991e15ca57d3925c7857295f504991e160f694d3264785709392647806d5da65d39264785729c2528991e15f270939264785
  | 4, 1, 5 => 0x729c24e4ae2655ca5a1392647857f55f3c8991e1607709162647857c997404a32655ca57cdf264785729524e4991e15fd57d392ac78557d39490991e160757d392f478576d5f528991e15ca4e49c2647857a55f4e4961e15ca4e4991e05257295f4e4b51e15ca5ed39264785
  | 4, 1, 6 => 0x831a5640991e140081dc21e03b400207708991411d95c53926478581dc2264931e16076b1972647857c997264780ad607708991e0135729624e4991e160c6e8d32647857495f4e4991e15fd57d392f47857295f4e4a51e155f4e4991e0265729c22b8991e15eb57cac264785
  | 4, 1, 7 => 0x7295f4e4c31e15ca57d392cc995729a04e4991e15ca5a93926478572993404991e16116dd392647857295f358991e15ca57d01294a3581dc26e8991e15554e4991e0775831392648d1e15ca4e4991e87857955f4e4991e15ca69d3926478572939264780c95e6729c2264785
  | 4, 1, 8 => 0x7f5ac34ca32655ca57c991e011581dc857c991e15e46b0f0264785729c64e4991e1607708991e01c57295f4e4990dd5ca57c991e05a57295f4e4990d95ca4e4991e04e57295f524991e160e55539264785729c22b899229400831ba2647847295f3c4991e161155539264785
  | 4, 1, 9 => 0x7295f4c0991e161181dc22647857295f4e4a41e1607708991e07257295f504c41e15f2404d9264785729604e4991e15dd555392647858215f4e4991e1607785c2264785729c24ec991e15e357d3926478557d392f0991e15ca57d3926478557d392f4931e1607708d3264785
  | 4, 1, 10 => 0x81dc2264911e15ca57d36264785831ba4e4991e15ca57d3928c9957e1ac34c991e160c404d32cc9957295f4e4b01e16077089921878500207708991e11e657d392b89957f5ac640991e15ca6410f26478581dc2264781415ee57d392647857297e4e4b61e15ca4e4d8264785
  | 4, 1, 11 => 0x831ba554991e15ee6393926478581dbd4e4991e15ca57d391e04657295f540ae265607708991e06b576d754e4991e1607708c4264785729c2520991e15ca5d1392647854e4bc2c8991e15ca57cb0228785729392c4991e15ca57d392b499581dc2540991e160757939264785
  | 4, 1, 12 => 0x1ca57cb02b07857295f4e4ae26560c5e1392647857295f2b8991ad5ca4e4bb26478557d392647806d5ca6153926478581dc24e4991e15ca57cac264785
  | 5, 0, 0 => 0x7295f34c9921c7867f5a9404d32647867615f404d326478672997404991e02067295f418d3264786775ac404d326478676dca57d392647860020c641012647857295f4e4991e04f6729a557cd326478672997461012647867295f4e4c7264786791ac34c992187867295f404d32e07867295f4e4991e064657d3926478094236
  | 5, 0, 1 => 0x7c95f541392647867655f404ed2647867295f404e42647867295f4e4991e0316729974e4d32647867a1ca57d392647867295f4e4991e006672997404d32f47867655f404d32947867295f4e4991f478681d974e501264786404d32647808c226001392647804c07576d5f404d32647867d55f404d32647868318f404d3264786
  | 5, 0, 2 => 0x72981404d3264786001ca4e4991e00a5785ca65d3926478672939404991e02267299e404d32647867295f404ac2647867c95f4e4991e0256729c24e4991e01c67295f4e51e2647867295f404d32a87867295f5414a2647867295f4e4991e04367295f4e49920478681e0757d392647867295f42cd3264786729bd4e4d3264786
  | 5, 0, 3 => 0x729ac64101264786729b56b1392647867295f4e4db2647867a55f4e49924c786729c857d392647868320757d392647867c90134c991e02267295f4e4991e06067296f4e4991e0616729974e4991e00767295f404f53b4c46729974e4991e06567ed5f4e4d32647867295f4e4991e06967295f4e4ef2647867f5ac34c991e0306
  | 5, 0, 4 => 0x7295f4e4991e00567455f404d326478681d5f4e4f526478672983404d32a49967295f3f0d3264786001ac4e4991e0075729c24e4d326478672997404992547867295f310ac26478672973404d326478681dc24e5012647867295f460f526478681dca7095f264786729ac4e4992087867296f57d392647867b997404d3264786
  | 5, 0, 5 => 0x57d39404991e01b6785ca709392647867c95f4c501264786729ad404d32647867295f404991e02167c9f257d3926478672970404d326478675d5f404d32647867298657d39264786001ca6b0d32a499581d5f4e4c92647867295f404d32d87867c95f4e5012647867f5974e5012647867f55f430d326478657d554e4991e0726
  | 5, 0, 6 => 0x7295f4e4991e03467295f4e4991e0686729944e4ce2647867295f4e4e62647867295f4e4d12647867295f404e02647867595f404d32647867295f4e4d7264786729c24e4991e0076729ac34ca926486681dfd57d39264786729c24e4991e0656001e365d012647857295f4e4991e04867295f4e4991fc786729ac3b8d3264786
  | 5, 0, 7 => 0x7915f4e50126478657d0134c991e05b6729ac4e4991e0256001ca57d202647857295f4e4992107867c95f4e49923878672982404d32647867295f404d3288996729974e4991e072676d5f4e4d3264786831fd57d392647867c95f4e4c42647867c997404991e03b67795f404d3264786729a257d392647867295f52939310996
  | 5, 0, 8 => 0x7c55f404d3264786729ac4e4991e07067f55f4e4f52647867695f4e50126478683df265d012647867295f4e4ac264786729ac4e4cd2647867295f4e50e2647867295f528991e06b67295f4e5342647867295f4e500264786729ac478d32647867b55f404d32647867f5c24e5012647867c95f4e4991e06b67295f4e4991e0536
  | 5, 0, 9 => 0x83155404d32647867295f4e4991e01d67c997459012647866b10134c991e02367295f404a12647867295f4e52726478672958404d3264786831ca555392647867295f404f02647867f55f4e4c92647867295f520ea2647867c95f4d0d326478672997404d328c9967295f4e4ab1e06867295f4e499224786729975f939264786
  | 5, 0, 10 => 0x729974e4991e05067295f404991e05965955f404d32647867295f4e4991e02867295f444d32647860020757c991e01c57295f430d32947867295f52d392647867295f4e4f42647867295f4e4991e06167290134c9f2647867295f298a12647867295f4e4f926478657d012f0a12647866c17657cd32647867a5ca57d39264786
  | 5, 0, 11 => 0x7295f50cd326478672994404d3264786001ca65d3926478557d01368d3264786729ac4c5012647867f5b357cd32647867c9ca6b1392647867295f4e5012b89967295b404d3264786729724e4991e06867295f57d392647867295f430ed26478672961404d32647867b1ca57d3926478681dc257cd3264786729c24e4991e0726
  | 5, 0, 12 => 0x729c25f9392647867f55f460d32647867c95f4e531264786001ca6f5392647857295f529392647867f5ac34c991e0096845ca709392647867c997404fa26478675d5f4e4d32647867c997404ed2647867290134cb72647867295f4e4d32d87867c95f4e5392647867c9ac404d32647865e55f404d32647867295f5050b264786
  | 5, 0, 13 => 0x7290134c991e02c67c997404991e0136001ca57c991401c5001fb57d392647857299740499208786001fd6b0991e030557d0134c991e05567295f458d32ac786729974e4991e06e657d0134c991f07867295f4c90126478681dfd6b0d32647867295f4e4cf2647867295f4e4b626478681d5f404ed2647867f55f408d3264786
  | 5, 0, 14 => 0x729c24e4991e0506831fd6b0d32647867295f4e5012a49967c9974049924c786729ac4e4992387866955f34c991e072681d5f34c992187867297c404d32647867295f4e4c62647868095f460d32647867f55f404eb26478683d8f404d32647867755f404e82647867c99747d012647867f55f404ea2647867299734c991e02b6
  | 5, 0, 15 => 0x7295f420d32647867297257d392647867295f404991e06667295f4e528264786001ca57c780ec1c5729ac4d0d32647867f5c257cd32647867295f4e4991e0756001ca70939264785001f265d01264505791ac404d3264786729aa404d3264786001fd57c991e01c57c95f404d32a499681d5f4e4991e03b67295f4e4991e0586
  | 5, 1, 0 => 0x831554e4d3264786729c04c5012647867295f34ca92646867295f4e4a1264786729584e4d32647867295f4e4f0264786729c24e4991e06e67f55f404d32947867c997404ce2647867298857d3931078673d5f404d32647867295f4e49923c7867295f4e0d3264786729c24e4992187867297e4e4991e06e6769ac404d3264786
  | 5, 1, 1 => 0x7295f4e4991e03067f5ac694d32647867295f45cd3264786785ca561392647867f55f44cd32647867655f404d3264786729c234c9922878672989404d32647867c9ab404d326478657d0134c991e03f67ddf265d012647867c9ac65d01264786001f265d011e03b581d5f4e51626478681d5f4e4991e00267f5fd6b0d3264786
  | 5, 1, 2 => 0x7757e404d32647865a55f404d32647867295f4a901264786729ac528d326478657d23404d32647867f55f4e4991e03b67295f4e4ae2647867a5e157d392647867295f404d31e0476831ca694d3264786729944e4d32647867295f4b0d32647867c997569012647867c95f40499228786001db57d39264785729b057cd3264786
  | 5, 1, 3 => 0x7f59257d012647867f55f404e12647867295f4e4991e00c67c95f404a32647867c9ca65d01264786729ba57cd32647867695f404e52647867c9c26b1012647867295f44cea26478680dfd6b0d3264786785ca69cd326478672997404cc2647867295f4e4991e0716729974e49920878672997641012647867295f404e7264786
  | 5, 1, 4 => 0x7295f4e4991e0516001ca57d432647857295f4e4a02647860020757d392645057c98857d3926478672999404d32647867295f464d32647867295f3dcd3264786002077095f2647857295f4e4991e00d67295f4e4991e00867295f4e4991e06d67f55f4e5162647867295f4e4a926478681d5f4e49924c78674dca57d39264786
  | 5, 1, 5 => 0x1c24e4991e00757295f4e4b61e06e67295f50c991e06e67f55f4e4fa2647867295f34c991e05767f55f4e4ed26478681d5f4e4ce2647865610134c991e07267b95f4e4c626478683d55404d32647867f5ca60cd3264786729c24e4992447868315f4e49924c786001d757d39264785729ac404e5264786001ca57d392d8785
  | 5, 1, 6 => 0x7295f4e4991e02a67995f404d3264786841ca6b1392647867295f4e5292647867f56f404d32647867c95f404e82647867f55f4e51f264786799ca57d39264786739ca57d392647867c95f555392647867c95f4e4992287867295f404a328499681dac57d392647860020757d391e03b562176404d32647867c9ca70901264786
  | 5, 1, 7 => 0x1ca56139264785729c2541392647867295f4e4991e02e6729ae430d32647867295f434d32647867295f53d3926478677dac404d3264786001fd57d39264505729a1404d32647865ed76404d326478672967404d32647867a95f404a12647867295f480c42647867d15f404d32647867295f56539264786729a56415f264786
  | 5, 1, 8 => 0x729ac621392647867c997404d32647867f55f3ecd32647867555f404d32647867f55f4e4ce2647867295f4e4991e0096729c24e4991e02567c9ca65d392647867295f4e4991e00460020c555392647857755f404d32d87865ed0134c9924c7867295f4e51d2647867295f4e4992347867295f430d3264786001ca57d391403b5
  | 5, 1, 9 => 0x831ca57d392647867c997404991e0656001f26b1392647857295f42cd3310786001f2404991e00a57c9e165d012647867c95f43cd32647867295f4e4991e07367295f4e4991e012657d013a89924c786001fd57d391e03b581d5f404d32647867295f404ec2647867295f4e50f26478681dca57d39264786001ca70899228785
  | 5, 1, 10 => 0x7295f4d4d3264786001ca6e95f2647857c9c2404d32647867295f4e4f52647867295f4e4ae2648a66bdac404d32647867295f404d31e045679197404d32647867295f4e4dc264786001ca4e4991e02c57c9ac404992087867295f4e4991e03967290134cb62c87866315f404d32647867295f4e4991e01f6001ca69cd3264785
  | 5, 1, 11 => 0x7295f4e4991e015675d5f404d331078657d0134c9b2647867f55f404d3264786729c24e4c42647867c95f404991e0486729ac4e4992407867295f4e4c8264786728d3264780b02b67f5ca57d392647867995f4e4d32647867f5ac47cd326478676997404d32647867298e57d392647867295f4e4c92647867355f404991e0206
  | 5, 1, 12 => 0x7f55f4e4fe2647867295f4e50b2647867f55f34c99220786729ac3c0992187867c997404991e07267290134c991e02d67295f404d32d47867f55f404d33007867295f4e4991e02967297b404d3264786729c24e4991e06b6001ca6b0f02647857295f404991e00e67f55f34ca626478672983404f0264786729a557d39264786
  | 5, 1, 13 => 0x7295f460991e06567a59057d012647867295f519392647867295f4e4b22647867295f404ea2647867296f404e1264786831905550126478682a0757d392647867295f4e4991e06267f55f404d32ac7860015f4e4d426478557d24404d3264786001d957d392647857295f515392647867298357d392647867c9974e4d3264786
  | 5, 1, 14 => 0x7295f4e4c41e06167c997404992547868115f404d32647867c997404991e05067299763d39264786729c24e539264786811ca57d392647867f55f4e4991e01c6001ca57c991e01c576d5f4e4991e06b681d5f4e4991e0076729392648e1e06e67295f4e4991e03e67295f4ed392647867655f4049920878672966404d3264786
  | 5, 1, 15 => 0x7295f4e49a2647867f55f404d32f47867295f404ca2647867c997404992187867295f404f528c9967295f34c991e04a672995404d32647867295f504d3264786001f265d012647857295f404d32947867295f4e516310996729c2528d32647867c997404fd26478657d0134c991e02667f55f41cd3264786831e157d39264786
  | 5, 2, 0 => 0x7f5ca57cd32a4996729c1404d3264786729ac42cd32647867295f51d012647867f55f4e4991e007681dca57c9922878676571404d32647867297b4e4d32647867295f4e4991e03b67c95f4e4991e06867295f4e4992607867295f4fd392647867bd5f4b4d32647867299757d1826478672962404d32647867295f404d5264786
  | 5, 2, 1 => 0x7855f404ea2647867f597458d326478672998404e12647867295f4e4992507867c95f4e4991e061681dc257d392647867295f4e5162647867c95f4e5272647867299257d012647867c958404d32647867295f414d3264786001e657d392647857295f34cab21878683dca57d392647867295f404ea2f4786001f270901264785
  | 5, 2, 2 => 0x5550134c991e077672939404991e02c6729ba6415f2647868310134c992347867295f430992087867c95f529392647867295f4e4a52647860015f264780700757295f4e49e264786729c970939264786001f265d392647857295f4e4d3294786729a7404d3264786729ac458d33109967295f50d392647867290134c991e0326
  | 5, 2, 3 => 0x1ca57d392645057295f3dca62647867f5c257d39264786729c26dd392647867295f404f72647867295f4e49924c7867f5ac34c991e0656729c2621392647867c95f4e4c62647867297b4e4991e07267295f4e4991e01367295f4e4991e01967295f4e4d02647867295f428d32647867c997404992087867297657d39264786
  | 5, 2, 4 => 0x729c255539264786729c24e499228786729ac458d32647867295f404d330c7867295f460d328c996001ca57d412647857295f404d32cc996729ac404a1264786729ac4e5272647867295f4e4991e03a6729ac404f0264786729a0404d32647867299f65d392647867296a404d3264786001ca7094a264785001f270939264785
  | 5, 2, 5 => 0x7295f404d32a09967295f4e4b42647867295f4e4c526478681d5f4e4991e07667295f404d3264376731ca57d39264786831a5404d32647867295f56939264786001ca5ed392647857ed97404d32647867290134c991e04e67295f404f32647867ddca57d3926478683955404d3264786001ca57d391e03b57655f4e501264786
  | 5, 2, 6 => 0x15f4e4991400757f50134cb226478672960404d326478677555404d32647867295f34c991e04167c997404c4264786001ca57d3929478578d5f404d32647867295f440d326478657d0134cbc2647867295f410d32647867295f404d326478657d0134cbd24c7867295f4e4991e038672997404991e0056729ba57d39264786
  | 5, 2, 7 => 0x7295f4e4991e478657d3934cbc2647867295f404d329078681dca57d4a2647867295f4e4d32647867295f531392647860015f4e4991e00257295f404991e02067c9974e5012647867295f4e50c2647860015f4e4780ec0757295f4e4991e01c67c997404991e07467295f4e4f53107867295f4049920c7867295f34cab298786
  | 5, 2, 8 => 0x7295f404d32c07867295f4e4991e07767f5f257d392647867c98057d0126478683176404d32647867b95f404d326478681d5f4e4992387867295f4e4d32ac7867c95f4e4991e00367297e404d32d87867a55f555392647867295f4e4991e04b6785ca57d3926478672901360d32647860015f4e9392647857295f4e499264786
  | 5, 2, 9 => 0x7295f4f9392647867c99762101264786839ca57d392647867295f404d328c9967296b57d39264786845ca57d39264786729c24e4991e06167f5ac34c991e02567a5ca709392647867295f4e4991e00b6729c24e5272647867295f4e4991e03c67295f4e4991e07267895f404d32647867295f4e4991e0206729ba57d55264786
  | 5, 2, 10 => 0x7bdca57d392647867295f4e4991e01867295f4e4991e0006001e357d392647857295f4e4d32c07867295f4e4992187860015f4e4bc264785729c24e4c62647867295f4e4991e06a6001ca57d3926478500207708d32647857295f505392647867295f4e4991e0506729c2529392647860015f264780701b57b95f4e4d3264786
  | 5, 2, 11 => 0x835ca57d392647867290134cb12647867995f4e4992287868055f43cd32647867295f4e4991e05e67295f4e4991e03567295f4e4e3264786729bd4e52e2647867295f4e499200786775ca57d392647867295f4e4991e01667297857d392647867c997555012647867295f4e4b02647867295f3d8d32647867296357d39264786
  | 5, 2, 12 => 0x7295f4e49d2647867295f4e5092647867295f4e4991e0016729834e4d32647867b98e404d32647867295f54139264786001ca57d392c078578d80404d32647860000081dc2264784001ee57d3926478578d5f4e4992087860015f4e4991e00757295f4e4991e05c67295f4e499244786404d32f0b2264786729c24e52e264786
  | 5, 2, 13 => 0x7295f4e5392647867295f5513926478683178404d326478657d39264780701b67c997404991e06167295f4e5262647867295f4e4991e06b67295f4e4991e03367295f4e4991e05d657d39310bc2647867295f4e4c426478657d0134c991e01b67295f4e4991e06c672955404e826478681dc2404d3264786001ca57d3928c995
  | 5, 2, 14 => 0x7295f42ce1264786729b757d3926478600207709392647857295f2648a1e06b67295f504991e0616001ca57cac2647857295f4e50128c996729c957d392647867295f4e4b01e06b672955404d32d87867295f540992287867c997404c62647867295f4e4991e04467295f4e4a32648267295f4e4991e07867295f404d32b8996
  | 5, 2, 15 => 0x7295f4e4991ec78675d6f404d32647867295f4e537264786849ca57d39264786001ca57d392b89957295f541393107867295f4e4992307867295f4e5252647867295f4e4991e01767295f555392647867295f4e4992287860015f4e4991e01b57295f4e4991e0146
  | 6, 0, 0 => 0x7295f404d326478031dca61d5f404d326478700197404d32647801d9ca57d3934cc626478772997404d3264821e1c007295f42cd32647867295f5293934c991e1dfd57d0134c991e03b77a5e157d0134c991e1c00729974e4d3264786729ac4e50134c991e1dca57d0134c991e0307785ca5610134c991e1c00729a557cd32647867f5ca57cd3264861e1dca57d01350d3264787
  | 6, 0, 1 => 0x7b95f404d3318991e1e0c57d0134c9924c787001d757d0134c991e18007295f404d32d8786001f257d39404991e19ca57d0134c991e05177295f404d3280991e1df26215f404d3264787001ca7093934c991e19ca57d0134c991e00d77295f404d3264781b5dfd57d16404d32647877295f404d32a4991e1dca6215f4e50126478774dca57d0134c991e1dca57d2e404d3264787
  | 6, 0, 2 => 0x1ca57c991e0300959fd57d1f404d32647877f55f404d32647804ddce7295f404d32647877c95f5550134c991e1c0072939404991e01367295f4490134c991e1dca57d3934c991e0307729a9404fe34c991e1c007295f4e4991e068672997404d326478095dca57d554e5012647877295f4e5012648a1e1dca57d0134cb61e06e77f55f404fa34c991e1dfd57d013b4d3264787
  | 6, 0, 3 => 0x7295f404d32648d1e1c007295f404a1264786001ca57d0134c500ed8007295f4e527264786001ca5610134c991e18007295f404f02647867295f404d3264780b9dca57d0134c991e04d7001fd57d0134c991419ca57d0134c992147877295f5650134c991e1dca57d2a404d32647877655f404d326478195dca57d0134c991e02a77f55f404d3264931e1e10729ac404d3264787
  | 6, 0, 4 => 0x1fd57d0134c780ed8007295f404991e03067295f43d0134c991e1e077295f404d3264787729ac6210134c991e1dfd57d0134cce2647877295f404f0264861e1c007295f4e4991e0616001e97295f4e4991e19ca57d394b8d32647877295f404d326478025df272997404d32647877295f404d326478011c0083155404d32647867295f404d3264781bddca57d1d404d3264787
  | 6, 0, 5 => 0x7295f404dc34c991e1c007290134c991e02c67295f404d32647819dc0072997404992087867e5f257d0134c991e1dca57d013fcd32647877295f404d32647807dc007295f52939264786831ca57d0134c991e1dca65d0134cc4264787001f26b10134c991e180072994404d326478600000729974e4991e15ca57d0134c991e07377295f404d326478049dca57d013a4d3264787
  | 6, 0, 6 => 0x7297157d0134c991e1dca60d5f404d32647877f55f404fe34c991e1dca57d0b404d32647877295f404d3264780a5dca57d0134c991e05f7729a557d0134c991e1dca6b10134c992407877295f47cd3264861e1dca57d0134cc826478700000729c24e4991e15fd7295f404d32647877298e57d0134c991e1dca57d0134cc9264787001ca57d39318991e19ca57d013d4d3264787
  | 6, 0, 7 => 0x7295f4e4f534c991e1dca65d8f404d3264787729c24e50134c991e1c0057d01264780c00767295f34c991e0300addca404d32648e1e06e7001ca57d2a404991e1a0c7295f4e4d32647877295f404d32c8991e1e037295f404d32647877295f404d326478189c0057d01350d32647867295f430d326478195c007295f4e4991e0306001d957d0134c991e1a077295f4e4d3264787
  | 6, 0, 8 => 0x7295f404d32647803ddfd57d0134c991e00777295f404d3264780eddfd7855f404d32647877c95f404d3264781a1dca57d0134c992607877295f404e234c991e1dca57d39404991e06877295f404d3268991e1dfd7295f4e4d32647877295f4e4d3324991e1dca57d16404d3310997001f272997404991e1a0c7855f404d32647877295f404d331078185de97295f404d3310787
  | 6, 0, 9 => 0x7295f404d3294991e1dca57d0134c9e264787001ca57cd32645009580081dca57d39264786001f265d0134c991e19ca57d01310a12647877f59757d0134c991e1dca57d0134ccb264787001ca57d0c34c991e19ca57d0134c992507877c95f404d326478185c007295f34c991e01c67295f4590134c991e1dca57d39404991e061783dca57d0134c991e1dca57d0134c991e0497
  | 6, 0, 10 => 0x7295f404d3264931e1dfd5f95f404d3264787001ca57c991e0300ad9ca57d3934c991e03b77c95f404d3318991e1dca5ed0134c991e0727001fd57cd3264780959ca57d013b4991e06577295f404d32647804dc00831ca57d392647867295f404d3340991e1dca5d95f404d32647877295f404d329478195dca6b10134c991e06877f55f404d3264781c9c0081d5f404d3264786
  | 6, 0, 11 => 0x7ddca57d0134c991e1c007295f404d31e03b67295f4e501264780c1dca57d0134c991f8787001fd57d0134c991e19ca57d39458d3264787001fd7295f4e4991e19fd57d0134c991e05077295f404d3264780e9dca67d97404d3264787001ca57d39324991e19ca57d013a8991e0727001ca57d0134c991418007295f4e4f52647860015f404d32647800d8007295f34c780ec256
  | 6, 0, 12 => 0x7295f4e51f34c991e1dca57d3934c991e013772955404d3264781b9dca57d0134cb42647877295f404d3314991e1c007295f404ea264786729a557d5534c991e1dca57d393e8d32647877295f4e4ed34c991e1dcc7295f404d32647877295f5690134c991e1c007297b404d32647867f55f404d3264781b9df257d0134c991e03077295f404d326478101dca65d5f404ed264787
  | 6, 0, 13 => 0x7295f4310134c991e1c0057d0134c780ec0767295f404d326478071dca57d013d4d33107877f55f404d3264821e1c007295f4e4991e03b6001ca57d3934c780ed80057d0134c991400767295f404d32647818dc00001f265d01264785001ca57d0134ca51e18007295f4e4d3264506729ca57d0134c991e1dca57d0134c991e03877295f4e4d3264931e1c00001ca57c991e01c5
  | 6, 0, 14 => 0x7f5ca57d39404991e1c007295f4e49924c7867295f4690134c991e1c007295f4e4991e01367c95f404d32647800ddf257d013fcd32647877a55f5550134c991e1e0c7c95f404d32647877295f404d326478195de17295f404d32647877295f404d3264991e1dca57d0134c991e02777295f404d3264791e1e077c95f404d32647877295f404d334c991e1c007295f4e516264786
  | 6, 0, 15 => 0x7295f4710134c991e1dfd57d0134c992387877295f4e4d334c991e1c00001ca57d391e03b5001ca6b101264780c19ca57d0134c991e03c77295f404d3264781c9dca6210134c992387877295f404d326478081c00729ac458d32647867295f4610134c991e1dca57d0134c991e0777000007295f4e4991415fd7c95f404d32647877295f4e4d326478071dfd57d01404d3264787
  | 6, 1, 0 => 0x7295f4e4d3264781c9def7295f404d32647877295f42cd326478185dca57d0134c991e0007001e357d0134c991e19ca57d0134c992187870015f404d32f0991e18007295f404d32647867295f404d3264951e1dca57d0134c991e0507729ac404f534c991e1e0e7295f404d3264787785ca57d3934c991e1dca5ad5f404d32647877295f404d32647802ddca57d0134cbd264787
  | 6, 1, 1 => 0x7295f404d326478171c00785ca57d392647867295f4e4d3264861e1df257d013e8d3264787835ca57d0134c991e1c007295f4e4d3264786001ca57d01264780819ca57d3934c991e050775d5f404d326478185dca57d0134c991e03577295f404e334c991e1dca57d0134c99200787001ca57d39264780719dd7295f404d32647877855f404d3264781c9dca5e15f404d3264787
  | 6, 1, 2 => 0x1ca57d39264781419ca57d0134ca6264787001ca57d0134ca32659ca57d3934c992087877295f4d0d3338991e1dca57d09404d32647877295f404d326478005c007295f4e4991e07267295f5410134c991e1dca57d0134c991e056772997404d3264781bde0c57d55404d32647877295f4049920878195c007b95f404d326478678d5f404d3264821e1c0057d0134c991e0076
  | 6, 1, 3 => 0x7295f404d326478111dca57d0134ca32648277295f404d3264781e1dca57d39404d32647877c9ca65d5f404991e1dca404d3264780c02c77295f404d3264781addca57d0134c991e03377295f5413934c991e1dca57d0134c991e05d757d0134cc42f0991e1c007295f4e499218786729ac6b10134c991e1dca57d0134cc4264787000007295f4e4991e15ca57d0134c99220787
  | 6, 1, 4 => 0x1ca57d39264781ad9ca57d55404d32647877295f404d32648a1e1c007295f4e4c42647867295f404d326478051dca6215f404d3264787001ca57cdb34c991e18007295f541392647867295f404d326478079dca57d394e4d3264787001ca34c991e0250898000015f4e4991e00757295f4e4d3264781addca57d0134cd22647877295f4e4d3310991e1dca57d39404991e0657
  | 6, 1, 5 => 0x7295f404d326478185dca57d013e4d3264787001ca57d554e4991e18007295f4e4992287867295f404d3264780d1dca57d0134c991fc7877298657d0134c991e1dca5bd5f404d32647877295f47d1634c991e1dca57d013bcd32647870010134c991e01301da127295f404d3264787001ca57d394e4991e19ca6355f404d32647877295f4950134c991e1dca57d03404d3264787
  | 6, 1, 6 => 0x7295f404d3318991e1dca57d4a404d3264787
  | 7, 0, 0 => 0x1ca57d0134c991e0727001ca57d0134c991e0657001e17295f404d3264787000007295f404d31e03b6000007f55f404d3264786000007295f404d3264506001ca57d0134c9924c787001ca57d0134c991e0137001ca57d16404d3264787001ca57d0134c991e03b7001fd7295f404d3264787001ca57d0134cc9264787001ca57d013d4d32647870020c7295f404d3264787000007295f404991e0306001ca57d0134c991e0307
  | 7, 0, 1 => 0x1ca57d0134cc6264787001ca57d0134c991e0617001ca57d55404d3264787001ca6215f404d3264787001ca57d39404d3264787001ca57d0134cc426478700000001ca57d392647850000057d0134c991e0076000007295f4e4d3264786001ca57d0134c99218787000007295f404d3264786001ca57d0134c991e0507
  | 8, 0, 0 => 0x7295f404d3264786
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
private theorem z3_48 : span (Z 3) 14 48 = true := by decide +kernel

private theorem z3_a1 : span (Z 3) 48 0 = true :=
  span_join (f := Z 3) (a := 24) (o := 0) (b := 24) z3_0 z3_24

private theorem z3_a2 : span (Z 3) 62 0 = true :=
  span_join (f := Z 3) (a := 48) (o := 0) (b := 14) z3_a1 z3_48

private theorem z3 : span (Z 3) 62 0 = true := z3_a2

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
private theorem z4_456 : span (Z 4) 1 456 = true := by decide +kernel

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

private theorem z4_a19 : span (Z 4) 457 0 = true :=
  span_join (f := Z 4) (a := 456) (o := 0) (b := 1) z4_a18 z4_456

private theorem z4 : span (Z 4) 457 0 = true := z4_a19

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
private theorem z5_744 : span (Z 5) 21 744 = true := by decide +kernel

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

private theorem z5_a31 : span (Z 5) 765 0 = true :=
  span_join (f := Z 5) (a := 744) (o := 0) (b := 21) z5_a30 z5_744

private theorem z5 : span (Z 5) 765 0 = true := z5_a31

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
private theorem z6_336 : span (Z 6) 18 336 = true := by decide +kernel

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

private theorem z6_a14 : span (Z 6) 354 0 = true :=
  span_join (f := Z 6) (a := 336) (o := 0) (b := 18) z6_a13 z6_336

private theorem z6 : span (Z 6) 354 0 = true := z6_a14

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

def CG : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12613

theorem PEqualNP.Outside.L_meta_12613 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636138 * 2 ^ 32 + 4008373992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636138 * 2 ^ 32 + 4008373992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12613.mainG PEqualNP.Outside.L_meta_12613.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12613.CG, PEqualNP.Outside.L_meta_12613.CG_mono, by
      have : PEqualNP.Outside.L_meta_12613.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12613.CG_eval⟩
