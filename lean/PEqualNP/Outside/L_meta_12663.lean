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
namespace PEqualNP.Outside.L_meta_12663

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 3974160608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 8, 9, 10, 11, 12, 0, 0, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25, 0, 0, 28, 0, 0, 0, 32, 0, 34, 0, 36, 0, 0, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 5, 5, 5, 5, 5, 5, 6, 7, 5, 5, 5, 5, 5, 13, 14, 15, 5, 5, 5, 5, 5, 21, 22, 23, 5, 5, 26, 27, 5, 29, 30, 31, 5, 33, 5, 35, 5, 37, 38, 39, 5, 41, 5, 43, 5, 45, 46, 47, 5, 49, 5, 51, 5, 53, 54, 55, 5, 57, 58, 59, 60, 61, 62, 63, 6, 6, 6, 6, 6, 5, 6, 7, 6, 6, 6, 6, 6, 13, 14, 15, 6, 6, 6, 6, 6, 21, 22, 23, 6, 6, 26, 27, 6, 29, 30, 31, 6, 33, 6, 35, 6, 37, 38, 39, 6, 41, 6, 43, 6, 45, 46, 47, 6, 49, 6, 51, 6, 53, 54, 55, 6, 57, 58, 59, 60, 61, 62, 63, 7, 7, 7, 7, 7, 5, 6, 7, 7, 7, 7, 7, 7, 13, 14, 15, 7, 7, 7, 7, 7, 21, 22, 23, 7, 7, 26, 27, 7, 29, 30, 31, 7, 33, 7, 35, 7, 37, 38, 39, 7, 41, 7, 43, 7, 45, 46, 47, 7, 49, 7, 51, 7, 53, 54, 55, 7, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 13, 13, 13, 13, 13, 5, 6, 7, 13, 13, 13, 13, 13, 13, 14, 15, 13, 13, 13, 13, 13, 21, 22, 23, 13, 13, 26, 27, 13, 29, 30, 31, 13, 33, 13, 35, 13, 37, 38, 39, 13, 41, 13, 43, 13, 45, 46, 47, 13, 49, 13, 51, 13, 53, 54, 55, 13, 57, 58, 59, 60, 61, 62, 63, 14, 14, 14, 14, 14, 5, 6, 7, 14, 14, 14, 14, 14, 13, 14, 15, 14, 14, 14, 14, 14, 21, 22, 23, 14, 14, 26, 27, 14, 29, 30, 31, 14, 33, 14, 35, 14, 37, 38, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 58, 59, 60, 61, 62, 63, 15, 15, 15, 15, 15, 5, 6, 7, 15, 15, 15, 15, 15, 13, 14, 15, 15, 15, 15, 15, 15, 21, 22, 23, 15, 15, 26, 27, 15, 29, 30, 31, 15, 33, 15, 35, 15, 37, 38, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 21, 21, 21, 21, 21, 5, 6, 7, 21, 21, 21, 21, 21, 13, 14, 15, 21, 21, 21, 21, 21, 21, 22, 23, 21, 21, 26, 27, 21, 29, 30, 31, 21, 33, 21, 35, 21, 37, 38, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 58, 59, 60, 61, 62, 63, 22, 22, 22, 22, 22, 5, 6, 7, 22, 22, 22, 22, 22, 13, 14, 15, 22, 22, 22, 22, 22, 21, 22, 23, 22, 22, 26, 27, 22, 29, 30, 31, 22, 33, 22, 35, 22, 37, 38, 39, 22, 41, 22, 43, 22, 45, 46, 47, 22, 49, 22, 51, 22, 53, 54, 55, 22, 57, 58, 59, 60, 61, 62, 63, 23, 23, 23, 23, 23, 5, 6, 7, 23, 23, 23, 23, 23, 13, 14, 15, 23, 23, 23, 23, 23, 21, 22, 23, 23, 23, 26, 27, 23, 29, 30, 31, 23, 33, 23, 35, 23, 37, 38, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 26, 26, 26, 26, 26, 5, 6, 7, 26, 26, 26, 26, 26, 13, 14, 15, 26, 26, 26, 26, 26, 21, 22, 23, 26, 26, 26, 27, 26, 29, 30, 31, 26, 33, 26, 35, 26, 37, 38, 39, 26, 41, 26, 43, 26, 45, 46, 47, 26, 49, 26, 51, 26, 53, 54, 55, 26, 57, 58, 59, 60, 61, 62, 63, 27, 27, 27, 27, 27, 5, 6, 7, 27, 27, 27, 27, 27, 13, 14, 15, 27, 27, 27, 27, 27, 21, 22, 23, 27, 27, 26, 27, 27, 29, 30, 31, 27, 33, 27, 35, 27, 37, 38, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 29, 29, 29, 29, 29, 5, 6, 7, 29, 29, 29, 29, 29, 13, 14, 15, 29, 29, 29, 29, 29, 21, 22, 23, 29, 29, 26, 27, 29, 29, 30, 31, 29, 33, 29, 35, 29, 37, 38, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 58, 59, 60, 61, 62, 63, 30, 30, 30, 30, 30, 5, 6, 7, 30, 30, 30, 30, 30, 13, 14, 15, 30, 30, 30, 30, 30, 21, 22, 23, 30, 30, 26, 27, 30, 29, 30, 31, 30, 33, 30, 35, 30, 37, 38, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 58, 59, 60, 61, 62, 63, 31, 31, 31, 31, 31, 5, 6, 7, 31, 31, 31, 31, 31, 13, 14, 15, 31, 31, 31, 31, 31, 21, 22, 23, 31, 31, 26, 27, 31, 29, 30, 31, 31, 33, 31, 35, 31, 37, 38, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 33, 33, 33, 33, 33, 5, 6, 7, 33, 33, 33, 33, 33, 13, 14, 15, 33, 33, 33, 33, 33, 21, 22, 23, 33, 33, 26, 27, 33, 29, 30, 31, 33, 33, 33, 35, 33, 37, 38, 39, 33, 41, 33, 43, 33, 45, 46, 47, 33, 49, 33, 51, 33, 53, 54, 55, 33, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 35, 35, 35, 35, 35, 5, 6, 7, 35, 35, 35, 35, 35, 13, 14, 15, 35, 35, 35, 35, 35, 21, 22, 23, 35, 35, 26, 27, 35, 29, 30, 31, 35, 33, 35, 35, 35, 37, 38, 39, 35, 41, 35, 43, 35, 45, 46, 47, 35, 49, 35, 51, 35, 53, 54, 55, 35, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 37, 37, 37, 37, 37, 5, 6, 7, 37, 37, 37, 37, 37, 13, 14, 15, 37, 37, 37, 37, 37, 21, 22, 23, 37, 37, 26, 27, 37, 29, 30, 31, 37, 33, 37, 35, 37, 37, 38, 39, 37, 41, 37, 43, 37, 45, 46, 47, 37, 49, 37, 51, 37, 53, 54, 55, 37, 57, 58, 59, 60, 61, 62, 63, 38, 38, 38, 38, 38, 5, 6, 7, 38, 38, 38, 38, 38, 13, 14, 15, 38, 38, 38, 38, 38, 21, 22, 23, 38, 38, 26, 27, 38, 29, 30, 31, 38, 33, 38, 35, 38, 37, 38, 39, 38, 41, 38, 43, 38, 45, 46, 47, 38, 49, 38, 51, 38, 53, 54, 55, 38, 57, 58, 59, 60, 61, 62, 63, 39, 39, 39, 39, 39, 5, 6, 7, 39, 39, 39, 39, 39, 13, 14, 15, 39, 39, 39, 39, 39, 21, 22, 23, 39, 39, 26, 27, 39, 29, 30, 31, 39, 33, 39, 35, 39, 37, 38, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 41, 41, 41, 41, 41, 5, 6, 7, 41, 41, 41, 41, 41, 13, 14, 15, 41, 41, 41, 41, 41, 21, 22, 23, 41, 41, 26, 27, 41, 29, 30, 31, 41, 33, 41, 35, 41, 37, 38, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 43, 43, 43, 43, 43, 5, 6, 7, 43, 43, 43, 43, 43, 13, 14, 15, 43, 43, 43, 43, 43, 21, 22, 23, 43, 43, 26, 27, 43, 29, 30, 31, 43, 33, 43, 35, 43, 37, 38, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 45, 45, 45, 45, 45, 5, 6, 7, 45, 45, 45, 45, 45, 13, 14, 15, 45, 45, 45, 45, 45, 21, 22, 23, 45, 45, 26, 27, 45, 29, 30, 31, 45, 33, 45, 35, 45, 37, 38, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 58, 59, 60, 61, 62, 63, 46, 46, 46, 46, 46, 5, 6, 7, 46, 46, 46, 46, 46, 13, 14, 15, 46, 46, 46, 46, 46, 21, 22, 23, 46, 46, 26, 27, 46, 29, 30, 31, 46, 33, 46, 35, 46, 37, 38, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 58, 59, 60, 61, 62, 63, 47, 47, 47, 47, 47, 5, 6, 7, 47, 47, 47, 47, 47, 13, 14, 15, 47, 47, 47, 47, 47, 21, 22, 23, 47, 47, 26, 27, 47, 29, 30, 31, 47, 33, 47, 35, 47, 37, 38, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 49, 49, 49, 49, 49, 5, 6, 7, 49, 49, 49, 49, 49, 13, 14, 15, 49, 49, 49, 49, 49, 21, 22, 23, 49, 49, 26, 27, 49, 29, 30, 31, 49, 33, 49, 35, 49, 37, 38, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 51, 51, 51, 51, 51, 5, 6, 7, 51, 51, 51, 51, 51, 13, 14, 15, 51, 51, 51, 51, 51, 21, 22, 23, 51, 51, 26, 27, 51, 29, 30, 31, 51, 33, 51, 35, 51, 37, 38, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 53, 53, 53, 53, 53, 5, 6, 7, 53, 53, 53, 53, 53, 13, 14, 15, 53, 53, 53, 53, 53, 21, 22, 23, 53, 53, 26, 27, 53, 29, 30, 31, 53, 33, 53, 35, 53, 37, 38, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 58, 59, 60, 61, 62, 63, 54, 54, 54, 54, 54, 5, 6, 7, 54, 54, 54, 54, 54, 13, 14, 15, 54, 54, 54, 54, 54, 21, 22, 23, 54, 54, 26, 27, 54, 29, 30, 31, 54, 33, 54, 35, 54, 37, 38, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 58, 59, 60, 61, 62, 63, 55, 55, 55, 55, 55, 5, 6, 7, 55, 55, 55, 55, 55, 13, 14, 15, 55, 55, 55, 55, 55, 21, 22, 23, 55, 55, 26, 27, 55, 29, 30, 31, 55, 33, 55, 35, 55, 37, 38, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63, 57, 57, 57, 57, 57, 5, 6, 7, 57, 57, 57, 57, 57, 13, 14, 15, 57, 57, 57, 57, 57, 21, 22, 23, 57, 57, 26, 27, 57, 29, 30, 31, 57, 33, 57, 35, 57, 37, 38, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 58, 59, 60, 61, 62, 63, 58, 58, 58, 58, 58, 5, 6, 7, 58, 58, 58, 58, 58, 13, 14, 15, 58, 58, 58, 58, 58, 21, 22, 23, 58, 58, 26, 27, 58, 29, 30, 31, 58, 33, 58, 35, 58, 37, 38, 39, 58, 41, 58, 43, 58, 45, 46, 47, 58, 49, 58, 51, 58, 53, 54, 55, 58, 57, 58, 59, 60, 61, 62, 63, 59, 59, 59, 59, 59, 5, 6, 7, 59, 59, 59, 59, 59, 13, 14, 15, 59, 59, 59, 59, 59, 21, 22, 23, 59, 59, 26, 27, 59, 29, 30, 31, 59, 33, 59, 35, 59, 37, 38, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 58, 59, 60, 61, 62, 63, 60, 60, 60, 60, 60, 5, 6, 7, 60, 60, 60, 60, 60, 13, 14, 15, 60, 60, 60, 60, 60, 21, 22, 23, 60, 60, 26, 27, 60, 29, 30, 31, 60, 33, 60, 35, 60, 37, 38, 39, 60, 41, 60, 43, 60, 45, 46, 47, 60, 49, 60, 51, 60, 53, 54, 55, 60, 57, 58, 59, 60, 61, 62, 63, 61, 61, 61, 61, 61, 5, 6, 7, 61, 61, 61, 61, 61, 13, 14, 15, 61, 61, 61, 61, 61, 21, 22, 23, 61, 61, 26, 27, 61, 29, 30, 31, 61, 33, 61, 35, 61, 37, 38, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 58, 59, 60, 61, 62, 63, 62, 62, 62, 62, 62, 5, 6, 7, 62, 62, 62, 62, 62, 13, 14, 15, 62, 62, 62, 62, 62, 21, 22, 23, 62, 62, 26, 27, 62, 29, 30, 31, 62, 33, 62, 35, 62, 37, 38, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 58, 59, 60, 61, 62, 63, 63, 63, 63, 63, 63, 5, 6, 7, 63, 63, 63, 63, 63, 13, 14, 15, 63, 63, 63, 63, 63, 21, 22, 23, 63, 63, 26, 27, 63, 29, 30, 31, 63, 33, 63, 35, 63, 37, 38, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 58, 59, 60, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f000000000000000001151515131f1f1f01151515131f1f1f0000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f0000000000000000000000000000000000000000000000000000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xfeeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e00000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e000000000000000000000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e000000000000000000000000000000000000000000000000000000000000000000000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e000000000000000000000000000000000000000000000000000000000000000000000000000000000feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xfeeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0feeaeaeaece0e0e0

def cMZZ : Nat := 0x1151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f000000000000000001151515131f1f1f000000000000000001151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f0000000000000000000000000000000001151515131f1f1f01151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f00000000000000000000000000000000000000000000000001151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f01151515131f1f1f

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
  | 2, 0 => 0xd698e864b46d78d4acd448f1
  | 3, 0 => 0xda609c18d40a66f2ced5217e9cc38dfd8efbe2198ecbed158e8eb1e8859c9d8d8597edb86ca07d856770d45665074da25b4fbb5251704dd045d52ffe2dcc6c572bdd3724232e2eb020eb132417a3ce12
  | 4, 0 => 0x434226d5425a538f41d8918d3ed8e4e23e566c503dcfa23e3c156bb539b9f751390b49dc38fe54e4388fec8737cbb5073687d8f636717fd43603c17233b109883237073a31f89db530f92bb72e46fc0c2e06ff8b2d327cdd2c5617d32ac1d73f2a7f8e97278f98f5276b0c17254a4923249710b92343320d21bbbe7321b180ef2072b21120412f441ffc44611e1824601d8b66161d4ebc0c1b777d861b6a67ca1b32961819ff7f2e19e9811c17a01d2f16ee5cb015335ca80f8bf50b0dce4d480d97a01b0d229f370c82a5400bbfae190aacedb309a67dfd0873c522060303e405ea7e8d04af0d2c047c20fe043774340409ee4a03335ab102a99c24025874e2
  | 4, 1 => 0x8708262f864072f385d52a8185ad1b4c8399701f82f5da4e82382dc980659bf97e8e2fe87e172aed7e00c6157d9f816c77301feb76d88ea2754f7cc7754b668074821217743cf1c072a9732171e04a5f701a37536ff51d046f04ce976e7d430f6e0e64b76b5072446a1aa9fd6945145267bc612166e6be0a66c45f5466ae614265ea4d5d6522f57264ff3e7f64d3c655645e7e4860a5f1ee5fba232c5fad0d705d639d005c29cc845a40c5025a35fc6159290c165927ee5357ed133e57eabadc5752357257029662552d02d5521ceffe51132f3651067ba14f7251a84d627da94b50d67f4b3898034a41301e4a2f416b483a9cd947eb75ce46c1b6994655e958
  | 4, 2 => 0xeba936a3eb224457ea7134d8e958d444e757edc3e738a0fae6119bb8dee293fedb61335cdb4841b7db3755a9dac5a3f5d93a7afed931d1edd88dc271d48ec551d3d27936d2e4ba1bd121d678cd903ae8ccb7df2fc7043b2ec6bd9567c63b9650c57d7f7cc4793e83c2bd47ddc0c05628beb682f9bc109bfbbb2a649bbab1fb53b9fef8b6b9a9d91cb75304a4b6c74ef6b5543cb4b4450e0db3dc3ceab2a4967eb1e67faab193fdd8b05104ffad695e93ad331dcda4c58a65a25aedbea0b653209efaa79d9d86810498fb663d988e9c86951eeef18ff7ebe58dac786b8d6386078c81982c8c3d6ba38c03ea5d8b1b4c768a7a7cf3892fea7c88fc735f87153beb
  | 4, 3 => 0xffe8db30ff587a8efe9698d4fe3bcd5efe0834aaf9264c70f8139b4ff79b6efaf6db7c06f4d9b9daf4390ea9f419f436f3e253d9f152e98ef065b886efe3b96fec1f311d
  | 5, 0 => 0x172f31a616ee5cb016696a2e15e4d22b14714a7814036c7e13cb6e22133ee1371310b8c5130f394b1205d49c1149ddb0110b1fa910765bdc1061bb560f8bf50b0f74ac4f0f4f01b20efbb2c30db945570daf29cb0d9ca5680d7baba00ce25bf90c7841dd0bdac0110b8b9fc20aa082080a9e98780a7dff9d09e9484b09ac13be09a1726f09550c690940056e0827702107584dcf071e777706e9949e06848bf3065179b0060fceb3060303e405ed85190574073f053faedb053080bb04fe917b04c41562046cde03041924dc03e84af00322e5c4026069510253bbfb024680ba022252a301bdc31001b3498a0112f8770110b57900b24026009aa9ee0037cfc1
  | 5, 1 => 0x2d837b3d2d0c2dce2d00e8c72ca271bd2b77f5cd2b2b0efc2ac1d73f2a1f6fa0293519e828b94cb028134367280d58e527cc9bf527c1164426b611f6268745c8257166ec2559d71c2531808624fc8fcc24d961f224556fd2244ee4f624491d9623653bbe2352e6902332b5012316359122ed186d22d1a59a22462d62215235ae21413f66212900ea1f834e831e1824601dfb5aab1d8b66161d60d16e1cb372281c7a69421c7663491c6c190a1be703631be537ba1ba8debb1b3341691b3142cc1b1db5131ad7800c1a6a5ab81a28b5601a0db53f1a01c59019ebc77e19e9811c19c3e6e919bd80bb1876cea1183ceca517a19dfe179f04e7175795db173b2b5e
  | 5, 2 => 0x43d72d9e43d4e828432ec7db430f76fa423bc7a0422bcb08417eb72d414522734140db2b413b6188412f5fbd4122d62040a521a54083ebaf4076d5f3401f9d2f40123ef4400b12e43f8b9d1e3f59740a3f357d393e64b36f3e58b2b23e4def623e2989093dacca083c9eca293bf0543c3bdab6443b4fe5013b135e5939d41b77398a95e63988e4be3984be2f380d9c1b38018f98378ff2943683676036477d773602abf735e49f8835e08a4a35a349e7359d7657357a0d7435314d48335405e7334128fc3312519732a6e2043264df01325a188a323d7dac321a356b31ec24be31d0ae4431c2be6c31ac16b73188997e30995c63300d631b2f8376d82ddd7c25
  | 5, 3 => 0x5936ab4958f3397457ed133e57cf0ad757cd0ae657523572565604e05607848a55f75ab755dbae6c55408ef7547e98cf547b5029540793d453eda9d953b870d35359eca3526136df524e2e22524430a7521ceffe51f16e715189391b5137796a5109a6b150f9fce15088897150205f054efc59134eca14544e5ae56e4e38c0154e17cc734d8b0e294d466dc44d220f254d2088d24cdd7f564cc283804caa7fe94c8266af4c7e217c4c1f68824a727afe4a6f1cf94a6f0e084a0358bc49e9292f49999cab4991e64748d7f7b24890ade64749c72a473247e146ee04c34680458446159087460aa03a45e585eb45b494e044bca317446dabf6441ef85d43fecd9e
  | 5, 4 => 0x705de8956fe746f86ebee88c6e93b4d86e7f056d6de9e0f46dbb888d6d5dfee26d07f8586cf885d16c85a6606c0548716bdafaab6b4a90656b2bfded6af870fd6aa05fe46a95ed0b6a1aa9fd6962c56868f68c776858f4ba67ff516167fadbea67d2b2e466ae61426654011265f6a7fa65e854cc64d58edf64b04345644655ed63134785627cb59a61aa598e61678cfb60fc0dfd608cb3ed606ae5da6051e0d6603c9c036022f7dc5fa28f005f38d2ef5f2cbf655f1643ec5f0ee6545eecdc465eacfad15e4b60b05de5eaf35dd45fb55d639d005cf88f165cf123905c4536725c29cc845b9d84335b3fdc8e5ac95a635ac17f525a33fcdd5a25c10e5989d906
  | 5, 5 => 0x8c2974978bc30ebe8ae285058a32248789cca5d1895de638894a367a892df1be88fc735f88d4e28488af6c2b8894ff65880fe18887ecbb51875d32dc8751dd85860ceba6856d8e6b84aa1db0842e233c83a96092832386b4828ea3a2821c98118218d06381a47eb58183dc9080c0297680a45079808795d78070d1f580474cb07fa44b1f7ee7d50d7e48eeb77e079ce77dff993d7d237e827c7901e17bca43397bad720d7b5444e87a26da1b795dc1d178c7e60f77bea37177b2a52a778eeb05777e78307680fbb37673ecac7641393c7621bbc575fa061975b61a9674eb10847437d41674096a7372bab2d872420b2d71df8f6a71639e3c714a6a8a70c1b468
  | 5, 6 => 0xa9dd4caea9d036f2a976df6da8f34c38a88fafc9a7f5ff47a737e873a7123f5fa6c8fe58a6491721a6275deea485b64ba40820fea3e4a088a380a3cfa2a84816a2a76505a232c0f5a213f1eda1c50ff6a054eef5a016d2a19faf1fe99f85ce909f804b7c9f59b8839efa22289ebf94d19eb236459e9ba9a39e8d15189d8681049cec79529c44dd419c2bff379b582e049a69a76a9a1a52109948f361988e9c869805447b96b0bf0f96ae095595dcaaa6955fc9cf9555b60e953e605194a6056d93f74e9893f4b734939edd7c9164343a912db864911acd8290a2643a902dac788f9a42038f3747838d83b71e8d6345138d436d8b8cc68e518cb7b7dd8c91e664
  | 5, 7 => 0xc9aeeb08c8b34a6dc80e8a63c7bf1152c6a38c44c63b9650c6080f03c549f82fc467d08fc41acbf2c361489ac2dc8a0ac24c2c2fc1999f8ac129ce46c1141455c0a96dedc00f3d6bbfae418abf85701abf30ccafbef0a166bd4856aabd2909e1bcaf7d9abc82b6d0bc2adc9fbbf4a746bbb61755baef5cbdbab441b5ba4d3182b9578af4b915f2d0b8fc1b72b8bac5d1b83f0bdcb82abcc3b790b047b6d9ee16b6d4d1c5b6617205b52504d4b2c74388b2a4967eb2990af5b2712f9db127be90afbaea14af502189aef29a66aeebcd3dae7e2b58ae4a6724ad6d0a77ad695e93ad51039dac9caf40abb5ec2bab1fd4c5aaf779fdaad8d536aabefb81aa7f2e38
  | 5, 8 => 0xfe2d4c25fde9bc09fdd4ad5dfb3ab205fadedac1fa9840a2f8139b4ff79db55cf4d9b9daf4088d42f246cf3ff15ad0acf12961cdf019cd1defd9e9feefb03222ee43af09ed15f2f4ec8d871aeba936a3eb23c58ae757edc3e756e0f4e6cd7e7ae6acb895e6761de6e5352238e49c28aee2579b3ae0ed8369e09d5695e00916eadfcc22dadfc29da1dec76ffcde642e04de1ef5f0dd724a87dd3d5812dbf36cc6da9013fad97f939cd9688b28d89a0506d862e548d5d94417d420946bd3cbfcb3d39d6c76d240ba33d0cdd528d00ed1a0cf16b557cdb57f56cd8bd7e1ccda5be8ca859303ca297790ca0bda15ca0a5d1dc9d2bcc0
  | 6, 0 => 0x226e8a63220fd16920ddde0820a69e90205f85e01ff3c1a31fe4c9541f8a05921e8116cd1d60d16e1d3a30111d22b0c81d159b0c1c70ae6b1c3f79a91be703631ba4fdc71a0f61441a0db53f19ebc77e19c7968519c5510f199951f6191f30c2183f3307182c3087181c33ef176f201417358b5a17133f0716b4c0ae169729b916958a8c16673eda161006161602a7db15e4d22b1490c84c14551c5611c7cc120f7afecd0f794da50d805b7b0ce25bf90c37e65e0bd0f3310b8b9fc20b6a765b09e9484b09579b5b08840310086d766e084a8171082de69307dc8da507c1172b079c7f9e03779c3302fc96b502f151ae0292daa4011b77e300b24026009aa9ee
  | 6, 1 => 0x3be710e13b8b47d53a36bed439e8f05e39d41b77398a95e6386d1e81380d9c1b379ac27536ec76e436979ace36836760367d1cd4364e75d636477d77364249bd362d04ea361b0464361360c335e49f8835e08a4a351d284c3506acd334ff4f3b343bc99733d653da33c4c89c335405e732e18c7732c8d4da32851738321a356b31c2be6c316eeed73130457530b9c34a309a5201302465c42fd9dbce2ddd7c252d00e8c72bf7ed712bcc17532b30f7de2ade82d92a97e8ba2a6bb91029a8d9ba28c26e31283e9709280d58e527e1d7582779a2022727e25126f8b0e526ea65c82678f25826113d1c2531808624ecc1fa2336d6ab22cde83d22caf920229ae8d0
  | 6, 2 => 0x5ca00cf05b5df7525a9a86975a1e8c2359b6ee075999c9795906f754587f0c895851ab9b5809394a5777b382577445775677febe56613adc5637b5975531289954d83df453f805ce53f00224536b76a95359eca35313e76952696ac852521945513c884a4f1d15544eb84ef64da30e114d7f53ec4d6079814cdd7f564c71649a4c6455934c1f68824be6ab764ba6837d4b0672064a6f1cf94a0358bc49eb6f9149999cab48ab1bbf47cff85147484f4d46dd8ef246b21d4f464e517c45e47a3e44af51734404176a43da49db42dcaa0f42760f4741f5b15841cb639241452273413af94c408655f2400b12e43defba483dc31bcb3ce2040c3c9eca293c4469f9
  | 6, 3 => 0x7e8018b07de6682e7cdd27697c3980087c1f10957ae25bdd7a761f327a0300cf79d5096f799944be798af28578c7e60f782329dc78045ad477b578dd764557dc76073b8875b61a96759f88d075763777754a216a74a29f2c743a0def72dce239714896eb7144ca866f395c486e7f056d6cbad2d16c2767166c0548716bcd138d6b7a94dc6b5032b66b461ef56a966e54698a3df9690faf896858f4ba67549d216737f8a9671e214b669702d96647258a65fabb7965f6a7fa65e0325d6527b06a636cfef0630342df62824f4b627cb59a61c2667f61aa598e616e96ea6137e06d60d2edec5fb8b6f65f4e4f1f5f3a9f615f1e5aa55eecdc465e004a6f5de98b04
  | 6, 4 => 0xa7f5ff47a6be3e0fa5ff3a87a5b5c2a9a3a5e83da2cac4cfa0194a3d9f85ce909eb236459ea3b3549e9ba9a39dfef34a9c93f52b9c04f0849bf877ea9bc3d5e99b9cac9a971a372d96fecd1d96d2b58d95ffa65295f6500d9575d901955fc9cf9555b60e9532642394e10a4d929fe681927c5dad922fd938921b458691aa01a191a6803c912db86490a4aa9c903d9a698f47f3db8f065bb78eec84598e2f74c38e1b25aa8cca56fd8cc53aac8c51daec8ac6da5a8a3c865888fc735f88fb42f1888973dc8861988485ab52fb856eeea584e3034d84aa1db083df820583416c84828d1827820a656b81a6551280c93e1d80af64687fc09fd97fb69ef17f674854
  | 6, 5 => 0xfb4a3ffefb21e968fadedac1fa9840a2fa45d8b4f8dd814ff4088d42f3513a50f1d76c45f05ac39aefdc3060efd9e9feed15f2f4e9bbd704e90121a7e50e7dd2e38d0e4ae2d2c4dbe17c08a4e090eaeadfd9b12ddf45754bdc74f4d5dbddedfbd9d8b3d2d7ae2bf2d62838a3d41db50cd3da24f0d22ac180d0cf43a8d088a989cd8e1e43c8b34a6dc825aad2c60a3604c6080f03c5555e21c3065bdbbfae418abef0a166bd2bb969bcbde761bc9d217cbc6686cdb8fc1b72b6ddec50b6d4d1c5b5bc8bc1b4a9c5c3b440e9bfb0807ce1af58f40fae4a6724aabefb81aa10fd52a9bc659aa98dd55da8c78e22a831231a
  | 7, 0 => 0xfb21e968f3513a50f1d76c45efdc3060e17c08a4dfd9b12dc3065bdbb8fc1b729ea3b35494e10a4d922fd9388cc53aac88fc735f80af64687576377774a29f2c6b5032b66b461ef5671e214b5eecdc465851ab9b4eb84ef64ba6837d41f5b1583be710e1379ac27522cde83d205f85e01ff3c1a31f8a05921c3f79a917358b5a0f7afecd0c37e65e02f151ae
  | 8, 0 => 0x5eecdc46
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000ff00000000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f0000000000ffffff000000000000ffff0000000000000000
  | 0, 1 => 0xff00ff0000000000ff000000ff000000f0f0f000f0f0f000f000f000f000f000cccccc00cccccc00aaaaaa00aaaaaa00aa00aa00aa00aa005555550055555500550055005500550033333300333333000f0f0f000f0f0f0000ffffffffffff0000ffff0000ffff0000ff000000ff000000f0f00000f0f00000cccc0000cccc
  | 0, 2 => 0x11111111111111110fffffff0fffffff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000000000f000f000f000f000f0000000f0000000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0505050505050505030303030303030300ffffffffffffff00ffffff00ffffff00ffffff0000000000ff00ff00ff00ff
  | 0, 3 => 0x3f3f3f3f000000003f003f003f003f003f0000003f00000033ffffff33ffffff33ffffff000000003333ffff3333ffff33333333ffffffff333333333333333333333333000000003300330033003300330000003300000030f0f0f030f0f0f030303030303030302a2a2a2a2a2a2a2a22aaaaaa22aaaaaa2222222222222222
  | 0, 4 => 0x5f0000005f00000055ffffff55ffffff55ff55ff55ff55ff55555555ffffffff5555555555555555555555550000000055005500ff00ff00550055005500550055000000ff000000550000005500000050505050f0f0f0f050505050505050504c4c4c4c4c4c4c4c44444444cccccccc44444444444444443f3f3f3f3f3f3f3f
  | 0, 5 => 0xaa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a00000a0000000a00000008888888888888888888888880000000088880000888800008800000088000000808080808080808077777777777777775f5f5f5f5f5f5f5f5f5f5f5f000000005f005f005f005f00
  | 0, 6 => 0xaaaaaaaaaa000000aaaaaaaaa8a8a8a8aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa22222222aaaaaaaa00000000aaaaaa00aaaaaa00aaaa8888aaaa8888aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aaa0a0a0aaa0a0a0aa88aa88aa88aa88aa888888aa888888aa00aa00aa00aa00aa00aa0000000000
  | 0, 7 => 0xc0c0c0c000000000c000c000c000c000c0000000c0000000bbbbbbbbbbbbbbbbbbbbbbbb00000000afafafafafafafafaaffffffaaffffffaaffaaffaaffaaffaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaafafafafaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaaaaaaaaa0000aaaaaaaaaaa0a0a0aaaaaaaaaa00aa00
  | 0, 8 => 0xcccc8888cccc8888cccc0000cccc0000cccc000000000000ccc8ccc8ccc8ccc8ccc8c8c8ccc8c8c8ccc0ccc0ccc0ccc0ccc0c0c0ccc0c0c0cc88cc88cc88cc88cc888888cc888888cc44cc44cc44cc44cc444444cc444444cc00cc00cc00cc00cc000000cc000000cc00000000000000c8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0
  | 0, 9 => 0xcccfcfcfcccfcfcfcccfcccfcccfcccfcccceeeecccceeeeccccccccffffffffcccccccccccccccccccccccccccc0000ccccccccccc0ccc0ccccccccccc0c0c0cccccccccc00cc00cccccccccc000000ccccccccc0c0c0c0cccccccc88888888cccccccc00000000ccccccc0ccccccc0cccccc00cccccc00ccccc0c0ccccc0c0
  | 0, 10 => 0xececececececececececececcccccccceccceccceccceccceccccccceccccccceaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaaeaeaaaaaeaeaaaaaeaaaaaaaeaaaaaaae0e0e0e0e0e0e0e0dddddddddddddddddddd0000dddd0000dd000000dd000000cfcfcfcfcfcfcfcfccffffffccffffffccffccffccffccffcceeeeeecceeeeee
  | 0, 11 => 0xf000000000000000eeeeeeeeeeeeeeeeeeeeeeeeececececeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeee0000eeee0000eeeaeaeaeeeaeaeaeecceecceecceecceecceecccccccccceecccccceecccccceecccccccccccccceeaaeeaaeeaaeeaaeeaaaaaaeeaaaaaaeeaaaaaaaaaaaaaaee000000ee000000
  | 0, 12 => 0xf0f0f0f0e0e0e0e0f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0e0e0e0f0e0e0e0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f0a0a0a0f0a0a0a0f000f000f000f000f0000000f0000000
  | 0, 13 => 0xfaaafaaa00000000faaaaaaafaaaaaaafaaaaaaaaaaaaaaafaaaaaaa00000000fa000000fa000000f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0f8f0f0f0f8f0f0f0f5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f0fffffff0fffffff0fff0fff0fff0fff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0000000
  | 0, 14 => 0xfc00f000fc00f000fc00cc00fc00cc00fc000000fc000000fc000000cc000000fafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafaaaaa00000000fafa0000fafa0000faf0faf0faf0faf0faf0f0f0faf0f0f0faf0f0f0f0f0f0f0
  | 0, 15 => 0xfefefefe00000000fe00fe00fe00fe00fe000000fe000000fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcccccccccfcfcfcfc00000000fcfcf0f0fcfcf0f0fcfc0000fcfc0000fcf0f0f0fcf0f0f0fcf0f0f0f0f0f0f0fcccfcccfcccfcccfcccccccfcccccccfcccccccccccccccfc00fc00fc00fc00fc00fc00cc00cc00
  | 1, 0 => 0xff005500ff005500ff000000ffffffffff000000ffff0000ff000000fff0f0f0ff000000ff333333ff000000ff00f000ff000000ff003300ff000000ff000000ff000000fc000000ff000000f0000000ff000000ee000000ff000000cc000000ff000000aa000000ff0000000f000000ff00000000000000fefefefefefefefe
  | 1, 1 => 0xff00ff0000000000ff00fa00ff00fa00ff00f000ff00f000ff00ee00ff00ee00ff00cc00ff00cc00ff00cc00ff000000ff00cc00cc00cc00ff00c000ff00c000ff00c000ff000000ff00aa00ff00aa00ff00aa00ff00a000ff00aa00ff000000ff00a000ff00a000ff00a000ff000000ff008800ff008800ff008800ff000000
  | 1, 2 => 0xff00ffccff00ffccff00ffaaff00ffaaff00ff33ff00ff33ff00ff0fff00ff0fff00ff00ffffffffff00ff00fff0fff0ff00ff00ff33ff33ff00ff00ff00ff00ff00ff00ff00aa00ff00ff00ff000000ff00ff00fc00fc00ff00ff00f000f000ff00ff00cc00cc00ff00ff00cc000000ff00ff00aa00aa00ff00ff000f000f00
  | 1, 3 => 0xff800000ff800000ff55ff55ff55ff55ff555555ff555555ff333333ff333333ff330000ff330000ff222222ff222222ff220000ff220000ff0fff0fff0fff0fff0fff0f00000000ff0f0f0fff0f0f0fff0f0f0f00000000ff0f0000ff0f0000ff030303ff030303ff030000ff030000ff00ffffff00ffffff00fff0ff00fff0
  | 1, 4 => 0xffaaaaaacc000000ffaaaaaaaaaaaaaaffaaaaaa00000000ffaa0000ffaa0000ffaa0000ffa00000ffaa0000ff000000ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00ffa0a0a0ffa0a0a0ffa0a0a0ff000000ffa00000ffa00000ff88ff88ff00ff00ff888888ff888888ff888888ff000000ff80ff80ff80ff80ff808080ff808080
  | 1, 5 => 0xffccccccccccccccffcccccc00000000ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0ffc0ff00ff00ffc0ff00ffc0ff00ffc0c0c0ffc0c0c0ffc0c0c0ff000000ffc00000ffc00000ffaaffaaffaaffaaffaaffaaffa0ffa0ffaaffaaff00ff00ffaaffaa00000000ffaaaaaaffaaaaaaffaaaaaaffa0a0a0ffaaaaaaff000000
  | 1, 6 => 0xfff0f0f0fff0f0f0fff0f0f0ff000000fff0f0f0f0f0f0f0fff0f0f000000000fff00000fff00000fff00000ff000000ffeeffeeffeeffeeffeeeeeeffeeeeeeffeeeeee00000000ffe0e0e0ffe0e0e0ffe00000ffe00000ffccffccffccffccffccffcc00000000ffccff00ffccff00ffccccccffccccccffccccccff000000
  | 1, 7 => 0xffff0055ffff0055ffff0000ffffffffffff0000ffff00ffffff0000ffff0000ffff0000fff00000ffff0000ffcc0000ffff0000ff000000ffff0000eeee0000ffff0000cccc0000ffff000000000000fffcfcfcfffcfcfcfffc0000fffc0000fffafafafffafafafffafafa00000000fff0fff0fff0fff0fff0fff0ff00ff00
  | 1, 8 => 0xffffaaaaffffa0a0ffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00ffffaa00ffff0000ffffa0a0ffffa0a0ffffa0a0ffff0000ffff8888ffff8888ffff5555ffff5555ffff3333ffff3333ffff2222ffff2222ffff0f0fffff0f0fffff0303ffff0303ffff00ffffff00ffffff00ffffff0000
  | 1, 9 => 0xfffffcfcfffffcfcfffffafafffffafafffffafa00000000fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff0f000000000fffff000fffff000ffffeeee00000000ffffe0e0ffffe0e0ffffccccffffccccffffccccffff0000ffffccccccccccccffffcccc00000000ffffc0c0ffffc0c0ffffaaaaffffaaaa
  | 1, 10 => 0xffffffff05050505ffffffff00ffffffffffffff00f0f0f0ffffffff00555555ffffffff00550055ffffffff0000ffffffffffff0000f0f0ffffffff00005555ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffffaa00000000ffffff00ffffff00ffffff00ffff0000ffffff0000000000
  | 1, 11 => 0xffffffffc0c0c0c0ffffffffc0c00000ffffffffc0000000ffffffffaaaaaaaaffffffffaaaa0000ffffffffaa000000ffffffffa0a0a0a0ffffffffa0a00000ffffffffa0000000ffffffff88888888ffffffff88000000ffffffff80808080ffffffff55555555ffffffff44444444ffffffff33333333ffffffff0f0f0f0f
  | 1, 12 => 0xffffffffffccccccffffffffffaaaaaaffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0fffffffff0f00000fffffffff000f000fffffffff0000000ffffffffeeeeeeeeffffffffe0e0e0e0ffffffffccccccccffffffffcccc0000ffffffffccc0c0c0ffffffffcc000000
  | 1, 13 => 0xffffffffffffffffffffffffffffff00ffffffffffffaaaaffffffffffff0000fffffffffff0fff0fffffffffff0f0f0ffffffffffccffcc
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x104752f8e9ed25f1d35ecbe3
  | 3, 0, 0 => 0xe0c21a4b84823a936744a6b497c834e0549a4be4d3b0912744a7b493674482349366d4a6bd936744d3d45a4bd4a6b4912744d3d49ecbe4d3c21ecb84d3d7dec744823497c6a4d3c21d4bd4bbca1d4be4
  | 3, 0, 1 => 0x84339366d4e1d41a4be4e1c21d4be4a7421d49b4
  | 4, 0, 0 => 0xd3d7da4833a2e9e10d25a1d174f0a6926ce8b086fb4936745e2421a49b3a2d3610d25f26d773086926cdabc08434936745d3ce5a49b3a2eae10d24d9d174f0869214e8b8c9434920745d3b49489b3a2e9e10c64d9d174f08692ad1cb678434936745
  | 4, 0, 1 => 0xd3d41d49b3a2eb210d24d9d174f0879348e8b087434936745d3c51a49b3a2e9e109b3a0d16f923692f8d4bc3843497c6a5d3c21a49b18ae9e26d2579d174f08692bce8ba7aeb4914745d3d15a49b3a2ea610d24d9d174f186926ce8ba7843493e745
  | 4, 0, 2 => 0xd3c21a4b63a2e9e10e04d9d174f0869218e8ba7a8b49366d5d3ccda49b3a2e9e10d2461d174f08692a536ba784349366d5d3d41a4bc3a2e9ea4d25f20d783086926ce8ba7843a978745d3c21ecb24dae9e96d24d9d174f5969224e8ba784375a49b5
  | 4, 0, 3 => 0xe0421ec9b3a2e9e64d24d9d174f4a692f0e8ba7abb49569b5d3d1da4af3a2f02a4d24d9d1610e8692f936ba7b2b4936745dfc21a4ab4dae9e7ed24d9d174f086c26ce8ba7a53a936745d3c21a474212e9e10d25426d74f106926ce8b086926ce83f5
  | 4, 0, 4 => 0xd3d41a49b3a2e9e10f54d9d174f156926cdaba7843a936745e0c21a4893a2efeaed24d9d174f0862a6ce8b978434936745d3c21cc9b3a2efa10d24d9d174f1869240e8bbd8434936745e4c11a49b3a2e9e98d2451d169ad24da0ce8b358434936745
  | 4, 0, 5 => 0xd1c21a49b3a2ed210d24d9d16a74a6926ce8b6fa6b4936745e0421a4b24dae9ec2d2449d16f9236926cdabc384349366d5c6421a49b3a2e9e10d25e1d174eed692f8e8ba7ac34936745b5d4da49b3a2e9e10d2501d174f08692ad36b086926ce83b5
  | 4, 0, 6 => 0xd3c21a4993a2e9ec2f64d9d174ed260224e8bc08234936745d3c21d4be4daee210d24d9d174efd6926ce8ba7843497a6d5d3c21a4923a2e9e109b3a11577f086926ce8ba7843495c745d7c21a49b3a2e9e24d24d9d1773136926ce8bb98434936745
  | 4, 0, 7 => 0xe1c21d49b3a2e9decc04d9d16e5086926ce8ba78434936325d3c21a49b39ae9e10f65f1d174ed24d9d07aba784348e8435d3c21a49b372e9e10d24d9ad74f056926ce8ba78434916745d3c219e9b3a2e9dd8d24d9d174f50692f936ba78bb4936745
  | 4, 0, 8 => 0xd3c21a49d3a2e9ddad24d9d174f6f6126ce8ba78434914745d3c21a49b38aef210d24d9b574f3a6926ce8ba76926ce84f5d3d45a49b3a2f0ea0d24d9d174f0869260e8bb9a3b49367459bc21a49b3a2c21b8d24d9d174f086926ce8b7c91ba936745
  | 4, 0, 9 => 0xa8535a49b3a2e9e10d24d9d5779087526ce8ba784349549b5d3c21a4ac3a2e9e04d24d9d163f086926cdaba78434912745d3c05a4893a2e9e08d25f1d16f9286726cdaba7a3b4936745cec21a49b3a2f0ef928752f974f0c6926ce8ba78434956835
  | 4, 0, 10 => 0xdac21a49b3a2e9e84d24d9d1610d24d9d0a2bb28434936745d3c21a4bd3a2e9eb2d255a6d74f08692e136ba7843d936745d3c05ec9b3a2e9e10d24d9d978108692f8e8ba7843495a74584405a49b36ae9e10d258a6d793086726ce8ba7843495e6a5
  | 4, 0, 11 => 0xa6c21a49b3a2eb610d24d9d174f5269224e8b4e84349366a5d3c21a4b24dac21d4e84d9d1611017526ce8ba785b4936745823493674352e9e8cd24d9d163f087526ce8ba77b3b536745d3c25a49b3a2efeb2d24d9d1610d26626cdab086926cf6745
  | 4, 0, 12 => 0xdbc21a49b3a2e9e80d24d9d174f666926ce8ba7a93d936745843fda49b3a2e9eb2d24d9d177308692bce8ba7be4a1d4bd5d3c11a49b3a2e9e10d24f1d174f086ca6ce8ba7843a9366d5d3c1da49b3a2e9e10d25c22574f087b224e8ba76926ce8475
  | 4, 0, 13 => 0x1087533136745
  | 5, 0, 0 => 0xd3e3e50d24d9d1b4f596926d00746d3ce210d24d9d1b79086926ce86a6d3df250d2461d1b4f7c8434914746d3c21a49b3a139b4f7c94349529b6d3cae10d24d9d1b4f08692dd36746d3c21a49b3a199b4f7b9434936746d3dda50d2481d1b4f7c94349366d6d3df23ad24d9d1b4f086928536746
  | 5, 0, 1 => 0xbe4a1a49b3a0fdb95a78434936746d3df290d24d9d1b4f7c943496c746d3df1dad24d9d1b4f086926ce8116d3df250d2431d1b4fa58434936746d3c21a4b24da0db4f0883349367460070210d24d9d174f086926ce8696d3df2b8d255a6db4f9b8434936746d3c21a49b3a029b4f086926d2c746
  | 5, 0, 2 => 0xdcdf292d24d9d1b8fa78434936746dfdf250d255a6db4f6d8434936746d3c21a49b3e9d1b4f086926ce8256be4a1c8d24d9d1b4f086930136746d3df250d23a109b4f168434936746e4e9e10d24d9d1801086926c960c5d3c21a49b479d1b4f7c93b4936746d3c21a49b471d1b4ef176b4936746
  | 5, 0, 3 => 0xd3c21a49b4b9d1801a7a2b4936745d3cf610d24d9d1b4f086930536746d3dc6bad24d9d1b4f086ab4936746d3c21a49b3a101b4f086926ce8026d3c21a49b4a1d1b4f548434936746be4a1d0d25f26db517c9434936746d3c21ecd24d9d1b4f7c8cb4936746ab54e10d24d9d1801a78c34936745
  | 5, 0, 4 => 0xd3dae3ed24d9d1b4f4d8434936746d3c21a49b3a151b4f7c94b4936746d3d5a10d24d9d1b4f136926ce85c6d3c21a49b3a171801a7843495e745d3d268ad24d9d1b4f268434936746d3e1a10d24d9d1b4f89943495e746dfdf2b8d24d9d1b4f7c9432936746d3ca210d25926db4f7ca3b4936746
  | 5, 0, 5 => 0xd3df250e64d9d1b7d7c9434936746d3df1a49b3a0f9801087434936745d3c21e6d24d9d1801a78a34936745de69e10d24d9d1b4f3b9434936746d3e3a50ea4d9d1b4f7c8434912746bbca1a49b3a1a9b4f08692f936746d3c61a49b401d1a9b288434936746d3d4210d24d9d1b4f898434936746
  | 5, 0, 6 => 0xd3c21a49b3a1a1b4f086bb4936746d3c21d6d24d9d1b81086926d06746d3ca208d24d9d1b4f086926d22746d3e7210d2481d1b4f086926ce8126d3c3a10d24d9d1b2f7c9434936746d3e0250d24d9d1b4f086926ce8706d3c21f4d24d9d1b4f638434936746d3d7a10d24d9d1b4f7d9434936746
  | 5, 0, 7 => 0xd3df210d2481d1801a78426c962b5d3c21a49b3a185801084d9d0560c5d3df23cd24d9d1b4f086926ce81060069e10d24d9b57398c9434936746d3ca1a4c8481d1b4f087134936746d3d6650d24d9d1b4f7c943a9367468fc21a49b3a1a9b1d8c9434936746d3dae10d24d9d1b4f8e9434978746
  | 5, 0, 8 => 0xd3c51a49b3a1a9b4f086db493674684405a49b3a1a9b99a7a934936746d3c21a4bc4d9d1b4f086a34936746d3df250d25e1d1b4f938434936746d3c21a4c94d9d1b4f7ca4b4936746d3c21a49b3a0b5b4f7c9734936746d3df254d24d9d1b4f7c843d936746e670e10d24d9d1b4f7c94349569b6
  | 5, 0, 9 => 0xd3c21a49b499d1b4f086926ce84c6d3df24ad24d9d1b4f5d9434936746d3e5650d2481d1b4fa18434936746d3df2b8d24d9d1b4f086926ce8136e04a210d24d9d1b4f779434936746d3c21a49b3a17db4f778234936746e1df250d24d9b5b4f086926ce8086e069e10d24d9d1b197c9434936746
  | 5, 0, 10 => 0xd3c21a48e401d1b7f7c9434936746d3ca230d24d9d1b4f7caab49366d6d3df250d2571d1b4f086926ce8296d3d1da49b3a171b4f789434936746d3df238d24d9d1b5f7c9434936746dcdf250d24d9d1b4f086926ce8236d1df250d24d9d1b4f7c8eb4920746da5f250d24d9d1b4f287bb4936746
  | 5, 0, 11 => 0xd3c21a49b3a09db4f086926ce8306d3c21d6d25f26db5da78434936746d3c21cad24d9d1b4f818434936746d3c21a49b3f9d1b4f1f8434936746d3df2509b3a115b4f086926ce8646e769e10d24d9d1b4fa68434936746d569e10d24d9d1b937c91b4936746e4f0e10d24d9d1b4f0871b4936746
  | 5, 0, 12 => 0x421a49b3a03174f79ab34936746d3c21a4b54d9d1ba9a78434936746d3c21a4a74d9d1b4f238434936746d3d1650d24d9d1b4f086926ce81f6d3df2b8d2451d1b4f7c943a97c9b6dc5f250d24d9d1b4f086926ce85b6d3dc698d24d9d1b4f7c943497a6d6d3c21a49b3a121b4f7c9434924746
  | 5, 0, 13 => 0x94421d0d24d9d1b4f288a34936746d3c21d0d24d9d1b4f7c6926ce8496d3df250cf4d9d1b4f088434936746d3e1250d24d9d1b4f08692ed36746d3c21a49b3a061a10d26626ce86a6d3c2202d24d9d1b4f7c9434932746e6e9e10d24d9d1b19286926d1c7460069e10d24d92d74f28843495e746
  | 5, 0, 14 => 0xd3e3a50d24d9d1b4f7c7f34936746d3c21a49b3e1d1b4f7a94349367460069e10ea4d9d174f086926ce8656d3e4610d24d9d1b4f086934536746d3c21a49b3a06db4f086926ce8526d3c21a49b3a0d9b4f286929536746d3c21a49b3a169b4f349434936746d3c21a49b3a059b4f086926d04746
  | 5, 0, 15 => 0xd3c21bcd24d9d1b87a782349367460069e10d255a6d74f2886b4936746d3df1e2d25f1d1801a7a834936745d3df250d23a10db4f086928d36746d3d85a49b419d1b4f087a34936746eae9e10d24d9d1b4f7c94349366e6d3c21a4b94d9d1b4f7c94349366b6d3c21a49b3a0b9b4f698434936746
  | 5, 1, 0 => 0xa9d3250d24d9d1b4f086926ce80e6d3c21a49b3f1d1b67a784349367460063210d24d9d17877c943a936746e4e9e10eb4d9d1b4f08692c9367460069e10d25e1d174f7c9434936326d3c21a49b3a0bdb4f086926ce8046d3ca210d24d9b5b4f086926ce8566d3e2692d24d9d1b4f7c9434936736
  | 5, 1, 1 => 0xd3e4250d2481d1b4f086926ce8226d3e8a10d24d9d1b4f0876b4936746d3c21a49b3a051801a78434896385be4de50d24d9d1b4f086930d36746d3e6210d24d9d180108691d0700c50069da49b25889400d24d9d0440c5d3c21a49b4d9d1b4f9e8434936746d3c21a4cd4d9d1b4f7c9434936746
  | 5, 1, 2 => 0xd3c21a4c24d9d1b77a78434936746006fe10d24d9d174f969434936746d3e0a50d24d9d1b4f4c9434936746d3e8210d24d9d1b4ed26026d06746d3c21d49b3a1a9801b98434936745e969e10d24d9d1b4f086933136746de5f250d24d9b5b4f889434936746d3c21a4be419d1b4f08692ad36806
  | 5, 1, 3 => 0xd3c9210d24d9d1b4f086926ce8096d3c21a49b451d1b4f6a9434936746d3df250d2451d1b4f8b8434936746d3df288d24d9d1b4f8a9434936746d3d41a49b3a1a9b4f7cad34936746d3c21a49b4a9d1801a78426ce82b5d3c21a49b3a005b4f08692e936746d3c21a4c44d9d1b4f086926ce8216
  | 5, 1, 4 => 0xd3d72aed24d9d1b4f9f8434936746dfc21a49b401d1b4f086926ce8596d3c6da49b471d1b4ef778b4936746d3c21a49b3a0e1b4f7c943493a746d3cf210d24d9d1b4f6fb0b4936746d3c21a49b3a0ddb4f086926ce8356d3c21a4bc3a1a9b4f7c97b4936746d3d1e10d24d9d1b93bc8434936746
  | 5, 1, 5 => 0xd3df234d24d9d1b4f858434936746d3da210d24d9d1b4f087db4936746d3e1e10d24d9d1b4f086b34936746e869e10d24d9d1b4f8e8a34936746d3df25ad24d9d1b4f758434936746d3dd250d24d9d1b4f7c8c34936746d3c21a49b3a031b4f4e8434936746d3c21a49b3a035b4f088034936746
  | 5, 1, 6 => 0xd3dbda4c04d9d1b4f087e3497c746d3d4a10d24d9d1b4f086926ce82a6d3c21a49b3c1d1b3b7c94349367460069e10741c0ad74f28843a936746d3c21a49b3a015801a74d9d056225d3c21a4c74d9d1b4f7ca2b4936746d3df240d24d9d1b4f086926ce80f6d3e3610d24d9d1b4f086932d36746
  | 5, 1, 7 => 0xd3ca210d25e1d1ba7a78b34936746d3c21a49b3a001b4f086926ce83c6be4a23ed24d9b5b4f086926ce8176d3c21a49b3a01db4f0869b49367460069e10d24d9d174f086926d12746d3d7e10d24d9d1b4f7c9434912746d3c21a49b3a135b4f2884349569b6d3df228d24d9d1b4f509434936746
  | 5, 1, 8 => 0xd3dfe50d24d9d1b4f7c88b4936746d3dba10d24d9d1b63a78434936746d3e5610d24d9d1b937c9433936746d3df250d2579a9b4f1d6932136746d3df250d24d9d5b8ba78434936746d3df1dcd24d9d1b19288434936746de5f250ea4d9d1b4f086926ce8466d3df250d25526db4f8c8434936746
  | 5, 1, 9 => 0xd3c21d4d24d9d1b4f7cadb4936746d3df250f64d9d1b6da78434936746d3df250d24d9d9b7f288434936746dfe9e10d24d9d1801a78434914745d3c21a49b3a189b4f7c943495a746dcca210d24d9d1b73a78434936746d3dc610d24d9d1b4f086926d00746d3e46b8d24d9d1b931f8434936746
  | 5, 1, 10 => 0xd3d4a10d25f26db85a78434936746d3c21a49b3a0e9b4f086926ce85d6d3c21a49b3a0b1b4f086926ce8036d3c21a49b3a1b5801a784348e8385e4c2202d24d9d1b4f086926ce8576d3e563ad24d9d1b4f7c9834936746d3c21a49b3a1a9801a76926ce8225d3df258d24d9d1801a776b4936745
  | 5, 1, 11 => 0xd3df246d25f1d1b87a7843497c746d3c21a49b409d1b4f0881b4936746d3c21a49b3a0cdb4f086926d06746d3c05a49b419d1af9286926ce8516d3c21a4bf4d9d1b4f086926ce8536e7e9e10d24d9d1b4f086926ce8246d3c21a4a24d9d1b4f628434936746d95f250d24d9d1b4f7c943497a746
  | 5, 1, 12 => 0xd3c21a49b3a065aa7288434936746d3c21a49b3a0e5b4f086926ce8156be4a1a4cc4d9b5b4f819434936746d3e3aa8d24d9d1801a7a3b4936745e4e9e10d24d9b5b4f086926ce8416d3c21a49c4d9d1b4f7c9134936746d3c21a49b3a0a1b4f08692bce85c6d3c21a49b3a161af9286926cf6746
  | 5, 1, 13 => 0xe4c21a4cc4d9d1b4f1b8434936746d3ca210d24d9d1b4f088234936746d3c8610d24d9d1b4fa78434936746d3c21a49b3a075b4f086926ce8446d3c21a49b3a0adb4f9a84349367460069da4741c08974f0870b49367460069e10d2449d174f086933936746d3c21a49b3b9d1af9288fba936746
  | 5, 1, 14 => 0xd3d0e10d24d9d1b4f08692cd36746d3df24cd24d9d1b4f998434936746d3df21ed24d9d1b4f086926ce84b6d3df250d25926daf928753a136746d3c21a4be4d9a9b4f608434936746d3c21a49b469d1b4f598434936746e5e9e10d24d9d1b4f6f843f136746d3c21a49b35171a10eb7434936746
  | 5, 1, 15 => 0xd3c21a49b3a1bdb4f087e34936746d3c21b4d24d9d1b4f7c7834936746d3c21a4be471d1801a7843d936745d3dbe10d24d9d1b4f6f80b4936746e8e9e10d24d9d1b4f7791b4936746d3d31a49b421d1b4f08692c136746d3cda10d24d9d1af94d9434936746d3c21a49b3a099b4f7c77b4936746
  | 5, 2, 0 => 0xbe4a1d4cc4d9d1b4f086926ce84a6d3c21a4d24d9d1b87086926ce86a6d3e5210d24d9d1b4f087c34936746d3c21f2d24d9d1af9287fb4936746d3c21eed24d9d1b737c943495e746d3c21a4ab4d9d1b4f7c6926ce8506d3df250d24f1d1b4f908eb4936746d3df250d94d9d1b4f7c943a9366d6
  | 5, 2, 1 => 0xeb69e10d24d9d1b897c9434936746d3df282d24d9d1b61a78434936746d3d49a49b419d1b4f6c8434936746dcdf250d24d9b5b4f086920d00746dd69e10d24d9d1b4efc76b4936746e05f250d24d9d1b4f086926ce8066d3c21a49b3a179b4f086926ce86c6d3df250d255a39b4f086926ce81a6
  | 5, 2, 2 => 0xd3c21a4af4d9d1b4f7c943495e746d3dbe10d2449d1b4f086926d0e746e1e9e10d24d9d1b4f0869341367460053610d24d9d17537c94349367460069e10d25926d6a54d8434936746d3c21a49b3d1d1b4fa48434936746d3c21a4a64d9d1b4f087b26d06746e369e10d24d9d1b4f086926ce8556
  | 5, 2, 3 => 0x34f0874b4936746d3c21a49b3a1d1b4f6fa934936746d3df250ea5e1d1b4f618434936746e669e10d24d9d1801a7acb4936745dcc21a49b3a171801a78234936745be4a1d0d24d9d1b4f086926cf2746e1df250d25f1a9b4f738434936746
  | 6, 0, 0 => 0x69e10d24da38e8c00d3df210d23a0e1b4f7c8434936743538034f7c6926ce8226d3df250d25e26ce8fa7be4a1a8d24d9d1f4f93be4a1a49b3a3e9ef9286932536747d3df250d24d9d05afd3d3df24cd24d9d1c01a7be4a1364b15b69ef9286926ce8617005f2509b3a0ac18da7be4a1a49b3a041c01a7be4a1a49b36b0034f7c8eb4936746
  | 6, 0, 1 => 0xd569ef9286926ce8fc9e1df250d24d9d1f4f7c9438da49b3a3e9ef92869239007470069e10d260a6ce8da7be421a49b3a161f4f7c94349367414be9ef9086926d06747d3df250d24da4ce8fa7be4a1a49b3a131f4fa1be4a1a49b3a38034f086930136746d3df250d24d9d026fa7be4a1a49b3a17dc01c9d3c21a49b3a369ef9286926ce8087
  | 6, 0, 2 => 0xd3df250d24d9d0b6fa7be4a1a49b3a121c01a7ab421a49b3a30034f086926ce85c6d3df250d24d9d04efa7be4a1a49b3a0c1f4f9c94421a49b3a3e9ef92875b497c9b7d3e2650d24d9d0b8fa7be4a1cad24d9d1f4f81be4a1a49b3a3e9ef9286926cfe747d3df2511f6926ce8fa7d35f250d24d9d1ef976943493674353e9f257c9434936747
  | 6, 0, 3 => 0xbe4a1a4cc4d9d0d4fa7be4a202d24d9d1f4f7cb234936843a3e9ef9086926ce82b7e6e9ef9286926ce8e00d3df250d24d92db4f6494421a49b3a3802f9286926ce80c6ea69ef9286926ce8e00de69e10d24d9d1b4f7c943494e9b3a3e9ef92891b4936747e1e9e51086926ce8fa7be4a1a49b3a07dc01a7be34936741030034f08692f936746
  | 6, 0, 4 => 0xd3df210d24d9d096fa7be4a1a49b3e1d1c01a7be4a1d49b3a369ef9286926ce8657d3e46f9286926ce8fa7be4a1a4d14d9d1f4f9cbb4a1a49b3a3e9ef9286926ce8527d3df250d24d9d06cfa7c85f210d24d9d1c01a7843ada49b3a369ef9286926ce85a7d3df250e86926ce8fa7be4a210d24d9d1f4f7c9434936883a3e9ef928692ed36747
  | 6, 0, 5 => 0x69ef9496926ce8c00d3df1a49b3a079b4f7c94349367417be9ef9286926ce8047d3df2511d6926ce8fa7be4a1a49b3a159f4f7cb7c21a49b3a38034f7c94349569b60069e10d24d9d0c2da7be4a1a4a34d9d1f4f7c943d1a49b3a3f574f7c9434936747d3d8651086926ce8fccd3ca210d24d9d1f4f7c94349729b3a3e9ef9699434936747
  | 6, 0, 6 => 0xd3e62f9286926ce8fa7be421a49b3a19dc017c94348e8380630034f7794349367460069e10d24d9d0beda7be4a1a49b4d9d1f4f9ebe4a1a49b3a3e9ef9286933536747d3df250d24d9d01cfa7be4a1a49b3f1d1f67a7be4a1a49b3a3803197c9434936746e4e9ef92875a6ce8e00d3df1a4741c081b4f7c843f1a49b3a38034f7c9434978746
  | 6, 0, 7 => 0xd3df250d26626ce8fc9d3ca210d24d9d1f4f7c94349569b403e9e51086926d1c7470069e50f76926ce8c00d3c21a49b499d1b4f7c9434936741138034f5d9434936746d3e8af9286926ce8fa7be4a1a49b3a051fa7a7be421a49b3a38034f7cae349367460069ef9286912c70c00d3cc5a49b3a04d801a784349367409b69ef9286930d36747
  | 6, 0, 8 => 0xd3df250d24da28e8fa794421a49b421d1f4f8bbe4a1a49b3a3e9ef95c6926d00747d3df250d24da54e8e00d3df2509b3a0adb4f7c94349367400b8034f1f8434936746d3df250d25d26ce8fbbd3df250d24d9d1c01bfbe4a1a49b3a369f417c9434936747d3df250ea4d9d0d4fa794421a4c04d9d1c01b9be4a1a49b3a374b4f7c9434936747
  | 6, 0, 9 => 0xdfdf250d24da00e8e00d3c2202d24d9d1b4f28843497c9b3a3e9ef9286926ce8387d3df2acd24da10e8e00e6e9e10d24d9d180000d3c21a49b25ae9e51086926ce85c70000210d24d9d018ba7be4a1a49b3a0ddf4f7c943497874353e9eed286926d1c747d3df1a4c14da10e8fc9de5f250d24d9d1f4f7c94491a49b3a3e9e51086930536747
  | 6, 0, 10 => 0xd3e16f9286926ce8fa7be4a1f6d24d9d1f4f87be4a1a49b3a3e9f397c84349367470069f1d286926ce8da7be4a1acd24d9d1fa1a7be4a1a49b3a3e9ef9799434936747e1e9ef9236926ce8fa7ce4a1a4c84d9d1f4f7c943493674063e9ef9286926ce80d7d3df251006926ce8fbcd3ca210d24d9d1c01a784421a49b3a369f3f7c9434936747
  | 6, 0, 11 => 0xd3df2f9086926ce8fa7be4a1f8d25f1d1f4f7ca94a1a49b3a3e9ef9286926ce82a7d3df2c9086926ce8fa7be4a1a49b3c1d1f4f7c9434936740e38034f7c941d0702b6d3df250d26426ce8fa7be4a1a49b3a015f4f7c9f4a1a49b3a3e9ef9286931d36747d3df250d24d9d01efa7c6df250d24d9d1f4f7c94349969b3a3e9e510875b4936747
  | 6, 0, 12 => 0x69e50d24d92c26c0094349367409831b4f8cbe4a1a49b3a38034f086926ce8226d3df293286926ce8e00d3e8a10d24d9d1b4f7c9434936740f3e9f397c8eb4936747d3df250d24d9d000e00d3b4936741004db4f7c9434936740bbe9ef9286926ce8077d3df250d36926ce8e00d3df250d24d9d1b4f7c94349367426be9f39959434936747
  | 6, 0, 13 => 0xd3df250d24d9d0c6fa7be5c650d24d9d1f4f7c9434936803a3f26f9288fb4936747d3ca210d24da4ce8fa7c74a1a49b3a1a9c01a7a64a1a49b3a36c74f7c9434936747d3e56f91b6926ce8fa7cadf250d24d9d1f218cbe4a1a49b3a3e9e51086926ce8137d3df2e1286926ce8e00d3c21a4cc4d9d1b4f288434936742fbf174f7c9434936747
  | 6, 0, 14 => 0xd3df250d24d9d006e00d3c21a49b3a0e1b4f7c94349367436b8034f7c94348e8386d3df250d24d9d0aefa7be4a1a49b3a1a9f4f7c94349367405be9ef9287534936747db69ef9286926ce8fa79447e10d24d9d1f7fa7be4a1a49b3a38034f7c9434914746d3df250e76926ce8fd3d3e4250d24d9d1c0000d3c21367415aee74f7c9434936747
  | 6, 0, 15 => 0xd3df250d24d9d066fa7be4a1a49b419d1f4f2884421a49b3a3e9ef9286926ce8537d3ca211016926ce8fa7be5c650d2451d1f4f7c9434936741238034f2884349364b6d3df2c5286926ce8e0094421a49b3a031b4f287e3dda49b3a38034f086926ce80c6e169ef9286926ce8fa7be4a1a49b3a0e9f4f7c9434936742ebe9ef9286926ce82c7
  | 6, 1, 0 => 0xd3df250d26726ce8fa7be4a1a49b3b9d1f4f7c9434936740cb8034f284d9d056136d3df250d24d9d072e00d3d4a10d24d9d1b4f7cab421a49b3a3f274f7c94349366d7d3df250d24d9d082fa7be4a1a49b4d1d1f4f7c94349389b3a3e9ef928692bce85c7d3df250d24d9d0b0fc3d3df250d25f1d1f4f7c84349829b3a3e9ef9286926d02747
  | 6, 1, 1 => 0xe5e9ef9286926ce8e00d3e5610d24d9d1b4f7c94349366a2e3df250eb7434936747e4df250d26626ce8fa7be4a236d24d9d1f4f7c944a1a49b3a3e9ef92890b4936747d3e9ef9286926ce8fa7be4a1a49b3a111f4f7c94349367415be9f357c9434936747d3e0ef9286926ce8fa7bb4a210d24d9d1c0000d3c21a49b3a2e9f39909434936747
  | 6, 1, 2 => 0xd3e0650d24d9d040fa7be4a1a49b3a099f91a7be4a1a49b3a3e9ef9086926ce8617d3df250d259a6ce8fa794421a4cc4d9d1f4f99be4a1a49b3a38034f7184349367460069e10d24da00e8da7bf5f250d24d9d1f4f7c94349367425be9ef928692f9366a7d3ca210d24d9d044fa7c85f250d24d9d1f4f7c94349368d3a3e9f45288434936747
  | 6, 1, 3 => 0x69e10d24da0ce8da7be4a1f0d24d9d1f4f7c943e5a49b3a3e9e51086926ce8387d3df250f76926ce8fa7be4a1a4ab4d9d1f4f7c84349367409b80001a784348e83850069e10d24d9d0d4da7be4a1f8d24d9d1c0000d3b493674112e9ef9286d34936747d3df250d25f238e8e00d3ca2109b3a0adb4f7cb7ca1a49b3a3e9ef9286926ce8607
  | 6, 1, 4 => 0xd3df250d25326ce8e00d3ca210d24d9d1bada7be4a1a49b3a38034f086926ce82b6d869ef9286926ce8fa7a94a210d24d9d1f9ba7be421a49b3a3e9ef9286926ce8067d3df250d24d9d0d8e00d3e0650d24d9d1801a78434936742c369ef9286926ce84a7d3df250d26926ce8fc3be4a1a49b3a1a9f4f28843493674063e9f297c9434936747
  | 6, 1, 5 => 0xd3df250d24d9d0e8fa7be53250d24d9d1f4f7cb0ca1a49b3a3f334f7c9434936747dcdf250d24d9d0b8e00d3c21f8d24d9d1b4f7c943493674393e9ef928692bd367470069edf086926ce8da794421a49b401d1f87a7be4a1a49b3a38034f7c93349367460069e10d24d9d096da7c75f250d24d9d1f4f7c94349367a3a3e9f497c9434936747
  | 6, 1, 6 => 0x70f4f086926ce8da7be4a1a49b3a101f4f7c9434936943a3e9f217c8b34936747d3df250d24d9d04afa7be4a1a4c04d9d1f93a7be4a1a49b3a3802f9286926c960c6d3df250d24da38e8fcad3df250d24d9d1f4fa5be4a1a49b3a3e9ef9286926ce8697de5f250d24d9d0d4fa7be4a1a4b74d9d1f4f7c94349429b3a3e9ef92874b4936747
  | 6, 1, 7 => 0xd3df250d76926ce8fa7be4a1d6d24d9d1c01a7b0c21a49b3a300399a78434936746d3df250d24da44e8fa7be4a1f4d24d9d1c017c943a1a49b3a36f34f7c9434936747d3df250d25f26ce8fa7be4a1a49b3a151f4f7c9434936742e38034f7c943495e746
  | 7, 0, 0 => 0x34f7c94349367460069ef92869321367470069ef9286926ce80c70069ef9286926ce8387000034f7c9426ce82b60069ef92869331367470069f457c94349367470069ef9288434936747007374f7c9434936747000034f7c94349364b600002f9286926ce80c6000034f7c6926ce82060069ef9288fb49367470069ef9286926d267470069ef9286926ce81370069ef9286926ce8617
  | 7, 0, 1 => 0x69ef9286926ce85c7007274f7c94349367470069ef9286926d1c7470070f4f7c9434936747000034f2884349367460069ef9287e349367470069ef9286926ce84b70069f217c94349367470069ef9286926ce82b70000001a784349367450069ef9286926ce8587000034f7c94348e83860069ef9286926ce86a70069ef97194349367470069ef9286926d007470069f2b7c9434936747
  | 7, 0, 2 => 0x69ef92875b4936747006f34f7c94349367470069ef928692f936747
  | 8, 0, 0 => 0x34f7c9434936746
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

def CG : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [7, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12663

theorem PEqualNP.Outside.L_meta_12663 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 3974160608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 3974160608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12663.mainG PEqualNP.Outside.L_meta_12663.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12663.CG, PEqualNP.Outside.L_meta_12663.CG_mono, by
      have : PEqualNP.Outside.L_meta_12663.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12663.CG_eval⟩
