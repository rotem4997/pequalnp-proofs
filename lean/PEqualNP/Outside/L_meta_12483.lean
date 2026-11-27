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
namespace PEqualNP.Outside.L_meta_12483

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

abbrev fG : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3937058816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
def rowsG : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 58, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 0, 16, 0, 18, 0, 20, 0, 22, 0, 24, 0, 26, 0, 28, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 0, 40, 0, 42, 0, 44, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 56, 0, 58, 0, 60, 0, 0, 0, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 14, 17, 14, 19, 14, 21, 14, 23, 14, 25, 14, 27, 14, 29, 30, 31, 14, 14, 14, 14, 14, 14, 14, 39, 14, 41, 14, 43, 14, 45, 46, 47, 14, 49, 14, 51, 14, 53, 54, 55, 14, 57, 14, 59, 14, 61, 62, 63, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 15, 15, 17, 15, 19, 15, 21, 15, 23, 15, 25, 15, 27, 15, 29, 30, 31, 15, 15, 15, 15, 15, 15, 15, 39, 15, 41, 15, 43, 15, 45, 46, 47, 15, 49, 15, 51, 15, 53, 54, 55, 15, 57, 15, 59, 15, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 14, 15, 17, 17, 17, 19, 17, 21, 17, 23, 17, 25, 17, 27, 17, 29, 30, 31, 17, 17, 17, 17, 17, 17, 17, 39, 17, 41, 17, 43, 17, 45, 46, 47, 17, 49, 17, 51, 17, 53, 54, 55, 17, 57, 17, 59, 17, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 14, 15, 19, 17, 19, 19, 19, 21, 19, 23, 19, 25, 19, 27, 19, 29, 30, 31, 19, 19, 19, 19, 19, 19, 19, 39, 19, 41, 19, 43, 19, 45, 46, 47, 19, 49, 19, 51, 19, 53, 54, 55, 19, 57, 19, 59, 19, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 14, 15, 21, 17, 21, 19, 21, 21, 21, 23, 21, 25, 21, 27, 21, 29, 30, 31, 21, 21, 21, 21, 21, 21, 21, 39, 21, 41, 21, 43, 21, 45, 46, 47, 21, 49, 21, 51, 21, 53, 54, 55, 21, 57, 21, 59, 21, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 14, 15, 23, 17, 23, 19, 23, 21, 23, 23, 23, 25, 23, 27, 23, 29, 30, 31, 23, 23, 23, 23, 23, 23, 23, 39, 23, 41, 23, 43, 23, 45, 46, 47, 23, 49, 23, 51, 23, 53, 54, 55, 23, 57, 23, 59, 23, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 14, 15, 25, 17, 25, 19, 25, 21, 25, 23, 25, 25, 25, 27, 25, 29, 30, 31, 25, 25, 25, 25, 25, 25, 25, 39, 25, 41, 25, 43, 25, 45, 46, 47, 25, 49, 25, 51, 25, 53, 54, 55, 25, 57, 25, 59, 25, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 14, 15, 27, 17, 27, 19, 27, 21, 27, 23, 27, 25, 27, 27, 27, 29, 30, 31, 27, 27, 27, 27, 27, 27, 27, 39, 27, 41, 27, 43, 27, 45, 46, 47, 27, 49, 27, 51, 27, 53, 54, 55, 27, 57, 27, 59, 27, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 14, 15, 29, 17, 29, 19, 29, 21, 29, 23, 29, 25, 29, 27, 29, 29, 30, 31, 29, 29, 29, 29, 29, 29, 29, 39, 29, 41, 29, 43, 29, 45, 46, 47, 29, 49, 29, 51, 29, 53, 54, 55, 29, 57, 29, 59, 29, 61, 62, 63, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 14, 15, 30, 17, 30, 19, 30, 21, 30, 23, 30, 25, 30, 27, 30, 29, 30, 31, 30, 30, 30, 30, 30, 30, 30, 39, 30, 41, 30, 43, 30, 45, 46, 47, 30, 49, 30, 51, 30, 53, 54, 55, 30, 57, 30, 59, 30, 61, 62, 63, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 14, 15, 31, 17, 31, 19, 31, 21, 31, 23, 31, 25, 31, 27, 31, 29, 30, 31, 31, 31, 31, 31, 31, 31, 31, 39, 31, 41, 31, 43, 31, 45, 46, 47, 31, 49, 31, 51, 31, 53, 54, 55, 31, 57, 31, 59, 31, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 14, 15, 39, 17, 39, 19, 39, 21, 39, 23, 39, 25, 39, 27, 39, 29, 30, 31, 39, 39, 39, 39, 39, 39, 39, 39, 39, 41, 39, 43, 39, 45, 46, 47, 39, 49, 39, 51, 39, 53, 54, 55, 39, 57, 39, 59, 39, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 14, 15, 41, 17, 41, 19, 41, 21, 41, 23, 41, 25, 41, 27, 41, 29, 30, 31, 41, 41, 41, 41, 41, 41, 41, 39, 41, 41, 41, 43, 41, 45, 46, 47, 41, 49, 41, 51, 41, 53, 54, 55, 41, 57, 41, 59, 41, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 14, 15, 43, 17, 43, 19, 43, 21, 43, 23, 43, 25, 43, 27, 43, 29, 30, 31, 43, 43, 43, 43, 43, 43, 43, 39, 43, 41, 43, 43, 43, 45, 46, 47, 43, 49, 43, 51, 43, 53, 54, 55, 43, 57, 43, 59, 43, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 14, 15, 45, 17, 45, 19, 45, 21, 45, 23, 45, 25, 45, 27, 45, 29, 30, 31, 45, 45, 45, 45, 45, 45, 45, 39, 45, 41, 45, 43, 45, 45, 46, 47, 45, 49, 45, 51, 45, 53, 54, 55, 45, 57, 45, 59, 45, 61, 62, 63, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 14, 15, 46, 17, 46, 19, 46, 21, 46, 23, 46, 25, 46, 27, 46, 29, 30, 31, 46, 46, 46, 46, 46, 46, 46, 39, 46, 41, 46, 43, 46, 45, 46, 47, 46, 49, 46, 51, 46, 53, 54, 55, 46, 57, 46, 59, 46, 61, 62, 63, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 14, 15, 47, 17, 47, 19, 47, 21, 47, 23, 47, 25, 47, 27, 47, 29, 30, 31, 47, 47, 47, 47, 47, 47, 47, 39, 47, 41, 47, 43, 47, 45, 46, 47, 47, 49, 47, 51, 47, 53, 54, 55, 47, 57, 47, 59, 47, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 14, 15, 49, 17, 49, 19, 49, 21, 49, 23, 49, 25, 49, 27, 49, 29, 30, 31, 49, 49, 49, 49, 49, 49, 49, 39, 49, 41, 49, 43, 49, 45, 46, 47, 49, 49, 49, 51, 49, 53, 54, 55, 49, 57, 49, 59, 49, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 14, 15, 51, 17, 51, 19, 51, 21, 51, 23, 51, 25, 51, 27, 51, 29, 30, 31, 51, 51, 51, 51, 51, 51, 51, 39, 51, 41, 51, 43, 51, 45, 46, 47, 51, 49, 51, 51, 51, 53, 54, 55, 51, 57, 51, 59, 51, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 53, 14, 15, 53, 17, 53, 19, 53, 21, 53, 23, 53, 25, 53, 27, 53, 29, 30, 31, 53, 53, 53, 53, 53, 53, 53, 39, 53, 41, 53, 43, 53, 45, 46, 47, 53, 49, 53, 51, 53, 53, 54, 55, 53, 57, 53, 59, 53, 61, 62, 63, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 54, 14, 15, 54, 17, 54, 19, 54, 21, 54, 23, 54, 25, 54, 27, 54, 29, 30, 31, 54, 54, 54, 54, 54, 54, 54, 39, 54, 41, 54, 43, 54, 45, 46, 47, 54, 49, 54, 51, 54, 53, 54, 55, 54, 57, 54, 59, 54, 61, 62, 63, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 14, 15, 55, 17, 55, 19, 55, 21, 55, 23, 55, 25, 55, 27, 55, 29, 30, 31, 55, 55, 55, 55, 55, 55, 55, 39, 55, 41, 55, 43, 55, 45, 46, 47, 55, 49, 55, 51, 55, 53, 54, 55, 55, 57, 55, 59, 55, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 14, 15, 57, 17, 57, 19, 57, 21, 57, 23, 57, 25, 57, 27, 57, 29, 30, 31, 57, 57, 57, 57, 57, 57, 57, 39, 57, 41, 57, 43, 57, 45, 46, 47, 57, 49, 57, 51, 57, 53, 54, 55, 57, 57, 57, 59, 57, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 59, 14, 15, 59, 17, 59, 19, 59, 21, 59, 23, 59, 25, 59, 27, 59, 29, 30, 31, 59, 59, 59, 59, 59, 59, 59, 39, 59, 41, 59, 43, 59, 45, 46, 47, 59, 49, 59, 51, 59, 53, 54, 55, 59, 57, 59, 59, 59, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 61, 14, 15, 61, 17, 61, 19, 61, 21, 61, 23, 61, 25, 61, 27, 61, 29, 30, 31, 61, 61, 61, 61, 61, 61, 61, 39, 61, 41, 61, 43, 61, 45, 46, 47, 61, 49, 61, 51, 61, 53, 54, 55, 61, 57, 61, 59, 61, 61, 62, 63, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 62, 14, 15, 62, 17, 62, 19, 62, 21, 62, 23, 62, 25, 62, 27, 62, 29, 30, 31, 62, 62, 62, 62, 62, 62, 62, 39, 62, 41, 62, 43, 62, 45, 46, 47, 62, 49, 62, 51, 62, 53, 54, 55, 62, 57, 62, 59, 62, 61, 62, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 14, 15, 63, 17, 63, 19, 63, 21, 63, 23, 63, 25, 63, 27, 63, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 39, 63, 41, 63, 43, 63, 45, 46, 47, 63, 49, 63, 51, 63, 53, 54, 55, 63, 57, 63, 59, 63, 61, 62, 63]

def cMC : Nat := 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001

def cSM : Nat := 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cRR : Nat := 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

def cMZx : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def cMOZ : Nat := 0x1515157f15553fff1515157f15553fff1515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff1515157f15553fff1515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff1515157f15553fff1515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001515157f15553fff1515157f15553fff1515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff1515157f15553fff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMOO : Nat := 0xeaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac0000000000000000000eaeaea80eaaac000eaeaea80eaaac00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def cMxO : Nat := 0xeaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000eaeaea80eaaac000

def cMZZ : Nat := 0x1515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff0000000000000000000000000000000000000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff0000000000000000000000000000000000000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff0000000000000000000000000000000000000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff00000000000000001515157f15553fff000000000000000000000000000000001515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff1515157f15553fff

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
  | 3 => 19
  | 4 => 201
  | 5 => 564
  | 6 => 378
  | 7 => 35
  | 8 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 2, 0 => 0xcb8e069f9a11f6ed195af4cd
  | 3, 0 => 0xf6370557dc69e56abba534bbb812b4ed9b9da650954ab8898dab2f4c8056775178ea524442b181423c34b07938ffc58132f505131fc44b5f1ae6a430124cbb4f0ca9e3790842ff6d05dfa31b
  | 4, 0 => 0x34d251293480b476346e142631ebb47931e9454a3170c46d315a1a33314c4f4b303d58832f3569d42ec8da582dff33912dab94932c2fa70f2b75dc002b738f022a5dc7802643f3bf25d650332591f615258473cf256b1b9224ac9249231ebd3621c9259e20a73b501fe2fe3e1fcf08861f79b3611da4cccf1bfe58761bf9b41d1bf235441aa051331a5143211300a63612d2803411f28a750ff2fcd40ec652360e1c24fc0c62e4060b8442400b80f3ce0b6f2a790b3fe8300b127ebb0b00350d0a20c4ab099c0abc0987871a090f031a088cd8110860d3e9079472d1076b527e05dc53fc04fd73ae0325372802a8e22e026edd2701c1b99300f400ec00057763
  | 4, 1 => 0x79918ab97802a62777f46ef97759615776fe87ee76cf547c768fd78d768d14b975433e3f7386ca4b73755a697343251672ed44f36f30a7976f11fe966be0f2e76adfb1f26a90b2536a83eb5c68713de06833ed5767c36acc679ce5286683000a659bcecc6563fd0364591a3764509c756386a8e762a98f26629f6ff761faaeaf61a558db60bc4fab5ff9d3715fee79275c7944285c511b955aa9cf8857d5a8cb579b931856f2016956ec70d852ad90ba5278de8150f092474f01b4184dca1ef14a2559e448f4b03e48d4c4a546c5f08d469b6ade451675b444ff64d744b9b4dc4462bad0443d30a543e950493f64d1863ed04d1f394bbad735a83ca0354b1dd0
  | 4, 2 => 0xeefbd082eca265bce386b1a3e2b98840e248322ce1687ba6e04f6858ded7cefadda88043dd950d2bdc953f20d946bcd8d845ae25d4aad4d4d200cce7cddf4c2ccd84a270cb15367bcac294a5c8bc2a4cc7af79b8c6f8fa04c4c336ebc3624dd4c2ae65cec2627dfac14ae839bfa906efbf81817bbee7448abe22cffdbe0eda45bd06778abc8df9fbbc4c6d30ba14caf5b76404d0b4fe5766b332be46b0e81b25afe8ab2cad88ad0eab0a7f3da9afeccca5865b8fa4d0833ba2329ee69e1ae1d69c1a6b6a99bdc2d096fbf21794a0c8e190c3d06d902dae6d8fc9f1bb8d2baf0c8b263fb08ae2378087857d4286504c7e81e226b4810ab76e7fbe7a2c79d74fb0
  | 4, 3 => 0xfed16998fbe64a01fab915e7f6d79dd3f69b9f34f65d0ee7f5982596f4e1bf17f4c7adb6
  | 5, 0 => 0x15128b0114c2f2dd149e00dc1443572012c8a20d125914bd121b55d71204ed2e120069b9118d3b33115b73dc1157d3c81122845d102b55540ef352ef0e51bd080d2e0f4a0c63f4ea0c06d6510b8442400b751ad50b2965d70b0baca10afc33ec0ab527b20a81afbe0a812b480a6918290a6476920a39e6530a20c4ab0a1cd9330a0da45809a65fdc0945ac5f093635db092132aa0857b37408099ce907fd1a1107f7d3b707747ffa071394310640362b05ff352205dc53fc05da24630538b19404e184ad04d5d68204cd8ef502df70be02a8e22e02a55e8e029ff064028c0ba502417dff01eef4fc01b382e2011cff4b00c652ec00b2dd0e008a5ca8005cf2e4
  | 5, 1 => 0x2a6cc7eb2a2134f829783cf0294af4612940b28429092b3a28355a1e282730562806611d279fe21c270e1d0826f6caf526d5a61b261b762f256b1b9225054c73250421ae24b5d03b246896d4246734f3243abbb323f270bb232e349a22d10e122284588021c9259e2171bb4d2159e223210562c420e12d9520bde49d20ba0c9f20115234200571881f4be6371f0d980a1ec7f3781e4fe2071e2d22571e1d74741dd4e6b51daaedab1d05368f1cd757e21c94b2f41bbb60151b6be44619af3fa6199b49ee1958863c1929455318e3aa3f18bf819718ba0a3e17b2fdd617a1a226178efdb3176647b91731008b166f12f316357ba716059d3115f076a31573d6af
  | 5, 2 => 0x4132e4c1403101b44010f9053f9de7653ecd841f3e22eeac3df3fab53d1bc3973c7ebd223c56da463b8662663b320f063aeaafde3a89137039d6b4c739a503e2398727b3388575503869bbda37d1a3af379a225e3755a1a23721fcb6371616e53710f28136fc575e365e61cf35c967be3500206334e0cdbc34a66cc5343fc24933ac541f339cee07339a0e72338ed8ac3345378f3313dd1732d93c3032877bb532612f4a324c2b8b3209654131fdfbb7316d302c314c4f4b30fe912830c1253230c119373089bd022f65d5602f29c9b22f24748d2e4c03ba2dff33912dff03ce2dfefc262dae8b4a2d87c5372d8523332d5137912cdf9d2d2bb586b22b75dc00
  | 5, 3 => 0x5660cd0255fcbf66554d72d054deb3fe54d18eb454b0add354864a90547972ec5421937653e9f53b539b3f18527c6fee5242f6eb523fa879522eef5e52207d1a51fe9cdb51d1336651b366f8517f67a9511717fc5111ee0150df795650928df750463bc55044fee2500b57354fcfbc144f7e84744f6bac3b4ecc13404e7558124e2a07294e0e8e014d8384ac4d5c88b94c9b08a74be3d1de4bbc28594bb311164aaf24aa4a7e12cb4a2a56b649ca1d52496c7ee5496796d9492d91d248d21c1e484dc25d47b2b5974725bce745ee6a33459c4d8845753fe644ff8eac44d9aa66445ee65a43b001584370d81642ef01ed42d320ac424121dc4177ca9741592da7
  | 5, 4 => 0x74d3afcf74c4fb5d74bde83c74a8f43a749313d4747e5c5274633f13745e79e4741aee0473ecbac873e57e1173dd15ee723490ab71b27eff7139d3927005691d6f65e2316f3a57da6f30a7976ee595ff6dfd5bf56d8f65bc6d45c8246c9504de6c43287a6be0f2e76adfb1f26acadda26a1c5a0c6997ff9067c30a0f676acbb36765effb66a1b2e9668dbd3165ea413464c8d6ab6463817a639460b162b0e9ef6211d4b561b7fc70618ba615610ff7cc6087e1556036be3760229b745ef598835ea989a25e3551d25dc913405d509b0c5b5615ff5b0796d55a2fe1565a17db065a12fba759de485b58e4139858b13f205811e54b57d8dc43576fb34556f20169
  | 5, 5 => 0x92646bb290c3d06d900983378ff795f98fb364e98f9379508f46444b8f1a62a68de2459c8d574c0b8cfefe728cd8beef8c73c2438c57b20b8c4613e08bd52a5f8bbe19828b9ec0dd8b6a5ed98afbe5508ae237808aabbbcb8a928321898ba3358931aa1688ec946b882d21fd87cc688886aedf86862386318404c35583a3c41782f5d0ce8218cf6a800a6f828003b8f47e7146367de892937de5a0c27dbe471b7d09b1d17cc981067c6584557b9105d47b73fbfb7b3f69217966fca0790a9ae578aa6924782f45b17818cede780b03f677a5c06376fc0d2e76c4a001768d14b97626858c75f9ff5a75d69bb775878f037584259375433e3f751279ae74f45ea4
  | 5, 6 => 0xafe8ab2caf6e465daf646233af2ff28baef2a202ac5a8377ac22b1aeab39d42dab0f5120aaa77e4baa8a3b5faa4ba69faa4acd89aa455d92aa3ef24ba9f779afa9effdb3a99c6ffea961725ca8e5eb23a8c7dd4aa8b9635aa8916a1ca83a53a8a82eaa60a7dbbff6a6df88f4a67d428ca62d9404a5bd0289a4d0833ba4beaacca42cf772a4186e1fa379aa69a337f8d3a310a5eca2ff0b85a2150ca2a113ced9a08db25b9ee86af19ea02e0e9e945d769e5a47c39db0b6149dab25839cf60d109ca478589bd0dccb9b921be79adfcabf9adb703b9a90d1fc993d833e986c3dcf96a1158596a08182963707ab96031d8b95dd20f395325500934f0d4092ece9d8
  | 5, 7 => 0xd3559906d30b40ded2c57ed7d2354ad7d1439fa2cfab9ceacf9085bacf47e691ce8e00d7ce1d1baece0fb847cddf4c2cccd959ecccd416a6cab52fcfca68cae3ca47d9afc834e1c3c7e72fbcc7c96c19c5c64a19c5708fe1c4cd9e7ec490969dc46bdd74c3d724bbc35dd018c2817300c14ae839c096045bc0503f64bf9a7f37bf8ef6f4bf1a883abe5d77fabe5520fbbe22cffdbe0eda45bd4e8c38bd4bc964bcf41ccbbc7ec081bc01f2eabbcb1cb1ba340f14ba01d9c1b9edfe52b9abf99eb85236d5b7eead1ab7856231b74132b5b6e2c79bb62b5a78b4ad83aeb49ee0b3b33bfc3cb29fa792b2289e04b2041e50b14f66feb0c4dd01b0ba0ff2b098e67c
  | 5, 8 => 0xff4b9e17ff42b5a3ff0720effeb49535fe8de751fd640a61fd29c260fccf827bfc94e1eefb13d281fad1d9b9fab915e7f6a874dff6a75fd7f573a355f41a266ef3d4aa8af24d8d79f143aab4f06d0a9fef317993edc52f22ec9ba2b5ec5c9073ec45103aeb8f37e6e80639f2e6a2bc5de5db4860e2b98840e171241de13a69d3e0b2f676e07c777bdfe96ededeaccf6ddd74e70cdcae68fcdb48e78ddb3fb3a5db27e2b1d9b15438d88416c0d86e190ed86aa226d7b26258d7828518d6ec6318d688a666d45cb1edd435d07bd4331925
  | 6, 0 => 0x1d0513ca1af4852b1af1cdd51a144db61a0871e119c9f58e19c031af1984338718ba0a3e1852c316183a58d917aee42e1720583816e905a516a69699164f3a6a157a6dfb1573d6af154cb58714dbd05e149e00dc1401828113980e9c1392cb5613598ee6129ff2a01204ed2e118930541176144d11277f930f3854130ec86be50e0be7380e0598bb0c84fec90b4f4b4d0b2a92240a95d96b0a693e8d0a20c4ab0a1c84c809a65fdc094027b008e28ff40838fc2407723e50075fbd770724136b06c3591006ae3958065933e70640cddf0633edf4061d2e5805d93cea0513d5ab04e184ad04cd8ef504b3b8a504585c63043d453302bf259e0289d16100acb302
  | 6, 1 => 0x4407710543e8771043b001584353969e42d320ac41d2873141908e694177ca9740af6c694010f9053ecd841f3e531f503c7ebd223c3131fc3ad8db1e3a935f3a397fa2d0390c422938025f64372bbf4f371616e53684bf9434ee8cb434a600a73483e3d2336154ae331b45233249bbe6320bc96e31895e51316d302c3141a1673089bd02305d049a3013a5902f7e99322d61710d2d207e0f2c5fdf2e2b561b8929f2c8de28f0b5f528816a03282fd8cd27f91e832771ab2626fa4cf226f6caf526a8238e25f53a8c256b841d25262e142519ca1824ce8c3924b1e7d72367716f233f13eb2159e223207008e81f2956d61efacc951ea832e61e4fe2071d0e3cb5
  | 6, 2 => 0x681896ce67c4176f679fe2406778c14a66f622f566d006df6619efa065cc4cb56586a82365367c76650e96b264ebd70264dc291f63c3eb3a5fa25eea5e6056d15defb5365c328b5a5ba38a695b85b0d75a12fba75917c96858c3a1d958b2ce80584befde581688735811e54b55fcbf6655b2079a54d18eb453e9f53b53b95da0539b3f1852fca17b52c58afc5274182151ca614c51bae897513fdff35127ccd450f89afe50df795650cc5903506514874ff4ea864ebbcebc4eb688624e0e8e014d5c88b94ce7184d4cbde9cd4aaf24aa4a209623496796d94872378d477191b9474911534725bce746b7f5de460a52c7457349e5454c9c01446a1b32443c94c6
  | 6, 3 => 0x8cbea4bf8cad1ede8ca74a788c5b02338c4613e08c33f4918b985f118b1d9b058aa97eda8a6eb6038991d557897e4e288896b4af8847fe8c865c9c10858c38ca84e1a3578490c17682bb4d758209482d81a964898063b88d7f5be41e7e7146367e58d7097dcfa72c7ce651c77bd27c5b7bbed50e7afe76f47a5ba2b27a4d8d5779463060790ae03678bcb062785cc0cc782be4d7780b03f677bd45d3777fe020777fd9dd777fcde2774871ad750ab86574bde83c7443d7de740fec3c73dd15ee739e51d8737a4393723490ab712b7c967005691d6ef40ec96ec515c86db57fa06d915cd26bc4011e6b274b7f6acadda26ab1256669ece945698fc2bd68306ff8
  | 6, 4 => 0xbbb4cdd6bbb3134fbb92647abb67a8e5bb51c87fbb3d10fdbb1d2e8fbaa432bcba9bca99b9edfe52b87133aab7856231b6c41dc8b44e1a67b33bfc3cb31e05aab29fa792b1892f0ab0db0eb7aca8f5dfab878b56aaa77e4ba8d08960a889d562a84a5ac0a7469600a63b944ea5b44d2ea5683e4da4b22891a42cf772a40f4fb7a2150ca2a214caaaa1c64b80a0d1b0529ed099f69d1f81ad9cbb74119ca478589b90435f9b3827979aa8a9e69a59f3c398eda40998df31c5983e1c5497d5cca79759cda59703b38d96ca0be0968e70bf9532550094cd42ac94423957941b3d64916dd955913cc77690e90b61902b33908ff795f98f0c77088ebfbb1b8de47192
  | 6, 5 => 0xff10eb80feb49535fead61c5fc94e1eefad1d9b9f9fab0e7f8c2d2fbf78391acf778c49df7579b27f6a75fd7f62cfb08f3d4aa8af24d8d79f16632f6f148f00af0b62e5af06d0a9fefa49fceef8691f5ee9a74a1ecec48afec7bb734e9cf5a97e5dea69ee3b4c1bbe14f86a7dffc37e9deaccf6ddd5fca30dc9bd59eda0dc1ebd6c837e2d435d07bd2c57ed7cfab9ceacfab4916cf9085baceebd6a8ce8b1d33cd6d9431cac37800ca68cae3ca6278c2c9df1474c8d78415c52ffae1c47cfbc6c38835b1c232b0a6c025b14bbf058dbabeedfa5cbd8354acbd4bc964bce53a37bcb8b405bbd12e59
  | 7, 0 => 0xf9fab0e7f16632f6ba9bca999ed099f69cbb74119b90435f9a59f3c3941b3d64916dd9558de471928a6eb603782be4d7774871ad6db57fa0681896ce650e96b25c328b5a58c3a1d950df79565065148746b7f5de457349e541908e693ecd841f3a935f3a372bbf4f24b1e7d71af4852b198433871852c316164f3a6a11277f930f3854130a20c4ab00acb302
  | 8, 0 => 0x50df7956
  | _, _ => 0

def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3f3f00003f3f000033330000333300000f0f00000f0f000000ff000000ff00000000ffffffff00000000ffff000000000000ff00ff0000000000cccccccc00000000c0c0c0c000000000aaaaaaaa0000000055555555000000003f3f3f3f000000000f0f0f0f0000000000ff00ff000000000000ffff0000000000000000
  | 0, 1 => 0xcc00cc00cc00cc00c000c000c000c000aa00aa00aa00aa0055005500550055003f003f003f003f0033003300330033000f000f000f000f0000ffffffffffff0000ffff0000ffff0000ffff000000000000ff00ff00ff000000ff000000ff000000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa0000555500005555
  | 0, 2 => 0x15151515151515150fff0fff0fff0fff0f0fffff0f0fffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f00000f0f00000c0c0c0c0c0c0c0c0505050505050505030303030303030300ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff0000000000ff0000ffff000000ff000000ff0000
  | 0, 3 => 0x3f3fffff3f3fffff3f3f3f3fffffffff3f3f3f3f3f3f3f3f3f3f3f3f000000003f3f00003f3f00003f003f003f003f0033ff33ff33ff33ff33333333ffffffff333333333333333333333333000000003333000033330000330033003300330030303030303030302aaa2aaa2aaa2aaa2a2a2a2a2a2a2a2a2222222222222222
  | 0, 4 => 0x5555ffff5555ffff5555ffff0000000055555555ffffffff5555555555555555555555550000000055550000555500005500ff005500ff00550055005500550050505050505050504444cccc4444cccc44444444444444444040c0c04040c0c040404040404040403fff3fff3fff3fff3fff3fff000000003fff00003fff0000
  | 0, 5 => 0xaa00aa00aa00aa00aa00aa0000000000aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a0008888888888888888888888880000000080808080808080808080808000000000808000008080000080008000800080007f7f7f7f7f7f7f7f5f5f5f5f5f5f5f5f55ff55ff55ff55ff
  | 0, 6 => 0xaaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa80808080aaaaaaaa00000000aaaaaaa0aaaaaaa0aaaaaa88aaaaaa88aaaaaa80aaaaaa80aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa8080aaaa8080aaaa0000aaaa0000aaaa000000000000aaa0aaa0aaa0aaa0aa80aa80aa80aa80
  | 0, 7 => 0xc000c000c000c000c000c00000000000c0000000c0000000bfbfbfbfbfbfbfbfafafafafafafafafaaffaaffaaffaaffaaffaaff00000000aaff0000aaff0000aaaaffffaaaaffffaaaaaaaaffffffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaaa0a0aaaaaaaaaaaa8080aaaaaaaaaaaa0000
  | 0, 8 => 0xc0c0c0c0c0ffc0ffc0c0c0c0c0ccc0ccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c000c0c0c0c0c0c00000c0c0c0c0c080c080c0c0c0c0c000c000c0c0c0c080808080c0c0c0c000000000c0c0c080c0c0c080c0c0c000c0c0c000c0c08080c0c08080c0c00000c0c00000c0c0000000000000c080c080c080c080c000ff00c000ff00
  | 0, 9 => 0xcc88cc88cc88cc88cc00cc00cc00cc00cc000000cc000000c8c8c8c8c8c8c8c8c8c8c0c0c8c8c0c0c8c0c8c0c8c0c8c0c8c0c8c0c0c0c0c0c8c0c0c0c8c0c0c0c4c4c4c4c4c4c4c4c0ffc0ffc0ffc0ffc0ccc0ccc0ccc0ccc0c0ffffc0c0ffffc0c0ffff00000000c0c0ccccc0c0ccccc0c0c0c0ffffffffc0c0c0c0cccccccc
  | 0, 10 => 0xcccccccccccccccccccccccccccc0000cccccccccc88cc88cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc00000000ccccccc0ccccccc0cccccc88cccccc88cccccc00cccccc00ccccc8c8ccccc8c8ccccc0c0ccccc0c0cccc0000cccc0000cccc000000000000ccc0ccc0ccc0ccc0ccc0ccc0c0c0c0c0
  | 0, 11 => 0xea00ea00ea00ea00ea00ea00c000c000e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0c0c0e0e0c0c0e0e0c0c0c0c0c0c0ddddddddddddddddd5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfcfcfcfcfcccccccccececececececececcccffffccccffffccccffff00000000cccccfcfcccccfcfccccccccffffffffccccccccccffccff
  | 0, 12 => 0xeaeaeaeaaaaaaaaaeaeaeaea00000000eaeac0c0eaeac0c0eaeac0c0c0c0c0c0eaeaaaaaeaeaaaaaeaeaaaaaaaaaaaaaeaeaaaaa00000000eaea0000eaea0000eaea0000aaaa0000eac0eac0eac0eac0eac0eac0c0c0c0c0eac0eac000000000eac0c0c0eac0c0c0eaaaeaaaeaaaeaaaeaaaeaaaaaaaaaaaeaaaaaaaeaaaaaaa
  | 0, 13 => 0xf000f00000000000f0000000f0000000eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaa00000000eeee0000eeee0000eecceecccccccccceeaaeeaaeeaaeeaaee00ee00ee00ee00ee00ee00cc00cc00ececececececececeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0
  | 0, 14 => 0xf0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0c000c000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0c0f0c0f000f000f0c0c0c0f0c0c0c0f000ff00f000ff00f000f000f000f000
  | 0, 15 => 0xf5f5f5f5f5f5f5f5f3f3f3f3f3f3f3f3f3f3f0f0f3f3f0f0f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f3f0f3f0f3f0f3f0f0fffff0f0fffff0f0ffff00000000f0f0f0f0fffffffff0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0c0c0f0f0f0f0f0f00000f0f0f0f0f0c0f0c0
  | 1, 0 => 0xfafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaf0f0f0f0f0f0fafaaaaafafaaaaafafaaaaa00000000fafa0000fafa0000fafa0000aaaa0000faf0faf0faf0faf0faf0faf000000000faf0f0f0faf0f0f0faaafaaafaaafaaafa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0
  | 1, 1 => 0xff00c000ff00c000ff00aa00ff00aa00ff000000ff000000ff00000000000000fefefefefefefefefefefefe00000000fefe0000fefe0000fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcccccfcfcccccfcfc0000fcfc0000fcf0fcf0fcf0fcf0fc00fc00fc00fc00fafafafafafafafa
  | 1, 2 => 0xff00ff00ff00ff00ff00ff00ff00cc00ff00ff00ff00c000ff00ff00ff000000ff00ff00fc00fc00ff00ff00fa00fa00ff00ff00f000f000ff00ff00ee00ee00ff00ff00ea00ea00ff00ff00cc00cc00ff00ff00c000c000ff00ff00aa00aa00ff00ff0000000000ff00f000ff00f000ff00ee00ff00ee00ff00ea00ff00ea00
  | 1, 3 => 0xff80ff80ff80ff80ff80ff80ff00ff00ff80ff00ff80ff00ff55ff55ff55ff55ff3fff3fff3fff3fff3fff00ff3fff00ff33ff33ff33ff33ff33ff00ff33ff00ff15ff15ff15ff15ff11ff11ff11ff11ff0fff00ff0fff00ff00ffffff00ffffff00ff00ffffffffff00ff00ff3fff3fff00ff00ff33ff33ff00ff00ff0fff0f
  | 1, 4 => 0xffc0ffc0c0c0c0c0ffc0ffc000000000ffc0ff00ffc0ff00ffc0ff00ff00ff00ffc0c0c0ffc0c0c0ffc00000ffc00000ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaff00ff00ff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00
  | 1, 5 => 0xfff0fff0f0f0f0f0fff0fff000000000fff0ff00fff0ff00fff00000fff00000ffeeffeeffeeffeeffee0000ffee0000ffeaffeaffeaffeaffeaffea00000000ffea0000ffea0000ffccffccffccffccffccffcc00000000ffccff00ffccff00ffccff00ff00ff00ffccccccffccccccffc0ffc0ffc0ffc0ffc0ffc0ff00ff00
  | 1, 6 => 0xffff0000ffaa0000ffff0000ff000000ffff0000fafa0000ffff0000f0f00000ffff0000eaea0000ffff0000cccc0000ffff0000c0c00000ffff0000aaaa0000ffff000000000000fffcfffcfffcfffcfffcfffc00000000fffafffafffafffafffafffa00000000fffa0000fffa0000fff0fff0fff0fff0fff0fff0ff00ff00
  | 1, 7 => 0xffffaa00ffff0000ffffa0a0ffffa0a0ffff8888ffff8888ffff8080ffff8080ffff8080ffff0000ffff8000ffff8000ffff5555ffff5555ffff5500ffff5500ffff3f3fffff3f3fffff1515ffff1515ffff1111ffff1111ffff0f0fffff0f0fffff00ffffff00ffffff0000ffffffffffff0000ffff5555ffff0000ffff0000
  | 1, 8 => 0xffffccccffffccccffffccccffff0000ffffcccc00000000ffffcc00ffffcc00ffffcc00ffff0000ffffc0c0ffffc0c0ffffc0c0ffff0000ffffc0c0c0c0c0c0ffffc0c000000000ffffc000ffffc000ffffc000ffff0000ffffaaaaffffaaaaffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffaa00ffffaa00
  | 1, 9 => 0xffffff00ffffff00ffffff00ffffc000ffffff00ffff0000ffffff00ffaaff00ffffff00ff00ff00ffffff0000000000fffffcfcfffffcfcfffffafa00000000fffff0f0fffff0f0fffff0f0ffff0000fffff0f0f0f0f0f0fffff000ffff0000ffffeeeeffffeeeeffffeeee00000000ffffeaeaffffeaeaffffeaea00000000
  | 1, 10 => 0xffffffff0f0f0f0fffffffff05050505ffffffff00ff00ffffffffff003f003fffffffff00330033ffffffff000f000fffffffff0000ffffffffffff00005555ffffffff00000000fffffff000000000ffffffccffffffccffffffcc00000000ffffffc0ffffffc0ffffffc000000000ffffffaaffffffaaffffffaa00000000
  | 1, 11 => 0xffffffffaa00aa00ffffffffaa000000ffffffffa0a0a0a0ffffffffa0a00000ffffffff88888888ffffffff80808080ffffffff80800000ffffffff80008000ffffffff55555555ffffffff55005500ffffffff3f3f3f3fffffffff3f3f0000ffffffff33333333ffffffff33330000ffffffff15151515ffffffff11111111
  | 1, 12 => 0xfffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0fffffffff0000000ffffffffeeeeeeeeffffffffeaeaeaeaffffffffccccccccffffffffcccc0000ffffffffcc00cc00ffffffffcc000000ffffffffc0c0c0c0ffffffffc0c00000ffffffffc000c000ffffffffc0000000ffffffffaaaaaaaaffffffffaaaa0000
  | 1, 13 => 0xffffffffffffffffffffffffffffff00fffffffffffff0f0ffffffffffffc0c0ffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffccffccffffffffffc0ffc0ffffffffffaaffaaffffffffffaa0000ffffffffff00ff00ffffffffff00c000ffffffffff000000
  | _, _ => 0

def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x19c469c0f3c893a1e7d12703
  | 3, 0, 0 => 0xec6711a744e96791a744cea1cfe744b82f90e744b849512744cda34d6634cecbd1274497b1d1a6b4cddc11a704b84bd12704e06711a744e967d1a704ce3d15e704cfbbd5e704b44bd1a704ec67d12744
  | 3, 0, 1 => 0xb8310fe744e1e791a74497b251a634
  | 4, 0, 0 => 0xd3dc25e8d3a2dc25ed0439d16e16397a34e8ba7b85311a745d3dc27a8d3a2e9e5ec7469d173b2f7a2b0e8bd8e967d1a745d3e1a5e8d3a2ecae12f469d174f9e92a34e8b7097c351a745d3db65e8d3a2e9f3d2f469d165edb6ba34e8ba7b84bd30745
  | 4, 0, 1 => 0xd3dc1c28d3a2e9ee131469d16e10d81234e8bb4b84bd1a745d25c25e8d3a2e9ee121469d165ece64234e8ba7b84bd74745e1dc25ec246ae9e5ed75d9d174f7092a34e8ba7b8234e8155b85625e8d3a2e9ee153469d174f7097234e8ba7b84bd1a685
  | 4, 0, 2 => 0xd3e2e5e8d3a2dc25eef579c174f2f8ca34e8ba797b3590745ec66ee08d3a2e9ee12f449d174f709c234e8ba7b851576745d3dc2048d3a2e9ee0d3469d17817097a34e0bc0b85151a745ec5c25e893a2f4ee12f469d17457097a34e8b9d7a2a53c745
  | 4, 0, 3 => 0xd3dd65e8d3a2f4ae12f469c174f7a97a34e8ba7ceb811a745e05c25e9b3a2e9ee12f602356e12f82a34e8ba797c211a745d3dc65e8d3a2e9f3f70449d17819f97a34e8ba7b84991a745d3dc17c8d3a2e9ee12f479d174f9bb8234e8ba7642fd1a745
  | 4, 0, 4 => 0xb85391a7f3a2e9e1102469d16d12f469d0d6b70a73811a745d3dc2508d3a2e9f368d3a18d74f2f83a34e8ba7b14bd1a745b84be46893a2f4b3b2f469d178d7097a34e8ba7b84d91a745d3dc28acd3a2ef2e12f469d174f7096a34e8ba7cea34fe745
  | 4, 0, 5 => 0xe967de8af382e9f3f70612356e12f469d082ba7b84bd8a745e05a25e8d3a2e9ee132469d16e12f6c234e8ba7bc4bd1a745d45c25e8d3a2e9ee12f612356e12f8d234e8ba7c34bd848d5d3dc25e8c3a2e9ee12f469a96d12f7a2bce0ba7cfcbd9a745
  | 4, 0, 6 => 0xb857a5e8d3a2dc25e8d3a0957617097a34e8bb6b84bd1a745d3dbe5e8d3a2e9ef72f469d16e12f46a1ce0bc0ce3d15e745b859e5e8d382dc25e8d3c9d174f2f469d080ba797a34e8215b84bd528d382eb2e12f469d174f7097a28e8ba797a34f0745
  | 4, 0, 7 => 0xcddc11a7435adc25eb3469d174f7046a00e8b9d97a350e745d3cbd968d31ae9eed2f469d174f70a0234e8b81b84bd1a745b84bd9c8d3a2dc25e893a1ad74f7f97a34e8b9d97aa51a745d3dc25e8d3aae9ee12f5d9d174f7097b291abc0b84bd1a745
  | 4, 0, 8 => 0xe15c25e8d3a2dc25e8d3a1396e123439fce8bd1b84bd1a745d3dc17e8d3a2e065e8d3a18d6e16597a34e8ba7b8318fe745d3dc25ecc3a2e9ee12f669d174f7097b0ce8b7097b3d1a6b5e95c24a8d3a2e9f3f2f469c1737707a2bce0ba7b84ad1a745
  | 4, 0, 9 => 0xe1e1a5e8d3a2e9ee12f60a356e12f64a34e8ba7b5cbd1a745d3dc25e993a2dc24a8d439d174f7097a18e8b7092aa51a745e85c25e8d3a2e9eaf2f469d17317097a34e8b7097a4d1a745b3cbd1a6b31ae9e5ec8469d174f8597a34e8babb84bd1a745
  | 4, 0, 10 => 0xd05c25e8d3a2f0f3f70469d17b19f7a2b0e8bc5b84bd12745d3dc26e8d3a2e9ee12f471d174f7097a3464bb9b84bd1a745e1dc24a8d3a2e9ee12f469c97877097a34e8b9b7a2bcd6635df5c25e8d3a2e42e12f469d174f7097a34e0ba7b85151a745
  | 4, 0, 11 => 0xd3dc25e74222f02e12f669d17717097a34e8b70a74bd1a745d3dc24e8d3a2e9f3970469d17837097a34e0ba7b84bd1a715d3dc11a7424ae9ee0c25fa357877097a24e8ba7b84bd1a735b84bd888d3a2e9ee120469d174f9cb4234e8ba7cecbd1a745
  | 4, 0, 12 => 0x1d8ce3d15e745b83397e8d3a2e9ed12f469d174f709f234e8bb1b84bd1a745d3dc2888d3a2e9ee118469d174f709d234e8bd8b44bd1a745
  | 5, 0, 0 => 0xd3dc25ef4579c1b4f7097abd36746d3dc28af4579d1b4f2f7a35d1a746005c25f0d469d174f7097a34e81b6d3dc25e8d3a0e5b4f9d97abd1a746d3dc2a12f469d1b4f70983d15e746d3dc25e8d3a169b4f7097bd14a746d3dc25ef4581d1b4f70afcbd1a746d3dc25f14469d1b4f2f7a3211a746
  | 5, 0, 1 => 0xd3e7e5e8d3a18db4f7097c751a746b84be46f4561d1b4f7097a34e8136d3dc25ef4579c9b4f7094bd11a746e1dc25ef4579d1b4f2f6eb5d1a746d3e6ee12f469d1b4f8fb84bd7a746d3dc25eed579d1b7d7097bd15e746d3dc25ee7469d1801a7c34bd1a745d3e3ae12f469d1b877097a34fe746
  | 5, 0, 2 => 0xd3dc25e9b3a18db4f7097a34e8646d3dc25e8d3a001801a7b84951a745e85c25ef4469d1b4f7097bd156746d3dc25e8d3a165b4f709ccbd1a746d3cbda2c8469d1b4f704f234e85f6d3dc25f26469d1b4f7097a34e8056d3dc25ef4591d1b4f7097b6d1a7460069ee12f469d174f7097bd124746
  | 5, 0, 3 => 0xd3dc27f2f469d1ae12f84bd15e746d3e765ef4579d1b417097bd15e746ec5c25eef579d1b81a7b84bd1a746d3dc25ee9469d1b4f7097a34e8586d3dc25e8d3a11db4f7097c6d1a746d3dc25e8d441d1b4f70af4bd1a746d3dc25ee5579d1b4f7cb84bd1a746d3dc25e9f469d1b4f70813d138746
  | 5, 0, 4 => 0xd3dc28af4469d1b4f91b84bd1a746d3dc25f0c6d1d1b4f7097c591a746d3e72d0f4579d1b4f7097bbd5e746d3dc26af4579d1b4f70884091a746d3dc2c92f469d1ae14e97abd1a746d3dc25e8d3a0c1b4f7097a34e83b6d3cbd1a833a18db4f70a4cbda28d6d3dc25ef3579d1b4f7097a34e8376
  | 5, 0, 5 => 0xd3dc25e8d3b1d1b4f7097bd15e736d3dc25f0b579d1b4f7097a34e8616d3dc25e8d3a07d801a7b8234e8235d3e36e12f469d1b4f70b44bd1a746d3cbe10f44e1d1ae1237a2a53c746d3e06e12f469d1b877097bd11a746d3dc25ee8579d1b4f7097b391a746b85469d2f469d1b4f7097bd11a706
  | 5, 0, 6 => 0xd3dc1a8af469d1b5d7097bd15e746d3dc25e8d3a1d1b4f707a2bce8496d3dc25ef45a9d1b4f82b84bd1a746d3dc2cd2f469d1b4f7097a34e85c6d3e7ee0ef579d1801a7b84091a745d3dc25e8d3598db4f70b0cbd1a746ec74ae12f469d1b837097a34e86b6d3dc25e8d3a1b1b9fa7b84bd1a746
  | 5, 0, 7 => 0xd3dc25eb7469d1b4f7097b895e746b853a5ef4579d1b4f7097ba5ba746d3e1ae12f469d1b4f7097ad11a746d3dc25f12469d1b4f9cb83d15e746d3dc25e8d3a0d9b4f70953d15e746e0dc25ef4579c1ba5a7b84bd1a746d3dc25e8d459d1b4f9497bd15e7460069ee12f449d174f7097c391a746
  | 5, 0, 8 => 0xe969f3f70469d1b4f84b84bd1a746d3da25eaf469d1b257097bd15e746e05c25f0c579d1b53a7b84bd1a7460069ee126469d16e15597abd1a746d3dc25e8d3e9d1b4f7097af15e746d3dc25eef469d1b4f70b84bd1a746d3dc25e8d3a075b4f7097a34e8226d3dc25ef44d9d1801a7cddc11a745
  | 5, 0, 9 => 0xd3dc2a92f469d1b4f7091b811a746d55c25ef4579d1b4f7097a34e84b6e2dc25eeb469d1b997097bd15e746d3dc25ef4579a5b4f70a0cbd1a746d3dc25eea469d1b4f70b04bd1a746d3dc25f04579d1b4f7097a34e82d60069e5e8d3a05d401a797c211a745d3dc25efa469d1b4f95b84bd1a746
  | 5, 0, 10 => 0xd3dc25ed9469d1b4f7097bf55e746b84bde8ac3a1adae12f7bbd15e746d3dc25e8d3a15dae12f86abd1a746d3dc25ef44b9d1b4f707a3515e746d3dc25e8d3a0a1b4f7091a34fe746d35c25ef4579d1b4f7097bed5e746d6e9ee12f469d1b4f7097a34e83a6d3dc25e9d469d1b4f7097a34e8346
  | 5, 0, 11 => 0xd3dc25ef44d1d1b4f7092abd1a746b85565ef4579d1b4f7097a34e8016d3dc25eaf469d1b4f7097c191a746d3dc25e8d3a065b4f70a23d15e746d3dc25ef45b9d1b4f708c3d15e746ec5a25ef4579d1b4f5a97bd15e746d3dc25e8d3a129b4f8697abd1a746d3cbde8da6b9d1b4f7097c911a746
  | 5, 0, 12 => 0xd3dc2a52f469d1a5ef46db5d5e746d3dc25e8d3a18dba57097c8d1a7460069d1a741185d74f7097a34e84f60069ee12f260f574f7097a34e8036d3dc25f22469d1b4f7097a8d1a746d3dc25e8d3a199b4f7097bf15e746d3dc2a32f469d1ba5a7b84bd12746d3da25ef4579d1b4f9fc54bd1a746
  | 5, 0, 13 => 0xec74b3ef4579d1b4f7097a34fe746d3dc25e8d3a0318017097a34e80b5d3e1a5ef4579d1b4f707a3511a746d95c25ef4579d1b4f7097bd14e746d3dc25ee0469d1b4f93b84bd1a746d3e125e8d3a18db4f8697a34fe746dbe9ee12f469d1ae12f86bd15e746d3db65ef4579d1b4f7097bbd12746
  | 5, 0, 14 => 0xd3dc2a6f4579d1b4f70973d15e746e569ee12f469d1b4f70a1cbd1a746d3dc25e8d3a121b4f7097b711a746d3dc25ef4579d1b4f70a2bd1b4746b858e5ef4579d1b4f7097a34e8186ec5c25ea9469d1b91a7b84bd1a746ed69ee12f469d1b4f7097a34e86d6d3dc29f2f469d1b4f7097a34e8536
  | 5, 0, 15 => 0xe869ee12f469d1b4f7097aa51a746e2e9ee125469d1ae15597bd11a746d3dc25e8d3a05db4f7097c211a746d3dc25e873f9d1b4f9fb83811a746ec5c25e8d439d1b8ba7b84bd1a746d3dc25e8d469d1b4f7097b3d1a746d3dc24af4579d1b4f707a2bce8156d3dc25e8d3d1d1bb170b3cbd1a746
  | 5, 1, 0 => 0xec69ee12f469c1ae12f86bd11a746dee9ee12f469d1b4f2f51a34e8636ece9ee12f469d1b4f7097a891a746e6e9ee129469d1b4f7097abd12746d3dc25e8d439d1b4f7097bd120746d3dc25f00579d1b4f7090bd15e746d3dc2cf2f469d1b4f9fb8234fe746d3dc25e8d3a0f1801a7b84bd848d5
  | 5, 1, 1 => 0xd3dc1e8d3579d1b817097bd15e706e05c28af4579d1b4f7097a34e8026e3e9ee12f469d1ba77097bd15e746eb69ee12f469d1b4f707a3855e746eee9ee12f469d1b4f709dcbd1a746005c11a741182d6e10d813d15e746d3e66e12f469d1b4f70b4cbd1a746d3e6ee0af469d1b4f7097c551a746
  | 5, 1, 2 => 0xd3e1ee12f469d1b4f7097b191a7460069ee12f5d9d174f7097a3512746d3dc25e8d3a01dbb1a7cfcbd1a746d3dc25ebf469d1b4f2f8cbd15e746ec66ee0f4579d1801c0b84bd1a745005c2bd2f469d174f7097b751a746d3dc25e8d3a059b4f7097a34f8746e1e9ee12f469d1b4f70a54bd1a746
  | 5, 1, 3 => 0xd3dc25e8d3a051b4f7097a511a746d3dc24cf4579d18012f469d02e0b5d3dc25f11469d1b4f7097a34e8116d3dc25e8d3a011b4f7097a34e8516d3dc252f4551d1b89a7b84bd1a746d3dc28d2f469d1b4f7097a34e85f6d3e6ee0f4579d1b4f6797a34e8636d3dc25ec2469d1b4f7097b451a746
  | 5, 1, 4 => 0xd3e75e8e0579d1b4f70ae4bd1a746b84be0af4579d1b4f2f843d15e746d3dc25ecb469d1b4f7197bd15e746d3dc25f13469d180181b84bd1a745d3dc25f2c469d1b4f7097a34e8266dae9ee12f469d1b819f97bd15e746d3dc25e91469d18017097b391a745e95c25e8d3a1adae12f91aa51a746
  | 5, 1, 5 => 0xd3dc25e8d3a155ae161af4bd1a746de5c25ef4579d1b4f7097a34e82c6d3e2ae12f469d1b4f7097a34e83e6d3dc25ea1469d1b4f7097bb11a746dd69ee12f469d1b4f70a44bd1a746d3dc25ef46b1d1b4f7597bd15e746d3dc25f1c469d1ba57097bd15e706d3e6ee167469d1ae12f91a350e746
  | 5, 1, 6 => 0xd3cbe0ef4579d1b4f7097b095e8d6e769ee12f469d1ba59d97bd15e7460069ee12f669d175fa7b84bd1a746d3dc25eda469d1b4f70933d11a746d3dc29d2f469d1b4f7097a34e8626d3dc2852f469d1b4f7097a34f6746d3dc25e8d3a071b4f709b3d15e746d3dc25e8d3a091b4f70a3cbd1a746
  | 5, 1, 7 => 0xd3dc25ef1469d1801a7b82fd1a745d3dc25e8d3a179b4f7097bd142746d3c2204f4579d1ad12f7a2bce86b6d3dc25e8d3a03db4f7eb84bd1a746d3dc25e8d411d1b4f7097bc15e746d3dc25e8d3a035b4f2f843d11a746d3dc25eb8469d1b4f7097bd15a746d3dc25eee579d1b4f9b7a2bce8636
  | 5, 1, 8 => 0xd3dc25ef46d1d1b4f7097bd16c746d3dc2b32f469d1b4f7097b091a7f6d3e2ae12f689d1b4f70a2cbd1a746d3dc25e8d3a0cdb4f7097a34fc746d3dc25e8d3a135b4f7097c7d1a746d3dc25ee3579d1b4f7097ac51a746d3dc25e8d3a081801a7b84bce83d5d3e765f23469d1b4f7097a34e82a6
  | 5, 1, 9 => 0xd3e3ee12f469d1ae12f54a34e86b6d3dc25ed5469d1b816897bd15e746d3dc2792f469d1b4f89b84bd1a746d3dc25ebd579d1b4f7097bb91a746e05c25eaf469d1b4f70a6cbd1a746d3dc25ef2579d1b4f7897bd15e746d45c25ef4579d1b4f7097bd184af6b84be34f4579d1b0981b84bd1a746
  | 5, 1, 10 => 0xb84bd9caf469d1b4f7097b411a7460069ee0741e88d7817097a34e8636d3dc25e8d3a021b4f2f7a2bcf0746d3dc2d52f469d1b4f7097c3136746b84bd1a873a1adbb9a7b84bd1a746d3dc2a2e0469d1b4f7097bd150746b859e5e8d3a1adba9a7b84bd1a7460069e5ec8469d174f7097c051a746
  | 5, 1, 11 => 0x742e12f469d17a17097c751a746d3dc25e8d3a109b6d7097bd15e746d3dbe5ef4579d1ae16797bd15e706b84bde8af3c9d1b037097abd1a746d3cbde8af3a085bb1a7b84bd1a746d3dc2dd2f469d1ae15597b915e746d3dc2972f469d1ae12f7a2bd52706d3dc2a28d3f9d1b4f80b84bd1a746
  | 5, 1, 12 => 0xdfe9ee12f469d1b4f73b84bd1a746e6e9ee12f469d1b4f7097bd12a746d3dc25ebd469d1b4f7097bfd1a746d3e8ee12f469d1b4f7097bd140746d3dc25f17469d1b817097bd15e746d3dc25eef561d1b4f74b84bd1a746b84bde8af3a095bb7a7b84bd1a746d3e86e12f469d1b4fa7b84bd1a746
  | 5, 1, 13 => 0xd3dc25ecd579d1b4fa5b84bd1a746d3dc25ef5579d1b4f7097a34e82760069ee12f469c1401a7b85151a745d3dc280f4579d1b037097bd15e746d3dc25e8d421d1801a7979d07a175b84bde8ce579d1b4f8cb84bd1a746d3dfe5ef4579d1b3b2f7a2bd527460069ee12f4693174f7097bd15e756
  | 5, 1, 14 => 0xe9716e12f469d1b4f7097b211a746d3dc25ecd3a18db4f9f97bd15e706d3dc25edf469d1b4f705fabd1a746d3dc25e96469d1b4f7097c791a746b84bdbadb469d1b4f7097a34e85d6e0e9ed12f469d1b4f7097a34e80a60070ee12f469d174f7095bd15e746cddc1e8af3a1adb4f7097a34e86f6
  | 5, 1, 15 => 0xd3dc2692f469d1b4f7099cbd1a746e0e9ee12f469d1b4f7097a34e83f6d3dc25e8d3a149b4f7097bd148746d3dc25f23469d1b4f7097a34e81e6d3e0ee12f469d1801a7b823498235d3ddee12f469d1801a7cecbd1a745d3dc25ed4469d1bb1c1b84bd1a746d3dc25e8d429d1b4f70a4cbd1a746
  | 5, 2, 0 => 0xd3dc25e8d3a0c5b4f7097be55e746d3dc11a7f3a17db4f7097a34e8606b84bda2ce469d1b4f7097a34ee746d3e22e12f469d180170979d07a0b5d3dc25e8d3a1c1b4f7097bd0e8466d3dc1e8bf579d1b032f7a2bce8636b85965ef4579d1b4f7097b351a746d3dc25e8d3a131b4f9fb85251a746
  | 5, 2, 1 => 0xb84be1af44e1d1b4f7097a34e8096d3dc25e8d3a151b4f7097a34e8066b3cbde8af3598db4f2f7a3215e746d3dc25f25469d1b4f7097cbd1a746d3dc25e8d409d180170a74bd1a745d3dcae12f469d1801a797a3498175d3dc25e8d3a19dae12f7a2bce84e6d3dc25e8d3a041b4f7097a34e83d6
  | 5, 2, 2 => 0xd3dc25e8d3a141b8b7097a350e746005c25e8d2602d74f7097a34e82f6d3dc25e8d419d1b4f70a2a34e8636d3dc25e8d3a08d801a7b44bd1a745d3dc1a2bf469d1ba17097bd15e746eae9ee12f469d1b4f79b84bd1a746d3dc25e8d3a02db4f7097a34e8566d3e76e12f469d1b4f9fb84bd1a746
  | 5, 2, 3 => 0xd3e6ae12f469d1b4f7097a34e8436d3dc25e8d3a049b4f7097a34e86b6
  | 6, 0, 0 => 0xebe9ee12f7a2bce8fa7b84bde88d3a16df4f7097bd15e7437bf274f7097abd1a747ec69ee12f7a234e8fa7b84bde8af551d1f4fa5b84bde8af3a3e9ee12f7a2bce82770069ee12f7a2bce0c00d3dc28af4579d1b4f96b84bde8af3a3e9ee12f7a2bd48747d3dc25f2357a34e8fa7b84bdbabd579d1f4f8cb84bde8af3a38034f7097bd15e4c6
  | 6, 0, 1 => 0xd3dc25ef4579d0cafa7b84bde8af3a0e1f4f7097bd1beaf3a3e9ee12f8f3d15e747b84bde8dd6dabce8fa7b84bde8af3a175f4f7097c315e7431b80001a7b84bd1a745e0e9ed12f7a2bce8e00d3dc25f1d469d1b4f7097bd15e74053e9ee12f57a34e84c7d3dc2bb2f7a2bce8fc1d3dc25eaf469d1f4f7097c3de8af3a3f4b4f7097bd158747
  | 6, 0, 2 => 0x69ee12f7a23498c00d3dc25e8d3a0ddb4f83b84bde8af3a38034f707a2bc982360069f3b2f7a2bce8da7b85b25ef4579d1f4f7097bd1a8af3a3f63837097bd15e747d3dc25eaf469d07afa7cbdc25eaf469d1c01a7b84bd1a742c369ee15697bd11a747d3dc25ef46babce8fa7b85265ef4579d1c01a7b84bd5e7415b69ee12f8bbd11a747
  | 6, 0, 3 => 0xe5e9ee12f7a2bce8fa7b84bde8af3a131f4f9fb8525e8af3a3e9ee13497bd15e747d3dc25ef4579d034fa7b84ce5ef4579d1f4f7db84bde8af3a3f074f7097bd15e7470069ee12f77abce8dc9d3dc25ef4579d1c01a7b84bdfc741bb69ee12f7a2bd5c747d3dc25ef4579d05cfa7c7dc25ef46e9d1f4f7097bd1c8af3a3e9ee12f91bd15e747
  | 6, 0, 4 => 0xd3dc25ef4579d020fa7b85265ef4469d1f4f7097bd15e741ebe9ee12f7a2bce86e7d3e7ee12f57a34e8f7097bd1d6af3a1adf4f97b84bde8af3a38034f70579d056236d3dc25ef4579d01ce00d3dc2c32f469d1b4f7097bd15e773a3e9ee12f7a2bce8707d3dc25ef457ab0e8fa7b83d1c0af3a17dc0000d3dc11a7411ae9ee12f7a2e55e747
  | 6, 0, 5 => 0x69f097097a34e8da7b84bde8af3a0d5f4f7097bd1bcaf3a3e9ee12f57a34e8237d3dc25f2f7a2bce8fc9d3dc25ef4469d1f4f7097c29e8af3a3e9ee12f7a2bd38747d3dc2b72f7a2bce8fa7b84be18f4579d1f4f7097abd1a7405be9ee57097bd15e7470069e5ef4579302eda7b84bde8af3a19df4f7097abd1a742b3803a5a7b84bd1a746
  | 6, 0, 6 => 0xd3e5ee12f7a234e8fa7b84bde8af3a159f4f9db84bde8af3a3e9f3f7097bd15e7470069ee0f46a2bce8c00d3cbd5e741585db4f7097c0de8af3a3e9ee12f882bd1a747d3dc25ef4579d012fa7b84bd5e8d3a1adf4f7097bd15e74033e9ee12f7a2bd4c747d3dc25ef4579d08afb3d3dc25ef4579d1c0000d3cbd1a740bae9ee12f57a3506747
  | 6, 0, 7 => 0xdde9ee12f7a2bce8e00b84bde8af2602d801a7b84bd468d3a369ee12f7a2bd067470069ee15197a34e8da7b8515e8af3a18df4f7097bd15e7411b8034f6897bd15e746d3dc25ef67a2bce8e00b85565ef4579d1801a7b84bd5e8d3a369ee12f8eabd1a7470069ee12f7a2dce8dc9d3dc24cf4579d1f4f79b84bde8af3a3e9ee12f7a2bce80b7
  | 6, 0, 8 => 0x2e12f469d016ba7b84bdfcaf3a0ddf4f7097bd1ceaf3a38034f7097b811a746d3dc25eaf469d06ee00b84be1af4579d1b4f7097bd15e742d3e9ee15f97bd15e747d3dc25f147a2bce8e00d3dc25e8d3a18db4f7097c41e8af3a3e9f357097bd15e747d3dc25ef4579d0d6fa7b84bde8af3a141f4f7097be1e8af3a3e9ee12f7a3495e747
  | 6, 0, 9 => 0x69ee12f46a34e8c00d3dc15e8d3a08db4f7097bd15e74003802e12f579d0560b6d3dc25ef4579d0b2fa7b84e65ef4579d1f4f7097c99e8af3a3e9ee12f7a2bce8057d3dc25ef46dabce8e00d3dc25ef4579d1b4f9f97bd15e7431be9ee12f8ebd15e747d3dc25ef4579d026fa797bd1bad7579d1f4f9bb84bde8af3a38034f7097a34fe746
  | 6, 0, 10 => 0xd3dc25ef4579d060fa7b84bde8af3a0ddfa5a7b84bd5e8d3a3e9ee12f883d11a7470069ee12f46a1ce8dc0d3dc25ef4579d1f4f7097bd15e742c3e9ee12f57a34e82b7d3dc25f1b7a2bce8fa7b857a5ef4579d1c01a7b859e5e8d3a30034f7097aa51a746d3dc25ef457a7ce8e00d3dc25e8d3a05d801c5d3dc25e8d3a37274f7097bb95e747
  | 6, 0, 11 => 0xd3dc2c32f7a2bce8fd8e95c25ef4579d1f837097bd15e7435bf3f4f7097bd15e747d3dc2ad2f722bce8fa7b84bde8af3b1d1c01a797abd1a740bb69ee12f7a2bce8617d3dc25ef4579d03efa7c25c25eaf469d1c01a7b83d15e7411b69f1b7097bd15e747d3dc2d12f7a2bce8fa7c0dc25ef4579d1f4f7097c59e8af3a3e9ee110813d15e747
  | 6, 0, 12 => 0xd3dc25ef4579d044fa7b84bd5eaf469d1c01a7cddc1e8af3a369ee12f7a2dd5e7470069ee12f68a34e8da7b84be24f4579d1f4f7097bd15e741b3f4b4f7097bd15e747d3dc25ef4469d0b0fa7b84be1cf4579d1f4f7097bd15e743a38034f7097b751a746d3e0ae12f7a2bce8fa7b859a5ef4579d1f4f7097bd15e742e3e9ee12f7a2bcd6637
  | 6, 0, 13 => 0xd3dc2832f7a2bce8fa7b85825ef4579d1f4f7097bd15e7416be9ee12f57a8d1a7470069e5ef4579d02ec00d3cbe10f4579d1b4f7097be9e8af3a3e9ee15197abd1a747d3e56e12f7a2bce8fd2d3e7ee0f4579d1f4f84b84bde8af3a3ea74f7097bd15e7470069ee1267a2bce8da7b85c25ef4579d1f4f7097bd15e740eb8034f7097a34e85f6
  | 6, 0, 14 => 0xd3dc25f067a2bce8fa7b84bdccaf469d1f4f7097abd1a7f3a3802e12f57a34e80b6d3dc25ef4579d094fa7b84be48f4579d1f4f7097b815e8d3a38034f8ab84bd1a746d3dc25ef4579d0aefa7b84bde8af3a0a1f4f70b0cbde88d3a3e9ee12f57a34e8637d6e9ee12f7a2bce8fa7b84bde8af3a0d1f4f7091bd1c0af3a3e9ee12f7a2bce84b7
  | 6, 0, 15 => 0xd3dc2cf2f57a34e8fd2b84be46f4579d1c01a7b84bd5e7414b0034ef4579d0461760069ee12f772bce8da7b84bde8af3a13df4f7097bd15e7401be9ee12f913d15e747d3dc25eaf54a34e8fa7b84bde8af519d1f4f70a8cbde8af3a3e9ee12f57a34e8177e2e9ee12f57a34e8fa7b84bd5e8d469d1f4f7097bd15e7400be9ee12f7a2bd5e747
  | 6, 1, 0 => 0xd3e3ee12f74abce8fa7b84bde8af3a061fb17097bd15ea93a3f234f7097bd15e747000034f70979d07aba7b84bde8af3f9d1f4f7097bd15e74063802e12f7a2bce80b6d3dc25ef4702bce8fa7c9dc25ef4579d1f4f8497bd15e7431bedf4f7097bd15e7470069ee12f7a284e8da7b854a5ef4579d1f4f7097abd1a873a3e9ee12f7a2bce8637
  | 6, 1, 1 => 0x69ee12f5eabce8dd9d3dc25ef4579d1f4f7097bd15ea23a3e9ee12f7a2bd0e747d3dc2cf2f7a2bce8fd0d3dc25ef4579d1f4f7097bd15ea93a38034f7097bd1b4746d3dc25ef4579d02efa7cfdc1e8e0579d1f8ba7b84bde8af3a3e9ee12f7a2bd1a747d3dc25ef4579e8e8fd8b859e5ef4579d1f4f70a1cbde8af3a3e9ee12f7a2bce8487
  | 6, 1, 2 => 0x702e12f7a2bce8da7b84bde8a9469d1f4f7097bd15e740b3e9ee12f7a2bce8027e3e9ee12f7a2bce8e00ec69ee12f469d1bbba7b84bde8af3a3e9ee12f57a34e85f7005c1e8af3a08c16da7ccdc25ef4579d1f4f7097bd1c08d3a3e9ee12f8abd15e747ec69ee12f7a2bce0fa7b84bda2af469d1c01a7c7dc25e8d3a369e5ef457a8ce8637
  | 6, 1, 3 => 0xd3dc25eeb702bce8f7097c8de8af549d1f4f7097bd15e740a38025ef4579d02e0b6d3dc25f117a2bce8fa7b84bde8af3a045f4f7097bd15e7428be9ee14697bd15e747d3dc25ef4579d0bee000069ee12f4693174f6797bd15e7431b8039ba7b84bd1a746d3dc25ef468abce8fd8d3e7e5ef4579d1c01a7b84be2e8d3a369f157097abd1a747
  | 6, 1, 4 => 0x69ee14997a34e8da7b851e5ef4579d1c01a7b84bd5e741eb5c2c35e97bd15e747d3e2ae12f7a2bce8fa7b84bde8ec579d1f4f70a44bde8af3a3e9ee12f8e3d15e747d3e6ee1677a2bce8e00d3dc25eaf260adb4f70ae4bde8af3a3e9ee12f89bd15e74700606e12f7a2bce8da7b84be58f4579d1f4f7097bd15e74133f4ae12f7a2bce86b7
  | 6, 1, 5 => 0xd3dc28b2f7a2bce8fa7b84bde8af3a0cdc01a7b84bd1a741eb69ee12f7a2bce84d7d3dc25ef4579d040fa7cecbe46f4579d1f4f7097bd15e742f38034f7097a34e84c6007074f7097a34e8c00d3dc25ef4521d1b4f7097bd15e743138034f7097c8d1a746d3dc2852f7a2bce8fa7b84bde8af3d9d1f4f7097bd15e740e3e9ee12f7a2bce8247
  | 6, 1, 6 => 0x742e12f7a2bce8dd0b84be3af4579d1c01a7b84bd1a7405b0034f7097a34e8566ec69ee12f7a2bce8fa7b85ba5ef4579d1f4f80b84bde8af3a38034f9fb84bd1a746e05c25ef4579d0c6fa7b84bde8af3a021fb9a7b84bde8af3a3dc2cf2f7a2bce86b7ea69ee12f7a2bce8fa7b84f25ef4579d1c01a7b84bce83715b613037097bd15e747
  | 6, 1, 7 => 0x37fa7b84bde8af3a38034f7097a34e86b6d3dcee12f7a2bce8e00d3dc25e8d419d1801a7b84bd1a7411b69ee12f8bbd15e747d3dd2e12f7a2bce8fdbd3dc25ef4579d1f4fa1b84bde8af3a3e9f4f7097bd15e747
  | 7, 0, 0 => 0x69ee12f8ebd15e7470069ee12f883d15e7470069ee12f7a2bce86b70069ee12f7a2bce8237000034f7097abd1a7460069ee12f7a2bce80b70069f3f7097bd15e7470069f2f7097bd15e7470069ee12f7a2bce84c7007074f7097bd15e747007274f7097bd15e7470069ee12f91bd15e7470069ee14997bd15e747000034f7097abce82b60000001a7b84bd1a745000034f7097bd15e4c6
  | 7, 0, 1 => 0x69ee16797bd15e7470069ee12f7a2bd527470069ee12f7a2bce81770069ee12f7a2bd1a74700002e12f7a2bce80b60069ee12f7a3815e7470069ee12f7a2bce86370069ee12f7a2bd46747000034f2f7a2bce81760069f097097bd15e7470074b4f7097bd15e7470069ee16197bd15e747000034f707a2bce82360069ee12f7a2bce83770069ee12f7a2bce8587000034f7097bd15e746
  | 7, 0, 2 => 0x69ee12f8bbd15e747007634f7097bd15e7470069ee12f7a2bce85f7
  | 8, 0, 0 => 0x34f7097bd15e746
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]

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
private theorem z3_0 : span (Z 3) 19 0 = true := by decide +kernel

private theorem z3 : span (Z 3) 19 0 = true := z3_0

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
private theorem z4_192 : span (Z 4) 9 192 = true := by decide +kernel

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

private theorem z4_a8 : span (Z 4) 201 0 = true :=
  span_join (f := Z 4) (a := 192) (o := 0) (b := 9) z4_a7 z4_192

private theorem z4 : span (Z 4) 201 0 = true := z4_a8

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
private theorem z5_552 : span (Z 5) 12 552 = true := by decide +kernel

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

private theorem z5_a23 : span (Z 5) 564 0 = true :=
  span_join (f := Z 5) (a := 552) (o := 0) (b := 12) z5_a22 z5_552

private theorem z5 : span (Z 5) 564 0 = true := z5_a23

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
private theorem z6_360 : span (Z 6) 18 360 = true := by decide +kernel

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

private theorem z6_a15 : span (Z 6) 378 0 = true :=
  span_join (f := Z 6) (a := 360) (o := 0) (b := 18) z6_a14 z6_360

private theorem z6 : span (Z 6) 378 0 = true := z6_a15

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

def CG : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩
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

end PEqualNP.Outside.L_meta_12483

theorem PEqualNP.Outside.L_meta_12483 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3937058816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264000 * 2 ^ 32 + 3937058816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  by_cases hs : s ≤ 8
  · exfalso
    obtain ⟨C, hf, hsz, hev⟩ := h
    exact PEqualNP.Outside.L_meta_12483.mainG PEqualNP.Outside.L_meta_12483.noRunFull ⟨C, hf, by omega, hev⟩
  · exact ⟨PEqualNP.Outside.L_meta_12483.CG, PEqualNP.Outside.L_meta_12483.CG_mono, by
      have : PEqualNP.Outside.L_meta_12483.CG.size = 9 := rfl
      omega, PEqualNP.Outside.L_meta_12483.CG_eval⟩
