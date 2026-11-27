import Mathlib.Data.Tree.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10608_aux

open PEqualNP.CircuitLowerBounds

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def isBinOp (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def isNotOp (op : GateOp) : Bool :=
  match op with
  | GateOp.not => true
  | _ => false

def binCount (gs : List Gate) : ℕ :=
  (gs.filter fun g => isBinOp g.op).length

def notCount (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

theorem binCount_nil : binCount [] = 0 := rfl
theorem notCount_nil : notCount [] = 0 := rfl

theorem binCount_cons (g : Gate) (gs : List Gate) :
    binCount (g :: gs) = (isBinOp g.op).toNat + binCount gs := by
  unfold binCount; simp only [List.filter_cons]; cases isBinOp g.op <;> simp [Nat.add_comm]

theorem notCount_cons (g : Gate) (gs : List Gate) :
    notCount (g :: gs) = (isNotOp g.op).toNat + notCount gs := by
  unfold notCount; simp only [List.filter_cons]; cases isNotOp g.op <;> simp [Nat.add_comm]

theorem binCount_append (a b : List Gate) : binCount (a ++ b) = binCount a + binCount b := by
  simp [binCount, List.filter_append]

theorem notCount_append (a b : List Gate) : notCount (a ++ b) = notCount a + notCount b := by
  simp [notCount, List.filter_append]

theorem binCount_add_notCount (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) :
    binCount gs + notCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have hgs := ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    rw [binCount_cons, notCount_cons, List.length_cons]
    rcases hg.1 with h | h | h <;> simp [isBinOp, isNotOp, h] <;> omega

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => if j == k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => if j == k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

theorem cleanG_ok {m : ℕ} {g : Gate} (h : CleanG m g) : Ok g := by
  rcases h with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
  · exact ⟨Or.inr (Or.inr hop), by simp [hin]⟩
  · rcases hop with hop | hop <;> exact ⟨by simp [hop], by simp [hin]⟩

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem cleanL_ok {n : ℕ} {gs : List Gate} (h : CleanL n gs) : ∀ g ∈ gs, Ok g := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hg
  exact cleanG_ok (h p _ (List.getElem?_eq_getElem hp))

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    rename_i j k
    by_cases hjk : j = k
    · simp [hjk] at hg
    · simp [hjk] at hg; subst hg
      exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    rename_i j k
    by_cases hjk : j = k
    · simp [hjk] at hg
    · simp [hjk] at hg; subst hg
      exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    split at hg <;> simp at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    split at hg <;> simp at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; rfl
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c => cases b with
        | inl e => simp [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr j => cases b with
        | inl e => cases e <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr k =>
          have hj : j < w.length := hv (Sum.inr j) (by simp)
          by_cases hjk : j = k
          · subst hjk; simp [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom, hj]
          · simp [simplify, simpAnd, hjk, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c => cases b with
        | inl e => simp [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr j => cases b with
        | inl e => cases e <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr k =>
          have hj : j < w.length := hv (Sum.inr j) (by simp)
          by_cases hjk : j = k
          · subst hjk; simp [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom, hj]
          · simp [simplify, simpOr, hjk, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (gs1 gs2 : List Gate) (acc : List Stat × List Gate) :
    elim n (gs1 ++ gs2) acc = elim n gs2 (elim n gs1 acc) := by
  simp [elim, List.foldl_append]

theorem elim_stat_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Stat, (elim n gs acc).1 = acc.1 ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht, hl⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 :: t, ?_, by simp [hl]⟩
    rw [elim_cons, ht]; simp [elimStep]

theorem elim_stat_getD_lt (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (i : ℕ) (hi : i < acc.1.length) :
    (elim n gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  obtain ⟨t, ht, _⟩ := elim_stat_prefix n gs acc
  rw [ht, List.getD_append _ _ _ _ hi]

theorem binCount_elimStep_le (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binCount (elimStep n acc g).2 ≤ binCount acc.2 + (isBinOp g.op).toNat := by
  simp only [elimStep, binCount_append]
  set r := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
  cases ho : r.1 with
  | none => simp [binCount_nil]
  | some g0 =>
    have hop := simplify_op g.op (n + acc.2.length) _ g0 (by rw [← hr, ho]; rfl)
    simp only [Option.toList_some, binCount_cons, binCount_nil, add_zero, hop]
    exact le_rfl

theorem notCount_elimStep_le (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    notCount (elimStep n acc g).2 ≤ notCount acc.2 + (isNotOp g.op).toNat := by
  simp only [elimStep, notCount_append]
  set r := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
  cases ho : r.1 with
  | none => simp [notCount_nil]
  | some g0 =>
    have hop := simplify_op g.op (n + acc.2.length) _ g0 (by rw [← hr, ho]; rfl)
    simp only [Option.toList_some, notCount_cons, notCount_nil, add_zero, hop]
    exact le_rfl

theorem binCount_elim_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binCount (elim n gs acc).2 ≤ binCount acc.2 + binCount gs := by
  induction gs with
  | nil => intro acc; simp [elim, binCount_nil]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := binCount_elimStep_le n acc g
    rw [elim_cons, binCount_cons]
    omega

theorem notCount_elim_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    notCount (elim n gs acc).2 ≤ notCount acc.2 + notCount gs := by
  induction gs with
  | nil => intro acc; simp [elim, notCount_nil]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := notCount_elimStep_le n acc g
    rw [elim_cons, notCount_cons]
    omega

theorem binCount_elim_drop1 (n : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hbin : isBinOp g.op = true)
    (hdrop : (simplify g.op (n + (elim n pre acc).2.length)
      (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 = none) :
    binCount (elim n (pre ++ g :: post) acc).2 + 1 ≤ binCount acc.2 + binCount (pre ++ g :: post) := by
  rw [elim_append, elim_cons, binCount_append, binCount_cons, hbin]
  have h1 := binCount_elim_le n post (elimStep n (elim n pre acc) g)
  have h2 : binCount (elimStep n (elim n pre acc) g).2 = binCount (elim n pre acc).2 := by
    unfold elimStep; rw [hdrop]; simp
  have h3 := binCount_elim_le n pre acc
  simp only [Bool.toNat_true]
  omega

theorem binCount_elim_drop2 (n : ℕ) (p1 p2 p3 : List Gate) (g1 g2 : Gate)
    (acc : List Stat × List Gate)
    (hb1 : isBinOp g1.op = true) (hb2 : isBinOp g2.op = true)
    (hd1 : (simplify g1.op (n + (elim n p1 acc).2.length)
      (g1.inputs.map fun i => (elim n p1 acc).1.getD i (Sum.inl false))).1 = none)
    (hd2 : (simplify g2.op (n + (elim n (p1 ++ g1 :: p2) acc).2.length)
      (g2.inputs.map fun i => (elim n (p1 ++ g1 :: p2) acc).1.getD i (Sum.inl false))).1 = none) :
    binCount (elim n (p1 ++ g1 :: p2 ++ g2 :: p3) acc).2 + 2 ≤
      binCount acc.2 + binCount (p1 ++ g1 :: p2 ++ g2 :: p3) := by
  have heq : p1 ++ g1 :: p2 ++ g2 :: p3 = (p1 ++ g1 :: p2) ++ g2 :: p3 := by simp
  rw [heq]
  have hdrop1 := binCount_elim_drop1 n p1 p2 g1 acc hb1 hd1
  rw [elim_append, elim_cons, binCount_append, binCount_cons, hb2]
  have hpost := binCount_elim_le n p3 (elimStep n (elim n (p1 ++ g1 :: p2) acc) g2)
  have hstep2 : binCount (elimStep n (elim n (p1 ++ g1 :: p2) acc) g2).2 =
      binCount (elim n (p1 ++ g1 :: p2) acc).2 := by
    unfold elimStep; rw [hd2]; simp
  simp only [Bool.toNat_true]
  omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem split_at_two {α : Type} (gs : List α) {p1 p2 : ℕ} {g1 g2 : α}
    (h1 : gs[p1]? = some g1) (h2 : gs[p2]? = some g2) (hlt : p1 < p2) :
    ∃ a b c, gs = a ++ g1 :: b ++ g2 :: c ∧ a.length = p1 ∧ (a ++ g1 :: b).length = p2 := by
  obtain ⟨a, rest, hgs, ha⟩ := split_at gs p1 g1 h1
  have h2' : rest[p2 - p1 - 1]? = some g2 := by
    rw [hgs, List.getElem?_append_right (by omega)] at h2
    have : p2 - a.length = (p2 - p1 - 1) + 1 := by omega
    rw [this] at h2
    exact h2
  obtain ⟨b, c, hrest, hb⟩ := split_at rest (p2 - p1 - 1) g2 h2'
  refine ⟨a, b, c, ?_, ha, by simp [ha, hb]; omega⟩
  rw [hgs, hrest]; simp

theorem not_unique {gs : List Gate} (hn : notCount gs ≤ 1) {p1 p2 : ℕ} {g1 g2 : Gate}
    (h1 : gs[p1]? = some g1) (h2 : gs[p2]? = some g2)
    (ho1 : g1.op = GateOp.not) (ho2 : g2.op = GateOp.not) : p1 = p2 := by
  by_contra hne
  wlog hlt : p1 < p2 generalizing p1 p2 g1 g2
  · exact this h2 h1 ho2 ho1 (Ne.symm hne) (by omega)
  obtain ⟨a, b, c, hgs, _, _⟩ := split_at_two gs h1 h2 hlt
  rw [hgs, notCount_append, notCount_cons, notCount_append, notCount_cons,
    ho1, ho2] at hn
  simp only [isNotOp, Bool.toNat_true] at hn
  omega

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

def Has1NotBin (n : ℕ) (f : BFn n) (b : ℕ) : Prop :=
  ∃ gs o, CleanL n gs ∧ binCount gs ≤ b ∧ notCount gs ≤ 1 ∧ o < n + gs.length ∧
    ∀ x, val gs n o x = f x

def NonConst {n : ℕ} (f : BFn n) : Prop := ∃ y y', f y ≠ f y'

def Depends {n : ℕ} (f : BFn n) (i : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true)

def insFin {n : ℕ} (i : Fin (n + 1)) (b0 : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun j => if h1 : j.val < i.val then y ⟨j.val, by omega⟩
    else if h2 : j.val = i.val then b0
    else y ⟨j.val - 1, by omega⟩

def restrict {n : ℕ} (i : Fin (n + 1)) (b0 : Bool) (f : BFn (n + 1)) : BFn n :=
  fun y => f (insFin i b0 y)

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr i.val

def initRest (n : ℕ) (i : Fin (n + 1)) (b0 : Bool) : List Stat :=
  List.ofFn fun j : Fin (n + 1) =>
    if j.val < i.val then Sum.inr j.val
    else if j.val = i.val then Sum.inl b0
    else Sum.inr (j.val - 1)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem inv_initRest (n : ℕ) (i : Fin (n + 1)) (b0 : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (insFin i b0 y)) (initRest n i b0, []) := by
  refine ⟨by simp [initRest], ?_⟩
  intro j
  by_cases hlt : j < n + 1
  · simp only [initRest, List.length_nil, add_zero, wiresFrom, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_ofFn, insFin]
    split_ifs with h1 h2
    · exact ⟨by simp [statValid]; omega, by simp [statVal, show j < n by omega]⟩
    · exact ⟨trivial, rfl⟩
    · exact ⟨by simp [statValid]; omega, by simp [statVal, show j - 1 < n by omega]⟩
  · rw [List.getD_eq_default _ _ (by simp [initRest]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem of_raw_1not (n : ℕ) (f : BFn n) (hnc : NonConst f)
    (gates : List Gate) (o : ℕ) (hok : ∀ g ∈ gates, Ok g)
    (hnot : notCount gates ≤ 1) (heval : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    Has1NotBin n f (binCount gates) := by
  set acc := elim n gates (initId n, []) with hacc
  have hinv : ∀ y, Inv n (List.ofFn y) (wiresFrom gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) gates _ _ hok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n gates (initId n, []) hok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hb := binCount_elim_le n gates (initId n, [])
  have hn := notCount_elim_le n gates (initId n, [])
  rw [binCount_nil, zero_add] at hb
  rw [notCount_nil, zero_add] at hn
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 o).2
    have e2 := ((hinv y').2 o).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom gates (List.ofFn y)).getD o false = f y := heval y
    have h2 : (wiresFrom gates (List.ofFn y')).getD o false = f y' := heval y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    obtain ⟨y, _, _⟩ := hnc
    have hj := ((hinv y).2 o).1
    rw [hst] at hj
    refine ⟨acc.2, j, hcl, by rw [hacc]; exact hb, by rw [hacc]; omega, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 o).2
    rw [hst] at e1
    exact e1.trans (heval x)

theorem perm_has1NotBin {n : ℕ} {f g : BFn n} {b : ℕ} (p : Fin n → Fin n)
    (heq : ∀ x, f (fun i => x (p i)) = g x) (hnc : NonConst g)
    (h : Has1NotBin n f b) : Has1NotBin n g b := by
  obtain ⟨gs, o, hcl, hb, hn, _, hev⟩ := h
  let initP : List Stat := List.ofFn fun i : Fin n => Sum.inr (p i).val
  set acc := elim n gs (initP, []) with hacc
  have hinv0 : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (List.ofFn (fun i => y (p i))) (initP, []) := by
    intro y
    refine ⟨by simp [initP], ?_⟩
    intro i
    by_cases hlt : i < n
    · simp [initP, hlt, statValid, statVal, wiresFrom, (p ⟨i, hlt⟩).isLt]
    · rw [List.getD_eq_default _ _ (by simp [initP]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y, Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (fun i => y (p i)))) acc :=
    fun y => inv_elim n _ (by simp) gs _ _ (cleanL_ok hcl) (hinv0 y)
  have hcl' : CleanL n acc.2 := by
    apply elim_clean n gs (initP, []) (cleanL_ok hcl)
    · intro i
      by_cases hlt : i < n
      · simp [initP, hlt, statValid, (p ⟨i, hlt⟩).isLt]
      · rw [List.getD_eq_default _ _ (by simp [initP]; omega)]; trivial
    · intro q g' hq; simp at hq
  have hb' := binCount_elim_le n gs (initP, [])
  have hn' := notCount_elim_le n gs (initP, [])
  rw [binCount_nil, zero_add] at hb'
  rw [notCount_nil, zero_add] at hn'
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 o).2
    have e2 := ((hinv y').2 o).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom gs (List.ofFn fun i => y (p i))).getD o false = g y :=
      (hev _).trans (heq y)
    have h2 : (wiresFrom gs (List.ofFn fun i => y' (p i))).getD o false = g y' :=
      (hev _).trans (heq y')
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    obtain ⟨y, _, _⟩ := hnc
    have hj := ((hinv y).2 o).1
    rw [hst] at hj
    refine ⟨acc.2, j, hcl', by rw [hacc]; omega, by rw [hacc]; omega, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 o).2
    rw [hst] at e1
    exact e1.trans ((hev _).trans (heq x))

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

theorem val_eq_of_not_reach {n : ℕ} {gs : List Gate} {o : ℕ} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (hagree : ∀ i : Fin n, Reach n gs o i.val → x i = y i) :
    ∀ a, a < n + gs.length → Reach n gs o a → val gs n a x = val gs n a y := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro hlt hr
    by_cases han : a < n
    · have h1 := val_input gs n ⟨a, han⟩
      have hx := congrFun h1 x
      have hy := congrFun h1 y
      simpa [hx, hy] using hagree ⟨a, han⟩ hr
    · set p := a - n with hp_def
      have hp : p < gs.length := by omega
      have ha_eq : a = n + p := by omega
      rw [ha_eq] at hr ⊢
      have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
      have hglt := cleanG_lt (hcl p gs[p] hg)
      rw [val_gate n gs p gs[p] hg hglt x, val_gate n gs p gs[p] hg hglt y]
      congr 1
      apply List.map_congr_left
      intro u hu
      exact ih u (by have := hglt u hu; omega) (by have := hglt u hu; omega) (reach_step hg hr hu)

theorem reach_of_depends {n : ℕ} {gs : List Gate} {o : ℕ} (hcl : CleanL n gs)
    (ho : o < n + gs.length) {f : BFn n} (hev : ∀ x, val gs n o x = f x)
    {i : Fin n} (hdep : Depends f i) : Reach n gs o i.val := by
  by_contra hnr
  obtain ⟨x, hne⟩ := hdep
  apply hne
  rw [← hev, ← hev]
  apply val_eq_of_not_reach hcl _ _ _ o ho (reach_self n gs o)
  intro j hrj
  have hji : j ≠ i := fun h => hnr (h ▸ hrj)
  simp [Function.update, hji]

theorem elim_stat_at {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    (elim n gs (init, [])).1.getD (m + p) (Sum.inl false) =
      (simplify g.op (n + (elim n (gs.take p) (init, [])).2.length)
        (g.inputs.map fun u => (elim n (gs.take p) (init, [])).1.getD u (Sum.inl false))).2 := by
  obtain ⟨pre, post, hgs, hpre⟩ := split_at gs p g hp
  have htake : gs.take p = pre := by rw [hgs, List.take_left' hpre]
  rw [htake]
  have heq : gs = pre ++ g :: post := hgs
  conv_lhs => rw [heq, elim_append, elim_cons]
  obtain ⟨t1, ht1, hl1⟩ := elim_stat_prefix n pre (init, [])
  have hlen1 : (elim n pre (init, [])).1.length = m + p := by rw [ht1]; simp [hinit, hl1, hpre]
  have hlen2 : (elimStep n (elim n pre (init, [])) g).1.length = m + p + 1 := by
    simp [elimStep, hlen1]
  rw [elim_stat_getD_lt n post _ (m + p) (by omega)]
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hlen1]

theorem elim_stat_at_lt {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (p u : ℕ) (hu : u < m + p) :
    (elim n (gs.take p) (init, [])).1.getD u (Sum.inl false) =
      (elim n gs (init, [])).1.getD u (Sum.inl false) := by
  have heq : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  conv_rhs => rw [heq, elim_append]
  obtain ⟨t, ht, hl⟩ := elim_stat_prefix n (gs.take p) (init, [])
  by_cases hp : p ≤ gs.length
  · have hlen : (elim n (gs.take p) (init, [])).1.length = m + p := by
      rw [ht]; simp [hinit, hl, Nat.min_eq_left hp]
    exact (elim_stat_getD_lt n (gs.drop p) _ u (by omega)).symm
  · have : gs.drop p = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; simp [elim]

theorem const_reach_hits_bin {n m : ℕ} {gs : List Gate} {o : ℕ} (hcl : CleanL m gs)
    (init : List Stat) (hinit : init.length = m)
    (ho : ∃ j, (elim n gs (init, [])).1.getD o (Sum.inl false) = Sum.inr j)
    {w : ℕ} (hr : Reach m gs o w)
    (hw : ∃ c, (elim n gs (init, [])).1.getD w (Sum.inl false) = Sum.inl c) :
    ∃ p g, gs[p]? = some g ∧ Reach m gs o (m + p) ∧ isBinOp g.op = true ∧
      (∃ u ∈ g.inputs, ∃ c, (elim n gs (init, [])).1.getD u (Sum.inl false) = Sum.inl c) ∧
      (∃ j, (elim n gs (init, [])).1.getD (m + p) (Sum.inl false) = Sum.inr j) ∧
      w < m + p := by
  set st := (elim n gs (init, [])).1 with hst
  have key : ∀ a, Reach m gs o a →
      Reach m gs o a ∧ ((∃ c, st.getD a (Sum.inl false) = Sum.inl c) →
        ∃ p g, gs[p]? = some g ∧ Reach m gs o (m + p) ∧ isBinOp g.op = true ∧
          (∃ u ∈ g.inputs, ∃ c, st.getD u (Sum.inl false) = Sum.inl c) ∧
          (∃ j, st.getD (m + p) (Sum.inl false) = Sum.inr j) ∧ a < m + p) := by
    intro a hra
    apply hra (fun x => Reach m gs o x ∧ ((∃ c, st.getD x (Sum.inl false) = Sum.inl c) →
        ∃ p g, gs[p]? = some g ∧ Reach m gs o (m + p) ∧ isBinOp g.op = true ∧
          (∃ u ∈ g.inputs, ∃ c, st.getD u (Sum.inl false) = Sum.inl c) ∧
          (∃ j, st.getD (m + p) (Sum.inl false) = Sum.inr j) ∧ x < m + p))
    · refine ⟨reach_self m gs o, ?_⟩
      rintro ⟨c, hc⟩
      obtain ⟨j, hj⟩ := ho
      rw [hc] at hj; cases hj
    · intro q g hq ⟨hrq, ih⟩ u hu
      refine ⟨reach_step hq hrq hu, ?_⟩
      rintro ⟨cu, hcu⟩
      have hult : u < m + q := cleanG_lt (hcl q g hq) u hu
      cases hqst : st.getD (m + q) (Sum.inl false) with
      | inl cq =>
        obtain ⟨p, g', hp, hrp, hbin, hin, hj, hlt⟩ := ih ⟨cq, hqst⟩
        exact ⟨p, g', hp, hrp, hbin, hin, hj, by omega⟩
      | inr jq =>
        have hbin : isBinOp g.op = true := by
          rcases hcl q g hq with ⟨hop, j0, _, hinp⟩ | ⟨hop, _, _, _, _, _, _⟩
          · exfalso
            have e1 := elim_stat_at (n := n) gs init hinit q g hq
            rw [← hst, hqst, hop, hinp] at e1
            simp only [List.map_cons, List.map_nil, simplify] at e1
            have hu_eq : u = j0 := by simp [hinp] at hu; exact hu
            subst hu_eq
            rw [elim_stat_at_lt (n := n) gs init hinit q u hult, ← hst, hcu] at e1
            simp [simpNot] at e1
          · rcases hop with hop | hop <;> simp [isBinOp, hop]
        exact ⟨q, g, hq, hrq, hbin, ⟨u, hu, cu, hcu⟩, ⟨jq, hqst⟩, hult⟩
  exact (key w hr).2 hw

theorem simplify_bin_none_of_inl {m m' : ℕ} {g : Gate} (hc : CleanG m' g) (hbin : isBinOp g.op = true)
    (f : ℕ → Stat) (u : ℕ) (hu : u ∈ g.inputs) (c : Bool) (hcu : f u = Sum.inl c) :
    (simplify g.op m (g.inputs.map f)).1 = none := by
  rcases hc with ⟨hop, _, _, _⟩ | ⟨hop, j, k, _, _, _, hinp⟩
  · simp [hop, isBinOp] at hbin
  · rw [hinp] at hu ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hop with hop | hop <;> rw [hop] <;> simp only [simplify, List.map_cons, List.map_nil]
    · rcases hu with rfl | rfl
      · rw [hcu]; cases f k <;> simp [simpAnd]
      · rw [hcu]; cases f j <;> simp [simpAnd]
    · rcases hu with rfl | rfl
      · rw [hcu]; cases f k <;> simp [simpOr]
      · rw [hcu]; cases f j <;> simp [simpOr]

theorem restrict_elim_setup {n : ℕ} {f : BFn (n + 1)} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x, val gs (n + 1) o x = f x)
    (i : Fin (n + 1)) (b0 : Bool) (hnc : NonConst (restrict i b0 f)) :
    let acc := elim n gs (initRest n i b0, [])
    CleanL n acc.2 ∧ notCount acc.2 ≤ notCount gs ∧
      ∃ jo, acc.1.getD o (Sum.inl false) = Sum.inr jo ∧ jo < n + acc.2.length ∧
        ∀ x, val acc.2 n jo x = restrict i b0 f x := by
  set init := initRest n i b0 with hinit_def
  set acc := elim n gs (init, []) with hacc
  have hinv : ∀ y, Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (insFin i b0 y))) acc :=
    fun y => inv_elim n _ (by simp) gs _ _ (cleanL_ok hcl) (inv_initRest n i b0 y)
  have hcl' : CleanL n acc.2 := by
    apply elim_clean n gs (init, []) (cleanL_ok hcl)
    · intro j
      by_cases hlt : j < n + 1
      · simp only [init, initRest, List.length_nil, add_zero]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        by_cases h1 : j < i.val
        · simp [h1, statValid]; omega
        · by_cases h2 : j = i.val
          · simp [h2, statValid]
          · simp [h1, h2, statValid]; omega
      · rw [List.getD_eq_default _ _ (by simp [init, initRest]; omega)]; trivial
    · intro p g hp; simp at hp
  have hn' := notCount_elim_le n gs (init, [])
  rw [notCount_nil, zero_add] at hn'
  cases hso : acc.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 o).2
    have e2 := ((hinv y').2 o).2
    rw [hso] at e1 e2
    have h1 : val gs (n + 1) o (insFin i b0 y) = restrict i b0 f y := hev _
    have h2 : val gs (n + 1) o (insFin i b0 y') = restrict i b0 f y' := hev _
    unfold val at h1 h2
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr jo =>
    obtain ⟨y, _, _⟩ := hnc
    have hjo_lt := ((hinv y).2 o).1
    rw [hso] at hjo_lt
    refine ⟨hcl', hn', jo, hso, hjo_lt, ?_⟩
    intro x
    have e1 := ((hinv x).2 o).2
    rw [hso] at e1
    exact e1.trans (hev (insFin i b0 x))

theorem has1NotBin_of_two_drops {n : ℕ} {f : BFn (n + 1)} {b : ℕ} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hb : binCount gs ≤ b) (hn : notCount gs ≤ 1)
    (hev : ∀ x, val gs (n + 1) o x = f x) (i : Fin (n + 1)) (b0 : Bool)
    (hnc : NonConst (restrict i b0 f))
    {p1 p2 : ℕ} {g1 g2 : Gate} (hlt : p1 < p2)
    (hp1 : gs[p1]? = some g1) (hp2 : gs[p2]? = some g2)
    (hb1 : isBinOp g1.op = true) (hb2 : isBinOp g2.op = true)
    (hu1 : ∃ u ∈ g1.inputs, ∃ c, (elim n gs (initRest n i b0, [])).1.getD u (Sum.inl false) = Sum.inl c)
    (hu2 : ∃ u ∈ g2.inputs, ∃ c, (elim n gs (initRest n i b0, [])).1.getD u (Sum.inl false) = Sum.inl c) :
    2 ≤ b ∧ Has1NotBin n (restrict i b0 f) (b - 2) := by
  set init := initRest n i b0
  have hinit_len : init.length = n + 1 := by simp [init, initRest]
  obtain ⟨hcl', hn', jo, _, hjo_lt, hev'⟩ := restrict_elim_setup hcl hev i b0 hnc
  obtain ⟨a, d, c, hgs, ha, had⟩ := split_at_two gs hp1 hp2 hlt
  have ht1 : gs.take p1 = a := by
    have hgs1 : gs = a ++ (g1 :: (d ++ g2 :: c)) := by simpa [List.append_assoc] using hgs
    rw [hgs1, List.take_left' ha]
  have ht2 : gs.take p2 = a ++ g1 :: d := by
    have hgs2 : gs = (a ++ g1 :: d) ++ g2 :: c := by simpa [List.append_assoc] using hgs
    rw [hgs2, List.take_left' had]
  obtain ⟨u1, h1m, c1, hc1⟩ := hu1
  obtain ⟨u2, h2m, c2, hc2⟩ := hu2
  have hd1 : (simplify g1.op (n + (elim n a (init, [])).2.length)
      (g1.inputs.map fun x => (elim n a (init, [])).1.getD x (Sum.inl false))).1 = none := by
    have hcu : (elim n a (init, [])).1.getD u1 (Sum.inl false) = Sum.inl c1 := by
      rw [← ht1, elim_stat_at_lt (n := n) gs init hinit_len p1 u1 (cleanG_lt (hcl p1 g1 hp1) u1 h1m)]
      exact hc1
    exact simplify_bin_none_of_inl (hcl p1 g1 hp1) hb1 _ u1 h1m c1 hcu
  have hd2 : (simplify g2.op (n + (elim n (a ++ g1 :: d) (init, [])).2.length)
      (g2.inputs.map fun x => (elim n (a ++ g1 :: d) (init, [])).1.getD x (Sum.inl false))).1 = none := by
    have hcu : (elim n (a ++ g1 :: d) (init, [])).1.getD u2 (Sum.inl false) = Sum.inl c2 := by
      rw [← ht2, elim_stat_at_lt (n := n) gs init hinit_len p2 u2 (cleanG_lt (hcl p2 g2 hp2) u2 h2m)]
      exact hc2
    exact simplify_bin_none_of_inl (hcl p2 g2 hp2) hb2 _ u2 h2m c2 hcu
  have hdrop := binCount_elim_drop2 n a d c g1 g2 (init, []) hb1 hb2 hd1 hd2
  rw [← hgs, binCount_nil, zero_add] at hdrop
  exact ⟨by omega, (elim n gs (init, [])).2, jo, hcl', by omega, le_trans hn' hn, hjo_lt, hev'⟩

theorem elim_one {n : ℕ} {f : BFn (n + 1)} {b : ℕ} (i : Fin (n + 1)) (b0 : Bool)
    (hdep : Depends f i) (hnc : NonConst (restrict i b0 f)) (h : Has1NotBin (n + 1) f b) :
    1 ≤ b ∧ Has1NotBin n (restrict i b0 f) (b - 1) := by
  obtain ⟨gs, o, hcl, hb, hn, ho, hev⟩ := h
  set init := initRest n i b0
  have hinit_len : init.length = n + 1 := by simp [init, initRest]
  obtain ⟨hcl', hn', jo, hjo, hjo_lt, hev'⟩ := restrict_elim_setup hcl hev i b0 hnc
  have hri : Reach (n + 1) gs o i.val := reach_of_depends hcl ho hev hdep
  have hsti : (elim n gs (init, [])).1.getD i.val (Sum.inl false) = Sum.inl b0 := by
    rw [elim_stat_getD_lt n gs (init, []) i.val (by simp [init, initRest]; omega)]
    simp only [init, initRest]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]; simp
  obtain ⟨p, g, hp, _, hbin, ⟨u, hu, cu, hcu⟩, _, _⟩ :=
    const_reach_hits_bin hcl init hinit_len ⟨jo, hjo⟩ hri ⟨b0, hsti⟩
  obtain ⟨pre, post, hgs, hpre⟩ := split_at gs p g hp
  have htake : gs.take p = pre := by rw [hgs, List.take_left' hpre]
  have hdrop : (simplify g.op (n + (elim n pre (init, [])).2.length)
      (g.inputs.map fun a => (elim n pre (init, [])).1.getD a (Sum.inl false))).1 = none := by
    have hcu' : (elim n pre (init, [])).1.getD u (Sum.inl false) = Sum.inl cu := by
      rw [← htake, elim_stat_at_lt (n := n) gs init hinit_len p u (cleanG_lt (hcl p g hp) u hu)]
      exact hcu
    exact simplify_bin_none_of_inl (hcl p g hp) hbin _ u hu cu hcu'
  have hb_drop := binCount_elim_drop1 n pre post g (init, []) hbin hdrop
  rw [← hgs, binCount_nil, zero_add] at hb_drop
  exact ⟨by omega, (elim n gs (init, [])).2, jo, hcl', by omega, le_trans hn' hn, hjo_lt, hev'⟩

def OnceProp (n : ℕ) (gs : List Gate) (o : ℕ) (w : ℕ) : Prop :=
  ((∀ p g, gs[p]? = some g → Reach n gs o (n + p) → w ∈ g.inputs → g.op = GateOp.or) ∧
   (∀ p1 g1 p2 g2, gs[p1]? = some g1 → gs[p2]? = some g2 →
     Reach n gs o (n + p1) → Reach n gs o (n + p2) → w ∈ g1.inputs → w ∈ g2.inputs → p1 = p2)) ∨
  (∃ q, gs[q]? = some ⟨GateOp.not, [w]⟩ ∧ Reach n gs o (n + q) ∧
    (∀ p g, gs[p]? = some g → Reach n gs o (n + p) → w ∈ g.inputs → p = q) ∧
    (∀ p g, gs[p]? = some g → Reach n gs o (n + p) → n + q ∈ g.inputs → g.op = GateOp.and) ∧
    (∀ p1 g1 p2 g2, gs[p1]? = some g1 → gs[p2]? = some g2 →
      Reach n gs o (n + p1) → Reach n gs o (n + p2) →
      n + q ∈ g1.inputs → n + q ∈ g2.inputs → p1 = p2))

theorem two_drops_of_absorbed {n : ℕ} {f : BFn (n + 1)} {b : ℕ} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hb : binCount gs ≤ b) (hn : notCount gs ≤ 1)
    (hev : ∀ x, val gs (n + 1) o x = f x) (i : Fin (n + 1)) (b0 : Bool)
    (hnc : NonConst (restrict i b0 f))
    {p : ℕ} {g : Gate} (hp : gs[p]? = some g) (hrp : Reach (n + 1) gs o (n + 1 + p))
    (hbin : isBinOp g.op = true)
    (hu : ∃ u ∈ g.inputs, ∃ c, (elim n gs (initRest n i b0, [])).1.getD u (Sum.inl false) = Sum.inl c)
    (hout : ∃ c, (elim n gs (initRest n i b0, [])).1.getD (n + 1 + p) (Sum.inl false) = Sum.inl c) :
    2 ≤ b ∧ Has1NotBin n (restrict i b0 f) (b - 2) := by
  set init := initRest n i b0
  have hinit_len : init.length = n + 1 := by simp [init, initRest]
  obtain ⟨_, _, jo, hjo, _, _⟩ := restrict_elim_setup hcl hev i b0 hnc
  obtain ⟨q, gq, hq, _, hbinq, huq, _, hlt⟩ :=
    const_reach_hits_bin hcl init hinit_len ⟨jo, hjo⟩ hrp hout
  exact has1NotBin_of_two_drops hcl hb hn hev i b0 hnc (by omega) hp hq hbin hbinq hu huq

theorem stat_of_not_gate {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (q w : ℕ) (hq : gs[q]? = some ⟨GateOp.not, [w]⟩) (hwlt : w < m + q) (c : Bool)
    (hw : (elim n gs (init, [])).1.getD w (Sum.inl false) = Sum.inl c) :
    (elim n gs (init, [])).1.getD (m + q) (Sum.inl false) = Sum.inl (!c) := by
  rw [elim_stat_at (n := n) gs init hinit q _ hq]
  simp only [List.map_cons, List.map_nil, simplify]
  rw [elim_stat_at_lt (n := n) gs init hinit q w hwlt, hw]
  rfl

theorem stat_of_and_false {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : CleanG (m + p) g) (hop : g.op = GateOp.and)
    (u : ℕ) (hu : u ∈ g.inputs)
    (hcu : (elim n gs (init, [])).1.getD u (Sum.inl false) = Sum.inl false) :
    (elim n gs (init, [])).1.getD (m + p) (Sum.inl false) = Sum.inl false := by
  rw [elim_stat_at (n := n) gs init hinit p g hp]
  rcases hc with ⟨hno, _, _, _⟩ | ⟨_, j, k, hj, hk, _, hinp⟩
  · rw [hop] at hno; cases hno
  · rw [hinp] at hu
    rw [hop, hinp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    simp only [simplify, List.map_cons, List.map_nil]
    rw [elim_stat_at_lt (n := n) gs init hinit p j hj, elim_stat_at_lt (n := n) gs init hinit p k hk]
    rcases hu with rfl | rfl
    · rw [hcu]; cases (elim n gs (init, [])).1.getD k (Sum.inl false) <;> simp [simpAnd]
    · rw [hcu]; cases (elim n gs (init, [])).1.getD j (Sum.inl false) <;> simp [simpAnd]

theorem stat_of_or_true {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : CleanG (m + p) g) (hop : g.op = GateOp.or)
    (u : ℕ) (hu : u ∈ g.inputs)
    (hcu : (elim n gs (init, [])).1.getD u (Sum.inl false) = Sum.inl true) :
    (elim n gs (init, [])).1.getD (m + p) (Sum.inl false) = Sum.inl true := by
  rw [elim_stat_at (n := n) gs init hinit p g hp]
  rcases hc with ⟨hno, _, _, _⟩ | ⟨_, j, k, hj, hk, _, hinp⟩
  · rw [hop] at hno; cases hno
  · rw [hinp] at hu
    rw [hop, hinp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    simp only [simplify, List.map_cons, List.map_nil]
    rw [elim_stat_at_lt (n := n) gs init hinit p j hj, elim_stat_at_lt (n := n) gs init hinit p k hk]
    rcases hu with rfl | rfl
    · rw [hcu]; cases (elim n gs (init, [])).1.getD k (Sum.inl false) <;> simp [simpOr]
    · rw [hcu]; cases (elim n gs (init, [])).1.getD j (Sum.inl false) <;> simp [simpOr]

theorem stat_of_both_inl {n m : ℕ} (gs : List Gate) (init : List Stat) (hinit : init.length = m)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : CleanG (m + p) g) (hbin : isBinOp g.op = true)
    (u v : ℕ) (huv : u ≠ v) (hu : u ∈ g.inputs) (hv : v ∈ g.inputs) (cu cv : Bool)
    (hcu : (elim n gs (init, [])).1.getD u (Sum.inl false) = Sum.inl cu)
    (hcv : (elim n gs (init, [])).1.getD v (Sum.inl false) = Sum.inl cv) :
    ∃ c, (elim n gs (init, [])).1.getD (m + p) (Sum.inl false) = Sum.inl c := by
  rw [elim_stat_at (n := n) gs init hinit p g hp]
  rcases hc with ⟨hno, _, _, _⟩ | ⟨hop, j, k, hj, hk, _, hinp⟩
  · simp [hno, isBinOp] at hbin
  · rw [hinp] at hu hv ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    have hjk : (u = j ∧ v = k) ∨ (u = k ∧ v = j) := by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl huv
    rcases hop with hop | hop <;> rw [hop] <;> simp only [simplify, List.map_cons, List.map_nil] <;>
      rw [elim_stat_at_lt (n := n) gs init hinit p j hj, elim_stat_at_lt (n := n) gs init hinit p k hk] <;>
      rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hcu, hcv]
    · exact ⟨cu && cv, rfl⟩
    · exact ⟨cv && cu, rfl⟩
    · exact ⟨cu || cv, rfl⟩
    · exact ⟨cv || cu, rfl⟩

theorem elim_two_or_once {n : ℕ} {f : BFn (n + 1)} {b : ℕ} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hb : binCount gs ≤ b) (hn : notCount gs ≤ 1)
    (ho : o < n + 1 + gs.length) (hev : ∀ x, val gs (n + 1) o x = f x)
    (i : Fin (n + 1)) (hdep : Depends f i)
    (hnc0 : NonConst (restrict i false f)) (hnc1 : NonConst (restrict i true f)) :
    (2 ≤ b ∧ Has1NotBin n (restrict i false f) (b - 2)) ∨
    (OnceProp (n + 1) gs o i.val ∧ 2 ≤ b ∧ Has1NotBin n (restrict i true f) (b - 2)) := by
  set init0 := initRest n i false
  set init1 := initRest n i true
  have hlen0 : init0.length = n + 1 := by simp [init0, initRest]
  have hlen1 : init1.length = n + 1 := by simp [init1, initRest]
  have hsti0 : (elim n gs (init0, [])).1.getD i.val (Sum.inl false) = Sum.inl false := by
    rw [elim_stat_getD_lt n gs (init0, []) i.val (by simp [init0, initRest]; omega)]
    simp only [init0, initRest]; rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]; simp
  have hsti1 : (elim n gs (init1, [])).1.getD i.val (Sum.inl false) = Sum.inl true := by
    rw [elim_stat_getD_lt n gs (init1, []) i.val (by simp [init1, initRest]; omega)]
    simp only [init1, initRest]; rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]; simp
  have hri : Reach (n + 1) gs o i.val := reach_of_depends hcl ho hev hdep
  have hio : i.val ≠ o := by
    intro heq
    obtain ⟨y, y', hne⟩ := hnc0
    apply hne
    have h1 := hev (insFin i false y)
    have h2 := hev (insFin i false y')
    rw [← heq] at h1 h2
    have hi1 := congrFun (val_input gs (n + 1) i) (insFin i false y)
    have hi2 := congrFun (val_input gs (n + 1) i) (insFin i false y')
    simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
    change f (insFin i false y) = f (insFin i false y')
    rw [← h1, ← h2, hi1, hi2]
  by_cases hexNot : ∃ q, gs[q]? = some ⟨GateOp.not, [i.val]⟩ ∧ Reach (n + 1) gs o (n + 1 + q)
  · obtain ⟨q, hq, hrq⟩ := hexNot
    have hstq0 : (elim n gs (init0, [])).1.getD (n + 1 + q) (Sum.inl false) = Sum.inl true :=
      stat_of_not_gate gs init0 hlen0 q i.val hq (by omega) false hsti0
    have hstq1 : (elim n gs (init1, [])).1.getD (n + 1 + q) (Sum.inl false) = Sum.inl false :=
      stat_of_not_gate gs init1 hlen1 q i.val hq (by omega) true hsti1
    have hqo : n + 1 + q ≠ o := by
      intro heq
      obtain ⟨y, y', hne⟩ := hnc0
      apply hne
      have h1 := hev (insFin i false y)
      have h2 := hev (insFin i false y')
      rw [← heq, val_gate (n + 1) gs q _ hq (cleanG_lt (hcl q _ hq))] at h1 h2
      have hi1 := congrFun (val_input gs (n + 1) i) (insFin i false y)
      have hi2 := congrFun (val_input gs (n + 1) i) (insFin i false y')
      simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at h1 h2
      change f (insFin i false y) = f (insFin i false y')
      rw [← h1, ← h2, hi1, hi2]
    obtain ⟨p0, g0, hp0, hin0, hrp0⟩ : ∃ p0 g0, gs[p0]? = some g0 ∧ n + 1 + q ∈ g0.inputs ∧
        Reach (n + 1) gs o (n + 1 + p0) := by
      rcases reach_cases hrq with h | h
      · exact absurd h hqo
      · exact h
    have hp0_gt : q < p0 := by have := cleanG_lt (hcl p0 g0 hp0) _ hin0; omega
    have hbin_of_ne : ∀ p g, gs[p]? = some g → p ≠ q → isBinOp g.op = true := by
      intro p g hp hne
      rcases hcl p g hp with ⟨hop, _, _, _⟩ | ⟨hop, _, _, _, _, _, _⟩
      · exact absurd (not_unique hn hp hq hop rfl) hne
      · rcases hop with hop | hop <;> simp [isBinOp, hop]
    have hp0_bin : isBinOp g0.op = true := hbin_of_ne p0 g0 hp0 (by omega)
    by_cases hdir : ∃ p g, gs[p]? = some g ∧ Reach (n + 1) gs o (n + 1 + p) ∧ i.val ∈ g.inputs ∧ p ≠ q
    · obtain ⟨p, g, hp, hrp, hinp, hne⟩ := hdir
      have hp_bin : isBinOp g.op = true := hbin_of_ne p g hp hne
      by_cases hpp0 : p = p0
      · subst hpp0
        rw [hp0] at hp; cases hp
        left
        have hboth := stat_of_both_inl gs init0 hlen0 p g0 hp0 (hcl p g0 hp0) hp0_bin
          i.val (n + 1 + q) (by omega) hinp hin0 false true hsti0 hstq0
        exact two_drops_of_absorbed hcl hb hn hev i false hnc0 hp0 hrp0 hp0_bin
          ⟨i.val, hinp, false, hsti0⟩ hboth
      · left
        rcases lt_or_gt_of_ne hpp0 with hlt | hlt
        · exact has1NotBin_of_two_drops hcl hb hn hev i false hnc0 hlt hp hp0 hp_bin hp0_bin
            ⟨i.val, hinp, false, hsti0⟩ ⟨n + 1 + q, hin0, true, hstq0⟩
        · exact has1NotBin_of_two_drops hcl hb hn hev i false hnc0 hlt hp0 hp hp0_bin hp_bin
            ⟨n + 1 + q, hin0, true, hstq0⟩ ⟨i.val, hinp, false, hsti0⟩
    · by_cases htwo : ∃ p1 g1 p2 g2, gs[p1]? = some g1 ∧ gs[p2]? = some g2 ∧
          Reach (n + 1) gs o (n + 1 + p1) ∧ Reach (n + 1) gs o (n + 1 + p2) ∧
          n + 1 + q ∈ g1.inputs ∧ n + 1 + q ∈ g2.inputs ∧ p1 < p2
      · obtain ⟨p1, g1, p2, g2, hp1, hp2, _, _, h1m, h2m, hlt⟩ := htwo
        left
        have hlt1 : q < p1 := by have := cleanG_lt (hcl p1 g1 hp1) _ h1m; omega
        have hlt2 : q < p2 := by omega
        exact has1NotBin_of_two_drops hcl hb hn hev i false hnc0 hlt hp1 hp2
          (hbin_of_ne p1 g1 hp1 (by omega)) (hbin_of_ne p2 g2 hp2 (by omega))
          ⟨n + 1 + q, h1m, true, hstq0⟩ ⟨n + 1 + q, h2m, true, hstq0⟩
      · have huniq_q : ∀ p1 g1 p2 g2, gs[p1]? = some g1 → gs[p2]? = some g2 →
            Reach (n + 1) gs o (n + 1 + p1) → Reach (n + 1) gs o (n + 1 + p2) →
            n + 1 + q ∈ g1.inputs → n + 1 + q ∈ g2.inputs → p1 = p2 := by
          intro p1 g1 p2 g2 hp1 hp2 hr1 hr2 h1m h2m
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact htwo ⟨p1, g1, p2, g2, hp1, hp2, hr1, hr2, h1m, h2m, hlt⟩
          · exact htwo ⟨p2, g2, p1, g1, hp2, hp1, hr2, hr1, h2m, h1m, hlt⟩
        rcases hcl p0 g0 hp0 with ⟨hno, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
        · simp [hno, isBinOp] at hp0_bin
        · right
          refine ⟨Or.inr ⟨q, hq, hrq, ?_, ?_, huniq_q⟩, ?_⟩
          · intro p g hp hrp hin
            by_contra hne; exact hdir ⟨p, g, hp, hrp, hin, hne⟩
          · intro p g hp hrp hin
            have heq := huniq_q p g p0 g0 hp hp0 hrp hrp0 hin hin0
            subst heq; rw [hp0] at hp; cases hp; exact hop
          · have habs := stat_of_and_false gs init1 hlen1 p0 g0 hp0 (hcl p0 g0 hp0) hop
              (n + 1 + q) hin0 hstq1
            exact two_drops_of_absorbed hcl hb hn hev i true hnc1 hp0 hrp0 hp0_bin
              ⟨n + 1 + q, hin0, false, hstq1⟩ ⟨false, habs⟩
        · left
          have habs := stat_of_or_true gs init0 hlen0 p0 g0 hp0 (hcl p0 g0 hp0) hop
            (n + 1 + q) hin0 hstq0
          exact two_drops_of_absorbed hcl hb hn hev i false hnc0 hp0 hrp0 hp0_bin
            ⟨n + 1 + q, hin0, true, hstq0⟩ ⟨true, habs⟩
  · have hbin_dir : ∀ p g, gs[p]? = some g → Reach (n + 1) gs o (n + 1 + p) →
        i.val ∈ g.inputs → isBinOp g.op = true := by
      intro p g hp hrp hin
      rcases hcl p g hp with ⟨hop, j0, _, hinp⟩ | ⟨hop, _, _, _, _, _, _⟩
      · exfalso
        have hj : i.val = j0 := by simp [hinp] at hin; exact hin
        subst hj
        exact hexNot ⟨p, by cases g; simp_all, hrp⟩
      · rcases hop with hop | hop <;> simp [isBinOp, hop]
    obtain ⟨p0, g0, hp0, hin0, hrp0⟩ : ∃ p0 g0, gs[p0]? = some g0 ∧ i.val ∈ g0.inputs ∧
        Reach (n + 1) gs o (n + 1 + p0) := by
      rcases reach_cases hri with h | h
      · exact absurd h hio
      · exact h
    have hp0_bin := hbin_dir p0 g0 hp0 hrp0 hin0
    by_cases htwo : ∃ p1 g1 p2 g2, gs[p1]? = some g1 ∧ gs[p2]? = some g2 ∧
        Reach (n + 1) gs o (n + 1 + p1) ∧ Reach (n + 1) gs o (n + 1 + p2) ∧
        i.val ∈ g1.inputs ∧ i.val ∈ g2.inputs ∧ p1 < p2
    · obtain ⟨p1, g1, p2, g2, hp1, hp2, hr1, hr2, h1m, h2m, hlt⟩ := htwo
      left
      exact has1NotBin_of_two_drops hcl hb hn hev i false hnc0 hlt hp1 hp2
        (hbin_dir p1 g1 hp1 hr1 h1m) (hbin_dir p2 g2 hp2 hr2 h2m)
        ⟨i.val, h1m, false, hsti0⟩ ⟨i.val, h2m, false, hsti0⟩
    · have huniq : ∀ p1 g1 p2 g2, gs[p1]? = some g1 → gs[p2]? = some g2 →
          Reach (n + 1) gs o (n + 1 + p1) → Reach (n + 1) gs o (n + 1 + p2) →
          i.val ∈ g1.inputs → i.val ∈ g2.inputs → p1 = p2 := by
        intro p1 g1 p2 g2 hp1 hp2 hr1 hr2 h1m h2m
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact htwo ⟨p1, g1, p2, g2, hp1, hp2, hr1, hr2, h1m, h2m, hlt⟩
        · exact htwo ⟨p2, g2, p1, g1, hp2, hp1, hr2, hr1, h2m, h1m, hlt⟩
      rcases hcl p0 g0 hp0 with ⟨hno, _, _, _⟩ | ⟨hop | hop, _, _, _, _, _, _⟩
      · simp [hno, isBinOp] at hp0_bin
      · left
        have habs := stat_of_and_false gs init0 hlen0 p0 g0 hp0 (hcl p0 g0 hp0) hop i.val hin0 hsti0
        exact two_drops_of_absorbed hcl hb hn hev i false hnc0 hp0 hrp0 hp0_bin
          ⟨i.val, hin0, false, hsti0⟩ ⟨false, habs⟩
      · right
        refine ⟨Or.inl ⟨?_, huniq⟩, ?_⟩
        · intro p g hp hrp hin
          have heq := huniq p g p0 g0 hp hp0 hrp hrp0 hin hin0
          subst heq; rw [hp0] at hp; cases hp; exact hop
        · have habs := stat_of_or_true gs init1 hlen1 p0 g0 hp0 (hcl p0 g0 hp0) hop i.val hin0 hsti1
          exact two_drops_of_absorbed hcl hb hn hev i true hnc1 hp0 hrp0 hp0_bin
            ⟨i.val, hin0, true, hsti1⟩ ⟨true, habs⟩

def NoFalseTwins {n : ℕ} (f : BFn n) : Prop :=
  ∀ u v : Fin n, u ≠ v → ∃ x : Fin n → Bool,
    f (Function.update (Function.update x u true) v false) ≠
      f (Function.update (Function.update x u false) v true) ∨
    f (Function.update (Function.update x u true) v false) ≠
      f (Function.update (Function.update x u true) v true)

theorem elim_two_no_false_twins {n : ℕ} {f : BFn (n + 1)} {b : ℕ}
    (hall : ∀ i : Fin (n + 1), Depends f i ∧ NonConst (restrict i false f) ∧ NonConst (restrict i true f))
    (hnft : NoFalseTwins f) (h : Has1NotBin (n + 1) f b) :
    ∃ i : Fin (n + 1), 2 ≤ b ∧ Has1NotBin n (restrict i false f) (b - 2) := by
  by_contra hno
  push Not at hno
  obtain ⟨gs, o, hcl, hb, hn, ho, hev⟩ := h
  have honce : ∀ i : Fin (n + 1), OnceProp (n + 1) gs o i.val := by
    intro i
    obtain ⟨hdep, hnc0, hnc1⟩ := hall i
    rcases elim_two_or_once hcl hb hn ho hev i hdep hnc0 hnc1 with hA | ⟨hO, _⟩
    · exact absurd hA.2 (hno i hA.1)
    · exact hO
  have hexBin : ∃ p, ∃ g, gs[p]? = some g ∧ Reach (n + 1) gs o (n + 1 + p) ∧ isBinOp g.op = true := by
    have h0 := hall 0
    have hr0 := reach_of_depends hcl ho hev h0.1
    set init0 := initRest n 0 false
    have hlen0 : init0.length = n + 1 := by simp [init0, initRest]
    obtain ⟨_, _, jo, hjo, _, _⟩ := restrict_elim_setup hcl hev 0 false h0.2.1
    have hst0 : (elim n gs (init0, [])).1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [elim_stat_getD_lt n gs (init0, []) 0 (by simp [init0, initRest])]
      simp only [init0, initRest]; rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; simp
    obtain ⟨p, g, hp, hrp, hbin, _, _, _⟩ :=
      const_reach_hits_bin hcl init0 hlen0 ⟨jo, hjo⟩ hr0 ⟨false, hst0⟩
    exact ⟨p, g, hp, hrp, hbin⟩
  classical
  let p0 := Nat.find hexBin
  obtain ⟨g0, hp0, hrp0, hbin0⟩ := Nat.find_spec hexBin
  have hp0_min : ∀ p g, p < p0 → gs[p]? = some g → Reach (n + 1) gs o (n + 1 + p) →
      isBinOp g.op = false := by
    intro p g hlt hp hrp
    by_contra hnb
    have hbtrue : isBinOp g.op = true := by cases h : isBinOp g.op <;> simp_all
    exact Nat.find_min hexBin hlt ⟨g, hp, hrp, hbtrue⟩
  rcases hcl p0 g0 hp0 with ⟨hno0, _, _, _⟩ | ⟨hop0, j, k, hj, hk, hjk, hin0⟩
  · simp [hno0, isBinOp] at hbin0
  have hwire_not_or_in : ∀ a, a ∈ g0.inputs →
      (a < n + 1 ∧ g0.op = GateOp.or) ∨
      (∃ q w, a = n + 1 + q ∧ gs[q]? = some ⟨GateOp.not, [w]⟩ ∧ g0.op = GateOp.and) := by
    intro a ha
    have halt : a < n + 1 + p0 := cleanG_lt (hcl p0 g0 hp0) a ha
    have hra : Reach (n + 1) gs o a := reach_step hp0 hrp0 ha
    by_cases han : a < n + 1
    · left
      refine ⟨han, ?_⟩
      rcases honce ⟨a, han⟩ with ⟨hor, _⟩ | ⟨q, hq, _, honly, _, _⟩
      · exact hor p0 g0 hp0 hrp0 ha
      · exfalso
        have hpq := honly p0 g0 hp0 hrp0 ha
        subst hpq; rw [hq] at hp0; cases hp0; simp [isBinOp] at hbin0
    · right
      set q := a - (n + 1) with hq_def
      have haeq : a = n + 1 + q := by omega
      have hqlt : q < p0 := by omega
      have hq_len : q < gs.length := by have := (List.getElem?_eq_some_iff.1 hp0).1; omega
      have hqg : gs[q]? = some gs[q] := List.getElem?_eq_getElem hq_len
      rw [haeq] at hra ha
      have hnb := hp0_min q gs[q] hqlt hqg hra
      rcases hcl q gs[q] hqg with ⟨hqop, w, hwlt, hwin⟩ | ⟨hqop, _, _, _, _, _, _⟩
      · have hw_in : w < n + 1 := by
          by_contra hwn
          set q' := w - (n + 1)
          have hweq : w = n + 1 + q' := by omega
          have hq'lt : q' < q := by omega
          have hq'_len : q' < gs.length := by omega
          have hq'g : gs[q']? = some gs[q'] := List.getElem?_eq_getElem hq'_len
          have hrw : Reach (n + 1) gs o (n + 1 + q') := by
            rw [← hweq]; exact reach_step hqg hra (by simp [hwin])
          have hnb' := hp0_min q' gs[q'] (by omega) hq'g hrw
          rcases hcl q' gs[q'] hq'g with ⟨hq'op, _, _, _⟩ | ⟨hq'op, _, _, _, _, _, _⟩
          · exact absurd (not_unique hn hq'g hqg hq'op hqop) (by omega)
          · rcases hq'op with h | h <;> simp [isBinOp, h] at hnb'
        have hqeq : gs[q]? = some ⟨GateOp.not, [w]⟩ := by
          rw [hqg]; congr 1
          cases hg_eq : gs[q] with
          | mk op ins =>
            rw [hg_eq] at hqop hwin
            dsimp at hqop hwin
            rw [hqop, hwin]
        have hand : g0.op = GateOp.and := by
          rcases honce ⟨w, hw_in⟩ with ⟨hor, _⟩ | ⟨q2, hq2, _, _, hand2, _⟩
          · exfalso
            have := hor q ⟨GateOp.not, [w]⟩ hqeq hra (by simp)
            cases this
          · have hqq2 : q = q2 := not_unique hn hqeq hq2 rfl rfl
            subst hqq2
            exact hand2 p0 g0 hp0 hrp0 ha
        exact ⟨q, w, haeq, hqeq, hand⟩
      · rcases hqop with h | h <;> simp [isBinOp, h] at hnb
  have hj_res := hwire_not_or_in j (by simp [hin0])
  have hk_res := hwire_not_or_in k (by simp [hin0])
  have hboth_in : j < n + 1 ∧ k < n + 1 ∧ g0.op = GateOp.or := by
    rcases hj_res with ⟨hjn, hor⟩ | ⟨q1, w1, hq1, hgn1, hand⟩
    · rcases hk_res with ⟨hkn, _⟩ | ⟨_, _, _, _, hand⟩
      · exact ⟨hjn, hkn, hor⟩
      · rw [hor] at hand; cases hand
    · rcases hk_res with ⟨_, hor⟩ | ⟨q2, w2, hq2, hgn2, _⟩
      · rw [hor] at hand; cases hand
      · exfalso
        have h12 : q1 = q2 := not_unique hn hgn1 hgn2 rfl rfl
        rw [hq1, hq2, h12] at hjk; exact hjk rfl
  obtain ⟨hjn, hkn, hor0⟩ := hboth_in
  let u : Fin (n + 1) := ⟨j, hjn⟩
  let v : Fin (n + 1) := ⟨k, hkn⟩
  have huv : u ≠ v := fun h => hjk (congrArg Fin.val h)
  have huniqu : ∀ p g, gs[p]? = some g → Reach (n + 1) gs o (n + 1 + p) →
      j ∈ g.inputs → p = p0 := by
    intro p g hp hrp hin
    have hjm : u.val ∈ g0.inputs := by simp [u, hin0]
    rcases honce u with ⟨_, hu⟩ | ⟨q, hq, _, honly, _, _⟩
    · exact hu p g p0 g0 hp hp0 hrp hrp0 hin hjm
    · exfalso; have := honly p0 g0 hp0 hrp0 hjm; subst this; rw [hq] at hp0; cases hp0; simp [isBinOp] at hbin0
  have huniq_v : ∀ p g, gs[p]? = some g → Reach (n + 1) gs o (n + 1 + p) →
      k ∈ g.inputs → p = p0 := by
    intro p g hp hrp hin
    have hkm : v.val ∈ g0.inputs := by simp [v, hin0]
    rcases honce v with ⟨_, hv⟩ | ⟨q, hq, _, honly, _, _⟩
    · exact hv p g p0 g0 hp hp0 hrp hrp0 hin hkm
    · exfalso; have := honly p0 g0 hp0 hrp0 hkm; subst this; rw [hq] at hp0; cases hp0; simp [isBinOp] at hbin0
  have hagree : ∀ x y : Fin (n + 1) → Bool,
      (∀ w : Fin (n + 1), w ≠ u → w ≠ v → x w = y w) →
      (x u || x v) = (y u || y v) → f x = f y := by
    intro x y hrest hor_eq
    have hval_eq : ∀ a, a < n + 1 + gs.length → Reach (n + 1) gs o a → a ≠ j → a ≠ k →
        val gs (n + 1) a x = val gs (n + 1) a y := by
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
        intro halt hra haj hak
        by_cases han : a < n + 1
        · have hx := congrFun (val_input gs (n + 1) ⟨a, han⟩) x
          have hy := congrFun (val_input gs (n + 1) ⟨a, han⟩) y
          rw [hx, hy]
          exact hrest ⟨a, han⟩ (fun h => haj (congrArg Fin.val h)) (fun h => hak (congrArg Fin.val h))
        · set p := a - (n + 1)
          have hplt : p < gs.length := by omega
          have haeq : a = n + 1 + p := by omega
          rw [haeq] at hra ⊢
          have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hplt
          have hglt := cleanG_lt (hcl p gs[p] hg)
          rw [val_gate (n + 1) gs p gs[p] hg hglt x, val_gate (n + 1) gs p gs[p] hg hglt y]
          by_cases hpp : p = p0
          · have hgp0 : gs[p] = g0 := by
              have h1 : gs[p]? = some g0 := hpp ▸ hp0
              rw [hg] at h1; exact Option.some.inj h1
            rw [hgp0, hor0, hin0]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            have hxu := congrFun (val_input gs (n + 1) u) x
            have hxv := congrFun (val_input gs (n + 1) v) x
            have hyu := congrFun (val_input gs (n + 1) u) y
            have hyv := congrFun (val_input gs (n + 1) v) y
            change (val gs (n + 1) u.val x || val gs (n + 1) v.val x) =
              (val gs (n + 1) u.val y || val gs (n + 1) v.val y)
            rw [hxu, hxv, hyu, hyv]; exact hor_eq
          · congr 1
            apply List.map_congr_left
            intro w hw
            have hwj : w ≠ j := fun h => hpp (huniqu p gs[p] hg hra (h ▸ hw))
            have hwk : w ≠ k := fun h => hpp (huniq_v p gs[p] hg hra (h ▸ hw))
            exact ih w (by have := hglt w hw; omega) (by have := hglt w hw; omega)
              (reach_step hg hra hw) hwj hwk
    have hoj : o ≠ j := by
      intro heq; obtain ⟨y1, y2, hne⟩ := (hall u).2.1; apply hne
      have h1 := hev (insFin u false y1); have h2 := hev (insFin u false y2)
      rw [heq] at h1 h2
      have hi1 := congrFun (val_input gs (n + 1) u) (insFin u false y1)
      have hi2 := congrFun (val_input gs (n + 1) u) (insFin u false y2)
      simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
      change f (insFin u false y1) = f (insFin u false y2)
      rw [← h1, ← h2, hi1, hi2]
    have hok : o ≠ k := by
      intro heq; obtain ⟨y1, y2, hne⟩ := (hall v).2.1; apply hne
      have h1 := hev (insFin v false y1); have h2 := hev (insFin v false y2)
      rw [heq] at h1 h2
      have hi1 := congrFun (val_input gs (n + 1) v) (insFin v false y1)
      have hi2 := congrFun (val_input gs (n + 1) v) (insFin v false y2)
      simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
      change f (insFin v false y1) = f (insFin v false y2)
      rw [← h1, ← h2, hi1, hi2]
    rw [← hev x, ← hev y]
    exact hval_eq o ho (reach_self (n + 1) gs o) hoj hok
  obtain ⟨x, hne⟩ := hnft u v huv
  rcases hne with hne | hne
  · apply hne; apply hagree
    · intro w hwu hwv; simp [Function.update, hwu, hwv]
    · simp [Function.update, huv]
  · apply hne; apply hagree
    · intro w hwu hwv; simp [Function.update, hwu, hwv]
    · simp [Function.update, huv]

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def flipK (k : ℕ) : ℕ :=
  bif Nat.beq k 1 then 2 else bif Nat.beq k 2 then 1 else 0

def TRun {α : Type} (inv : α → α) (meet join : α → α → α) (y : α)
    (b n : ℕ) (ws : List (ℕ × α)) : Prop :=
  ∀ P : ℕ → ℕ → List (ℕ × α) → Prop,
    (∀ b n k, P b n [(k, y)]) →
    (∀ {b n xs zs}, List.Perm xs zs → P b n xs → P b n zs) →
    (∀ {b n k a r} (save : Bool), (save = true → k = 0) →
      P b n ((flipK k, inv a) :: kept save (k, a) r) →
      P b (n + 1) ((k, a) :: r)) →
    (∀ {b n k1 k2 a1 a2 r} (conj ka kb : Bool),
      (ka = true → k1 = 0) → (kb = true → k2 = 0) →
      (conj = true → k1 ≠ 1 ∧ k2 ≠ 1) →
      (conj = false → k1 ≠ 2 ∧ k2 ≠ 2) →
      P b n ((0, if conj then meet a1 a2 else join a1 a2) :: kept ka (k1, a1) (kept kb (k2, a2) r)) →
      P (b + 1) n ((k1, a1) :: (k2, a2) :: r)) →
    P b n ws

theorem TRun.done {α inv meet join y} (b n k : ℕ) : @TRun α inv meet join y b n [(k, y)] :=
  fun _ d _ _ _ => d b n k

theorem TRun.perm {α inv meet join y b n xs zs} (p : List.Perm xs zs)
    (h : @TRun α inv meet join y b n xs) : TRun inv meet join y b n zs :=
  fun P d q u v => q p (h P d q u v)

theorem TRun.notS {α inv meet join y b n k a r} (save : Bool) (hs : save = true → k = 0)
    (h : @TRun α inv meet join y b n ((flipK k, inv a) :: kept save (k, a) r)) :
    TRun inv meet join y b (n + 1) ((k, a) :: r) :=
  fun P d q u v => u save hs (h P d q u v)

theorem TRun.binS {α inv meet join y b n k1 k2 a1 a2 r} (conj ka kb : Bool)
    (h1 : ka = true → k1 = 0) (h2 : kb = true → k2 = 0)
    (h3 : conj = true → k1 ≠ 1 ∧ k2 ≠ 1) (h4 : conj = false → k1 ≠ 2 ∧ k2 ≠ 2)
    (h : @TRun α inv meet join y b n
      ((0, if conj then meet a1 a2 else join a1 a2) :: kept ka (k1, a1) (kept kb (k2, a2) r))) :
    TRun inv meet join y (b + 1) n ((k1, a1) :: (k2, a2) :: r) :=
  fun P d q u v => v conj ka kb h1 h2 h3 h4 (h P d q u v)

theorem TRun.fold {α inv meet join y} {P : ∀ b n ws, @TRun α inv meet join y b n ws → Prop}
    (done : ∀ b n k, P b n [(k, y)] (TRun.done b n k))
    (perm : ∀ {b n xs zs} (hp : List.Perm xs zs) (h : TRun inv meet join y b n xs),
      P b n xs h → P b n zs (TRun.perm hp h))
    (notS : ∀ {b n k a r} (save : Bool) (hs : save = true → k = 0)
      (h : TRun inv meet join y b n ((flipK k, inv a) :: kept save (k, a) r)),
      P _ _ _ h → P _ _ _ (TRun.notS save hs h))
    (binS : ∀ {b n k1 k2 a1 a2 r} (conj ka kb : Bool)
      (h1 : ka = true → k1 = 0) (h2 : kb = true → k2 = 0)
      (h3 : conj = true → k1 ≠ 1 ∧ k2 ≠ 1) (h4 : conj = false → k1 ≠ 2 ∧ k2 ≠ 2)
      (h : TRun inv meet join y b n
        ((0, if conj then meet a1 a2 else join a1 a2) :: kept ka (k1, a1) (kept kb (k2, a2) r))),
      P _ _ _ h → P _ _ _ (TRun.binS conj ka kb h1 h2 h3 h4 h))
    {b n ws} (h : TRun inv meet join y b n ws) : P b n ws h := by
  have hex := h (fun b n xs => ∃ h' : TRun inv meet join y b n xs, P b n xs h')
    (fun b n k => ⟨TRun.done b n k, done b n k⟩)
    (fun hp ⟨h', ih⟩ => ⟨TRun.perm hp h', perm hp h' ih⟩)
    (fun save hs ⟨h', ih⟩ => ⟨TRun.notS save hs h', notS save hs h' ih⟩)
    (fun conj ka kb h1 h2 h3 h4 ⟨h', ih⟩ =>
      ⟨TRun.binS conj ka kb h1 h2 h3 h4 h', binS conj ka kb h1 h2 h3 h4 h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem TRun.liftN {α inv meet join y b n ws} (h : @TRun α inv meet join y b n ws) :
    TRun inv meet join y b (n + 1) ws := by
  induction h using TRun.fold with
  | done b n k => exact TRun.done b (n + 1) k
  | perm hp _ ih => exact TRun.perm hp ih
  | notS save hs _ ih => exact TRun.notS save hs ih
  | binS conj ka kb h1 h2 h3 h4 _ ih => exact TRun.binS conj ka kb h1 h2 h3 h4 ih

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem TRun.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {b n : ℕ} {ws : List (ℕ × α)} (h : TRun inv meet join y b n ws) :
    TRun inv' meet' join' (e y) b n (ws.map fun p => (p.1, e p.2)) := by
  induction h using TRun.fold with
  | done b n k => exact TRun.done b n k
  | perm hp _ ih => exact TRun.perm (hp.map _) ih
  | @notS b n k a r save hs _ ih =>
    have e1 : (((flipK k, inv a) :: kept save (k, a) r).map fun p : ℕ × α => (p.1, e p.2))
        = (flipK k, inv' (e a)) :: kept save (k, e a) (r.map fun p : ℕ × α => (p.1, e p.2)) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact TRun.notS save hs ih
  | @binS b n k1 k2 a1 a2 r conj ka kb h1 h2 h3 h4 _ ih =>
    have e1 : (((0, if conj then meet a1 a2 else join a1 a2) ::
          kept ka (k1, a1) (kept kb (k2, a2) r)).map fun p : ℕ × α => (p.1, e p.2))
        = (0, if conj then meet' (e a1) (e a2) else join' (e a1) (e a2)) ::
            kept ka (k1, e a1) (kept kb (k2, e a2) (r.map fun p : ℕ × α => (p.1, e p.2))) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact TRun.binS conj ka kb h1 h2 h3 h4 ih

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin; omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp; rw [hg] at hg'; cases hg'; exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

def wTag (n : ℕ) (gs : List Gate) (S : Finset ℕ) (a : ℕ) : ℕ :=
  if a ∈ S then 1
  else if a ≥ n then
    match gs[a - n]? with
    | some g =>
      if isNotOp g.op then
        match g.inputs with
        | [w] => if w ∈ S then 2 else 0
        | _ => 0
      else 0
    | none => 0
  else 0

theorem isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

open Classical in
theorem trun_live (n : ℕ) (gs : List Gate) (o : ℕ) (S : Finset ℕ)
    (hcl : CleanL n gs) (hn : notCount gs ≤ 1) (ho : o < n + gs.length)
    (hSn : ∀ w ∈ S, w < n) (hoS : ∀ w ∈ S, o ≠ w)
    (hoNotS : ∀ q w, w ∈ S → gs[q]? = some ⟨GateOp.not, [w]⟩ → o ≠ n + q)
    (honce : ∀ w ∈ S, OnceProp n gs o w) :
    ∀ p, p ≤ gs.length →
      TRun (invF (n := n)) meetF joinF (val gs n o)
        (binCount (gs.drop p)) (notCount (gs.drop p))
        ((liveList gs n o p).map fun a => (wTag n gs S a, val gs n a)) := by
  intro p hp
  have key : ∀ d p, p + d = gs.length →
      TRun (invF (n := n)) meetF joinF (val gs n o)
        (binCount (gs.drop p)) (notCount (gs.drop p))
        ((liveList gs n o p).map fun a => (wTag n gs S a, val gs n a)) := by
    intro d
    induction d with
    | zero =>
      intro p hpd
      have hp_eq : p = gs.length := by omega
      subst hp_eq
      have hperm : [o].Perm (liveList gs n o gs.length) := by
        refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
        intro a
        rw [mem_liveList, List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨ho, Or.inl rfl⟩
        · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
          · exact h
          · have := (List.getElem?_eq_some_iff.1 hg').1; omega
      simp only [List.drop_length, binCount, notCount, List.filter_nil, List.length_nil]
      exact TRun.perm (hperm.map _) (TRun.done 0 0 (wTag n gs S o))
    | succ d ih =>
      intro p hpd
      have hplt : p < gs.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
      have hdrop : gs.drop p = g :: gs.drop (p + 1) := by
        have := List.drop_eq_getElem_cons hplt
        have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hg).2
        rw [hgp] at this; exact this
      have IH := ih (p + 1) (by omega)
      have liftB : ∀ b1 n1 xs, TRun (invF (n := n)) meetF joinF (val gs n o) b1 n1 xs →
          TRun (invF (n := n)) meetF joinF (val gs n o) (b1 + 1) n1 xs := by
        intro b1 n1 xs h
        induction h using TRun.fold with
        | done b' n' k' => exact TRun.done (b' + 1) n' k'
        | perm hp _ ih' => exact TRun.perm hp ih'
        | notS save hs _ ih' => exact TRun.notS save hs ih'
        | binS conj ka kb h1 h2 h3 h4 _ ih' => exact TRun.binS conj ka kb h1 h2 h3 h4 ih'
      by_cases hr : Reach n gs o (n + p)
      · have hstep := live_succ_reach n gs o hcl p g hg hr
        have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
          (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
        have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
          Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
        have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
        have hnd0 := nodup_liveList gs n o p
        have hno_live_once : ∀ a, a ∈ g.inputs → wTag n gs S a ≠ 0 → ¬ Live n gs o (p + 1) a := by
          intro a ha htag hlive
          unfold wTag at htag
          split_ifs at htag with haS han
          · rcases hlive with rfl | ⟨q, hq, g', hg', hin', hrq⟩
            · exact hoS a haS rfl
            · rcases honce a haS with ⟨_, huniq⟩ | ⟨q0, hq0, _, honly, _, _⟩
              · have := huniq p g q g' hg hg' hr hrq ha hin'; omega
              · have h1 := honly p g hg hr ha
                have h2 := honly q g' hg' hrq hin'
                omega
          · cases hga : gs[a - n]? with
            | none => simp [hga] at htag
            | some ga =>
              simp only [hga] at htag
              split_ifs at htag with hnot
              · cases hgin : ga.inputs with
                | nil => simp [hgin] at htag
                | cons w rest =>
                  cases rest with
                  | nil =>
                    simp only [hgin] at htag
                    split_ifs at htag with hwS
                    · have hga_eq : gs[a - n]? = some ⟨GateOp.not, [w]⟩ := by
                        rw [hga]; congr 1; cases ga; simp_all [isNotOp_eq_true]
                      have ha_eq : a = n + (a - n) := by omega
                      rcases hlive with rfl | ⟨q, hq, g', hg', hin', hrq⟩
                      · exact hoNotS (a - n) w hwS hga_eq ha_eq
                      · rcases honce w hwS with ⟨hor, _⟩ | ⟨q0, hq0, _, _, _, huniq⟩
                        · exfalso
                          have hr_an : Reach n gs o (n + (a - n)) := ha_eq ▸ reach_step hg hr ha
                          have := hor (a - n) _ hga_eq hr_an (by simp)
                          cases this
                        · have hqeq : a - n = q0 := not_unique hn hga_eq hq0 rfl rfl
                          have ha0 : a = n + q0 := by omega
                          have := huniq p g q g' hg hg' hr hrq (ha0 ▸ ha) (ha0 ▸ hin')
                          omega
                    · simp at htag
                  | cons _ _ => simp [hgin] at htag
              · simp at htag
          · simp at htag
        rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
        · have hbc : binCount (gs.drop p) = binCount (gs.drop (p + 1)) := by
            rw [hdrop]; simp [binCount, isBinOp, hop]
          have hnc : notCount (gs.drop p) = notCount (gs.drop (p + 1)) + 1 := by
            rw [hdrop]; simp [notCount, isNotOp, hop]
          rw [hbc, hnc]
          have hjm := hin j (by simp [hinp])
          have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
            List.perm_cons_erase hjm
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
              rw [mem_kept]; rintro (⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew _ (List.mem_of_mem_erase h) rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
              simp only [decide_eq_true_eq, hinp, List.mem_singleton]
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
          have htag_np : wTag n gs S (n + p) = flipK (wTag n gs S j) := by
            have hnpS : n + p ∉ S := fun h => by have := hSn _ h; omega
            have hj_not2 : wTag n gs S j ≠ 2 := by
              unfold wTag
              split_ifs with h1 h2
              · decide
              · cases hgj : gs[j - n]? with
                | none => simp
                | some gj =>
                  simp only [hgj]
                  split_ifs with hnot
                  · exfalso
                    have hjn : j - n ≠ p := by omega
                    exact hjn (not_unique hn hgj hg ((isNotOp_eq_true _).1 hnot) hop)
                  · decide
              · decide
            have hnp_val : wTag n gs S (n + p) = if j ∈ S then 2 else 0 := by
              unfold wTag
              simp only [hnpS, ite_false, show n + p ≥ n by omega, ite_true, Nat.add_sub_cancel_left,
                hg, hop, isNotOp, hinp]
            have hj_val : wTag n gs S j = if j ∈ S then 1 else 0 := by
              by_cases hjS : j ∈ S
              · simp [wTag, hjS]
              · unfold wTag at hj_not2 ⊢
                simp only [hjS, ite_false] at hj_not2 ⊢
                split_ifs at hj_not2 ⊢ with hjn
                · cases hgj : gs[j - n]? with
                  | none => rfl
                  | some gj =>
                    simp only [hgj] at hj_not2 ⊢
                    split_ifs at hj_not2 ⊢ with hnot
                    · cases hgin : gj.inputs with
                      | nil => rfl
                      | cons w rest =>
                        cases rest with
                        | nil => simp only [hgin] at hj_not2 ⊢; split_ifs at hj_not2 ⊢ <;> simp_all
                        | cons _ _ => rfl
                    · rfl
                · rfl
            rw [hnp_val, hj_val]
            by_cases hjS : j ∈ S <;> simp [hjS, flipK]
          have hval : val gs n (n + p) = invF (val gs n j) := by
            funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval, invF]
          have hsave : decide (Live n gs o (p + 1) j) = true → wTag n gs S j = 0 := by
            intro hs
            by_contra hnz
            exact hno_live_once j (by simp [hinp]) hnz (of_decide_eq_true hs)
          have IH' := TRun.perm (hp2.map fun a => (wTag n gs S a, val gs n a)) IH
          rw [List.map_cons, kept_map, htag_np, hval] at IH'
          exact TRun.perm (hp1.map fun a => (wTag n gs S a, val gs n a)).symm (TRun.notS _ hsave IH')
        · have hbc : binCount (gs.drop p) = binCount (gs.drop (p + 1)) + 1 := by
            rw [hdrop]; rcases hop with hop | hop <;> simp [binCount, isBinOp, hop]
          have hnc : notCount (gs.drop p) = notCount (gs.drop (p + 1)) := by
            rw [hdrop]; rcases hop with hop | hop <;> simp [notCount, isNotOp, hop]
          rw [hbc, hnc]
          have hjm := hin j (by simp [hinp])
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]; rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]; rintro (⟨_, h⟩ | h)
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
          have htag_np : wTag n gs S (n + p) = 0 := by
            have hnpS : n + p ∉ S := fun h => by have := hSn _ h; omega
            unfold wTag
            simp only [hnpS, ite_false, show n + p ≥ n by omega, ite_true, Nat.add_sub_cancel_left, hg]
            rcases hop with hop | hop <;> simp [hop, isNotOp]
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
          have hka : decide (Live n gs o (p + 1) j) = true → wTag n gs S j = 0 := fun hs => by
            by_contra hnz; exact hno_live_once j (by simp [hinp]) hnz (of_decide_eq_true hs)
          have hkb : decide (Live n gs o (p + 1) k) = true → wTag n gs S k = 0 := fun hs => by
            by_contra hnz; exact hno_live_once k (by simp [hinp]) hnz (of_decide_eq_true hs)
          have hop_tag : ∀ a, a ∈ g.inputs →
              (decide (g.op = GateOp.and) = true → wTag n gs S a ≠ 1) ∧
              (decide (g.op = GateOp.and) = false → wTag n gs S a ≠ 2) := by
            intro a ha
            constructor
            · intro hand h1
              have hand' : g.op = GateOp.and := of_decide_eq_true hand
              have haS : a ∈ S := by
                unfold wTag at h1
                by_cases hS : a ∈ S
                · exact hS
                · exfalso
                  simp only [hS, ite_false] at h1
                  by_cases han : a ≥ n
                  · simp only [han, ite_true] at h1
                    cases hga : gs[a - n]? with
                    | none => rw [hga] at h1; cases h1
                    | some ga =>
                      rw [hga] at h1
                      by_cases hnot : isNotOp ga.op = true
                      · simp only [hnot, ite_true] at h1
                        cases hgin : ga.inputs with
                        | nil => rw [hgin] at h1; cases h1
                        | cons w r =>
                          cases r with
                          | nil =>
                            rw [hgin] at h1
                            by_cases hwS : w ∈ S <;> simp [hwS] at h1
                          | cons _ _ => rw [hgin] at h1; cases h1
                      · simp [hnot] at h1
                  · simp [han] at h1
              rcases honce a haS with ⟨hor, _⟩ | ⟨q0, hq0, _, honly, _, _⟩
              · have := hor p g hg hr ha; rw [hand'] at this; cases this
              · have := honly p g hg hr ha; subst this; rw [hq0] at hg; cases hg; cases hand'
            · intro hnotand h2
              have hor' : g.op = GateOp.or := by
                rcases hop with hop | hop
                · simp [hop] at hnotand
                · exact hop
              unfold wTag at h2
              by_cases hS : a ∈ S
              · simp [hS] at h2
              · simp only [hS, ite_false] at h2
                by_cases han : a ≥ n
                · simp only [han, ite_true] at h2
                  cases hga : gs[a - n]? with
                  | none => rw [hga] at h2; cases h2
                  | some ga =>
                    rw [hga] at h2
                    by_cases hnot : isNotOp ga.op = true
                    · simp only [hnot, ite_true] at h2
                      cases hgin : ga.inputs with
                      | nil => rw [hgin] at h2; cases h2
                      | cons w rest =>
                        cases rest with
                        | nil =>
                          rw [hgin] at h2
                          by_cases hwS : w ∈ S
                          · have hga_eq : gs[a - n]? = some ⟨GateOp.not, [w]⟩ := by
                              rw [hga]; congr 1; cases ga; simp_all [isNotOp_eq_true]
                            have ha_eq : a = n + (a - n) := by omega
                            rcases honce w hwS with ⟨hor_w, _⟩ | ⟨q0, hq0, _, _, hand_q, _⟩
                            · have := hor_w (a - n) _ hga_eq (ha_eq ▸ reach_step hg hr ha) (by simp)
                              cases this
                            · have hqeq : a - n = q0 := not_unique hn hga_eq hq0 rfl rfl
                              have ha0 : a = n + q0 := by omega
                              have := hand_q p g hg hr (ha0 ▸ ha)
                              rw [hor'] at this; cases this
                          · simp [hwS] at h2
                        | cons _ _ => rw [hgin] at h2; cases h2
                    · simp [hnot] at h2
                · simp [han] at h2
          have hj_t := hop_tag j (by simp [hinp])
          have hk_t := hop_tag k (by simp [hinp])
          have IH' := TRun.perm (hp2.map fun a => (wTag n gs S a, val gs n a)) IH
          rw [List.map_cons, kept_map, kept_map, htag_np, hval] at IH'
          exact TRun.perm (hp1.map fun a => (wTag n gs S a, val gs n a)).symm
            (TRun.binS _ _ _ hka hkb (fun h => ⟨hj_t.1 h, hk_t.1 h⟩)
              (fun h => ⟨hj_t.2 h, hk_t.2 h⟩) IH')
      · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
          (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
            (live_succ_dead n gs o p hr)
        have IH' := TRun.perm (hp.map fun a => (wTag n gs S a, val gs n a)) IH
        rw [hdrop]
        rcases cleanG_ok (hcl p g hg) with ⟨hop | hop | hop, _⟩
        · have hbc : binCount (g :: gs.drop (p + 1)) = binCount (gs.drop (p + 1)) + 1 := by
            simp [binCount, isBinOp, hop]
          have hnc : notCount (g :: gs.drop (p + 1)) = notCount (gs.drop (p + 1)) := by
            simp [notCount, isNotOp, hop]
          rw [hbc, hnc]; exact liftB _ _ _ IH'
        · have hbc : binCount (g :: gs.drop (p + 1)) = binCount (gs.drop (p + 1)) + 1 := by
            simp [binCount, isBinOp, hop]
          have hnc : notCount (g :: gs.drop (p + 1)) = notCount (gs.drop (p + 1)) := by
            simp [notCount, isNotOp, hop]
          rw [hbc, hnc]; exact liftB _ _ _ IH'
        · have hbc : binCount (g :: gs.drop (p + 1)) = binCount (gs.drop (p + 1)) := by
            simp [binCount, isBinOp, hop]
          have hnc : notCount (g :: gs.drop (p + 1)) = notCount (gs.drop (p + 1)) + 1 := by
            simp [notCount, isNotOp, hop]
          rw [hbc, hnc]; exact TRun.liftN IH'
  exact key (gs.length - p) p (by omega)

abbrev NatTRun (m : ℕ) := TRun (· ^^^ m) (· &&& ·) (· ||| ·)

theorem trun_len {α inv meet join y b n xs} (h : @TRun α inv meet join y b n xs) :
    1 ≤ xs.length ∧ xs.length ≤ b + 1 := by
  induction h using TRun.fold with
  | done b n k => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | notS save _ _ ih => cases save <;> simp [kept] at ih ⊢ <;> omega
  | binS conj ka kb _ _ _ _ _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

theorem trun_zero_bin {m y n ws} (h : NatTRun m y 0 n ws) :
    ∃ k v, ws = [(k, v)] ∧ (v = y ∨ (n ≠ 0 ∧ v ^^^ m = y)) := by
  have key : ∀ b n ws, NatTRun m y b n ws → b = 0 →
      ∃ k v, ws = [(k, v)] ∧ (v = y ∨ (n ≠ 0 ∧ v ^^^ m = y)) := by
    intro b n ws h
    induction h using TRun.fold with
    | done b n k => intro _; exact ⟨k, y, rfl, Or.inl rfl⟩
    | perm hp _ ih =>
      intro hb
      obtain ⟨k, v, heq, hor⟩ := ih hb
      rw [heq] at hp
      exact ⟨k, v, List.perm_singleton.1 hp.symm, hor⟩
    | @notS b' n' k a r save hs h' ih =>
      intro hb
      obtain ⟨k', v', heq, hor⟩ := ih hb
      have hlen := congrArg List.length heq
      cases save
      · simp only [kept, Bool.false_eq_true, ite_false, List.cons.injEq] at heq
        obtain ⟨⟨_, rfl⟩, rfl⟩ := heq
        refine ⟨k, a, rfl, ?_⟩
        rcases hor with hv | ⟨_, hv⟩
        · exact Or.inr ⟨by omega, hv⟩
        · refine Or.inl (Nat.eq_of_testBit_eq fun i => ?_)
          have hi := congrArg (fun z => z.testBit i) hv
          simp only [Nat.testBit_xor] at hi
          revert hi; cases a.testBit i <;> cases m.testBit i <;> cases y.testBit i <;> decide
      · simp [kept] at hlen
    | binS => intro hb; omega
  exact key 0 n ws h rfl

theorem trun_bits {m y b n ws} (h : NatTRun m y b n ws) (i j : ℕ)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ p ∈ ws, p.2.testBit i = p.2.testBit j) : y.testBit i = y.testBit j := by
  induction h using TRun.fold with
  | done b n k => exact hw (k, y) List.mem_cons_self
  | perm hp _ ih => exact ih (fun p h => hw p (hp.mem_iff.1 h))
  | notS save _ _ ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro p hmem
    cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (List.mem_cons_of_mem _ hr)
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (List.mem_cons_of_mem _ hr)
  | binS conj ka kb _ _ _ _ _ ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro p hmem
    cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;>
      first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem trun_mono_bits {m y b ws} (h : NatTRun m y b 0 ws) (i j : ℕ)
    (hw : ∀ p ∈ ws, p.2.testBit i ≤ p.2.testBit j) : y.testBit i ≤ y.testBit j := by
  have key : ∀ b n ws, NatTRun m y b n ws → n = 0 →
      (∀ p ∈ ws, p.2.testBit i ≤ p.2.testBit j) → y.testBit i ≤ y.testBit j := by
    intro b n ws h
    induction h using TRun.fold with
    | done b n k => intro _ hw; exact hw (k, y) List.mem_cons_self
    | perm hp _ ih => intro hn hw; exact ih hn (fun p hp' => hw p (hp.mem_iff.1 hp'))
    | notS => intro hn; omega
    | @binS b n k1 k2 a1 a2 r conj ka kb _ _ _ _ _ ih =>
      intro hn hw
      apply ih hn
      have ha : a1.testBit i ≤ a1.testBit j := hw (k1, a1) List.mem_cons_self
      have hb : a2.testBit i ≤ a2.testBit j := hw (k2, a2) (List.mem_cons_of_mem _ List.mem_cons_self)
      intro p hmem
      have hop : (if conj then a1 &&& a2 else a1 ||| a2).testBit i ≤
          (if conj then a1 &&& a2 else a1 ||| a2).testBit j := by
        cases conj
        · simp only [Bool.false_eq_true, ite_false, Nat.testBit_or]
          revert ha hb; cases a1.testBit i <;> cases a1.testBit j <;> cases a2.testBit i <;> cases a2.testBit j <;> decide
        · simp only [ite_true, Nat.testBit_and]
          revert ha hb; cases a1.testBit i <;> cases a1.testBit j <;> cases a2.testBit i <;> cases a2.testBit j <;> decide
      rcases List.mem_cons.1 hmem with rfl | hrest
      · exact hop
      · rw [mem_kept] at hrest
        rcases hrest with ⟨_, rfl⟩ | hrest2
        · exact ha
        · rw [mem_kept] at hrest2
          rcases hrest2 with ⟨_, rfl⟩ | hrest3
          · exact hb
          · exact hw p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest3))
  exact key b 0 ws h rfl hw

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
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]; rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]; rfl

def packW (p : ℕ × ℕ) : ℕ := (p.2 <<< 2) ||| p.1

theorem packW_val (k v : ℕ) (hk : k < 4) : (packW (k, v)) >>> 2 = v := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [packW, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hlt : ¬ (2 + j < 2) := by omega
  have hkj : k.testBit (2 + j) = false := Nat.testBit_lt_two_pow (by
    have : 2 ^ 2 ≤ 2 ^ (2 + j) := Nat.pow_le_pow_right (by omega) (by omega)
    omega)
  simp [hlt, hkj]

theorem packW_kind (k v : ℕ) (hk : k < 4) : (packW (k, v)) &&& 3 = k := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [packW, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 2
  · have h3 : (3 : ℕ).testBit j = true := by
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> decide
    have hnot : ¬ (2 ≤ j) := by omega
    simp [h3, hnot]
  · have h3 : (3 : ℕ).testBit j = false := Nat.testBit_lt_two_pow (by
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega); omega)
    have hkj : k.testBit j = false := Nat.testBit_lt_two_pow (by
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega); omega)
    simp [h3, hkj]

def insOrd (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | a :: t => bif Nat.ble x a then x :: a :: t else a :: insOrd x t

def isort : List ℕ → List ℕ
  | [] => []
  | a :: t => insOrd a (isort t)

theorem perm_insOrd (x : ℕ) : ∀ l : List ℕ, (insOrd x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | a :: t => by
    unfold insOrd
    cases Nat.ble x a
    · exact ((perm_insOrd x t).cons a).trans (List.Perm.swap _ _ _)
    · exact List.Perm.refl _

theorem perm_isort : ∀ l : List ℕ, (isort l).Perm l
  | [] => List.Perm.refl _
  | a :: t => (perm_insOrd a (isort t)).trans ((perm_isort t).cons a)

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
    simp only [leqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def btMem : BinaryTree (List ℕ) → List ℕ → Bool
  | .nil, _ => false
  | .node k l r, x => leqL x k || (bif ltL x k then btMem l x else btMem r x)

def btToList {α : Type} : BinaryTree α → List α
  | .nil => []
  | .node k l r => btToList l ++ k :: btToList r

theorem btMem_toList : ∀ (T : BinaryTree (List ℕ)) (x : List ℕ), btMem T x = true → x ∈ btToList T
  | .nil, _, h => by simp [btMem] at h
  | .node k l r, x, hm => by
    simp only [btMem, Bool.or_eq_true] at hm
    simp only [btToList, List.mem_append, List.mem_cons]
    rcases hm with he | hm
    · exact Or.inr (Or.inl (leqL_eq x k he))
    · cases hlt : ltL x k <;> simp only [hlt, Bool.cond_false, Bool.cond_true] at hm
      · exact Or.inr (Or.inr (btMem_toList r x hm))
      · exact Or.inl (btMem_toList l x hm)

def buildBTAux {α : Type} : ℕ → List α → BinaryTree α × List α
  | 0, l => (.nil, l)
  | d + 1, l =>
    match buildBTAux d l with
    | (lt, []) => (lt, [])
    | (lt, x :: r1) =>
      match buildBTAux d r1 with
      | (rt, r2) => (.node x lt rt, r2)

def buildBT {α : Type} (l : List α) : BinaryTree α := (buildBTAux 13 l).1

theorem buildBTAux_toList {α : Type} : ∀ (d : ℕ) (l : List α),
    btToList (buildBTAux d l).1 ++ (buildBTAux d l).2 = l
  | 0, l => rfl
  | d + 1, l => by
    have h1 := buildBTAux_toList d l
    simp only [buildBTAux]
    cases hA : buildBTAux d l with
    | mk lt rest =>
      rw [hA] at h1
      cases rest with
      | nil => simpa using h1
      | cons x r1 =>
        have h2 := buildBTAux_toList d r1
        cases hB : buildBTAux d r1 with
        | mk rt r2 =>
          rw [hB] at h2
          simp only [hB, btToList, List.append_assoc, List.cons_append]
          rw [h2]
          exact h1

theorem btMem_buildBT (L : List (List ℕ × List ℕ)) (x : List ℕ)
    (hx : btMem (buildBT (L.map Prod.fst)) x = true) :
    ∃ h, (x, h) ∈ L := by
  have h1 := btMem_toList _ x hx
  have h2 := buildBTAux_toList 13 (L.map Prod.fst)
  have h3 : x ∈ L.map Prod.fst := by rw [← h2]; exact List.mem_append_left _ h1
  obtain ⟨⟨k, h⟩, hkh, rfl⟩ := List.mem_map.1 h3
  exact ⟨h, hkh⟩

theorem all_flatten {α : Type} {p : α → Bool} {ll : List (List α)}
    (h : ll.all (fun l => l.all p) = true) : ll.flatten.all p = true := by
  induction ll with
  | nil => rfl
  | cons l ll ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.flatten_cons, List.all_append, h.1, ih h.2]

theorem all_drop_take_split {α : Type} {p : α → Bool} (l : List α) (s k : ℕ)
    (h1 : ((l.drop s).take k).all p = true)
    (h2 : (l.drop (s + k)).all p = true) : (l.drop s).all p = true := by
  have h := List.take_append_drop k (l.drop s)
  rw [List.drop_drop] at h
  rw [← h, List.all_append, h1, h2]; rfl

theorem all_of_5 {α : Type} {p : α → Bool} {l : List α} (hl : Nat.ble l.length 150 = true)
    (h0 : ((l.drop 0).take 30).all p = true)
    (h1 : ((l.drop 30).take 30).all p = true)
    (h2 : ((l.drop 60).take 30).all p = true)
    (h3 : ((l.drop 90).take 30).all p = true)
    (h4 : ((l.drop 120).take 30).all p = true) : l.all p = true := by
  have hl' : l.length ≤ 150 := by simpa [Nat.ble_eq] using hl
  have hd5 : (l.drop 150).all p = true := by simp [List.drop_eq_nil_of_le hl']
  have hd4 : (l.drop 120).all p = true := all_drop_take_split l 120 30 h4 hd5
  have hd3 : (l.drop 90).all p = true := all_drop_take_split l 90 30 h3 hd4
  have hd2 : (l.drop 60).all p = true := all_drop_take_split l 60 30 h2 hd3
  have hd1 : (l.drop 30).all p = true := all_drop_take_split l 30 30 h1 hd2
  simpa using all_drop_take_split l 0 30 h0 hd1

def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => p k && allLt k p

theorem allLt_eq_true {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, hlt⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact hlt k h
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

def fullSepCov (m q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t =>
    let v := Nat.shiftRight w 2
    Nat.lor (bif Nat.testBit v q then Nat.xor v m else v) (fullSepCov m q t)

def fullSep (m y nz : ℕ) (ws : List ℕ) : Bool :=
  allLt nz fun q => Nat.beq (Nat.land (fullSepCov m q ws) y) y

def monoSepCov (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t =>
    let v := Nat.shiftRight w 2
    bif Nat.testBit v q then monoSepCov q t else Nat.lor v (monoSepCov q t)

def monoSep (y nz : ℕ) (ws : List ℕ) : Bool :=
  allLt nz fun q => Nat.beq (Nat.land (monoSepCov q ws) y) y

def via (m y nz b n : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble 1 ws.length && Nat.ble ws.length (b + 1) &&
  bif Nat.beq b 0 then
    match ws with
    | [w] => let v := Nat.shiftRight w 2; Nat.beq v y || (!Nat.beq n 0 && Nat.beq (Nat.xor v m) y)
    | _ => false
  else bif Nat.beq n 0 then monoSep y nz ws
  else fullSep m y nz ws

def prsOK (m y nz : ℕ) : Bool :=
  Nat.beq (y &&& m) y &&
  (List.range nz).all (fun q => !y.testBit q && m.testBit q)

theorem fullSepCov_testBit (m q i : ℕ) (hm : m.testBit i = true) :
    ∀ ws : List ℕ, (fullSepCov m q ws).testBit i = true ↔
      ∃ w ∈ ws, (w >>> 2).testBit i ≠ (w >>> 2).testBit q
  | [] => by simp [fullSepCov]
  | w :: t => by
    have hstep : fullSepCov m q (w :: t) =
        (bif (w >>> 2).testBit q then (w >>> 2) ^^^ m else (w >>> 2)) ||| fullSepCov m q t := rfl
    rw [hstep, Nat.testBit_or, Bool.or_eq_true, fullSepCov_testBit m q i hm t]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨w', hw', hne⟩)
      · refine ⟨w, Or.inl rfl, ?_⟩
        cases hq : (w >>> 2).testBit q <;> simp [hq, Nat.testBit_xor, hm] at h ⊢ <;> simp [h]
      · exact ⟨w', Or.inr hw', hne⟩
    · rintro ⟨w', rfl | hw', hne⟩
      · left; cases hq : (w' >>> 2).testBit q <;> cases hi : (w' >>> 2).testBit i <;>
          simp_all [Nat.testBit_xor]
      · exact Or.inr ⟨w', hw', hne⟩

theorem monoSepCov_testBit (q i : ℕ) :
    ∀ ws : List ℕ, (monoSepCov q ws).testBit i = true ↔
      ∃ w ∈ ws, (w >>> 2).testBit i = true ∧ (w >>> 2).testBit q = false
  | [] => by simp [monoSepCov]
  | w :: t => by
    have hstep : monoSepCov q (w :: t) =
        bif (w >>> 2).testBit q then monoSepCov q t else (w >>> 2) ||| monoSepCov q t := rfl
    rw [hstep]
    simp only [List.mem_cons]
    cases hq : (w >>> 2).testBit q
    · simp only [Bool.cond_false, Nat.testBit_or, Bool.or_eq_true]
      rw [monoSepCov_testBit q i t]
      constructor
      · rintro (h | ⟨w', hw', hi, hq'⟩)
        · exact ⟨w, Or.inl rfl, h, hq⟩
        · exact ⟨w', Or.inr hw', hi, hq'⟩
      · rintro ⟨w', rfl | hw', hi, hq'⟩
        · exact Or.inl hi
        · exact Or.inr ⟨w', hw', hi, hq'⟩
    · simp only [Bool.cond_true]
      rw [monoSepCov_testBit q i t]
      constructor
      · rintro ⟨w', hw', hi, hq'⟩; exact ⟨w', Or.inr hw', hi, hq'⟩
      · rintro ⟨w', rfl | hw', hi, hq'⟩
        · rw [hq] at hq'; cases hq'
        · exact ⟨w', hw', hi, hq'⟩

theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by
  simpa [Nat.ble_eq] using h

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h; simp

theorem via_sound {m y nz b n : ℕ} (hp : prsOK m y nz = true) {ws : List (ℕ × ℕ)}
    (hk : ∀ p ∈ ws, p.1 < 4) (h : NatTRun m y b n ws) :
    via m y nz b n (ws.map packW) = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp
  have hym : y &&& m = y := Nat.eq_of_beq_eq_true hp.1
  have hlen := trun_len h
  unfold via
  simp only [List.length_map, Bool.and_eq_true]
  refine ⟨⟨ble_true hlen.1, ble_true hlen.2⟩, ?_⟩
  by_cases hb0 : b = 0
  · subst hb0
    obtain ⟨k, v, rfl, hor⟩ := trun_zero_bin h
    have hk0 := hk (k, v) List.mem_cons_self
    have hv : Nat.shiftRight (packW (k, v)) 2 = v := packW_val k v hk0
    simp only [Nat.beq_refl, Bool.cond_true, List.map_cons, List.map_nil, hv,
      Bool.or_eq_true, Bool.and_eq_true]
    rcases hor with rfl | ⟨hn0, hv2⟩
    · left; exact beq_true rfl
    · right
      have hnb : Nat.beq n 0 = false := by
        cases hq : Nat.beq n 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) hn0
      exact ⟨by simp [hnb], beq_true hv2⟩
  · have hbf : Nat.beq b 0 = false := by
      cases hq : Nat.beq b 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hq) hb0
    simp only [hbf, Bool.cond_false]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Nat.beq_refl, Bool.cond_true, monoSep, allLt_eq_true]
      intro q hq
      have hyq : y.testBit q = false := by
        have := (hp.2 q hq).1; simpa using this
      apply beq_true
      apply Nat.eq_of_testBit_eq; intro i
      change ((monoSepCov q (ws.map packW)) &&& y).testBit i = y.testBit i
      rw [Nat.testBit_and]
      cases hyi : y.testBit i
      · simp
      · simp only [Bool.and_true]
        rw [monoSepCov_testBit q i]
        by_contra hnone
        push Not at hnone
        have hle : ∀ p ∈ ws, p.2.testBit i ≤ p.2.testBit q := by
          intro p hpm
          have hpk := hk p hpm
          have h1 := hnone (packW p) (List.mem_map.2 ⟨p, hpm, rfl⟩)
          rw [packW_val p.1 p.2 hpk] at h1
          cases hi2 : p.2.testBit i
          · exact Bool.false_le _
          · cases hq2 : p.2.testBit q
            · exact absurd hq2 (h1 hi2)
            · exact le_rfl
        have := trun_mono_bits h i q hle
        rw [hyi, hyq] at this; exact absurd this (by decide)
    · have hnf : Nat.beq n 0 = false := by
        cases hq : Nat.beq n 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) hn0
      simp only [hnf, Bool.cond_false, fullSep, allLt_eq_true]
      intro q hq
      have hyq : y.testBit q = false := by have := (hp.2 q hq).1; simpa using this
      have hmq : m.testBit q = true := (hp.2 q hq).2
      apply beq_true
      apply Nat.eq_of_testBit_eq; intro i
      change ((fullSepCov m q (ws.map packW)) &&& y).testBit i = y.testBit i
      rw [Nat.testBit_and]
      cases hyi : y.testBit i
      · simp
      · simp only [Bool.and_true]
        have hmi : m.testBit i = true := by
          have := congrArg (fun z => z.testBit i) hym
          rw [Nat.testBit_and, hyi, Bool.true_and] at this; exact this
        rw [fullSepCov_testBit m q i hmi]
        by_contra hnone
        push Not at hnone
        have heq : ∀ p ∈ ws, p.2.testBit i = p.2.testBit q := by
          intro p hpm
          have h1 := hnone (packW p) (List.mem_map.2 ⟨p, hpm, rfl⟩)
          rwa [packW_val p.1 p.2 (hk p hpm)] at h1
        have := trun_bits h i q (by rw [hmi, hmq]) heq
        rw [hyi, hyq] at this; cases this

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], _, _ => by simp [actL]
  | p :: _, w, 0 => by simp [actL]
  | _ :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def actW (pi : List ℕ) (w : ℕ) : ℕ :=
  Nat.lor (Nat.shiftLeft (actL pi (Nat.shiftRight w 2)) 2) (Nat.land w 3)

theorem actW_packW (pi : List ℕ) (p : ℕ × ℕ) (hk : p.1 < 4) :
    actW pi (packW p) = packW (p.1, actL pi p.2) := by
  have h1 : actW pi (packW p) = (((actL pi (packW p >>> 2)) <<< 2) ||| (packW p &&& 3)) := rfl
  rw [h1, packW_val p.1 p.2 hk, packW_kind p.1 p.2 hk]
  rfl

theorem trun_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y)
    {b n : ℕ} {ws : List (ℕ × ℕ)} (h : NatTRun m y b n ws) :
    NatTRun m y b n (ws.map fun p => (p.1, actL pi p.2)) := by
  have h2 := TRun.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

def hfind (G : List (List ℕ)) (T : BinaryTree (List ℕ)) (hdr : ℕ) (h : List ℕ)
    (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.find? (fun p => Nat.beq (Nat.shiftRight p 5) tag) with
  | some p =>
    match G[Nat.land p 31]? with
    | some pi => btMem T (hdr :: isort (ys.map (actW pi)))
    | none => false
  | none => false

def nextT (m : ℕ) (b n : ℕ) (ws : List ℕ)
    (f : ℕ → ℕ → ℕ → List ℕ → Bool) : Bool :=
  (Nat.beq n 1 && ws.any fun wa =>
    let i := ws.idxOf wa
    let ra := ws.erase wa
    let v := Nat.shiftRight wa 2
    let k := Nat.land wa 3
    let nw := Nat.lor (Nat.shiftLeft (Nat.xor v m) 2) (flipK k)
    f b 0 (2 * i) (nw :: ra) ||
      (Nat.beq k 0 && Nat.ble ws.length b && f b 0 (2 * i + 1) (nw :: wa :: ra))) ||
  (Nat.ble 1 b && ws.any fun wa =>
    let i := ws.idxOf wa
    let ra := ws.erase wa
    ra.any fun wb =>
      Nat.ble wa wb &&
      let j := ws.idxOf wb
      let r := ra.erase wb
      let va := Nat.shiftRight wa 2
      let ka := Nat.land wa 3
      let vb := Nat.shiftRight wb 2
      let kb := Nat.land wb 3
      let base := 32 + 8 * (j * (j + 1) / 2 + i)
      [false, true].any fun conj =>
        (bif conj then !Nat.beq ka 1 && !Nat.beq kb 1 else !Nat.beq ka 2 && !Nat.beq kb 2) &&
        let nw := Nat.shiftLeft (bif conj then Nat.land va vb else Nat.lor va vb) 2
        let b1 := b - 1
        (Nat.ble r.length b1 && f b1 n (base + 4 * conj.toNat) (nw :: r)) ||
        (Nat.beq ka 0 && Nat.ble (r.length + 1) b1 && f b1 n (base + 4 * conj.toNat + 2) (nw :: wa :: r)) ||
        (Nat.beq kb 0 && Nat.ble (r.length + 1) b1 && f b1 n (base + 4 * conj.toNat + 1) (nw :: wb :: r)) ||
        (Nat.beq ka 0 && Nat.beq kb 0 && Nat.ble (r.length + 2) b1 && f b1 n (base + 4 * conj.toNat + 3) (nw :: wa :: wb :: r)))

def stepOK (m y nz : ℕ) (G : List (List ℕ)) (T : BinaryTree (List ℕ)) :
    List ℕ → List ℕ → Bool
  | [], _ => false
  | hdr :: es, h =>
    let b := Nat.shiftRight hdr 1
    let n := Nat.land hdr 1
    Nat.ble 1 b &&
    !(match es with | [w] => Nat.beq (Nat.shiftRight w 2) y | _ => false) &&
    !(nextT m b n es fun nb nn tag ys =>
      via m y nz nb nn ys && !btMem T ((2 * nb + nn) :: isort ys) && !hfind G T (2 * nb + nn) h tag ys)

theorem packW_flipK (k : ℕ) : flipK k < 4 := by
  unfold flipK
  cases Nat.beq k 1
  · cases Nat.beq k 2 <;> simp
  · simp

def unpackW (w : ℕ) : ℕ × ℕ := (w &&& 3, w >>> 2)

theorem unpackW_packW (k v : ℕ) (hk : k < 4) : unpackW (packW (k, v)) = (k, v) := by
  simp [unpackW, packW_kind k v hk, packW_val k v hk]

theorem packW_unpackW (w : ℕ) : packW (unpackW w) = w := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [packW, unpackW, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  by_cases hj : j < 2
  · have h3 : (3 : ℕ).testBit j = true := by
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> decide
    have hnot : ¬ (2 ≤ j) := by omega
    simp [h3, hnot]
  · have h3 : (3 : ℕ).testBit j = false := Nat.testBit_lt_two_pow (by
      have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega); omega)
    have hge : 2 ≤ j := by omega
    have heq : 2 + (j - 2) = j := by omega
    simp [h3, hge, heq]

theorem map_packW_unpackW (ws : List ℕ) : (ws.map unpackW).map packW = ws := by
  rw [List.map_map]; simp [Function.comp_def, packW_unpackW]

theorem unpackW_fst_lt (w : ℕ) : (unpackW w).1 < 4 := by
  simp only [unpackW]
  have : (w &&& 3) ≤ 3 := Nat.and_le_right
  omega

theorem via_sound_nat {m y nz b n : ℕ} (hp : prsOK m y nz = true) {ws : List ℕ}
    (h : NatTRun m y b n (ws.map unpackW)) : via m y nz b n ws = true := by
  have h1 := via_sound hp (fun p hp' => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp'; exact unpackW_fst_lt w) h
  rwa [map_packW_unpackW] at h1

theorem actW_unpackW (pi : List ℕ) (w : ℕ) :
    unpackW (actW pi w) = ((unpackW w).1, actL pi (unpackW w).2) := by
  have hk : (w &&& 3) < 4 := unpackW_fst_lt w
  exact unpackW_packW (w &&& 3) (actL pi (w >>> 2)) hk

theorem trun_act_nat {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y)
    {b n : ℕ} {ws : List ℕ} (h : NatTRun m y b n (ws.map unpackW)) :
    NatTRun m y b n ((ws.map (actW pi)).map unpackW) := by
  have h1 := trun_act pi hm hy h
  have heq : (ws.map (actW pi)).map unpackW = (ws.map unpackW).map (fun p => (p.1, actL pi p.2)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro w _; exact actW_unpackW pi w
  rw [heq]; exact h1

theorem nextT_not {m y b k a rest} {save : Bool} {ws : List ℕ}
    (hs : save = true → k = 0)
    (p : ((k, a) :: rest).Perm (ws.map unpackW))
    (h : NatTRun m y b 0 ((flipK k, a ^^^ m) :: kept save (k, a) rest))
    (f : ℕ → ℕ → ℕ → List ℕ → Bool)
    (hf : ∀ tag ys, NatTRun m y b 0 (ys.map unpackW) → f b 0 tag ys = true) :
    nextT m b 1 ws f = true := by
  have hmem0 : (k, a) ∈ ws.map unpackW := p.mem_iff.1 List.mem_cons_self
  obtain ⟨wa, hwa, hwa_eq⟩ := List.mem_map.1 hmem0
  have hklt : k < 4 := by
    have h1 := congrArg Prod.fst hwa_eq; dsimp at h1; rw [← h1]; exact unpackW_fst_lt wa
  have hwa_pack : wa = packW (k, a) := by rw [← packW_unpackW wa, hwa_eq]
  have hpa : ((ws.erase wa).map unpackW).Perm rest := by
    have p1 : (ws.map unpackW).Perm (unpackW wa :: (ws.erase wa).map unpackW) := by
      simpa only [List.map_cons] using (List.perm_cons_erase hwa).map unpackW
    rw [hwa_eq] at p1
    exact (p.trans p1).cons_inv.symm
  have hlen := trun_len h
  have hlp := p.length_eq
  simp only [List.length_cons, List.length_map] at hlp
  unfold nextT
  rw [Bool.or_eq_true]; left
  simp only [Nat.beq_refl, Bool.true_and, List.any_eq_true]
  refine ⟨wa, hwa, ?_⟩
  have hv : Nat.shiftRight wa 2 = a := by rw [hwa_pack]; exact packW_val k a hklt
  have hkv : Nat.land wa 3 = k := by rw [hwa_pack]; exact packW_kind k a hklt
  rw [hv, hkv]
  have hnw : Nat.lor (Nat.shiftLeft (Nat.xor a m) 2) (flipK k) = packW (flipK k, a ^^^ m) := rfl
  rw [hnw]
  have hun_nw : unpackW (packW (flipK k, a ^^^ m)) = (flipK k, a ^^^ m) :=
    unpackW_packW (flipK k) (a ^^^ m) (packW_flipK k)
  cases save with
  | false =>
    simp only [kept, Bool.false_eq_true, ite_false] at h
    have hr : NatTRun m y b 0 ((packW (flipK k, a ^^^ m) :: ws.erase wa).map unpackW) := by
      simp only [List.map_cons, hun_nw]
      exact TRun.perm (hpa.symm.cons _) h
    simp [hf _ _ hr]
  | true =>
    have hk0 : k = 0 := hs rfl
    subst hk0
    simp only [kept, ite_true, List.length_cons] at h hlen
    have hle : ws.length ≤ b := by omega
    have hr : NatTRun m y b 0 ((packW (flipK 0, a ^^^ m) :: wa :: ws.erase wa).map unpackW) := by
      simp only [List.map_cons, hun_nw, hwa_eq]
      exact TRun.perm ((hpa.symm.cons _).cons _) h
    simp [ble_true hle, hf _ _ hr]

theorem nextT_bin_sorted {m y b n k1 k2 a1 a2 rest} {conj ka kb : Bool} {ws : List ℕ}
    (h1 : ka = true → k1 = 0) (h2 : kb = true → k2 = 0)
    (h3 : conj = true → k1 ≠ 1 ∧ k2 ≠ 1) (h4 : conj = false → k1 ≠ 2 ∧ k2 ≠ 2)
    (hle : packW (k1, a1) ≤ packW (k2, a2))
    (p : ((k1, a1) :: (k2, a2) :: rest).Perm (ws.map unpackW))
    (h : NatTRun m y b n
      ((0, if conj then a1 &&& a2 else a1 ||| a2) :: kept ka (k1, a1) (kept kb (k2, a2) rest)))
    (f : ℕ → ℕ → ℕ → List ℕ → Bool)
    (hf : ∀ tag ys, NatTRun m y b n (ys.map unpackW) → f b n tag ys = true) :
    nextT m (b + 1) n ws f = true := by
  have hm1 : (k1, a1) ∈ ws.map unpackW := p.mem_iff.1 List.mem_cons_self
  obtain ⟨wa, hwa, hwa_eq⟩ := List.mem_map.1 hm1
  have hk1 : k1 < 4 := by
    have h1' := congrArg Prod.fst hwa_eq; dsimp at h1'; rw [← h1']; exact unpackW_fst_lt wa
  have hwa_p : wa = packW (k1, a1) := by rw [← packW_unpackW wa, hwa_eq]
  have p1 : ((k2, a2) :: rest).Perm ((ws.erase wa).map unpackW) := by
    have q : (ws.map unpackW).Perm (unpackW wa :: (ws.erase wa).map unpackW) := by
      simpa only [List.map_cons] using (List.perm_cons_erase hwa).map unpackW
    rw [hwa_eq] at q
    exact (p.trans q).cons_inv
  have hm2 : (k2, a2) ∈ (ws.erase wa).map unpackW := p1.mem_iff.1 List.mem_cons_self
  obtain ⟨wb, hwb, hwb_eq⟩ := List.mem_map.1 hm2
  have hk2 : k2 < 4 := by
    have h2' := congrArg Prod.fst hwb_eq; dsimp at h2'; rw [← h2']; exact unpackW_fst_lt wb
  have hwb_p : wb = packW (k2, a2) := by rw [← packW_unpackW wb, hwb_eq]
  have pr : rest.Perm (((ws.erase wa).erase wb).map unpackW) := by
    have q : ((ws.erase wa).map unpackW).Perm (unpackW wb :: ((ws.erase wa).erase wb).map unpackW) := by
      simpa only [List.map_cons] using (List.perm_cons_erase hwb).map unpackW
    rw [hwb_eq] at q
    exact (p1.trans q).cons_inv
  have hlen := trun_len h
  have hpr_len : ((ws.erase wa).erase wb).length = rest.length := by
    have := pr.length_eq; simp at this; omega
  unfold nextT
  rw [Bool.or_eq_true]; right
  rw [Bool.and_eq_true]; refine ⟨ble_true (by omega), ?_⟩
  rw [List.any_eq_true]; refine ⟨wa, hwa, ?_⟩
  rw [List.any_eq_true]; refine ⟨wb, hwb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨ble_true (by rw [hwa_p, hwb_p]; exact hle), ?_⟩
  rw [List.any_eq_true]; refine ⟨conj, by cases conj <;> simp, ?_⟩
  have hva : Nat.shiftRight wa 2 = a1 := by rw [hwa_p]; exact packW_val k1 a1 hk1
  have hka_v : Nat.land wa 3 = k1 := by rw [hwa_p]; exact packW_kind k1 a1 hk1
  have hvb : Nat.shiftRight wb 2 = a2 := by rw [hwb_p]; exact packW_val k2 a2 hk2
  have hkb_v : Nat.land wb 3 = k2 := by rw [hwb_p]; exact packW_kind k2 a2 hk2
  rw [hva, hka_v, hvb, hkb_v]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · cases conj
    · simp only [Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true']
      have h4' := h4 rfl
      refine ⟨?_, ?_⟩
      · by_contra hc; simp only [Bool.not_eq_false] at hc; exact h4'.1 (Nat.eq_of_beq_eq_true hc)
      · by_contra hc; simp only [Bool.not_eq_false] at hc; exact h4'.2 (Nat.eq_of_beq_eq_true hc)
    · simp only [Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true']
      have h3' := h3 rfl
      refine ⟨?_, ?_⟩
      · by_contra hc; simp only [Bool.not_eq_false] at hc; exact h3'.1 (Nat.eq_of_beq_eq_true hc)
      · by_contra hc; simp only [Bool.not_eq_false] at hc; exact h3'.2 (Nat.eq_of_beq_eq_true hc)
  · have hnw_eq : Nat.shiftLeft (bif conj then Nat.land a1 a2 else Nat.lor a1 a2) 2 =
        ((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) := by cases conj <;> rfl
    rw [hnw_eq]
    have hnw_un : unpackW ((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) =
        (0, if conj then a1 &&& a2 else a1 ||| a2) := by
      have : ((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) =
          packW (0, if conj then a1 &&& a2 else a1 ||| a2) := by simp [packW]
      rw [this]; exact unpackW_packW 0 _ (by omega)
    have hsub : b + 1 - 1 = b := by omega
    rw [hsub]
    cases ka <;> cases kb
    · simp only [kept, Bool.false_eq_true, ite_false, List.length_cons] at h hlen
      have hr : NatTRun m y b n
          ((((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) :: (ws.erase wa).erase wb).map unpackW) := by
        simp only [List.map_cons, hnw_un]
        exact TRun.perm (pr.cons _) h
      simp [ble_true (show ((ws.erase wa).erase wb).length ≤ b by omega), hf _ _ hr]
    · have hk20 : k2 = 0 := h2 rfl
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.length_cons] at h hlen
      have hr : NatTRun m y b n
          ((((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) :: wb :: (ws.erase wa).erase wb).map unpackW) := by
        simp only [List.map_cons, hnw_un, hwb_eq]
        exact TRun.perm ((pr.cons _).cons _) h
      simp [hk20, ble_true (show ((ws.erase wa).erase wb).length + 1 ≤ b by omega), hf _ _ hr]
    · have hk10 : k1 = 0 := h1 rfl
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.length_cons] at h hlen
      have hr : NatTRun m y b n
          ((((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) :: wa :: (ws.erase wa).erase wb).map unpackW) := by
        simp only [List.map_cons, hnw_un, hwa_eq]
        exact TRun.perm ((pr.cons _).cons _) h
      simp [hk10, ble_true (show ((ws.erase wa).erase wb).length + 1 ≤ b by omega), hf _ _ hr]
    · have hk10 : k1 = 0 := h1 rfl
      have hk20 : k2 = 0 := h2 rfl
      simp only [kept, ite_true, List.length_cons] at h hlen
      have hr : NatTRun m y b n
          ((((if conj then a1 &&& a2 else a1 ||| a2) <<< 2) :: wa :: wb :: (ws.erase wa).erase wb).map unpackW) := by
        simp only [List.map_cons, hnw_un, hwa_eq, hwb_eq]
        exact TRun.perm (((pr.cons _).cons _).cons _) h
      simp [hk10, hk20, ble_true (show ((ws.erase wa).erase wb).length + 2 ≤ b by omega), hf _ _ hr]

theorem nextT_bin {m y b n k1 k2 a1 a2 rest} {conj ka kb : Bool} {ws : List ℕ}
    (h1 : ka = true → k1 = 0) (h2 : kb = true → k2 = 0)
    (h3 : conj = true → k1 ≠ 1 ∧ k2 ≠ 1) (h4 : conj = false → k1 ≠ 2 ∧ k2 ≠ 2)
    (p : ((k1, a1) :: (k2, a2) :: rest).Perm (ws.map unpackW))
    (h : NatTRun m y b n
      ((0, if conj then a1 &&& a2 else a1 ||| a2) :: kept ka (k1, a1) (kept kb (k2, a2) rest)))
    (f : ℕ → ℕ → ℕ → List ℕ → Bool)
    (hf : ∀ tag ys, NatTRun m y b n (ys.map unpackW) → f b n tag ys = true) :
    nextT m (b + 1) n ws f = true := by
  rcases le_total (packW (k1, a1)) (packW (k2, a2)) with hle | hle
  · exact nextT_bin_sorted h1 h2 h3 h4 hle p h f hf
  · apply nextT_bin_sorted h2 h1 (fun hc => (h3 hc).symm) (fun hc => (h4 hc).symm)
      hle ((List.Perm.swap _ _ _).trans p) _ f hf
    have heq : (if conj then a1 &&& a2 else a1 ||| a2) =
        (if conj then a2 &&& a1 else a2 ||| a1) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [heq] at h
    apply TRun.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem nextT_complete {m y b n ws} (h : NatTRun m y b n (ws.map unpackW))
    (hnotdone : ¬ (ws.length = 1 ∧ (ws.headD 0 >>> 2) = y))
    (hnle : n ≤ 1)
    (f : ℕ → ℕ → ℕ → List ℕ → Bool)
    (hf : ∀ b' n' tag ys, ((b' < b ∧ n' = n) ∨ (b' = b ∧ n' < n)) →
      NatTRun m y b' n' (ys.map unpackW) → f b' n' tag ys = true) :
    nextT m b n ws f = true := by
  have key : ∀ b n xs, NatTRun m y b n xs →
      ∀ ws : List ℕ, xs.Perm (ws.map unpackW) →
      ¬ (ws.length = 1 ∧ (ws.headD 0 >>> 2) = y) → n ≤ 1 →
      (∀ b' n' tag ys, ((b' < b ∧ n' = n) ∨ (b' = b ∧ n' < n)) →
        NatTRun m y b' n' (ys.map unpackW) → f b' n' tag ys = true) →
      nextT m b n ws f = true := by
    intro b n xs h
    induction h using TRun.fold with
    | done b n k =>
      intro ws hp hnd _ _
      exfalso; apply hnd
      have hlen : ws.length = 1 := by have := hp.length_eq; simp at this; omega
      cases ws with
      | nil => simp at hlen
      | cons w rest =>
        cases rest with
        | nil =>
          simp only [List.map_cons, List.map_nil] at hp
          have heq := List.perm_singleton.1 hp.symm
          simp only [List.cons.injEq, and_true] at heq
          exact ⟨rfl, by rw [List.headD_cons]; exact congrArg Prod.snd heq⟩
        | cons _ _ => simp at hlen
    | perm hp _ ih =>
      intro ws q hnd hnle hf'
      exact ih ws (hp.trans q) hnd hnle hf'
    | @notS b' n' k a r save hs h' ih =>
      intro ws hp _ hnle hf'
      have hn0 : n' = 0 := by omega
      subst hn0
      exact nextT_not hs hp h' f (fun tag ys hys => hf' b' 0 tag ys (by right; omega) hys)
    | @binS b' n' k1 k2 a1 a2 r conj ka kb h1 h2 h3 h4 h' ih =>
      intro ws hp _ _ hf'
      exact nextT_bin h1 h2 h3 h4 hp h' f (fun tag ys hys => hf' b' n' tag ys (by left; omega) hys)
  exact key b n _ h ws (List.Perm.refl _) hnotdone hnle hf

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true)
    (T : BinaryTree (List ℕ)) (b n : ℕ)
    (ih : ∀ ys : List ℕ, NatTRun m y b n (ys.map unpackW) → btMem T ((2 * b + n) :: isort ys) = false)
    (h : List ℕ) (tag : ℕ) {ys : List ℕ} (hys : NatTRun m y b n (ys.map unpackW)) :
    hfind G T (2 * b + n) h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (trun_act_nat pi hm hy hys)
    · rfl
  · rfl

theorem closure_sound {m y nz : ℕ} {G : List (List ℕ)} (T : BinaryTree (List ℕ))
    (hp : prsOK m y nz = true) (hG : symOK m y G = true)
    (hT : ∀ x, btMem T x = true → ∃ h, stepOK m y nz G T x h = true) :
    ∀ k, ∀ b n, 2 * b + n = k → n ≤ 1 → ∀ ws : List ℕ,
      NatTRun m y b n (ws.map unpackW) → btMem T ((2 * b + n) :: isort ws) = false := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b n hbn hnle ws hws
    cases hm : btMem T ((2 * b + n) :: isort ws)
    · rfl
    · exfalso
      obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
      have hb_div : Nat.shiftRight (2 * b + n) 1 = b := by
        change (2 * b + n) >>> 1 = b; rw [Nat.shiftRight_eq_div_pow]; omega
      have hn_and : Nat.land (2 * b + n) 1 = n := by
        change (2 * b + n) &&& 1 = n; rw [Nat.and_one_is_mod]; omega
      rw [hb_div, hn_and] at hs
      have hnd : ¬ ((isort ws).length = 1 ∧ ((isort ws).headD 0 >>> 2) = y) := by
        rintro ⟨hl, hy⟩
        cases his : isort ws with
        | nil => rw [his] at hl; simp at hl
        | cons w r =>
          cases r with
          | nil =>
            rw [his] at hs hy
            simp only [List.headD_cons] at hy
            dsimp only at hs
            have hy' : Nat.shiftRight w 2 = y := hy
            rw [hy'] at hs
            simp at hs
          | cons _ _ => rw [his] at hl; simp at hl
      have hperm : ((isort ws).map unpackW).Perm (ws.map unpackW) := (perm_isort ws).map unpackW
      have hr : NatTRun m y b n ((isort ws).map unpackW) := TRun.perm hperm.symm hws
      have hn := nextT_complete hr hnd hnle
        (fun nb nn tag ys => via m y nz nb nn ys && !btMem T ((2 * nb + nn) :: isort ys) &&
          !hfind G T (2 * nb + nn) h tag ys)
        (fun nb nn tag ys hlt hys => by
          have hnn : nn ≤ 1 := by
            rcases hlt with ⟨_, rfl⟩ | ⟨_, hlt⟩ <;> omega
          have hklt : 2 * nb + nn < k := by
            rcases hlt with ⟨hlt, rfl⟩ | ⟨heq, hlt⟩ <;> omega
          have hv := via_sound_nat hp hys
          have hmem_f := ih (2 * nb + nn) hklt nb nn rfl hnn ys hys
          have hhf := hfind_false hG T nb nn (fun zs hzs => ih (2 * nb + nn) hklt nb nn rfl hnn zs hzs) h tag hys
          simp [hv, hmem_f, hhf])
      rw [hn] at hs
      simp at hs

def rootOK (m y nz : ℕ) (G : List (List ℕ)) (T : BinaryTree (List ℕ)) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via m y nz cap 1 zs || btMem T ((2 * cap + 1) :: isort zs) ||
    G.any (fun pi => btMem T ((2 * cap + 1) :: isort (zs.map (actW pi))))

theorem cert_core {m y nz : ℕ} {xs : List ℕ} {G : List (List ℕ)} {T : BinaryTree (List ℕ)} {cap : ℕ}
    (hp : prsOK m y nz = true) (hG : symOK m y G = true)
    (hT : ∀ x, btMem T x = true → ∃ h, stepOK m y nz G T x h = true)
    (hi : xs.sublists.all (rootOK m y nz G T cap) = true)
    {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatTRun m y cap 1 (ws.map unpackW)) : False := by
  have hmem := List.all_eq_true.1 hi ws (List.mem_sublists.2 hsub)
  have hv := via_sound_nat hp hr
  have hc := closure_sound T hp hG hT (2 * cap + 1) cap 1 rfl (by omega) ws hr
  have hg : (G.any fun pi => btMem T ((2 * cap + 1) :: isort (ws.map (actW pi)))) = false := by
    rw [List.any_eq_false]
    intro pi hpi
    obtain ⟨hm, hy⟩ := symOK_mem hG hpi
    rw [closure_sound T hp hG hT (2 * cap + 1) cap 1 rfl (by omega) _ (trun_act_nat pi hm hy hr)]
    simp
  unfold rootOK at hmem
  rw [hv, hc, hg] at hmem
  simp at hmem

theorem trun_liftB_succ {α inv meet join y b n ws}
    (h : @TRun α inv meet join y b n ws) : TRun inv meet join y (b + 1) n ws := by
  induction h using TRun.fold with
  | done b' n' k' => exact TRun.done (b' + 1) n' k'
  | perm hp _ ih => exact TRun.perm hp ih
  | notS save hs _ ih => exact TRun.notS save hs ih
  | binS conj ka kb h1 h2 h3 h4 _ ih => exact TRun.binS conj ka kb h1 h2 h3 h4 ih

theorem trun_liftB_le {α inv meet join y b1 b2 n ws} (hle : b1 ≤ b2)
    (h : @TRun α inv meet join y b1 n ws) : TRun inv meet join y b2 n ws := by
  induction b2, hle using Nat.le_induction with
  | base => exact h
  | succ b2 _ ih => exact trun_liftB_succ ih

theorem trun_liftN_le {α inv meet join y b n1 n2 ws} (hle : n1 ≤ n2)
    (h : @TRun α inv meet join y b n1 ws) : TRun inv meet join y b n2 ws := by
  induction n2, hle using Nat.le_induction with
  | base => exact h
  | succ n2 _ ih => exact TRun.liftN ih

theorem lb_cert_tagged {n : ℕ} (f : BFn n) (S : Finset ℕ) (l : List ℕ) (m y nz : ℕ)
    (xs : List ℕ) (G : List (List ℕ)) (L : List (List ℕ × List ℕ)) (cap : ℕ)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hSn : ∀ w ∈ S, w < n)
    (hxs : (List.ofFn fun i : Fin n => packW (if i.val ∈ S then 1 else 0, encL (fun x : Fin n → Bool => x i) l)) = xs)
    (hp : prsOK m y nz = true) (hG : symOK m y G = true)
    (hL : L.all (fun kh => stepOK m y nz G (buildBT (L.map Prod.fst)) kh.1 kh.2) = true)
    (hi : xs.sublists.all (rootOK m y nz G (buildBT (L.map Prod.fst)) cap) = true) :
    ∀ gs o, CleanL n gs → binCount gs ≤ cap → notCount gs ≤ 1 → o < n + gs.length →
      (∀ x, val gs n o x = f x) →
      (∀ w ∈ S, o ≠ w) →
      (∀ q w, w ∈ S → gs[q]? = some ⟨GateOp.not, [w]⟩ → o ≠ n + q) →
      (∀ w ∈ S, OnceProp n gs o w) → False := by
  intro gs o hcl hb hn ho hev hoS hoNotS honce
  have hrun0 := trun_live n gs o S hcl hn ho hSn hoS hoNotS honce 0 (Nat.zero_le _)
  simp only [List.drop_zero] at hrun0
  have hrun1 : TRun (invF (n := n)) meetF joinF f cap 1
      ((liveList gs n o 0).map fun a => (wTag n gs S a, val gs n a)) := by
    have hf : val gs n o = f := funext hev
    rw [← hf]
    exact trun_liftN_le hn (trun_liftB_le hb hrun0)
  have hrun2 := TRun.map (fun a : BFn n => encL a l)
    (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by rw [hm]; exact encL_inv a l)
    (fun a b => encL_and a b l)
    (fun a b => encL_or a b l) hrun1
  rw [hy] at hrun2
  have hpack_sub : ((liveList gs n o 0).map fun a => packW (wTag n gs S a, encL (val gs n a) l)).Sublist xs := by
    rw [← hxs]
    have hsub0 : (liveList gs n o 0).Sublist (List.range n) := by
      simp [liveList]
    have heq_range : (List.range n).map (fun a => packW (wTag n gs S a, encL (val gs n a) l)) =
        List.ofFn (fun i : Fin n => packW (if i.val ∈ S then 1 else 0, encL (fun x : Fin n → Bool => x i) l)) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        have hi_lt : i < n := by simpa using h1
        have hwt : wTag n gs S i = if i ∈ S then 1 else 0 := by
          unfold wTag; split_ifs with hS hge
          · rfl
          · omega
          · rfl
        have hvi : val gs n i = fun x : Fin n → Bool => x ⟨i, hi_lt⟩ := val_input gs n ⟨i, hi_lt⟩
        rw [hwt, hvi]
    rw [← heq_range]
    exact hsub0.map _
  have hmap_eq : (((liveList gs n o 0).map fun a => packW (wTag n gs S a, encL (val gs n a) l)).map unpackW) =
      (((liveList gs n o 0).map fun a => (wTag n gs S a, val gs n a)).map fun p => (p.1, encL p.2 l)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro a ha
    have halt : a < n := by
      have := (mem_liveList gs n o 0 a).1 ha; omega
    have hwt : wTag n gs S a < 4 := by
      unfold wTag; split_ifs <;> omega
    exact unpackW_packW (wTag n gs S a) (encL (val gs n a) l) hwt
  rw [← hmap_eq] at hrun2
  have hT : ∀ x, btMem (buildBT (L.map Prod.fst)) x = true →
      ∃ h, stepOK m y nz G (buildBT (L.map Prod.fst)) x h = true := by
    intro x hx
    obtain ⟨h, hmem⟩ := btMem_buildBT L x hx
    exact ⟨h, List.all_eq_true.1 hL (x, h) hmem⟩
  exact cert_core hp hG hT hi hpack_sub hrun2



abbrev CE := List (List ℕ × List ℕ)
def K4_pts : List ℕ := [0, 1, 2, 4, 8, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]
def K4_m : ℕ := 65535
def K4_y : ℕ := 65504
def K4_nz : ℕ := 5
def K4_xs : List ℕ := [175496, 210576, 247584, 260160]
def K4_G : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 4, 3, 5, 9, 10, 11, 6, 7, 8, 12, 13, 14, 15], [0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 12, 13, 10, 11, 14, 15], [0, 1, 3, 4, 2, 6, 9, 12, 13, 5, 7, 8, 10, 11, 14, 15], [0, 1, 4, 3, 2, 9, 6, 12, 13, 5, 10, 11, 7, 8, 14, 15], [0, 1, 4, 2, 3, 9, 5, 10, 11, 6, 12, 13, 7, 8, 14, 15], [0, 2, 1, 3, 4, 5, 7, 6, 8, 10, 9, 11, 12, 14, 13, 15], [0, 2, 1, 4, 3, 5, 10, 9, 11, 7, 6, 8, 12, 14, 13, 15], [0, 2, 3, 1, 4, 7, 5, 6, 8, 10, 12, 14, 9, 11, 13, 15], [0, 2, 3, 4, 1, 7, 10, 12, 14, 5, 6, 8, 9, 11, 13, 15], [0, 2, 4, 3, 1, 10, 7, 12, 14, 5, 9, 11, 6, 8, 13, 15], [0, 2, 4, 1, 3, 10, 5, 9, 11, 7, 12, 14, 6, 8, 13, 15], [0, 3, 2, 1, 4, 7, 6, 5, 8, 12, 10, 14, 9, 13, 11, 15], [0, 3, 2, 4, 1, 7, 12, 10, 14, 6, 5, 8, 9, 13, 11, 15], [0, 3, 1, 2, 4, 6, 7, 5, 8, 12, 9, 13, 10, 14, 11, 15], [0, 3, 1, 4, 2, 6, 12, 9, 13, 7, 5, 8, 10, 14, 11, 15], [0, 3, 4, 1, 2, 12, 6, 9, 13, 7, 10, 14, 5, 8, 11, 15], [0, 3, 4, 2, 1, 12, 7, 10, 14, 6, 9, 13, 5, 8, 11, 15], [0, 4, 2, 3, 1, 10, 12, 7, 14, 9, 5, 11, 6, 13, 8, 15], [0, 4, 2, 1, 3, 10, 9, 5, 11, 12, 7, 14, 6, 13, 8, 15], [0, 4, 3, 2, 1, 12, 10, 7, 14, 9, 6, 13, 5, 11, 8, 15], [0, 4, 3, 1, 2, 12, 9, 6, 13, 10, 7, 14, 5, 11, 8, 15], [0, 4, 1, 3, 2, 9, 12, 6, 13, 10, 5, 11, 7, 14, 8, 15], [0, 4, 1, 2, 3, 9, 10, 5, 11, 12, 6, 13, 7, 14, 8, 15]]
noncomputable def K4_K0 : CE := [([4,11656,259728,261984],[]),([4,175496,226960,261984],[]),([4,175496,259728,261984],[]),([5,175496,259728,261984],[]),([5,175496,259984,261984],[]),([5,241544,260016,261696],[]),([6,156,175496,259728,261984],[]),([6,444,175496,260016,261696],[]),([6,1152,245656,247584,260160],[1812,2576]),([6,1416,210576,257824,260160],[2568]),([6,1980,175496,259728,261984],[]),([6,1980,175496,260016,261696],[]),([6,1980,241544,260016,260160],[]),([6,3464,210576,247584,260160],[]),([6,11656,13968,247584,260160],[]),([6,11656,210576,245760,261984],[1798]),([6,11656,210576,247584,260160],[]),([6,11656,247584,259728,260160],[]),([6,16224,175496,210576,245760],[]),([6,16380,175496,259728,261984],[]),([6,44424,210576,247584,260160],[]),([6,140416,245656,247584,260160],[1812,2576]),([6,142728,210576,247584,260160],[]),([6,156900,245656,247584,260160],[]),([6,175496,210576,247584,260160],[]),([6,175496,210576,247584,260164],[]),([6,175496,210576,247584,260288],[1296]),([6,175496,210576,247584,261312],[1296]),([7,140416,245656,247584,260160],[1812,2576]),([7,140416,245656,247584,261312],[16,1296,1804,2576]),([7,173440,210576,257960,260160],[1298,2571]),([7,175488,210576,247584,260160],[]),([7,175496,210576,247584,260160],[]),([7,175496,210576,247584,261184],[]),([7,175496,210576,247584,261312],[1296]),([7,175496,210576,247584,261568],[1296,1803]),([7,175496,210576,255904,261312],[1292]),([7,175496,210576,257416,261984],[9,1798]),([7,175496,210576,257824,261576],[9,2568]),([7,175496,259728,261984],[41,99]),([7,175496,260016,261840,261984],[2946,3204]),([8,0,175496,210576,247584,260160],[]),([8,12,175496,210576,247584,260160],[1289]),([8,136,175496,210576,247584,260160],[]),([8,156,175496,210576,245760,261984],[2576,2822]),([8,156,175496,210576,247584,260160],[]),([8,444,175496,210576,247584,260160],[]),([8,444,175496,210576,247584,261696],[]),([8,1152,175496,210576,247584,260160],[2561]),([8,1416,174080,210576,247584,260160],[2050,3588]),([8,1416,175496,210576,247584,260160],[]),([8,1416,176060,210576,247584,260160],[]),([8,1416,210576,245656,247584,260160],[]),([8,1944,175496,210576,247584,260160],[]),([8,1980,140416,245656,247584,260160],[2828,3852]),([8,1980,174080,210576,247584,261576],[2060,2824]),([8,1980,175496,210576,247584,260160],[]),([8,1980,175496,210576,247584,261312],[2060]),([8,1980,175496,210576,255904,260160],[2060]),([8,1980,175496,210576,257824,260160],[3848]),([8,4092,175496,210576,247584,260160],[]),([8,11656,16380,210576,247584,260160],[]),([8,11656,175496,210576,247584,260160],[]),([8,11656,210576,245760,247584,260160],[1809]),([8,11656,210576,247584,260160],[]),([8,16380,175496,210576,245760,261984],[1926,2822]),([8,16380,175496,210576,247584,260160],[1926]),([8,16380,175496,247584,259728,260160],[1934,2694,3735]),([8,65532,175496,210576,247584,260160],[1926,2702,3734]),([8,140416,175496,210576,247584,260160],[2561]),([8,140680,175496,210576,247584,260160],[]),([8,141244,175496,210576,247584,260160],[]),([8,175496,175496,210576,247584,260160],[]),([8,175496,175516,210576,247584,260160],[]),([8,175496,176024,210576,247584,260160],[]),([8,175496,176060,210576,247584,260160],[]),([8,175496,180220,210576,247584,260160],[2182]),([8,175496,210576,245656,247584,260160],[]),([8,175496,210576,245692,247584,260160],[]),([8,175496,210576,247584,260160],[]),([8,175496,210576,247584,260160,262140],[]),([8,175496,210576,247584,260316,261984],[3216]),([9,132096,175496,210576,247584,260160],[18]),([9,140416,175496,210576,247584,260160],[16,2561]),([9,140416,175496,210576,247584,261312],[16]),([9,140416,175496,245656,247584,260160],[73,2564,3587]),([9,140416,245656,247584,260160],[48,112,161,1812,1840,1857,2576,2612]),([9,173440,175496,210576,247584,260160],[18,1795,2050,2561]),([9,175496,175496,210576,247584,260160],[9]),([9,175496,210576,241544,247584,260160],[9,146,1801,2820]),([9,175496,210576,245656,247584,260160],[144]),([9,175496,210576,247584,260160],[41,99,161]),([9,175496,210576,247584,260160,262072],[274,4498]),([9,175496,210576,247584,261312],[41,99,161,236,1296,1321,1347]),([9,175496,210576,247584,261576,261840],[1292,2951,3713]),([10,0,1980,175496,210576,247584,260160],[]),([10,0,175496,210576,247584,260160],[1830,2604,3634]),([10,156,175496,210576,247584,260160],[1830,1958,2604,3635]),([10,156,175496,210576,247584,260160,261984],[2561]),([10,1416,1980,175496,210576,247584,260160],[]),([10,1416,175496,210576,247584,260160],[1830,2606,2722,2850,3620]),([10,1980,140416,175496,210576,247584,260160],[]),([10,1980,174080,175496,210576,247584,260160],[2818]),([10,1980,175496,176060,210576,247584,260160],[]),([10,1980,175496,210576,245656,247584,260160],[1926]),([10,1980,175496,210576,247584,260160,261576],[1289]),([10,1980,175496,210576,247584,260160,262140],[]),([10,16380,175496,210576,245760,247584,260160],[1926,2822,3724,5011]),([10,16380,175496,210576,247584,260160],[1830,1926,1958,1990,2732,3763]),([10,175496,176060,210576,247584,260160],[2214,2850,2990,3625,4004]),([10,175496,210576,247584,260160,262140],[4038,4300,4562]),([11,140416,175496,210576,247584,260160],[16,48,105,163,225,1830,2086,2561,2604,2625,3635,3745]),([11,175496,210576,245656,247584,260160],[41,99,144,176,225,1446,2246,2601,2851,3244,3626,3876,4129,4275]),([12,1980,175496,210576,247584,260160],[1830,1894,1958,2022,2604,2668,2732,2796,2914,3042,3176,3304,4198,4326,4460,4588]),([13,175496,210576,247584,260160],[41,99,161,1890,2018,2152,2280,2660,2788,2922,3050,3184,3312])]
noncomputable def K4_LL : List CE := [K4_K0]
noncomputable def K4_L : CE := K4_LL.flatten
noncomputable def K4_T : BinaryTree (List ℕ) := buildBT (K4_L.map Prod.fst)
set_option maxRecDepth 200000 in
theorem K4_c0 : K4_K0.all (fun kh => stepOK K4_m K4_y K4_nz K4_G K4_T kh.1 kh.2) = true := by decide +kernel
theorem K4_hL : K4_L.all (fun kh => stepOK K4_m K4_y K4_nz K4_G K4_T kh.1 kh.2) = true := by
  apply all_flatten; simp only [K4_LL, List.all_cons, List.all_nil, Bool.and_true, K4_c0]
def G3_pts : List ℕ := [1, 3, 6, 8, 12, 16, 20, 32, 34, 5, 9, 10, 17, 18, 24, 33, 36, 40, 48]
def G3_m : ℕ := 524287
def G3_y : ℕ := 523776
def G3_nz : ℕ := 9
def G3_xs : List ℕ := [153612, 42009, 264529, 602208, 1163648, 1967616]
def G3_G : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18], [7, 8, 2, 3, 4, 5, 6, 0, 1, 16, 17, 11, 18, 13, 14, 15, 9, 10, 12], [0, 1, 2, 5, 6, 3, 4, 7, 8, 9, 12, 13, 10, 11, 14, 15, 16, 18, 17], [7, 8, 2, 5, 6, 3, 4, 0, 1, 16, 18, 13, 17, 11, 14, 15, 9, 12, 10], [3, 4, 2, 0, 1, 7, 8, 5, 6, 11, 10, 9, 17, 16, 15, 14, 13, 12, 18], [5, 6, 2, 0, 1, 7, 8, 3, 4, 13, 12, 9, 18, 16, 15, 14, 11, 10, 17], [3, 4, 2, 7, 8, 0, 1, 5, 6, 11, 17, 16, 10, 9, 15, 14, 13, 18, 12], [5, 6, 2, 7, 8, 0, 1, 3, 4, 13, 18, 16, 12, 9, 15, 14, 11, 17, 10]]
noncomputable def k0 : CE := [([4,153604,1964528,2074112],[]),([4,153612,1964528,2073088],[]),([4,153612,1964528,2074112],[]),([4,194572,1964528,2033152],[]),([5,153612,1964528,2074112],[]),([5,153612,1964528,2078208],[]),([5,153612,1964528,2094592],[]),([5,194572,1964528,2033152],[]),([5,219148,1964528,2029056],[]),([5,219148,1964528,2074112],[]),([5,219148,1964528,2094592],[]),([5,260108,1964528,2074112],[]),([5,751724,1898512,2082688],[]),([6,23036,153612,1964528,2074112],[]),([6,40960,153612,1964528,2033152],[]),([6,42009,602144,1558912,1990156],[2564]),([6,42009,602208,1558656,1990156],[2564]),([6,42009,602208,1558912,1990156],[2564]),([6,42009,733280,1427840,1990156],[2565]),([6,65536,153612,1964528,2008576],[1281]),([6,66016,602208,1558912,2031132],[]),([6,106496,153604,1964528,1967616],[1281]),([6,106496,153612,1858016,1967616],[]),([6,106496,153612,1858032,1967616],[]),([6,106496,153612,1898992,1967616],[]),([6,106496,153612,1964528,1967616],[1281]),([6,106992,602208,1558912,2031132],[]),([6,107528,153612,1964528,1967616],[]),([6,107544,153612,1964512,1967616],[]),([6,129532,153612,1964528,2074112],[]),([6,129532,260108,1964528,1967616],[]),([6,129532,602208,1558912,2031132],[]),([6,153612,239116,1964528,1967616],[]),([6,153612,305168,1700320,2033152],[]),([6,153612,370704,1700320,1967616],[]),([6,153612,602208,1370128,2082688],[]),([6,153612,1964528,1989604,2074112],[]),([6,153612,1964528,1990652,2074112],[]),([6,153612,1964528,2031612,2074112],[]),([6,153612,1964528,2074136,2096100],[]),([7,42009,153612,1923408,2033152],[]),([7,42009,264529,1831392,2055692],[]),([7,42009,395600,1700320,2055692],[]),([7,42009,602208,1163648,1988608],[]),([7,42009,602208,1294720,1988608],[]),([7,42009,602208,1558912,1990156],[2564]),([7,42009,602208,1563008,1990156],[2564]),([7,42009,602208,1990156,2087296],[1796]),([7,42009,733280,1427840,1990156],[2565]),([7,42009,733280,1558912,1990156],[2564]),([7,42009,733280,1956224,1990156],[2564]),([7,42009,733280,1990156,2087296],[1796]),([7,42009,997472,1558912,1990156],[2564]),([7,61440,153612,1964528,2033152],[]),([7,61440,219148,1964528,1967616],[1281]),([7,65536,153612,1964528,2008576],[1281]),([7,65536,153612,1964528,2029056],[]),([7,65536,153612,1964528,2074112],[]),([7,106496,153612,1964528,1967616],[1281]),([7,106496,153612,1964528,2033152],[1281]),([7,106496,153612,1964528,2074112],[]),([7,106504,153612,1964528,1967616],[1281]),([7,107544,153612,1857872,1967616],[]),([7,107544,153612,1964528,2074112],[]),([7,107544,395600,1700320,1990156],[]),([7,107544,481628,1700320,2035536],[]),([7,107544,523612,1700320,2076504],[]),([7,110592,153612,1964528,1967616],[1281]),([7,126976,153612,1964528,1967616],[1281]),([7,126976,219148,1964528,1967616],[1281]),([7,153612,260108,1964528,1967616],[1,1281]),([7,153612,330064,1700320,2074112],[]),([7,153612,371024,1700320,2074112],[]),([7,153612,602208,1427920,2074112],[]),([7,153612,602208,1558912,2031132],[1,2564]),([7,153612,602208,1898512,2082688],[]),([7,153612,866672,1700320,2074112],[]),([7,153612,1700320,1964528,2074112],[68]),([7,153612,1964528,2074112],[33,100]),([7,153612,1964528,2074136,2095072],[]),([7,195612,1833452,1964528,2033152],[]),([7,261148,372056,1700320,2074136],[]),([7,751724,1964528,2031132,2082688],[]),([8,14364,264529,602208,1300876,2016768],[]),([8,23036,153612,264529,1700320,2074112],[]),([8,40960,65536,153612,1964528,1967616],[1793,2049]),([8,40960,153612,264529,1700320,2033152],[1286,3588]),([8,40976,264529,602208,1294720,1990156],[]),([8,40976,395600,602208,1163648,1990156],[]),([8,40984,153612,264529,1700320,2033152],[]),([8,40984,219148,264529,1700320,1967616],[]),([8,40984,264529,602208,1294720,1990156],[]),([8,40984,395600,602208,1163648,1990156],[]),([8,41992,395600,602208,1163648,1990156],[3588]),([8,42008,153612,264529,1700320,2033152],[]),([8,42008,264529,602208,1294720,1990156],[]),([8,42008,395600,602208,1163648,1990156],[]),([8,42009,61920,153612,1964528,2033152],[]),([8,42009,73824,153612,1956224,1967616],[]),([8,42009,73824,866672,1294720,1990156],[]),([8,42009,73824,997744,1163648,1990156],[]),([8,42009,77856,919888,1163648,1990156],[]),([8,42009,77920,153612,1956224,1967616],[]),([8,42009,77920,264529,1819008,1990156],[]),([8,42009,77920,866672,1294720,1990156],[]),([8,42009,77920,919888,1163648,1990156],[]),([8,42009,77920,997744,1163648,1990156],[]),([8,42009,80240,153612,1950080,2045536],[]),([8,42009,80240,940044,1163648,2045536],[]),([8,42009,96364,1300876,1964528,1967616],[]),([8,42009,106656,602208,1558992,1990156],[]),([8,42009,106992,153612,1931360,2082688],[]),([8,42009,106992,602208,1558912,1990156],[]),([8,42009,127148,602208,1558992,1990156],[]),([8,42009,127456,153612,1964528,2033152],[]),([8,42009,127456,219148,1964528,1967616],[]),([8,42009,129532,153612,1931360,2082688],[]),([8,42009,129532,602208,1558912,1990156],[]),([8,42009,131072,602208,1427840,1990156],[3588]),([8,42009,137228,1163648,1931360,1967616],[]),([8,42009,153612,264529,1683936,2049536],[]),([8,42009,153612,264529,1700320,2033152],[]),([8,42009,153612,264529,1700320,2037248],[]),([8,42009,153612,276848,1700320,2033152],[]),([8,42009,153612,305648,1700320,2033152],[]),([8,42009,153612,326128,1700320,2033152],[]),([8,42009,153612,329744,1700320,1967616],[]),([8,42009,153612,330064,1634464,2033152],[]),([8,42009,153612,330064,1634784,2033152],[]),([8,42009,153612,330064,1700000,1967616],[]),([8,42009,153612,330064,1700064,2033152],[]),([8,42009,153612,330064,1700320,2033152],[]),([8,42009,153612,342384,1700320,2033152],[]),([8,42009,153612,371184,1700320,2033152],[]),([8,42009,153612,391664,1700320,2033152],[]),([8,42009,153612,602208,1427840,1967616],[]),([8,42009,153612,602208,1427840,1969664],[]),([8,42009,153612,602208,1431936,1967616],[]),([8,42009,153612,602208,1950080,1982064],[]),([8,42009,153612,602208,1956224,1967616],[]),([8,42009,153612,651744,1427920,2033152],[]),([8,42009,153612,800880,1700320,2033152],[]),([8,42009,153612,800880,1950080,2045536],[]),([8,42009,153612,801136,1700320,2033152],[]),([8,42009,153612,801136,1950080,2045536],[]),([8,42009,153612,862576,1700320,2033152],[]),([8,42009,153612,862576,1950080,2045536],[]),([8,42009,153612,866400,1427840,1967616],[]),([8,42009,153612,866672,1634784,2033152],[]),([8,42009,153612,866672,1696224,2033152],[])]
noncomputable def k1 : CE := [([8,42009,153612,866672,1700064,2033152],[]),([8,42009,153612,866672,1700320,2033152],[]),([8,42009,153612,866672,1950080,2041440],[]),([8,42009,153612,866672,1950080,2045536],[]),([8,42009,153612,1634784,1964528,2033152],[]),([8,42009,153612,1700320,1898992,2033152],[]),([8,42009,153612,1700320,1944048,2033152],[]),([8,42009,153612,1700320,1964528,2033152],[]),([8,42009,153612,1767084,1964528,2033152],[]),([8,42009,153612,1832684,1964528,2033152],[]),([8,42009,153612,1832940,1964528,2033152],[]),([8,42009,153612,1914464,1964528,2082688],[]),([8,42009,153612,1944048,2045536,2082688],[]),([8,42009,153612,1948144,2045536,2082688],[]),([8,42009,153612,1964528,2041440,2082688],[]),([8,42009,153612,1964528,2045536,2082688],[]),([8,42009,153612,1964528,2045536,2082700],[]),([8,42009,204896,866672,1163648,1990156],[]),([8,42009,208992,866672,1163648,1990156],[]),([8,42009,219148,264529,1634784,2033152],[]),([8,42009,219148,264529,1700320,2033152],[]),([8,42009,227436,866672,1163648,1973760],[]),([8,42009,272752,602208,1294720,1990156],[]),([8,42009,272752,733280,1163648,1990156],[]),([8,42009,338288,602208,1294720,1990156],[]),([8,42009,338288,733280,1163648,1990156],[]),([8,42009,342384,602208,1294720,1990156],[]),([8,42009,342384,733280,1163648,1990156],[]),([8,42009,342384,751724,1163648,1973760],[]),([8,42009,371184,602208,1294720,1990156],[]),([8,42009,371184,602208,1296768,1990156],[]),([8,42009,371184,602208,1298816,1990156],[]),([8,42009,371184,733280,1294720,1990156],[]),([8,42009,395264,602144,1163648,1990156],[2050,3588]),([8,42009,395264,602208,1163648,1594892],[3588]),([8,42009,395264,602208,1163648,1859084],[3588]),([8,42009,395264,602208,1163648,1990156],[2050,3588]),([8,42009,395280,602208,1163648,1990156],[]),([8,42009,395344,602208,1163648,1990156],[]),([8,42009,395344,602208,1294720,1990156],[]),([8,42009,395344,733280,1163648,1990156],[]),([8,42009,395600,602144,1163392,1990156],[]),([8,42009,395600,602144,1163648,1990156],[]),([8,42009,395600,602144,1294720,1990156],[]),([8,42009,395600,602208,1163648,1990156],[]),([8,42009,395600,602208,1294464,1990156],[]),([8,42009,395600,602208,1294720,1990156],[]),([8,42009,399440,602208,1163648,1990156],[]),([8,42009,399696,602208,1163392,1990156],[]),([8,42009,399696,602208,1163648,1990156],[]),([8,42009,403824,602208,1163648,1990156],[]),([8,42009,415756,602208,1163648,1969664],[]),([8,42009,469360,602208,1163648,1990156],[]),([8,42009,473456,602208,1163648,1990156],[]),([8,42009,502256,602208,1163648,1990156],[]),([8,42009,502256,602208,1294720,1990156],[]),([8,42009,506352,602208,1163648,1990156],[]),([8,42009,602144,997744,1163648,1990156],[]),([8,42009,602144,1163648,1558992,1990156],[]),([8,42009,602144,1558992,1701548,1990156],[]),([8,42009,602208,652972,1558992,1990156],[]),([8,42009,602208,771968,1427920,1464332],[]),([8,42009,602208,800880,1294720,1990156],[]),([8,42009,602208,801136,1294720,1990156],[]),([8,42009,602208,866672,1294720,1990156],[]),([8,42009,602208,899568,1294720,1990156],[]),([8,42009,602208,931952,1163648,1990156],[]),([8,42009,602208,932208,1163648,1990156],[]),([8,42009,602208,933500,1558912,1990156],[3588]),([8,42009,602208,940044,1163648,1982064],[]),([8,42009,602208,997488,1163648,1990156],[]),([8,42009,602208,997744,1163648,1990156],[]),([8,42009,602208,1030640,1163648,1990156],[]),([8,42009,602208,1177260,1990156,2083280],[]),([8,42009,602208,1294720,1362320,1990156],[]),([8,42009,602208,1294720,1362384,1990156],[]),([8,42009,602208,1294720,1427920,1990156],[]),([8,42009,602208,1294720,1436144,1990156],[]),([8,42009,602208,1294720,1493392,1990156],[]),([8,42009,602208,1294720,1493456,1990156],[]),([8,42009,602208,1294720,1558992,1990156],[]),([8,42009,602208,1294720,1567216,1990156],[]),([8,42009,602208,1298828,1427920,1986048],[]),([8,42009,602208,1300876,1362320,1986048],[]),([8,42009,602208,1300876,1362384,1986048],[]),([8,42009,602208,1300876,1427920,1986048],[]),([8,42009,602208,1494940,1558912,1990156],[3589]),([8,42009,602208,1558912,1701548,1990156],[3588]),([8,42009,602208,1558912,1701884,1990156],[3588]),([8,42009,602208,1558912,1966076,1990156],[3588]),([8,42009,602208,1558992,1701548,1990156],[]),([8,42009,602208,1558992,1701804,1990156],[]),([8,42009,602208,1558992,1832620,1990156],[]),([8,42009,602208,1558992,1832876,1990156],[]),([8,42009,602208,1558992,1834668,1990156],[]),([8,42009,602208,1558992,1990156,2096812],[2564]),([8,42009,733280,1427920,1832876,1990156],[]),([8,42009,733280,1558992,1701548,1990156],[]),([8,42009,997744,1558992,1701548,1990156],[]),([8,47128,751724,866672,1163648,1967616],[]),([8,48144,751724,866672,1163648,1967616],[]),([8,48152,227436,866672,1163648,1967616],[]),([8,48152,342384,751724,1163648,1967616],[]),([8,48152,751724,800880,1163648,1967616],[]),([8,48152,751724,801136,1163648,1967616],[]),([8,48152,751724,866672,1163648,1966592],[]),([8,48152,751724,866672,1163648,1967616],[]),([8,48156,751724,866672,1163648,1967616],[]),([8,62476,395600,602208,1163648,1990156],[3588]),([8,62492,395600,602208,1163648,1990156],[]),([8,63516,227436,866672,1163648,1967616],[]),([8,63516,342384,751724,1163648,1967616],[]),([8,63516,395600,602208,1163648,1990156],[]),([8,63516,602208,1300876,1427920,1967616],[]),([8,63516,602208,1300876,1964528,1967616],[]),([8,64540,227436,866672,1163648,1967616],[]),([8,64540,342384,751724,1163648,1967616],[]),([8,64540,395600,602208,1163648,1990156],[]),([8,64540,602208,1300876,1427920,1967616],[]),([8,64540,602208,1300876,1964528,1967616],[]),([8,65536,153612,305168,1700320,1967616],[1281]),([8,66016,395264,602208,1163648,2031132],[1284,2050]),([8,77920,153612,1964528,2008600,2082688],[]),([8,77920,195612,1300876,1964528,1967616],[]),([8,106496,129532,153612,1964528,1967616],[]),([8,106496,153612,396828,1964528,1967616],[1286,3588]),([8,106496,153612,933500,1964528,1967616],[1286,3588]),([8,106496,153612,1964528,1967616,1989604],[1281,4481]),([8,106496,153612,1964528,1967616,1990652],[1281]),([8,106496,153612,1964528,1967616,2031612],[1281]),([8,106520,153612,330064,1700320,1967616],[]),([8,106520,153612,866672,1700320,1967616],[]),([8,106520,153612,1700320,1964528,1967616],[]),([8,107528,153612,602208,1427920,1967616],[]),([8,107544,127456,153612,1964528,1967616],[]),([8,107544,153604,330064,1700320,1967616],[]),([8,107544,153604,866672,1700320,1967616],[]),([8,107544,153604,1700320,1964528,1967616],[]),([8,107544,153612,330064,1700064,1967616],[]),([8,107544,153612,330064,1700320,1967616],[]),([8,107544,153612,342384,1700320,1967616],[]),([8,107544,153612,371184,1700320,1967616],[]),([8,107544,153612,391664,1700320,1967616],[]),([8,107544,153612,602208,1427904,1967616],[]),([8,107544,153612,602208,1956320,1967616],[]),([8,107544,153612,651744,1427920,1967616],[]),([8,107544,153612,866672,1700064,1967616],[]),([8,107544,153612,866672,1700320,1967616],[]),([8,107544,153612,1700320,1858016,1967616],[]),([8,107544,153612,1700320,1858032,1967616],[])]
noncomputable def k2 : CE := [([8,107544,153612,1700320,1898992,1967616],[]),([8,107544,153612,1700320,1964528,1967616],[]),([8,107544,153612,1832684,1964528,1967616],[]),([8,107544,153612,1832940,1964528,1967616],[]),([8,107544,153612,1964528,1967616,2096100],[1281]),([8,107608,153612,1427920,1700256,1967616],[]),([8,107608,153612,1832876,1964528,1967616],[]),([8,153604,602208,858464,1163648,2008600],[]),([8,153604,602208,1427920,2008600,2082688],[]),([8,153612,173596,1700320,1964528,2033152],[]),([8,153612,173596,1964528,2045536,2082688],[]),([8,153612,195612,602208,1427840,1967616],[]),([8,153612,239132,1700320,1964528,1967616],[]),([8,153612,305168,602208,1163648,1967616],[]),([8,153612,305488,602208,1163648,2008576],[]),([8,153612,325648,602208,1163648,1967616],[1799,2566]),([8,153612,330064,437788,1700320,2033152],[]),([8,153612,330064,503324,1700320,1967616],[]),([8,153612,330064,1700320,1989604,2074136],[]),([8,153612,372056,1700320,1989604,2074136],[]),([8,153612,437788,866672,1700320,2033152],[]),([8,153612,437788,1700320,1964528,2033152],[]),([8,153612,437788,1964528,2045536,2082688],[]),([8,153612,503324,866672,1700320,1967616],[]),([8,153612,503324,1700320,1964528,1967616],[]),([8,153612,602208,1163648,1964528,2008576],[]),([8,153612,602208,1411536,2008600,2082688],[]),([8,153612,602208,1411536,2031132,2082688],[]),([8,153612,602208,1427856,2008600,2082688],[]),([8,153612,602208,1427904,2008600,2082688],[]),([8,153612,602208,1427920,1502748,2082688],[]),([8,153612,602208,1427920,1506844,2082688],[]),([8,153612,602208,1427920,1558400,2008600],[]),([8,153612,602208,1427920,1558400,2031132],[]),([8,153612,602208,1427920,2008600,2082688],[]),([8,153612,602208,1427920,2008600,2084740],[]),([8,153612,602208,1427920,2008600,2086820],[]),([8,153612,602208,1427920,2008600,2088836],[]),([8,153612,602208,1427920,2008604,2082688],[]),([8,153612,602208,1427920,2010652,2082688],[]),([8,153612,602208,1427920,2012700,2082688],[]),([8,153612,602208,1427920,2014748,2082688],[]),([8,153612,602208,1427920,2027036,2082688],[]),([8,153612,602208,1427920,2031132,2066304],[]),([8,153612,602208,1427920,2031132,2082688],[]),([8,153612,602208,1427920,2074136,2087908],[]),([8,153612,602208,1427952,2031132,2082688],[]),([8,153612,602208,1436144,2031132,2082688],[]),([8,153612,734828,1964528,2008600,2082688],[]),([8,153612,751276,1948016,2008600,2082688],[]),([8,153612,866672,1700064,2008600,2082688],[]),([8,153612,866672,1700320,1989604,2074136],[]),([8,153612,1700320,1964528,1989604,2074136],[]),([9,22528,42009,602208,1163648,1966080],[]),([9,42008,153612,264529,1700320,2033152],[]),([9,42008,264529,602208,1294720,1990156],[]),([9,42008,395600,602208,1163648,1990156],[]),([9,42009,65536,153612,1857872,1967616],[]),([9,42009,65536,264529,1831392,1990156],[1284]),([9,42009,65536,395600,1700320,1990156],[]),([9,42009,65536,481628,1700320,2035536],[]),([9,42009,131072,602208,1163648,1857536],[]),([9,42009,131072,602208,1427840,1990156],[3588]),([9,42009,131072,602208,1558912,1990156],[1284,3588]),([9,42009,131072,602208,1956224,1990156],[3588]),([9,42009,151552,264529,1700320,2033152],[]),([9,42009,153612,264529,1650784,1819008],[]),([9,42009,153612,264529,1650784,2049536],[]),([9,42009,153612,264529,1658880,1967616],[]),([9,42009,153612,264529,1658880,2033152],[]),([9,42009,153612,264529,1667168,2033152],[]),([9,42009,153612,264529,1667168,2049536],[]),([9,42009,153612,264529,1700320,1769472],[]),([9,42009,153612,264529,1700320,2033152],[]),([9,42009,153612,264529,1700320,2037248],[]),([9,42009,153612,264529,1700320,2053632],[]),([9,42009,153612,264529,1781856,1819008],[]),([9,42009,153612,264529,1831392,2033152],[]),([9,42009,153612,268624,1700320,2033152],[]),([9,42009,153612,285008,1700320,2033152],[]),([9,42009,153612,330064,1700320,2033152],[]),([9,42009,153612,330064,1964528,2033152],[]),([9,42009,153612,334160,1700320,2037248],[]),([9,42009,153612,395600,1700320,2033152],[]),([9,42009,153612,593920,1329488,1967616],[]),([9,42009,153612,602208,1313104,2049536],[]),([9,42009,153612,602208,1329488,2033152],[]),([9,42009,153612,602208,1395024,2033152],[]),([9,42009,153612,602208,1395024,2049536],[]),([9,42009,153612,602208,1425792,1986048],[]),([9,42009,153612,602208,1427840,1967616],[]),([9,42009,153612,602208,1427840,1986048],[]),([9,42009,153612,602208,1431936,1967616],[]),([9,42009,153612,602208,1558912,1967616],[1286,3588]),([9,42009,153612,602208,1558912,1990156],[65,1284]),([9,42009,153612,602208,1950080,1973760],[]),([9,42009,153612,602208,1956224,1967616],[]),([9,42009,153612,602208,1956224,1973760],[]),([9,42009,153612,602208,1956224,2045536],[]),([9,42009,153612,604256,1950080,1967616],[]),([9,42009,153612,751724,1956224,1967616],[67]),([9,42009,153612,788816,1700320,2033152],[]),([9,42009,153612,854352,1700320,2033152],[]),([9,42009,153612,866400,1956224,1967616],[]),([9,42009,153612,866672,1427920,2033152],[]),([9,42009,153612,866672,1700320,2033152],[]),([9,42009,153612,866672,1700320,2037248],[]),([9,42009,153612,866672,1700320,2049536],[]),([9,42009,153612,866672,1833452,2049536],[]),([9,42009,153612,866672,1950080,2045536],[]),([9,42009,153612,866672,1956224,2045536],[]),([9,42009,153612,866672,2045536,2081152],[]),([9,42009,153612,1700320,1837392,2033152],[]),([9,42009,153612,1700320,1902928,2033152],[]),([9,42009,153612,1700320,1964528,2033152],[]),([9,42009,153612,1700320,1964528,2037248],[]),([9,42009,153612,1833452,1964528,2033152],[]),([9,42009,153612,1912928,1964528,2082688],[]),([9,42009,153612,1915248,2045536,2082688],[]),([9,42009,153612,1931360,1967616,2088844],[]),([9,42009,153612,1931360,1990156,2082688],[]),([9,42009,153612,1964528,2033152,2095072],[]),([9,42009,153612,1964528,2045536,2082688],[]),([9,42009,153612,1964528,2045536,2088844],[]),([9,42009,196608,264529,1700320,1990156],[]),([9,42009,219148,264529,1700320,1971712],[]),([9,42009,219148,264529,1700320,1988096],[]),([9,42009,219148,264529,1700320,2033152],[]),([9,42009,219148,264529,1700320,2037248],[]),([9,42009,219148,264529,1700320,2053632],[]),([9,42009,219148,330064,1700320,2033152],[]),([9,42009,219148,330064,1700320,2035536],[]),([9,42009,219148,866672,1700320,2033152],[]),([9,42009,219148,1700320,1964528,2033152],[]),([9,42009,264529,737280,1700320,1990156],[]),([9,42009,268624,602208,1294720,1990156],[]),([9,42009,268624,733280,1163648,1990156],[]),([9,42009,330064,602208,1294720,1990156],[]),([9,42009,395264,602208,1163648,1990156],[2050,3588]),([9,42009,395264,602208,1294720,1990156],[2050,3588]),([9,42009,395264,602208,1558912,1990156],[1284,3588]),([9,42009,395328,602208,1163648,1990156],[2050,3588]),([9,42009,395600,593920,1163648,1990156],[]),([9,42009,395600,602208,1163648,1593344],[3588]),([9,42009,395600,602208,1163648,1726476],[]),([9,42009,395600,602208,1163648,1990156],[]),([9,42009,395600,602208,1163648,1990220],[]),([9,42009,395600,602208,1163648,1990492],[]),([9,42009,395600,602208,1163648,2055692],[]),([9,42009,395600,602208,1163712,1990156],[])]
noncomputable def k3 : CE := [([9,42009,395600,602208,1167744,1990156],[]),([9,42009,395600,602208,1294720,1990156],[]),([9,42009,395600,602208,1296768,1990156],[]),([9,42009,395600,602208,1558912,1990156],[3588]),([9,42009,395600,602208,1558992,1990156],[]),([9,42009,395600,602208,1692032,1990156],[]),([9,42009,395600,733280,1294720,1990156],[]),([9,42009,395600,733280,1558992,1990156],[]),([9,42009,395600,997744,1558992,1990156],[1284]),([9,42009,399360,602208,1163648,1990156],[2050,3588]),([9,42009,399696,602208,1163648,1990156],[]),([9,42009,399696,602208,1298816,1990156],[]),([9,42009,399696,602208,1563088,1990156],[65]),([9,42009,399696,733280,1163648,1990156],[]),([9,42009,399696,997744,1163648,1990156],[67]),([9,42009,416080,602208,1163648,1988096],[]),([9,42009,416080,602208,1163648,1990156],[]),([9,42009,416092,602208,1163648,1970000],[]),([9,42009,416092,602208,1167744,1974096],[]),([9,42009,416092,602208,1558992,1990156],[65]),([9,42009,461136,602208,1163648,1990156],[]),([9,42009,481628,602208,1163648,2035536],[]),([9,42009,602208,792576,1294720,1990156],[2050,3588]),([9,42009,602208,792912,1294720,1990156],[]),([9,42009,602208,866672,1294720,1990156],[]),([9,42009,602208,866672,1298816,1990156],[]),([9,42009,602208,866672,1300864,1990156],[]),([9,42009,602208,923648,1163648,1990156],[2050,3588]),([9,42009,602208,923984,1163648,1990156],[]),([9,42009,602208,940044,1163648,1973760],[]),([9,42009,602208,997472,1163648,1990156],[66,2050,3588]),([9,42009,602208,997744,1163648,1990156],[]),([9,42009,602208,997744,1294720,1990156],[]),([9,42009,602208,1001808,1163648,1990156],[]),([9,42009,602208,1005836,1163648,2047856],[]),([9,42009,602208,1014128,1163648,1990156],[]),([9,42009,602208,1014140,1163648,1990144],[]),([9,42009,602208,1163648,1988620,2097136],[]),([9,42009,602208,1163648,1990156,2095600],[]),([9,42009,602208,1294720,1329152,1990156],[2818,3589]),([9,42009,602208,1294720,1329488,1990156],[]),([9,42009,602208,1294720,1427920,1990156],[]),([9,42009,602208,1294720,1460224,1990156],[2818,3589]),([9,42009,602208,1294720,1460560,1990156],[]),([9,42009,602208,1294720,1558992,1990156],[]),([9,42009,602208,1294720,1964528,1990156],[]),([9,42009,602208,1294720,1990156,2095600],[]),([9,42009,602208,1296768,1427920,1990156],[]),([9,42009,602208,1298816,1427920,1990156],[]),([9,42009,602208,1298816,1563088,1990156],[]),([9,42009,602208,1300876,1427920,1986048],[]),([9,42009,602208,1300876,1427920,1990144],[]),([9,42009,602208,1300876,1427920,2051648],[]),([9,42009,602208,1300876,1558992,1990156],[]),([9,42009,602208,1300876,1964528,1986048],[]),([9,42009,602208,1300876,1964528,1990144],[]),([9,42009,602208,1558912,1990156],[164,2564,2596]),([9,42009,602208,1558992,1990156,1990492],[]),([9,42009,602208,1558992,1990156,2088844],[2564]),([9,42009,620640,1300876,1427920,1986048],[]),([9,42009,677900,1427920,2045536,2082688],[]),([9,42009,733280,866672,1294720,1990156],[]),([9,42009,733280,997744,1294720,1990156],[]),([9,42009,733280,1300876,1427920,1990156],[]),([9,42009,733280,1427920,1990156,2088844],[2565]),([9,42009,743436,1427920,2045536,2082688],[]),([9,42009,749664,1427920,1990156,2082688],[]),([9,42009,751724,1427920,2045536,2088844],[]),([9,42009,751724,1964528,1990156,2082688],[]),([9,42072,395600,602208,1163648,1990156],[]),([9,46104,395600,602208,1163648,1990156],[]),([9,46104,416092,602208,1163648,1974096],[]),([9,46104,458076,602208,1163648,2015064],[]),([9,48152,751724,866672,1163648,1967616],[]),([9,48152,751724,866672,1163648,1973760],[]),([9,48152,751724,866672,1163648,2014744],[7]),([9,48152,751724,866672,1169792,1967616],[]),([9,48152,751724,866672,1179032,1967616],[]),([9,48152,751724,1163648,1964528,1967616],[]),([9,61440,65536,153612,1964528,1967616],[1793]),([9,62488,395600,602208,1163648,1967616],[]),([9,63504,602208,866672,1300876,1967616],[]),([9,63504,602208,1300876,1427920,1967616],[]),([9,63504,602208,1300876,1964528,1967616],[]),([9,64536,602208,1300876,1427920,1967616],[]),([9,64536,602208,1300876,1964528,1967616],[]),([9,65536,106496,153612,1964528,1967616],[1793,2049]),([9,65536,153612,1964528,2008600,2095072],[1281]),([9,106496,107544,153612,1964528,1967616],[1793]),([9,106496,153612,330064,1700320,1967616],[1281]),([9,106496,153612,371024,1700320,1967616],[1281]),([9,106496,153612,602208,1427920,1967616],[1281]),([9,106496,153612,602208,1964528,1967616],[130,1286,3588]),([9,106496,153612,866672,1700320,1967616],[1281]),([9,106496,153612,1700320,1964528,1967616],[1281]),([9,106496,153612,1964528,1967616],[97,164,1281,1345,2593]),([9,106512,153612,1700320,1964528,1967616],[]),([9,107544,153612,285008,1700320,1967616],[]),([9,107544,153612,330064,1700320,1967616],[]),([9,107544,153612,330064,1700320,2033152],[]),([9,107544,153612,330064,1700320,2035536],[]),([9,107544,153612,330064,1700320,2074136],[]),([9,107544,153612,338256,1700320,1967616],[]),([9,107544,153612,371024,1700320,1967616],[]),([9,107544,153612,372056,1700320,1967616],[]),([9,107544,153612,372056,1700320,2033152],[]),([9,107544,153612,372056,1700320,2074136],[]),([9,107544,153612,372056,1700320,2076504],[]),([9,107544,153612,395600,1700320,1967616],[]),([9,107544,153612,602208,1427920,2065920],[]),([9,107544,153612,634976,1427920,1967616],[]),([9,107544,153612,866672,1700320,1967616],[]),([9,107544,153612,866672,1700320,2033152],[]),([9,107544,153612,866672,1700320,2074136],[]),([9,107544,153612,900472,1700320,1967616],[]),([9,107544,153612,1700320,1964528,1967616],[]),([9,107544,153612,1700320,1964528,2033152],[]),([9,107544,153612,1700320,1964528,2074136],[]),([9,107544,153612,1700320,1965560,1967616],[]),([9,107544,153612,1833452,1964528,1967616],[1281]),([9,107544,481628,602208,1163648,2035536],[]),([9,107544,523612,602208,1163648,2076504],[]),([9,107608,153612,602208,1427920,2065920],[]),([9,111640,153612,334160,1700320,1967616],[]),([9,111640,153612,376152,1700320,1967616],[]),([9,111640,153612,866672,1700320,1967616],[]),([9,111640,153612,1427920,1700320,1967616],[]),([9,111640,153612,1700320,1964528,1967616],[]),([9,113944,751724,866672,1163648,1967616],[]),([9,151552,602208,1427920,2008600,2082688],[]),([9,153612,195612,330064,1700320,2033152],[]),([9,153612,195612,602208,1427840,1967616],[]),([9,153612,195612,602208,1427920,2082304],[]),([9,153612,195612,602208,1956224,1967616],[]),([9,153612,195612,866672,1700320,2033152],[]),([9,153612,195612,866672,1950080,2045536],[]),([9,153612,195612,1700320,1964528,2033152],[]),([9,153612,195612,1964528,2045536,2082688],[]),([9,153612,261148,330064,1700320,1967616],[]),([9,153612,261148,866672,1700320,1967616],[]),([9,153612,261148,1700320,1964528,1967616],[1793]),([9,153612,310616,866672,1432016,1967616],[]),([9,153612,325968,602208,1163648,2029056],[]),([9,153612,330064,372056,1700320,2033152],[]),([9,153612,330064,1700320,2008600,2033152],[]),([9,153612,330064,1700320,2033152,2074136],[]),([9,153612,437592,997744,1558992,1967616],[3588]),([9,153612,602208,1163648,1745944,1968464],[]),([9,153612,602208,1163648,1878352,2008576],[]),([9,153612,602208,1163648,1898512,1967616],[1283,1793,3842])]
noncomputable def k4 : CE := [([9,153612,602208,1163648,1964528,2008576],[]),([9,153612,602208,1163648,1964528,2029056],[]),([9,153612,602208,1310108,1427920,2016768],[]),([9,153612,602208,1371160,1427920,2082688],[]),([9,153612,602208,1411408,2008600,2082688],[]),([9,153612,602208,1425792,2008600,2084816],[]),([9,153612,602208,1427840,2008600,2082688],[]),([9,153612,602208,1427920,1506332,2082688],[]),([9,153612,602208,1427920,1556864,2008600],[]),([9,153612,602208,1427920,2008600,2082688],[]),([9,153612,602208,1427920,2008600,2084736],[]),([9,153612,602208,1427920,2008600,2086784],[]),([9,153612,602208,1427920,2012696,2082688],[]),([9,153612,602208,1427920,2012696,2086784],[]),([9,153612,602208,1427920,2024984,2082688],[]),([9,153612,602208,1427920,2027032,2082688],[]),([9,153612,602208,1427920,2027032,2084736],[]),([9,153612,602208,1427920,2031132,2082688],[]),([9,153612,602208,1427920,2074136,2082688],[]),([9,153612,602208,1427920,2074200,2082688],[]),([9,153612,602208,1964528,2031132,2082688],[]),([9,153612,618592,1427920,2008600,2082688],[]),([9,153612,620640,1427920,2008600,2082688],[]),([9,153612,651360,1310108,1427920,1967616],[]),([9,153612,733280,1427920,2008600,2082688],[]),([9,153612,733288,1427920,2008600,2082688],[]),([9,153612,749664,1427920,2008600,2082688],[]),([9,153612,751724,1964528,2008600,2082688],[]),([9,153612,866672,1683552,2008600,2082688],[]),([9,153612,866672,1687936,2008600,2045536],[]),([9,153612,866672,1696128,2008600,2045536],[]),([9,153612,866672,1700320,2008600,2033152],[]),([9,153612,866672,1700320,2033152,2074136],[]),([9,153612,866672,1950080,2008600,2045536],[]),([9,153612,866672,1958288,2008600,2045536],[]),([9,153612,1683552,1948016,2008600,2082688],[]),([9,153612,1700320,1964528,2008600,2033152],[2945]),([9,153612,1700320,1964528,2033152,2074136],[3969]),([9,153612,1964528,2008600,2045536,2082688],[]),([9,195612,751724,1427920,2045536,2082688],[]),([10,0,42009,153612,264529,1700320,2033152],[2564]),([10,0,42009,395600,602208,1163648,1990156],[]),([10,0,153612,602208,1427920,2008600,2082688],[]),([10,336,42009,395600,602208,1163648,1990156],[]),([10,2076,42009,153612,264529,1700320,2033152],[1284]),([10,2076,42009,219148,264529,1700320,1967616],[1284]),([10,2076,107544,153612,264529,1700320,1967616],[1284]),([10,2076,153612,264529,602208,1163648,2008576],[]),([10,2076,153612,602208,1427920,2008600,2082688],[]),([10,2128,42009,153612,602208,1425792,1967616],[]),([10,2128,153612,602208,1427920,2008600,2082688],[]),([10,2384,42009,395600,602208,1163648,1990156],[]),([10,4132,153612,602208,1427920,2008600,2082688],[]),([10,6144,42009,227436,866672,1163648,1967616],[3585]),([10,6144,42009,342384,751724,1163648,1967616],[3585]),([10,6144,42009,602208,948348,1163648,1967616],[3585,4865]),([10,6144,42009,745580,866672,1163648,1967616],[4867]),([10,6144,42009,749676,866672,1163648,1967616],[4866]),([10,6144,42009,751724,800880,1163648,1967616],[3585,4866]),([10,6144,42009,751724,801136,1163648,1967616],[3585,4866]),([10,6144,42009,751724,860528,1163648,1967616],[3585,4865]),([10,6144,42009,751724,866672,1163648,1967616],[3585,4866]),([10,6156,42009,264529,602208,1294720,1990156],[1284,4868]),([10,6156,42009,264529,749664,1163648,1967616],[4871]),([10,6156,42009,751724,866672,1163648,1967616],[]),([10,6156,153612,602208,1427920,2008600,2082688],[]),([10,6156,195612,264529,602208,1294720,1967616],[4870]),([10,6244,153612,602208,1427920,2008600,2082688],[]),([10,6244,153612,866672,1163648,2008600,2045536],[4866]),([10,14364,153612,264529,602208,1163648,2016768],[3588]),([10,14460,42009,153612,264529,1700320,2033152],[]),([10,14460,42009,153612,602208,1427840,1967616],[]),([10,14460,42009,153612,1427920,1912928,2082688],[]),([10,14460,42009,153612,1964528,2045536,2082688],[]),([10,14460,42009,219148,264529,1700320,1967616],[]),([10,14460,42009,264529,743436,1700320,1967616],[]),([10,14460,42009,395600,602208,1163648,1990156],[]),([10,14460,42009,411984,602208,1163648,1990156],[]),([10,14460,42009,602208,1427920,1464332,2082688],[]),([10,14460,153612,602208,1345872,2008600,2082688],[]),([10,14460,153612,602208,1427920,2008600,2082688],[]),([10,14460,153612,602208,1427920,2031132,2082688],[]),([10,14460,153612,866672,1163648,2008600,2045536],[]),([10,14460,195612,751724,866672,1163648,1967616],[]),([10,20492,42009,395600,602208,1163648,1990156],[]),([10,22532,153612,602208,1427920,2008600,2082688],[]),([10,22532,173080,264529,602208,1294720,1967616],[4870]),([10,22532,173080,395600,602208,1163648,1967616],[4870]),([10,22532,264529,602208,1294720,1967616,2008600],[3590]),([10,22532,264529,602208,1300876,2008600,2082688],[3588]),([10,22532,395600,602208,1163648,1967616,2008600],[3590]),([10,22532,395608,602208,1163648,1967616,2008600],[3588]),([10,22532,602208,1300876,1427920,1967616,2008600],[3590,4865]),([10,22540,42009,153612,264529,1700320,2033152],[1284]),([10,22540,42009,219148,264529,1700320,1967616],[1286,1793]),([10,22540,42009,227436,866672,1163648,1967616],[]),([10,22540,42009,264529,602208,1294720,1967616],[4868]),([10,22540,42009,264529,602208,1294720,1990156],[1284,4868]),([10,22540,42009,264529,602208,1298816,1967616],[4868]),([10,22540,42009,264529,602208,1819008,1967616],[4870]),([10,22540,42009,264529,733280,1294720,1967616],[4868]),([10,22540,42009,342384,751724,1163648,1967616],[]),([10,22540,42009,395600,602208,1163648,1967616],[]),([10,22540,42009,395600,602208,1163648,1990156],[]),([10,22540,42009,395600,602208,1294720,1967616],[]),([10,22540,42009,399696,602208,1163648,1967616],[]),([10,22540,42009,602208,866672,1294720,1967616],[]),([10,22540,42009,602208,919888,1163648,1967616],[4865]),([10,22540,42009,602208,997744,1163648,1967616],[]),([10,22540,42009,602208,1294720,1427920,1967616],[]),([10,22540,42009,602208,1294720,1558992,1967616],[]),([10,22540,42009,602208,1300876,1427920,1967616],[]),([10,22540,42009,602208,1300876,1964528,1967616],[1793]),([10,22540,64540,264529,602208,1294720,1967616],[4868]),([10,22540,64540,395600,602208,1163648,1967616],[]),([10,22540,64540,602208,1300876,1427920,1967616],[]),([10,22540,107544,153612,264529,1700320,1967616],[1284,1796]),([10,22540,153612,602208,1427920,2008600,2082688],[]),([10,22540,172056,264529,602208,1163648,1967616],[]),([10,22540,173080,264529,602208,1294720,1967616],[4868]),([10,22540,173080,395600,602208,1163648,1967616],[4868]),([10,22540,194588,264529,602208,1163648,1967616],[]),([10,22540,195612,264529,602208,1294720,1967616],[4868]),([10,22540,195612,395600,602208,1163648,1967616],[4868]),([10,22540,195612,602208,1300876,1427920,1967616],[1281,2561]),([10,22540,264529,602208,1294720,1967616,2008600],[3590]),([10,22540,264529,602208,1300876,2008600,2082688],[3588]),([10,22540,395600,602208,1163648,1967616,2008600],[3590]),([10,22540,602208,1300876,1427920,1967616,2008600],[4865]),([10,23012,107544,153612,264529,1700320,1967616],[]),([10,23012,153612,264529,1700320,1967616,2074136],[3588]),([10,23012,153612,264529,1700320,2033152,2074136],[3588]),([10,40960,65536,153612,264529,1700320,1967616],[1284,1798,2049,4868]),([10,40960,153612,264529,602208,1163648,1967616],[1286,4868]),([10,40960,153612,264529,602208,1163648,2008576],[1284,2565,3588,4868]),([10,40960,153612,264529,602208,1171840,1967616],[1286,2564,4868]),([10,40960,153612,305488,602208,1163648,1967616],[1281]),([10,40960,153612,602208,866672,1163648,1967616],[1286,4868]),([10,40960,153612,602208,1163648,1964528,1967616],[1281]),([10,40968,153612,264529,602208,1163648,1967616],[1286]),([10,40976,131072,264529,602208,1163648,1990156],[1284,2818]),([10,40976,153612,264529,602208,1163648,1967616],[]),([10,40976,153612,305488,602208,1163648,1967616],[]),([10,40976,153612,371184,602208,1163648,1967616],[]),([10,40976,153612,602208,866672,1163648,1967616],[]),([10,40976,153612,602208,1163648,1964528,1967616],[]),([10,40984,65536,153612,264529,1700320,1967616],[1284]),([10,40984,77920,153612,866672,1163648,1967616],[]),([10,40984,131072,264529,602208,1163648,1990156],[2818]),([10,40984,153612,264528,602208,1163648,1967616],[])]
noncomputable def k5 : CE := [([10,40984,153612,264529,602208,1163648,1967616],[]),([10,40984,153612,264529,602208,1163648,1971712],[]),([10,40984,153612,264529,602208,1163648,1975808],[]),([10,40984,153612,264529,602208,1163648,2033152],[]),([10,40984,153612,264529,602208,1167744,1967616],[]),([10,40984,153612,264529,602208,1171840,1967616],[]),([10,40984,153612,264529,602208,1294720,1967616],[]),([10,40984,153612,264529,602208,1687936,1967616],[]),([10,40984,153612,264529,602208,1696128,1967616],[]),([10,40984,153612,268624,602208,1163648,1967616],[]),([10,40984,153612,272720,602208,1163648,1967616],[]),([10,40984,153612,330064,602208,1163648,1967616],[]),([10,40984,153612,342384,602208,1163648,1967616],[]),([10,40984,153612,395600,602208,1163648,1967616],[]),([10,40984,153612,602208,788816,1163648,1967616],[]),([10,40984,153612,602208,797008,1163648,1967616],[]),([10,40984,153612,602208,866672,1163648,1967616],[]),([10,40984,153612,602208,1163648,1964528,1967616],[]),([10,40984,153612,602208,1300876,1427920,1967616],[1286]),([10,40984,153612,602208,1427920,1967616,2082688],[]),([10,40984,153612,602208,1427920,2008600,2082688],[]),([10,40984,161804,264529,602208,1163648,1967616],[]),([10,40984,219148,264529,602208,1163648,1967616],[]),([10,40984,264529,602208,677900,1163648,1967616],[]),([10,40984,264529,602208,686092,1163648,1967616],[]),([10,41456,42009,153612,264529,1700320,2033152],[]),([10,41992,153612,268624,602208,1163648,1967616],[]),([10,41992,153612,330064,602208,1163648,1967616],[]),([10,41992,153612,395600,602208,1163648,1967616],[1286,4868]),([10,42008,65536,153612,264529,1700320,1967616],[1284,2049]),([10,42008,77920,153612,866672,1163648,1967616],[]),([10,42008,107544,153612,264529,1700320,1967616],[1284]),([10,42008,131072,264529,602208,1163648,1990156],[2818]),([10,42008,153604,264529,602208,1163648,1967616],[]),([10,42008,153612,264528,602208,1163648,1967616],[]),([10,42008,153612,264529,602208,1163648,1967616],[]),([10,42008,153612,264529,602208,1163648,1971712],[]),([10,42008,153612,264529,602208,1163648,1975808],[]),([10,42008,153612,264529,602208,1163648,2033152],[]),([10,42008,153612,264529,602208,1167744,1967616],[]),([10,42008,153612,264529,602208,1171840,1967616],[]),([10,42008,153612,264529,602208,1294720,1967616],[]),([10,42008,153612,268624,602208,1163648,1967616],[]),([10,42008,153612,272720,602208,1163648,1967616],[]),([10,42008,153612,330064,602208,1163648,1967616],[]),([10,42008,153612,342384,602208,1163648,1967616],[]),([10,42008,153612,371184,602208,1163648,1967616],[]),([10,42008,153612,395600,602208,1163648,1967616],[]),([10,42008,153612,602208,800880,1163648,1967616],[]),([10,42008,153612,602208,801136,1163648,1967616],[]),([10,42008,153612,602208,866672,1163648,1967616],[]),([10,42008,153612,602208,1163648,1964528,1967616],[]),([10,42008,153612,602208,1300876,1427920,1967616],[1281]),([10,42008,153612,602208,1427920,1832876,1967616],[]),([10,42009,47612,153612,264529,1700320,2049536],[]),([10,42009,61920,153612,264529,1700320,2033152],[]),([10,42009,63996,153612,264529,1700320,2033152],[]),([10,42009,63996,153612,330064,1700320,2033152],[]),([10,42009,63996,153612,866672,1700320,2033152],[]),([10,42009,63996,153612,1700320,1964528,2033152],[]),([10,42009,63996,219148,264529,1700320,1967616],[]),([10,42009,63996,219148,264529,1700320,2033152],[]),([10,42009,65536,127456,153612,1964528,1967616],[]),([10,42009,65536,153612,264529,1634784,1967616],[]),([10,42009,65536,153612,264529,1634784,2033152],[]),([10,42009,65536,153612,264529,1700320,1967616],[1284,2049]),([10,42009,65536,153612,264529,1700320,2033152],[1284]),([10,42009,65536,153612,330064,1634464,1967616],[2049]),([10,42009,65536,153612,330064,1634784,1967616],[2049]),([10,42009,65536,153612,330064,1700064,1967616],[2049]),([10,42009,65536,153612,330064,1700320,1967616],[2049]),([10,42009,65536,153612,342384,1700320,1967616],[2049]),([10,42009,65536,153612,371184,1700320,1967616],[2049]),([10,42009,65536,153612,391664,1700320,1967616],[2049]),([10,42009,65536,153612,651744,1427920,1967616],[2051]),([10,42009,65536,153612,800880,1700320,1967616],[1284,2049]),([10,42009,65536,153612,801136,1700320,1967616],[1284,2049]),([10,42009,65536,153612,866672,1634784,1967616],[2049]),([10,42009,65536,153612,866672,1700064,1967616],[2049]),([10,42009,65536,153612,866672,1700320,1967616],[2049]),([10,42009,65536,153612,1634784,1898992,1967616],[]),([10,42009,65536,153612,1634784,1964528,1967616],[2049]),([10,42009,65536,153612,1700320,1898992,1967616],[2049]),([10,42009,65536,153612,1700320,1964528,1967616],[2049]),([10,42009,65536,153612,1767084,1964528,1967616],[2049]),([10,42009,65536,153612,1832684,1964528,1967616],[2049]),([10,42009,65536,153612,1832940,1964528,1967616],[2049]),([10,42009,65600,153612,1427920,1700256,1967616],[]),([10,42009,65600,153612,1832876,1964528,1967616],[]),([10,42009,67612,153612,264529,1700320,1967616],[1284]),([10,42009,69632,149516,264529,1700320,1967616],[1285,2049,5125]),([10,42009,69632,153612,264529,1630688,1967616],[]),([10,42009,69632,153612,264529,1696224,1967616],[5122]),([10,42009,69632,153612,264529,1700320,1967616],[1284,2049]),([10,42009,73760,153612,792912,1163648,1967616],[]),([10,42009,73824,131072,866672,1163648,1990156],[]),([10,42009,73824,153612,264529,1692032,1967616],[]),([10,42009,73824,153612,792576,1163648,1967616],[2818]),([10,42009,73824,153612,792912,1163648,1967616],[]),([10,42009,73824,153612,866672,1163648,1967616],[]),([10,42009,73824,153612,866672,1163648,1971712],[]),([10,42009,73824,153612,866672,1163648,1973760],[]),([10,42009,73824,153612,899568,1163648,1967616],[]),([10,42009,73824,153612,1163648,1964528,1967616],[]),([10,42009,73824,264529,602208,1294720,1990156],[2820]),([10,42009,73824,264529,733280,1163648,1990156],[2821]),([10,42009,73824,395600,602208,1163648,1990156],[]),([10,42009,77856,153612,788816,1163392,1967616],[]),([10,42009,77856,153612,788816,1163648,1967616],[]),([10,42009,77856,153612,788816,1163648,2045472],[]),([10,42009,77856,153612,788816,1687936,1967616],[]),([10,42009,77856,153612,866672,1163648,1967616],[]),([10,42009,77856,153612,919888,1163648,1967616],[]),([10,42009,77856,153612,1163648,1837392,1967616],[]),([10,42009,77856,153612,1163648,1952208,1967616],[]),([10,42009,77856,153612,1308332,1952208,1967616],[]),([10,42009,77856,677900,788816,1163648,1967616],[]),([10,42009,77920,115072,153612,1964528,1967616],[]),([10,42009,77920,131072,866672,1163648,1990156],[]),([10,42009,77920,153612,264529,1687936,1967616],[]),([10,42009,77920,153612,264529,1692032,1967616],[]),([10,42009,77920,153612,264529,1700320,2033152],[]),([10,42009,77920,153612,264529,1819008,1967616],[]),([10,42009,77920,153612,342384,1687936,1967616],[]),([10,42009,77920,153612,788816,1163648,1967616],[]),([10,42009,77920,153612,788816,1687936,1967616],[]),([10,42009,77920,153612,792576,1163648,1967616],[2818]),([10,42009,77920,153612,792912,1163648,1967616],[]),([10,42009,77920,153612,854352,1163648,1967616],[]),([10,42009,77920,153612,866672,1163648,1967616],[]),([10,42009,77920,153612,866672,1163648,1971712],[]),([10,42009,77920,153612,866672,1163648,1973760],[]),([10,42009,77920,153612,866672,1163648,1984000],[]),([10,42009,77920,153612,866672,1163648,2033152],[3842]),([10,42009,77920,153612,866672,1167744,1967616],[]),([10,42009,77920,153612,866672,1169792,1967616],[2049]),([10,42009,77920,153612,866672,1294720,1967616],[]),([10,42009,77920,153612,866672,1687936,1967616],[]),([10,42009,77920,153612,866672,1950080,1967616],[]),([10,42009,77920,153612,883056,1163648,1967616],[]),([10,42009,77920,153612,915952,1163648,1967616],[]),([10,42009,77920,153612,919888,1163648,1967616],[]),([10,42009,77920,153612,997744,1163648,1967616],[]),([10,42009,77920,153612,1163648,1837392,1967616],[]),([10,42009,77920,153612,1163648,1915248,1967616],[]),([10,42009,77920,153612,1163648,1952208,1967616],[]),([10,42009,77920,153612,1163648,1964528,1967616],[]),([10,42009,77920,153612,1300876,1964528,1967616],[2049]),([10,42009,77920,153612,1427920,1687936,1967616],[]),([10,42009,77920,153612,1687936,1952208,1967616],[])]
noncomputable def k6 : CE := [([10,42009,77920,153612,1964528,1967616,2082688],[]),([10,42009,77920,219148,264529,1700320,1967616],[2817,3841]),([10,42009,77920,219148,866672,1163648,1967616],[3841]),([10,42009,77920,264529,602208,1294720,1990156],[2820]),([10,42009,77920,264529,677900,1163648,1967616],[]),([10,42009,77920,264529,677900,1687936,1967616],[]),([10,42009,77920,264529,733280,1163648,1990156],[2821]),([10,42009,77920,264529,743436,1163648,1967616],[3843]),([10,42009,77920,264529,1163648,1726476,1967616],[]),([10,42009,77920,342384,677900,1163648,1967616],[]),([10,42009,77920,395600,602208,1163648,1990156],[]),([10,42009,77920,677900,788816,1163648,1967616],[]),([10,42009,77920,677900,866672,1163648,1967616],[]),([10,42009,77920,677900,1163648,1427920,1967616],[]),([10,42009,77920,751724,1300876,1427920,1967616],[3843]),([10,42009,77920,866672,940044,1163648,1967616],[5123]),([10,42009,77920,866672,1163648,1202188,1967616],[]),([10,42009,79968,153612,866672,1163648,1967616],[]),([10,42009,80240,153612,602208,1950080,1967616],[]),([10,42009,80240,153612,864352,1163648,1967616],[]),([10,42009,80240,602208,940044,1163648,1967616],[]),([10,42009,88076,153612,264529,1700320,1967616],[1284,2049]),([10,42009,88076,219148,264529,1700320,1967616],[1286,2049]),([10,42009,94304,153612,866672,1163648,1967616],[]),([10,42009,94304,153612,883056,1163648,1967616],[]),([10,42009,96364,153612,866672,1163648,1967616],[]),([10,42009,96364,153612,1163648,1964528,1967616],[]),([10,42009,96364,264529,1300876,1700320,1967616],[]),([10,42009,96364,602208,1300876,1427920,1967616],[]),([10,42009,96364,866672,1163648,1300876,1967616],[]),([10,42009,106656,395600,602208,1163648,1990156],[3074]),([10,42009,106992,153612,264529,1700320,2033152],[]),([10,42009,106992,153612,602208,1329152,2082688],[]),([10,42009,106992,153612,602208,1427840,1967616],[]),([10,42009,106992,153612,602208,1956224,1967616],[3075,5634]),([10,42009,106992,264529,602208,1294720,1990156],[]),([10,42009,106992,264529,602208,1298816,1990156],[]),([10,42009,106992,264529,733280,1294720,1990156],[]),([10,42009,106992,371184,602208,1294720,1990156],[]),([10,42009,106992,395264,602208,1163648,1990156],[3074,4868]),([10,42009,106992,395600,602208,1163648,1990156],[]),([10,42009,106992,395600,602208,1294720,1990156],[]),([10,42009,106992,399696,602208,1163648,1990156],[]),([10,42009,106992,502256,602208,1163648,1990156],[]),([10,42009,106992,602208,866672,1294720,1990156],[]),([10,42009,106992,602208,997744,1163648,1990156],[]),([10,42009,106992,602208,1294720,1427920,1990156],[]),([10,42009,106992,602208,1294720,1558992,1990156],[2946]),([10,42009,110764,153612,602208,1427920,1967616],[]),([10,42009,110764,153612,883056,1163648,1967616],[]),([10,42009,111100,602208,1300876,1427920,1986048],[]),([10,42009,127148,153612,602208,1427920,1967616],[]),([10,42009,127148,153612,602208,1558992,1967616],[]),([10,42009,127148,153612,602208,1952208,1967616],[]),([10,42009,127148,395600,602208,1163648,1990156],[3074]),([10,42009,127456,153612,264529,1700320,2033152],[]),([10,42009,127456,219148,264529,1700320,1967616],[2817,3841]),([10,42009,127456,264529,751724,1300876,1967616],[2049]),([10,42009,129532,153612,264529,1700320,2033152],[]),([10,42009,129532,153612,264529,1700320,2037248],[]),([10,42009,129532,153612,330064,1700320,2033152],[]),([10,42009,129532,153612,602208,1329152,2082688],[]),([10,42009,129532,153612,602208,1427840,1967616],[]),([10,42009,129532,153612,602208,1956224,1967616],[5634]),([10,42009,129532,153612,866672,1700320,2033152],[]),([10,42009,129532,153612,866672,1950080,2045536],[]),([10,42009,129532,153612,1700320,1964528,2033152],[]),([10,42009,129532,153612,1964528,2045536,2082688],[]),([10,42009,129532,219148,264529,1700320,1967616],[]),([10,42009,129532,219148,264529,1700320,2033152],[]),([10,42009,129532,219148,330064,1700320,1967616],[]),([10,42009,129532,219148,866672,1700320,1967616],[]),([10,42009,129532,219148,1700320,1964528,1967616],[]),([10,42009,129532,264529,602208,1294720,1990156],[]),([10,42009,129532,264529,602208,1298816,1990156],[]),([10,42009,129532,264529,602208,1819008,1990156],[]),([10,42009,129532,264529,733280,1294720,1990156],[]),([10,42009,129532,264529,743436,1700320,1967616],[]),([10,42009,129532,395264,602208,1163648,1990156],[3074,4868]),([10,42009,129532,395600,602208,1163648,1990156],[]),([10,42009,129532,395600,602208,1294720,1990156],[]),([10,42009,129532,399696,602208,1163648,1990156],[]),([10,42009,129532,602208,866672,1294720,1990156],[]),([10,42009,129532,602208,919888,1163648,1990156],[]),([10,42009,129532,602208,997744,1163648,1990156],[]),([10,42009,129532,602208,1294720,1427920,1990156],[]),([10,42009,129532,602208,1294720,1558992,1990156],[2946]),([10,42009,129532,602208,1300876,1427920,1986048],[]),([10,42009,129532,602208,1427920,1464332,2082688],[2946]),([10,42009,129532,620640,1300876,1427920,1967616],[]),([10,42009,129532,751724,1300876,1964528,1967616],[2946]),([10,42009,131072,272752,602208,1163648,1990156],[]),([10,42009,131072,338288,602208,1163648,1990156],[]),([10,42009,131072,342384,602208,1163648,1990156],[]),([10,42009,131072,371184,602208,1163648,1990156],[2818]),([10,42009,131072,371184,602208,1294720,1990156],[1284]),([10,42009,131072,395344,602208,1163648,1990156],[1284]),([10,42009,131072,395600,602144,1163648,1990156],[1284,2818]),([10,42009,131072,395600,602208,1163648,1859084],[]),([10,42009,131072,395600,602208,1163648,1990156],[1284,2818]),([10,42009,131072,502256,602208,1163648,1990156],[1284,2818]),([10,42009,131072,602208,800880,1163648,1990156],[2050]),([10,42009,131072,602208,801136,1163648,1990156],[2050]),([10,42009,131072,602208,866672,1163648,1859084],[]),([10,42009,131072,602208,866672,1163648,1990156],[2050]),([10,42009,131072,602208,899568,1163648,1990156],[2050]),([10,42009,131072,602208,1427920,1832876,1990156],[]),([10,42009,131072,602208,1558992,1701548,1990156],[1284]),([10,42009,132620,153612,1700320,1964528,2033152],[]),([10,42009,132620,153612,1964528,2045536,2082688],[3842]),([10,42009,133120,371184,602208,1163648,1990156],[2818]),([10,42009,135168,371184,602208,1163648,1990156],[2818]),([10,42009,135180,602208,1163648,1329152,1967616],[]),([10,42009,135180,602208,1163648,1427920,1986048],[]),([10,42009,135180,602208,1427920,1990156,2082688],[]),([10,42009,137228,280656,602208,1163648,1967616],[]),([10,42009,137228,280912,602208,1163648,1984000],[]),([10,42009,137228,280912,618592,1163648,1967616],[]),([10,42009,137228,395600,602208,1163648,1990156],[1284]),([10,42009,137228,602208,866672,1163648,1984000],[]),([10,42009,137228,602208,1163648,1329152,1967616],[]),([10,42009,137228,602208,1163648,1427920,1984000],[]),([10,42009,137228,602208,1163648,1427920,1986048],[]),([10,42009,137228,602208,1427920,1990156,2082688],[3588]),([10,42009,137228,618592,866672,1163648,1967616],[]),([10,42009,137228,618592,883056,1163648,1967616],[]),([10,42009,137228,618592,1163648,1427920,1967616],[]),([10,42009,137228,620640,1163648,1427920,1967616],[2819]),([10,42009,137228,751724,800880,1163648,1967616],[1284]),([10,42009,137228,751724,801136,1163648,1967616],[1284]),([10,42009,137228,751724,866672,1163648,1967616],[1287]),([10,42009,137228,751724,1163648,1964528,1967616],[1287,2817]),([10,42009,137228,866672,1163648,1967616,2063980],[]),([10,42009,137228,866672,1163648,1990156,2045536],[3588]),([10,42009,140924,153612,602208,1956224,1967616],[]),([10,42009,147068,153612,866672,1950080,2045536],[2948]),([10,42009,153612,153612,264529,1700320,2033152],[1284]),([10,42009,153612,195068,264529,1700320,2033152],[]),([10,42009,153612,198156,1700320,1964528,1967616],[]),([10,42009,153612,198668,264529,1700320,1967616],[1284,1796,2049]),([10,42009,153612,202764,264529,1700320,1967616],[1284,1796,2049]),([10,42009,153612,208992,866672,1163648,1967616],[]),([10,42009,153612,219148,264529,1700320,1967616],[1286,1796,2049]),([10,42009,153612,227436,866672,1163648,1967616],[1287]),([10,42009,153612,227436,1163648,1964528,1967616],[1287,2817]),([10,42009,153612,259756,602208,1952208,1967616],[]),([10,42009,153612,260604,264529,1700320,2033152],[]),([10,42009,153612,264529,417308,1700320,2033152],[2564]),([10,42009,153612,264529,458748,1700320,2033152],[]),([10,42009,153612,264529,462364,1700320,1967616],[2564])]
noncomputable def k7 : CE := [([10,42009,153612,264529,462364,1700320,2033152],[2564]),([10,42009,153612,264529,466460,1700320,1967616],[2564]),([10,42009,153612,264529,482844,1700320,1967616],[2564]),([10,42009,153612,264529,524284,1700320,2033152],[]),([10,42009,153612,264529,602208,1163648,1967616],[]),([10,42009,153612,264529,602208,1163648,1971712],[]),([10,42009,153612,264529,602208,1163648,1988096],[]),([10,42009,153612,264529,602208,1163648,2033152],[]),([10,42009,153612,264529,602208,1163648,2037248],[]),([10,42009,153612,264529,602208,1167744,1971712],[]),([10,42009,153612,264529,602208,1176032,2033152],[3074]),([10,42009,153612,264529,602208,1294720,1859084],[1284,5124]),([10,42009,153612,264529,602208,1294720,1986060],[1284,5124]),([10,42009,153612,264529,602208,1294720,1990156],[1284,5124]),([10,42009,153612,264529,653820,1700320,2033152],[]),([10,42009,153612,264529,733280,1294720,1967616],[5124]),([10,42009,153612,264529,949884,1700320,2033152],[]),([10,42009,153612,264529,983036,1700320,2033152],[]),([10,42009,153612,264529,999036,1700320,2033152],[]),([10,42009,153612,264529,1048572,1700320,2033152],[]),([10,42009,153612,264529,1634784,1700320,2033152],[]),([10,42009,153612,264529,1683936,2045536,2082688],[]),([10,42009,153612,264529,1700320,1702396,2033152],[]),([10,42009,153612,264529,1700320,1914464,2082688],[]),([10,42009,153612,264529,1700320,1947632,2033152],[]),([10,42009,153612,264529,1700320,1964016,2033152],[]),([10,42009,153612,264529,1700320,1966076,2033152],[]),([10,42009,153612,264529,1700320,1969692,2033152],[3588]),([10,42009,153612,264529,1700320,1982076,2033152],[]),([10,42009,153612,264529,1700320,2015228,2049536],[3972]),([10,42009,153612,264529,1700320,2031612,2033152],[]),([10,42009,153612,264529,1700320,2033152],[1316,3620]),([10,42009,153612,264529,1700320,2033152,2035228],[4868]),([10,42009,153612,264529,1700320,2033152,2047612],[]),([10,42009,153612,264529,1700320,2033152,2074608],[]),([10,42009,153612,264529,1700320,2033152,2076668],[]),([10,42009,153612,264529,1700320,2033152,2080764],[]),([10,42009,153612,264529,1700320,2033152,2097148],[]),([10,42009,153612,264529,1700320,2041440,2082688],[]),([10,42009,153612,264529,1700320,2045536,2082688],[]),([10,42009,153612,264529,1700320,2045536,2084764],[]),([10,42009,153612,264529,1702396,2045536,2082688],[]),([10,42009,153612,268288,602208,1163648,1967616],[3074]),([10,42009,153612,268304,602208,1163648,1967616],[]),([10,42009,153612,268368,602208,1163648,1967616],[]),([10,42009,153612,268368,602208,1163648,1971712],[]),([10,42009,153612,268368,602208,1167744,1967616],[]),([10,42009,153612,268560,602208,1163648,1967616],[]),([10,42009,153612,268624,602144,1163648,1967616],[]),([10,42009,153612,268624,602208,1163392,1967616],[]),([10,42009,153612,268624,602208,1163392,1971712],[]),([10,42009,153612,268624,602208,1163648,1967616],[]),([10,42009,153612,268624,602208,1163648,1971712],[]),([10,42009,153612,268624,602208,1167488,1967616],[]),([10,42009,153612,268624,602208,1167744,1967616],[]),([10,42009,153612,272752,602208,1163648,1967616],[]),([10,42009,153612,276592,602208,1163648,1967616],[]),([10,42009,153612,276592,602208,1687936,1967616],[]),([10,42009,153612,276848,602208,1163648,1967616],[]),([10,42009,153612,276848,602208,1163648,2033152],[]),([10,42009,153612,276848,602208,1687936,1967616],[]),([10,42009,153612,276848,751724,1163648,1967616],[1284]),([10,42009,153612,284688,602208,1163648,1967616],[]),([10,42009,153612,285008,602208,1163648,1967616],[]),([10,42009,153612,305648,602208,1163648,1967616],[]),([10,42009,153612,305648,602208,1163648,2033152],[]),([10,42009,153612,329808,602208,1163648,1967616],[]),([10,42009,153612,329808,1163648,1700320,1967616],[]),([10,42009,153612,330064,396828,1700320,2033152],[3204]),([10,42009,153612,330064,462364,1700320,1967616],[]),([10,42009,153612,330064,602144,1163648,1967616],[]),([10,42009,153612,330064,602208,1163648,1967616],[]),([10,42009,153612,330064,602208,1163648,2033152],[]),([10,42009,153612,330064,602208,1700256,1967616],[]),([10,42009,153612,330064,933500,1700320,2033152],[3204]),([10,42009,153612,330064,1700320,1767084,2033152],[]),([10,42009,153612,330064,1700320,1832620,1967616],[]),([10,42009,153612,330064,1700320,2031612,2033152],[4228]),([10,42009,153612,334096,602208,1163648,1967616],[]),([10,42009,153612,334160,602208,1163648,1967616],[]),([10,42009,153612,338016,602208,1163648,1967616],[3074]),([10,42009,153612,338288,602208,1163648,1967616],[]),([10,42009,153612,338288,602208,1163648,1971712],[]),([10,42009,153612,342384,602208,1163648,1967616],[]),([10,42009,153612,342384,602208,1163648,1971712],[]),([10,42009,153612,342384,602208,1163648,1973760],[]),([10,42009,153612,342384,602208,1163648,1984000],[]),([10,42009,153612,342384,602208,1163648,2033152],[]),([10,42009,153612,342384,602208,1167744,1967616],[]),([10,42009,153612,342384,602208,1169792,1967616],[2817]),([10,42009,153612,342384,602208,1294720,1967616],[]),([10,42009,153612,342384,602208,1425792,1967616],[]),([10,42009,153612,342384,602208,1687936,1967616],[]),([10,42009,153612,342384,604256,1163648,1967616],[]),([10,42009,153612,342384,618592,1163648,1967616],[]),([10,42009,153612,342384,620652,1163648,1967616],[]),([10,42009,153612,342384,733280,1163648,1967616],[]),([10,42009,153612,342384,751724,1163648,1967616],[1283]),([10,42009,153612,342384,864352,1163648,1967616],[]),([10,42009,153612,342384,1163648,1650784,1967616],[]),([10,42009,153612,358768,602208,1163648,1967616],[]),([10,42009,153612,358768,618592,1163648,1967616],[]),([10,42009,153612,371184,602208,1163648,1967616],[]),([10,42009,153612,371184,602208,1163648,1969664],[]),([10,42009,153612,371184,602208,1163648,1971712],[]),([10,42009,153612,371184,602208,1163648,2033152],[]),([10,42009,153612,371184,602208,1165696,1967616],[]),([10,42009,153612,371184,602208,1167744,1967616],[]),([10,42009,153612,371184,602208,1294720,1967616],[]),([10,42009,153612,371184,602208,1294720,1990156],[1284]),([10,42009,153612,371184,602208,1427840,1967616],[]),([10,42009,153612,371184,602208,1692032,1967616],[]),([10,42009,153612,375280,602208,1163648,1967616],[]),([10,42009,153612,391664,602208,1163648,1967616],[]),([10,42009,153612,391664,602208,1300876,1967616],[1286,2817]),([10,42009,153612,395280,602208,1163648,1967616],[]),([10,42009,153612,395344,602208,1163648,1967616],[]),([10,42009,153612,395344,602208,1163648,1990156],[1284]),([10,42009,153612,395344,602208,1294720,1967616],[]),([10,42009,153612,395344,733280,1163648,1967616],[]),([10,42009,153612,395600,602144,1163392,1967616],[]),([10,42009,153612,395600,602144,1163648,1967616],[]),([10,42009,153612,395600,602144,1163648,1990156],[1284]),([10,42009,153612,395600,602144,1294720,1967616],[]),([10,42009,153612,395600,602208,1163648,1859084],[]),([10,42009,153612,395600,602208,1163648,1967616],[]),([10,42009,153612,395600,602208,1163648,1973772],[1286]),([10,42009,153612,395600,602208,1163648,1988108],[]),([10,42009,153612,395600,602208,1163648,1990156],[1284]),([10,42009,153612,395600,602208,1294464,1967616],[]),([10,42009,153612,395600,602208,1294720,1967616],[]),([10,42009,153612,396828,866672,1700320,2033152],[3204]),([10,42009,153612,396828,1700320,1964528,2033152],[4228]),([10,42009,153612,396828,1964528,2045536,2082688],[]),([10,42009,153612,399440,602208,1163648,1967616],[]),([10,42009,153612,399696,602208,1163392,1967616],[]),([10,42009,153612,399696,602208,1163648,1967616],[]),([10,42009,153612,462364,866672,1700320,1967616],[]),([10,42009,153612,462364,1700320,1964528,1967616],[]),([10,42009,153612,473456,602208,1163648,1967616],[]),([10,42009,153612,502256,602208,1163648,1967616],[]),([10,42009,153612,502256,602208,1163648,1990156],[1284]),([10,42009,153612,602144,784044,1427920,1967616],[]),([10,42009,153612,602144,883056,1163648,1967616],[]),([10,42009,153612,602144,997744,1163648,1967616],[]),([10,42009,153612,602144,1163648,1329488,1967616],[]),([10,42009,153612,602144,1163648,1427920,1967616],[]),([10,42009,153612,602144,1163648,1558992,1967616],[]),([10,42009,153612,602144,1163648,1964528,1967616],[]),([10,42009,153612,602144,1300876,1427920,1967616],[1286])]
noncomputable def k8 : CE := [([10,42009,153612,602144,1427920,1700256,1967616],[]),([10,42009,153612,602144,1427920,1700320,1967616],[]),([10,42009,153612,602144,1427920,1832876,1967616],[]),([10,42009,153612,602144,1427920,1832940,1967616],[]),([10,42009,153612,602144,1427920,1834924,1967616],[]),([10,42009,153612,602144,1558992,1701548,1967616],[]),([10,42009,153612,602208,639360,1427920,1967616],[]),([10,42009,153612,602208,652972,1558992,1967616],[]),([10,42009,153612,602208,669228,1427840,1967616],[]),([10,42009,153612,602208,669308,1427840,1967616],[]),([10,42009,153612,602208,767660,1427920,1967616],[]),([10,42009,153612,602208,767996,1427840,1967616],[]),([10,42009,153612,602208,771968,1427920,1967616],[]),([10,42009,153612,602208,784044,1427920,1967616],[]),([10,42009,153612,602208,786092,1427920,1967616],[]),([10,42009,153612,602208,788752,1163648,2045536],[]),([10,42009,153612,602208,788816,1163648,2045472],[]),([10,42009,153612,602208,792576,1163648,1967616],[3074]),([10,42009,153612,602208,792656,1163648,1967616],[]),([10,42009,153612,602208,792848,1163648,1967616],[]),([10,42009,153612,602208,792912,1163648,1967616],[]),([10,42009,153612,602208,800880,1163648,1967616],[]),([10,42009,153612,602208,800880,1163648,1971712],[]),([10,42009,153612,602208,800880,1163648,1973760],[2050,2817]),([10,42009,153612,602208,800880,1163648,1984000],[]),([10,42009,153612,602208,800880,1163648,2033152],[]),([10,42009,153612,602208,800880,1167744,1967616],[]),([10,42009,153612,602208,800880,1169792,1967616],[2049,2817]),([10,42009,153612,602208,800880,1294720,1967616],[]),([10,42009,153612,602208,801136,1163648,1967616],[]),([10,42009,153612,602208,801136,1163648,1971712],[]),([10,42009,153612,602208,801136,1163648,1973760],[2050]),([10,42009,153612,602208,801136,1163648,1984000],[]),([10,42009,153612,602208,801136,1163648,2033152],[]),([10,42009,153612,602208,801136,1167744,1967616],[]),([10,42009,153612,602208,801136,1169792,1967616],[2049]),([10,42009,153612,602208,801136,1294720,1967616],[]),([10,42009,153612,602208,817264,1163648,1967616],[]),([10,42009,153612,602208,817520,1163648,1967616],[]),([10,42009,153612,602208,862576,1163648,1969664],[]),([10,42009,153612,602208,862576,1163648,1971712],[]),([10,42009,153612,602208,862576,1163648,1984000],[]),([10,42009,153612,602208,862576,1163648,2033152],[]),([10,42009,153612,602208,866400,1163648,1967616],[3074]),([10,42009,153612,602208,866416,1163648,1967616],[]),([10,42009,153612,602208,866672,1163648,1967616],[]),([10,42009,153612,602208,866672,1163648,1969664],[]),([10,42009,153612,602208,866672,1163648,1971712],[]),([10,42009,153612,602208,866672,1163648,1973760],[2050]),([10,42009,153612,602208,866672,1163648,1984000],[]),([10,42009,153612,602208,866672,1163648,2033152],[]),([10,42009,153612,602208,866672,1165696,1967616],[]),([10,42009,153612,602208,866672,1167744,1967616],[]),([10,42009,153612,602208,866672,1169792,1967616],[2049]),([10,42009,153612,602208,866672,1294720,1967616],[]),([10,42009,153612,602208,878960,1163648,1967616],[]),([10,42009,153612,602208,882800,1163648,1967616],[]),([10,42009,153612,602208,883056,1163648,1967616],[]),([10,42009,153612,602208,899568,1163648,1967616],[]),([10,42009,153612,602208,915952,1163648,1967616],[]),([10,42009,153612,602208,915952,1300876,1967616],[1286,2049]),([10,42009,153612,602208,915964,1163648,1973760],[]),([10,42009,153612,602208,915964,1169792,1967616],[]),([10,42009,153612,602208,931952,1163648,1967616],[]),([10,42009,153612,602208,932208,1163648,1967616],[]),([10,42009,153612,602208,933500,1427840,1967616],[]),([10,42009,153612,602208,933500,1956224,1967616],[]),([10,42009,153612,602208,997488,1163648,1967616],[]),([10,42009,153612,602208,997744,1163648,1967616],[]),([10,42009,153612,602208,1034112,1427920,1967616],[]),([10,42009,153612,602208,1163648,1898736,1967616],[]),([10,42009,153612,602208,1163648,1898992,1967616],[]),([10,42009,153612,602208,1163648,1964528,1967616],[]),([10,42009,153612,602208,1163660,1427920,1967616],[]),([10,42009,153612,602208,1163660,1964528,1967616],[]),([10,42009,153612,602208,1165696,1362320,1967616],[]),([10,42009,153612,602208,1165696,1362384,1967616],[]),([10,42009,153612,602208,1165696,1427920,1967616],[]),([10,42009,153612,602208,1165696,1440252,1967616],[]),([10,42009,153612,602208,1165708,1427920,1967616],[]),([10,42009,153612,602208,1167744,1362320,1967616],[]),([10,42009,153612,602208,1167744,1362384,1967616],[]),([10,42009,153612,602208,1167744,1427920,1967616],[]),([10,42009,153612,602208,1167744,1432016,1967616],[]),([10,42009,153612,602208,1167756,1427920,1967616],[]),([10,42009,153612,602208,1169804,1427920,1967616],[]),([10,42009,153612,602208,1169804,1964528,1967616],[2051]),([10,42009,153612,602208,1171872,1427920,1967616],[]),([10,42009,153612,602208,1175968,1427920,1967616],[]),([10,42009,153612,602208,1175980,1427920,1967616],[]),([10,42009,153612,602208,1177260,1967616,2083280],[]),([10,42009,153612,602208,1230476,1956224,1967616],[]),([10,42009,153612,602208,1230476,1964528,2033152],[]),([10,42009,153612,602208,1294720,1362320,1967616],[]),([10,42009,153612,602208,1294720,1362384,1967616],[]),([10,42009,153612,602208,1294720,1427920,1967616],[]),([10,42009,153612,602208,1294720,1493392,1967616],[]),([10,42009,153612,602208,1294720,1493456,1967616],[]),([10,42009,153612,602208,1294720,1558992,1967616],[]),([10,42009,153612,602208,1294732,1427920,1967616],[]),([10,42009,153612,602208,1294732,1964528,1967616],[]),([10,42009,153612,602208,1296012,1964528,1967616],[]),([10,42009,153612,602208,1296268,1427920,1967616],[]),([10,42009,153612,602208,1296268,1964528,1967616],[]),([10,42009,153612,602208,1296780,1362320,1967616],[1285]),([10,42009,153612,602208,1296780,1362384,1967616],[1285]),([10,42009,153612,602208,1296780,1427920,1967616],[1281]),([10,42009,153612,602208,1296780,1964528,1967616],[1286]),([10,42009,153612,602208,1298828,1427920,1967616],[]),([10,42009,153612,602208,1298828,1964528,1967616],[]),([10,42009,153612,602208,1300876,1362320,1967616],[1287]),([10,42009,153612,602208,1300876,1362384,1967616],[1287]),([10,42009,153612,602208,1300876,1427856,1967616],[1281]),([10,42009,153612,602208,1300876,1427920,1967616],[1281]),([10,42009,153612,602208,1300876,1436144,1967616],[1286]),([10,42009,153612,602208,1300876,1440240,1967616],[1286,2051]),([10,42009,153612,602208,1300876,1960432,1967616],[1286]),([10,42009,153612,602208,1300876,1964528,1967616],[1286,2049]),([10,42009,153612,602208,1302412,1427920,1967616],[]),([10,42009,153612,602208,1302412,1964528,1967616],[2049]),([10,42009,153612,602208,1304236,1956304,1967616],[]),([10,42009,153612,602208,1304572,1956224,1967616],[]),([10,42009,153612,602208,1308332,1952208,1967616],[]),([10,42009,153612,602208,1308588,1427920,1967616],[]),([10,42009,153612,602208,1308588,1952208,1967616],[]),([10,42009,153612,602208,1309100,1427920,1967616],[1286]),([10,42009,153612,602208,1310380,1952208,1967616],[]),([10,42009,153612,602208,1312848,1427920,2082688],[]),([10,42009,153612,602208,1325180,1427920,2082688],[]),([10,42009,153612,602208,1362320,1967616,2088844],[]),([10,42009,153612,602208,1362320,1990156,2082688],[3589]),([10,42009,153612,602208,1362320,2045536,2082688],[]),([10,42009,153612,602208,1362384,1967616,2088844],[]),([10,42009,153612,602208,1362384,1990156,2082688],[3589]),([10,42009,153612,602208,1362384,2045536,2082688],[]),([10,42009,153612,602208,1411536,1990156,2082688],[]),([10,42009,153612,602208,1411536,2045536,2082688],[]),([10,42009,153612,602208,1427840,1494940,1967616],[]),([10,42009,153612,602208,1427840,1967616],[3617]),([10,42009,153612,602208,1427840,1967616,1990156],[4868]),([10,42009,153612,602208,1427856,1700320,1967616],[]),([10,42009,153612,602208,1427920,1461772,2082688],[]),([10,42009,153612,602208,1427920,1465868,2082688],[]),([10,42009,153612,602208,1427920,1558400,1990156],[]),([10,42009,153612,602208,1427920,1560460,1967616],[]),([10,42009,153612,602208,1427920,1564556,1967616],[]),([10,42009,153612,602208,1427920,1700256,1967616],[]),([10,42009,153612,602208,1427920,1701804,1967616],[]),([10,42009,153612,602208,1427920,1767084,2033152],[]),([10,42009,153612,602208,1427920,1816236,1984000],[])]
noncomputable def k9 : CE := [([10,42009,153612,602208,1427920,1820544,1979948],[]),([10,42009,153612,602208,1427920,1820544,1990156],[]),([10,42009,153612,602208,1427920,1824652,1967616],[]),([10,42009,153612,602208,1427920,1826700,1967616],[]),([10,42009,153612,602208,1427920,1831340,1967616],[]),([10,42009,153612,602208,1427920,1832620,1967616],[]),([10,42009,153612,602208,1427920,1832876,1967616],[]),([10,42009,153612,602208,1427920,1832876,1971712],[]),([10,42009,153612,602208,1427920,1832876,1984000],[]),([10,42009,153612,602208,1427920,1832876,1986048],[]),([10,42009,153612,602208,1427920,1832876,2033152],[3074]),([10,42009,153612,602208,1427920,1833388,1967616],[1286]),([10,42009,153612,602208,1427920,1834668,1967616],[]),([10,42009,153612,602208,1427920,1834924,1967616],[]),([10,42009,153612,602208,1427920,1914464,2082688],[]),([10,42009,153612,602208,1427920,1951616,2045536],[3074]),([10,42009,153612,602208,1427920,1967616,2088844],[]),([10,42009,153612,602208,1427920,1967616,2097068],[]),([10,42009,153612,602208,1427920,1967628,2082688],[]),([10,42009,153612,602208,1427920,1969692,2082688],[]),([10,42009,153612,602208,1427920,1969744,2082688],[]),([10,42009,153612,602208,1427920,1971724,2082688],[]),([10,42009,153612,602208,1427920,1973772,2082688],[]),([10,42009,153612,602208,1427920,1975840,2082688],[]),([10,42009,153612,602208,1427920,1975920,2082688],[]),([10,42009,153612,602208,1427920,1975920,2088844],[]),([10,42009,153612,602208,1427920,1979936,2082688],[]),([10,42009,153612,602208,1427920,1979948,2082688],[]),([10,42009,153612,602208,1427920,1980000,2082688],[]),([10,42009,153612,602208,1427920,1982076,2082688],[]),([10,42009,153612,602208,1427920,1986060,2082688],[]),([10,42009,153612,602208,1427920,1990156,2066304],[]),([10,42009,153612,602208,1427920,1990156,2082688],[]),([10,42009,153612,602208,1427920,1998380,2082688],[]),([10,42009,153612,602208,1427920,1998460,2082688],[]),([10,42009,153612,602208,1427920,2041440,2082688],[]),([10,42009,153612,602208,1427920,2045536,2066304],[3074]),([10,42009,153612,602208,1427920,2045536,2082688],[]),([10,42009,153612,602208,1427920,2045548,2082688],[3074]),([10,42009,153612,602208,1427920,2047612,2082688],[]),([10,42009,153612,602208,1432016,1828524,1971712],[]),([10,42009,153612,602208,1432016,1832620,1967616],[]),([10,42009,153612,602208,1432016,1832876,1967616],[]),([10,42009,153612,602208,1432016,1834668,1967616],[]),([10,42009,153612,602208,1436144,1967616,2088844],[]),([10,42009,153612,602208,1436144,1990156,2082688],[]),([10,42009,153612,602208,1494940,1956224,1967616],[2946,5763]),([10,42009,153612,602208,1558992,1701548,1967616],[]),([10,42009,153612,602208,1558992,1701548,1990156],[1284]),([10,42009,153612,602208,1558992,1701804,1967616],[]),([10,42009,153612,602208,1558992,1832620,1967616],[]),([10,42009,153612,602208,1558992,1832876,1967616],[]),([10,42009,153612,602208,1558992,1834668,1967616],[1286]),([10,42009,153612,602208,1964528,1967628,2082688],[3588,4098]),([10,42009,153612,602208,1964528,1969692,2082688],[3588]),([10,42009,153612,602208,1964528,1979948,2082688],[4098]),([10,42009,153612,602208,1964528,1982076,2082688],[]),([10,42009,153612,604284,1427920,2045536,2082688],[]),([10,42009,153612,618592,1427920,1816236,1967616],[]),([10,42009,153612,618592,1427920,1832876,1967616],[]),([10,42009,153612,620640,1427920,1832876,1967616],[]),([10,42009,153612,653820,1427920,2045536,2082688],[]),([10,42009,153612,669228,1427920,1700320,2033152],[]),([10,42009,153612,669228,1427920,1912928,2082688],[]),([10,42009,153612,669228,1964528,2045536,2082688],[4098]),([10,42009,153612,733280,1427920,1832876,1967616],[]),([10,42009,153612,733280,1558992,1701548,1967616],[]),([10,42009,153612,734764,1427920,1700320,1967616],[]),([10,42009,153612,734828,1296268,1964528,1967616],[]),([10,42009,153612,734828,1300876,1964528,1967616],[1281,2051]),([10,42009,153612,734828,1427920,1700256,1967616],[]),([10,42009,153612,751724,1427920,1700256,1967616],[1283]),([10,42009,153612,784044,1427920,1915248,1967616],[]),([10,42009,153612,786428,1427920,1912928,2082688],[2178,3202]),([10,42009,153612,866672,933500,1700320,2033152],[]),([10,42009,153612,866672,933500,1950080,2045536],[]),([10,42009,153612,866672,1494940,1687936,2045536],[]),([10,42009,153612,866672,1494940,1700320,2033152],[3205]),([10,42009,153612,866672,1494940,1950080,2045536],[]),([10,42009,153612,866672,1700320,2031612,2033152],[]),([10,42009,153612,933500,1700320,1964528,2033152],[]),([10,42009,153612,933500,1964528,2045536,2082688],[]),([10,42009,153612,997744,1558992,1701548,1967616],[]),([10,42009,153612,1700320,1964528,2031612,2033152],[]),([10,42009,161916,602208,1427920,1990156,2082688],[]),([10,42009,219148,264529,1700320,2031612,2033152],[6017]),([10,42009,238064,371184,602208,1163648,1990156],[]),([10,42009,238064,395600,602208,1163648,1990156],[]),([10,42009,238064,502256,602208,1163648,1990156],[]),([10,42009,238064,602208,866672,1163648,1990156],[]),([10,42009,260604,395600,602208,1163648,1990156],[]),([10,42009,260604,602208,1427920,1990156,2082688],[5250]),([10,42009,371184,502256,602208,1163648,1990156],[]),([10,42009,371184,602208,733280,1163648,1990156],[2050,3074]),([10,42009,371184,602208,1294720,1990156],[3620,4004]),([10,42009,371184,602208,1300876,1990156,2082688],[3588]),([10,42009,395264,602208,933500,1163648,1990156],[2050,4868]),([10,42009,395264,602208,1163648,1701548,1990156],[2050,4482,4868]),([10,42009,395264,602208,1163648,1701884,1990156],[2050,4868]),([10,42009,395264,602208,1163648,1966076,1990156],[2050,4868]),([10,42009,395344,395600,602208,1163648,1990156],[]),([10,42009,395344,602208,933500,1163648,1990156],[]),([10,42009,395344,602208,1163648,1990156],[2850,3620]),([10,42009,395600,396828,602208,1163648,1990156],[1796]),([10,42009,395600,502256,602208,1163648,1990156],[]),([10,42009,395600,522748,602208,1163648,1990156],[]),([10,42009,395600,602144,602208,1163648,1990156],[]),([10,42009,395600,602144,1163648,1701548,1990156],[2050]),([10,42009,395600,602144,1163648,1990156],[3620]),([10,42009,395600,602208,602208,1163648,1990156],[]),([10,42009,395600,602208,635376,1163648,1990156],[]),([10,42009,395600,602208,653820,1163648,1990156],[]),([10,42009,395600,602208,802428,1163648,1990156],[]),([10,42009,395600,602208,802428,1294720,1990156],[2948]),([10,42009,395600,602208,925196,1163648,1990156],[2564,4868]),([10,42009,395600,602208,933500,1163648,1990156],[]),([10,42009,395600,602208,933500,1294720,1990156],[]),([10,42009,395600,602208,933756,1163648,1990156],[]),([10,42009,395600,602208,949884,1163648,1990156],[]),([10,42009,395600,602208,999036,1163648,1990156],[]),([10,42009,395600,602208,1032188,1163648,1990156],[]),([10,42009,395600,602208,1048572,1163648,1990156],[]),([10,42009,395600,602208,1163648,1594892,1990156],[3588]),([10,42009,395600,602208,1163648,1701548,1990156],[2050,4482]),([10,42009,395600,602208,1163648,1701612,1990156],[2050,4482]),([10,42009,395600,602208,1163648,1701884,1990156],[]),([10,42009,395600,602208,1163648,1703932,1990156],[]),([10,42009,395600,602208,1163648,1832620,1990156],[2050,4482]),([10,42009,395600,602208,1163648,1834668,1990156],[2050,4482]),([10,42009,395600,602208,1163648,1859084,1990156],[3588]),([10,42009,395600,602208,1163648,1966076,1990156],[]),([10,42009,395600,602208,1163648,1990156],[2850,3620]),([10,42009,395600,602208,1163648,1990156,1998460],[]),([10,42009,395600,602208,1163648,1990156,2031612],[]),([10,42009,395600,602208,1163648,1990156,2096812],[2050,3588,5762]),([10,42009,395600,602208,1163648,1990156,2096892],[5762]),([10,42009,395600,602208,1163648,1990156,2097148],[]),([10,42009,395600,602208,1294720,1494940,1990156],[3970]),([10,42009,395600,602208,1294720,1701548,1990156],[2050,4482]),([10,42009,395600,602208,1294720,1966076,1990156],[3972]),([10,42009,395600,602208,1558992,1701548,1990156],[1284,4482]),([10,42009,399696,602208,933500,1163648,1990156],[]),([10,42009,399696,602208,1163648,1494940,1990156],[3970]),([10,42009,399696,602208,1163648,1697452,1990156],[2051,2817,4225]),([10,42009,399696,602208,1163648,1961980,1990156],[4225]),([10,42009,502256,602208,1163648,1990156],[2850,3620]),([10,42009,522748,602208,1163648,1990156,2076656],[]),([10,42009,602208,669228,1163648,1464332,2084816],[]),([10,42009,602208,669228,1163648,1558992,1990156],[]),([10,42009,602208,669228,1294720,1427920,1990156],[])]
noncomputable def k10 : CE := [([10,42009,602208,669228,1300876,1427920,1986048],[]),([10,42009,602208,786428,1427920,1464332,2082688],[2177,3202]),([10,42009,602208,802428,866672,1294720,1990156],[]),([10,42009,602208,802428,1163648,1558992,1990156],[]),([10,42009,602208,802428,1294720,1427920,1990156],[4228]),([10,42009,602208,802428,1294720,1558992,1990156],[4228]),([10,42009,602208,866672,933500,1294720,1990156],[]),([10,42009,602208,866672,1230476,1294720,1990156],[2818]),([10,42009,602208,866672,1294720,1494940,1990156],[4229]),([10,42009,602208,866672,1294720,1966076,1990156],[]),([10,42009,602208,933500,997744,1163648,1990156],[]),([10,42009,602208,933500,1163648,1558992,1990156],[]),([10,42009,602208,933500,1202188,1427920,2082688],[]),([10,42009,602208,933500,1294720,1427920,1990156],[4228]),([10,42009,602208,933500,1294720,1558992,1990156],[]),([10,42009,602208,933500,1300876,1427920,1986048],[]),([10,42009,602208,997744,1163648,1701548,1990156],[2050,3842,4482]),([10,42009,602208,997744,1163648,1966076,1990156],[]),([10,42009,602208,1294720,1427920,1494940,1990156],[]),([10,42009,602208,1294720,1427920,1966076,1990156],[]),([10,42009,602208,1294720,1494940,1558992,1990156],[]),([10,42009,602208,1294720,1558992,1966076,1990156],[4226]),([10,42009,602208,1300876,1427920,1494940,1986048],[]),([10,42009,602208,1558992,1701548,1990156],[3266,3620]),([10,42012,153612,602208,866672,1163648,1967616],[]),([10,42012,153612,602208,1163648,1964528,1967616],[]),([10,43024,153612,371184,602208,1163648,1967616],[]),([10,44056,153612,371184,602208,1163648,1967616],[]),([10,44056,153612,602208,862576,1163648,1967616],[]),([10,44056,153612,602208,866672,1163648,1967616],[]),([10,44060,153612,602208,866672,1163648,1967616],[]),([10,44060,153612,602208,1163648,1964528,1967616],[]),([10,44060,153612,602208,1427920,1967616,2082688],[]),([10,45080,153612,268624,602208,1163648,1967616],[]),([10,45080,153612,602208,866672,1163648,1967616],[]),([10,45080,153612,602208,1163648,1427920,1967616],[]),([10,46096,153612,602208,866672,1163648,1967616],[]),([10,46096,153612,602208,1163648,1427920,1967616],[]),([10,46104,77920,153612,866672,1163648,1967616],[]),([10,46104,115072,153612,602208,1427920,1967616],[]),([10,46104,149508,268624,602208,1163648,1967616],[]),([10,46104,149508,602208,866672,1163648,1967616],[]),([10,46104,149508,602208,1163648,1427920,1967616],[]),([10,46104,149516,268624,602208,1163648,1967616],[]),([10,46104,149516,602208,866672,1163648,1967616],[]),([10,46104,149516,602208,1163648,1427920,1967616],[]),([10,46104,153612,268624,602208,1163392,1967616],[]),([10,46104,153612,268624,602208,1163648,1967616],[]),([10,46104,153612,342384,602208,1163648,1967616],[]),([10,46104,153612,371184,602208,1163648,1967616],[]),([10,46104,153612,379344,602208,1163648,1967616],[]),([10,46104,153612,598112,866672,1163648,1967616],[]),([10,46104,153612,602208,800880,1163648,1967616],[]),([10,46104,153612,602208,801136,1163648,1967616],[]),([10,46104,153612,602208,854368,1163648,1967616],[]),([10,46104,153612,602208,854384,1163648,1967616],[]),([10,46104,153612,602208,862576,1163648,1967616],[]),([10,46104,153612,602208,866672,1163648,1966592],[]),([10,46104,153612,602208,866672,1163648,1967616],[]),([10,46104,153612,602208,1147264,1427920,1967616],[]),([10,46104,153612,602208,1163648,1362320,1967616],[]),([10,46104,153612,602208,1163648,1362384,1967616],[]),([10,46104,153612,602208,1163648,1395136,1967616],[]),([10,46104,153612,602208,1163648,1395152,1967616],[]),([10,46104,153612,602208,1163648,1411536,1967616],[]),([10,46104,153612,602208,1163648,1427920,1966592],[]),([10,46104,153612,602208,1163648,1427920,1967616],[]),([10,46104,153612,602208,1427920,1832876,1967616],[]),([10,46104,153612,602208,1432016,1828524,1967616],[]),([10,46104,153612,866672,1163648,1828524,1967616],[]),([10,46104,153612,866672,1163648,1832684,1967616],[]),([10,46104,751724,866672,1163648,1494940,1967616],[]),([10,46108,153612,602208,1163648,1427920,1967616],[]),([10,47128,153612,602208,866672,1163648,1967616],[]),([10,48144,153612,602208,866672,1163648,1967616],[]),([10,48152,77920,153612,866672,1163648,1967616],[]),([10,48152,129532,751724,866672,1163648,1967616],[]),([10,48152,149516,602208,866672,1163648,1967616],[]),([10,48152,153612,342384,602208,1163648,1967616],[]),([10,48152,153612,598112,866672,1163648,1967616],[]),([10,48152,153612,602208,800880,1163648,1967616],[]),([10,48152,153612,602208,801136,1163648,1967616],[]),([10,48152,153612,602208,866672,1163648,1966592],[]),([10,48152,153612,602208,866672,1163648,1967616],[]),([10,48152,153612,866672,1163648,1832684,1967616],[]),([10,48152,751724,866672,933500,1163648,1967616],[]),([10,48152,751724,866672,1163648,1230476,1967616],[]),([10,48152,751724,866672,1163648,1494940,1967616],[]),([10,48152,751724,866672,1163648,1943536,1967616],[]),([10,48152,751724,866672,1163648,1967616,2048996],[3591]),([10,48152,751724,866672,1163648,1967616,2091004],[]),([10,48156,153612,602208,866672,1163648,1967616],[]),([10,48156,153612,602208,1163648,1427920,1967616],[]),([10,48156,153612,602208,1427920,1967616,2082688],[]),([10,62476,153612,395600,602208,1163648,1967616],[1286,4868]),([10,62492,153612,395600,602208,1163648,1967616],[]),([10,63516,77920,153612,866672,1163648,1967616],[]),([10,63516,129532,602208,1300876,1427920,1967616],[]),([10,63516,153612,330064,602208,1163648,1967616],[]),([10,63516,153612,342384,602208,1163648,1967616],[]),([10,63516,153612,395600,602208,1163648,1967616],[]),([10,63516,153612,602208,866672,1163648,1967616],[2050]),([10,63516,153612,602208,1163648,1964528,1967616],[2050]),([10,63516,153612,602208,1300876,1427920,1967616],[1286]),([10,63516,153612,602208,1427920,1967616,2082688],[]),([10,63516,195612,602208,1300876,1427920,1967616],[1281]),([10,63516,602208,751724,866672,1163648,1967616],[2050,2818]),([10,63516,602208,751724,1163648,1427920,1967616],[3842]),([10,63516,602208,1300876,1427920,1967616],[3617]),([10,64540,77920,153612,866672,1163648,1967616],[]),([10,64540,129532,602208,1300876,1427920,1967616],[]),([10,64540,153612,330064,602208,1163648,1967616],[]),([10,64540,153612,342384,602208,1163648,1967616],[]),([10,64540,153612,395600,602208,1163648,1967616],[]),([10,64540,153612,602208,866672,1163648,1967616],[2050]),([10,64540,153612,602208,1163648,1964528,1967616],[2050]),([10,64540,153612,602208,1169804,1427920,1967616],[]),([10,64540,153612,602208,1300876,1427920,1967616],[1281]),([10,64540,153612,602208,1427920,1967616,2082688],[]),([10,64540,602208,751724,866672,1163648,1967616],[2050,2818]),([10,64540,602208,751724,1163648,1427920,1967616],[3842]),([10,64540,602208,1300876,1427920,1967616],[3617]),([10,65536,153612,173596,1700320,1964528,1967616],[1281]),([10,65536,153612,330064,437788,1700320,1967616],[1281]),([10,65536,153612,437788,866672,1700320,1967616],[1281]),([10,65536,153612,437788,1700320,1964528,1967616],[1281]),([10,66016,153612,602208,1427920,2008600,2082688],[2564]),([10,66016,153612,602208,1427920,2031132,2082688],[1284]),([10,66016,395600,602208,1163648,1990156,2031132],[1284,3588]),([10,69728,153612,602208,1427920,2008600,2082688],[2564]),([10,69728,153612,866672,1163648,2008600,2045536],[1794,4866]),([10,72032,153612,866672,1163648,2008600,2045536],[1794]),([10,73824,153612,195612,866672,1163648,1967616],[1287]),([10,73824,153612,866672,1163648,1967616,2031132],[1283,3586]),([10,77920,107544,153612,866672,1163648,1967616],[3586]),([10,77920,153612,173080,866672,1163648,1967616],[]),([10,77920,153612,195612,866672,1163648,1967616],[1287]),([10,77920,153612,195612,1163648,1964528,1967616],[1287]),([10,77920,153612,602208,1427920,2008600,2082688],[2564]),([10,77920,153612,866672,1163648,1967616,2008600],[3586]),([10,77920,153612,866672,1163648,1967616,2031132],[1283,3586]),([10,77920,153612,866672,1163648,2008600,2045536],[1794,4866]),([10,77920,153612,866672,1163648,2008600,2082688],[]),([10,77920,153612,1163648,1964528,1967616,2008600],[3589]),([10,77920,195612,227436,866672,1163648,1967616],[1799,2567]),([10,77920,195612,342384,751724,1163648,1967616],[1795,2563]),([10,77920,195612,602208,1300876,1427920,1967616],[1793,3590]),([10,77920,195612,751724,866672,1163648,1967616],[1795,2563]),([10,77920,195612,751724,1163648,1427920,1967616],[3591]),([10,77920,195612,866672,1163648,1300876,1967616],[])]
noncomputable def k11 : CE := [([10,80240,153612,866672,1163648,2008600,2045536],[1794]),([10,80240,195612,751724,866672,1163648,1967616],[2563]),([10,88548,153612,602208,1427920,2008600,2082688],[]),([10,88548,153612,602208,1427920,2031132,2082688],[1284]),([10,88548,153612,602208,1964528,2008600,2082688],[]),([10,88548,395600,602208,1163648,1967616,2031132],[3590]),([10,88548,395600,602208,1163648,1990156,2008600],[]),([10,88548,395608,602208,1163648,1967616,2031132],[3588]),([10,88548,602208,1300876,1427920,1967616,2031132],[]),([10,96364,153612,195612,866672,1163648,1967616],[1287]),([10,96364,153612,866672,1163648,1967616,2008600],[]),([10,96364,195612,751724,866672,1163648,1967616],[1795]),([10,96764,153612,602208,1427920,2008600,2082688],[]),([10,106520,153612,330064,602208,1163648,1967616],[]),([10,106520,153612,602208,866672,1163648,1967616],[]),([10,106992,153612,305168,602208,1163648,1967616],[]),([10,106992,153612,602208,1427920,2008600,2082688],[2564]),([10,106992,153612,602208,1427920,2031132,2082688],[]),([10,106992,173080,395600,602208,1163648,1990156],[1796]),([10,106992,195612,395600,602208,1163648,1990156],[1796]),([10,106992,395600,602208,1163648,1990156,2031132],[1284,3972]),([10,107544,129532,153612,330064,1700320,1967616],[]),([10,107544,129532,153612,866672,1700320,1967616],[]),([10,107544,129532,153612,1700320,1964528,1967616],[]),([10,107544,153604,330064,602208,1163648,1967616],[]),([10,107544,153604,602208,866672,1163648,1967616],[]),([10,107544,153612,330064,602208,1163648,1967616],[]),([10,107544,153612,330064,933500,1700320,1967616],[3204]),([10,107544,153612,330064,1700320,1767084,1967616],[]),([10,107544,153612,330064,1700320,1967616,1989604],[1281,5508,6017]),([10,107544,153612,330064,1700320,1967616,2031612],[5508]),([10,107544,153612,342384,602208,1163648,1967616],[]),([10,107544,153612,371184,602208,1163648,1967616],[]),([10,107544,153612,372056,1700320,1967616,1989604],[1281,5508]),([10,107544,153612,602208,866672,1163648,1967616],[]),([10,107544,153612,602208,1427920,1767084,1967616],[]),([10,107544,153612,602208,1427920,1832876,1967616],[3074]),([10,107544,153612,602208,1427920,1967616,2087908],[1281]),([10,107544,153612,866672,933500,1700320,1967616],[3204]),([10,107544,153612,866672,1494940,1700320,1967616],[3205]),([10,107544,153612,866672,1700320,1967616,1989604],[1281,5508,6017]),([10,107544,153612,866672,1700320,1967616,2031612],[5508]),([10,107544,153612,933500,1700320,1964528,1967616],[4228]),([10,107544,153612,1700320,1964528,1967616,1989604],[1281,6017]),([10,107544,153612,1700320,1964528,1967616,2031612],[]),([10,107608,153612,602208,1427920,1832876,1967616],[]),([10,129532,153612,602208,1427920,2008600,2082688],[]),([10,129532,153612,602208,1427920,2031132,2082688],[]),([10,129532,153612,602208,1964528,2008600,2082688],[]),([10,129532,195612,227436,866672,1163648,1967616],[]),([10,129532,195612,342384,751724,1163648,1967616],[]),([10,129532,195612,602208,1300876,1427920,1967616],[]),([10,129532,195612,602208,1300876,1964528,1967616],[]),([10,129532,602208,1300876,1427920,1967616,2031132],[]),([10,153604,602208,866672,1163648,1967616,2008600],[3842]),([10,153604,602208,866672,1163648,2008600,2056164],[]),([10,153612,161916,602208,1427920,2008600,2082688],[]),([10,153612,172056,602208,866672,1163648,1967616],[]),([10,153612,173080,342384,602208,1163648,1967616],[]),([10,153612,173080,371184,602208,1163648,1967616],[]),([10,153612,173080,602208,858464,1163648,1967616],[]),([10,153612,173080,602208,858480,1163648,1967616],[]),([10,153612,173080,602208,866672,1163648,1967616],[]),([10,153612,173080,602208,1427920,1832876,1967616],[]),([10,153612,173080,602208,1558992,1701548,1967616],[4868]),([10,153612,173084,602208,866672,1163648,1967616],[]),([10,153612,173084,602208,1163648,1964528,1967616],[]),([10,153612,173596,602208,866672,1163648,1967616],[]),([10,153612,173596,602208,1163648,1964528,1967616],[]),([10,153612,173596,602208,1296268,1427920,1967616],[]),([10,153612,173596,602208,1296268,1964528,1967616],[]),([10,153612,173596,602208,1300876,1427920,1967616],[1281]),([10,153612,173596,602208,1300876,1964528,1967616],[1286,1793]),([10,153612,175132,602208,866672,1163648,1967616],[]),([10,153612,175132,602208,1163648,1964528,1967616],[]),([10,153612,177180,602208,1163648,1427920,1967616],[]),([10,153612,177180,602208,1163648,1964528,1967616],[]),([10,153612,177180,602208,1298828,1427920,1967616],[]),([10,153612,177180,602208,1300876,1427920,1967616],[1281]),([10,153612,177180,602208,1427920,1832876,1967616],[]),([10,153612,177180,602208,1427920,1967616,2082688],[]),([10,153612,179228,602208,866672,1163648,1967616],[1799]),([10,153612,179228,602208,1163648,1427920,1967616],[]),([10,153612,179228,602208,1163648,1964528,1967616],[1799]),([10,153612,179228,602208,1300876,1427920,1967616],[1281]),([10,153612,179228,602208,1427920,1967616,2082688],[]),([10,153612,179228,735340,866672,1163648,1967616],[1283,1799]),([10,153612,179228,751724,866672,1163648,1967616],[1283,1799]),([10,153612,179228,866672,1163648,1967616,2045536],[3842]),([10,153612,193548,602208,866672,1163648,1967616],[]),([10,153612,193548,602208,1427920,1832876,1967616],[4228]),([10,153612,193564,602208,866672,1163648,1967616],[]),([10,153612,193564,602208,1427920,1832876,1967616],[]),([10,153612,194588,602208,866672,1163648,1967616],[1799]),([10,153612,195612,227436,866672,1163648,1967616],[1287,1799]),([10,153612,195612,305488,602208,1163648,1967616],[]),([10,153612,195612,342384,751724,1163648,1967616],[1283,2563]),([10,153612,195612,371184,602208,1163648,1967616],[]),([10,153612,195612,391664,602208,1163648,1967616],[2567,3590]),([10,153612,195612,602208,784044,1427920,1967616],[]),([10,153612,195612,602208,866672,1163648,1967616],[1795]),([10,153612,195612,602208,866800,1163648,1967616],[1799]),([10,153612,195612,602208,899568,1163648,1967616],[1799]),([10,153612,195612,602208,915952,1163648,1967616],[1799,3590]),([10,153612,195612,602208,1163648,1903088,1967616],[]),([10,153612,195612,602208,1163648,1915376,1967616],[1799]),([10,153612,195612,602208,1163648,1944048,1967616],[]),([10,153612,195612,602208,1163648,1948144,1967616],[1799]),([10,153612,195612,602208,1163648,1964528,1967616],[1799,2566]),([10,153612,195612,602208,1169804,1427920,1967616],[2561]),([10,153612,195612,602208,1175980,1427920,1967616],[2566]),([10,153612,195612,602208,1296268,1427920,1967616],[]),([10,153612,195612,602208,1296268,1964528,1967616],[1795]),([10,153612,195612,602208,1296780,1427920,1967616],[1281,2561]),([10,153612,195612,602208,1298828,1427920,1967616],[2561]),([10,153612,195612,602208,1300876,1427920,1967616],[1281,2561]),([10,153612,195612,602208,1308044,1427920,1967616],[]),([10,153612,195612,602208,1308332,1952208,1967616],[]),([10,153612,195612,602208,1411536,1967616,2082688],[]),([10,153612,195612,602208,1426304,1427920,1967616],[2561]),([10,153612,195612,602208,1427920,1558400,1967616],[]),([10,153612,195612,602208,1427920,1688480,1967616],[3585]),([10,153612,195612,602208,1427920,1697696,1967616],[]),([10,153612,195612,602208,1427920,1700256,1967616],[1795,3590]),([10,153612,195612,602208,1427920,1816236,1967616],[]),([10,153612,195612,602208,1427920,1820544,1967616],[]),([10,153612,195612,602208,1427920,1832876,1967616],[]),([10,153612,195612,602208,1427920,1834924,1967616],[]),([10,153612,195612,602208,1427920,1950592,1967616],[3585]),([10,153612,195612,602208,1427920,1951616,1967616],[]),([10,153612,195612,602208,1427920,1967616,2066304],[]),([10,153612,195612,602208,1427920,1967616,2082688],[]),([10,153612,195612,602208,1427920,1967616,2095020],[]),([10,153612,195612,602208,1427920,1979948,2082688],[]),([10,153612,195612,602208,1427920,1982076,2082688],[]),([10,153612,195612,602208,1432016,1828524,1967616],[]),([10,153612,195612,602208,1440208,1820332,1967616],[1795]),([10,153612,195612,602208,1558992,1701548,1967616],[3590,4868]),([10,153612,196124,602208,1163648,1964528,1967616],[1799,2566]),([10,153612,219628,602208,1427920,2008600,2082688],[3588]),([10,153612,260604,602208,1427920,2008600,2082688],[]),([10,153612,285008,437788,602208,1163648,1967616],[]),([10,153612,305168,371184,602208,1163648,1967616],[]),([10,153612,305168,602208,1163648,1700320,1967616],[]),([10,153612,305168,602208,1163648,1964528,1967616],[]),([10,153612,305168,602208,1163648,1967616],[]),([10,153612,305488,437788,602208,1163648,1967616],[]),([10,153612,305488,602208,1163648,1967616,2031132],[]),([10,153612,310616,602208,1163648,2012696,2051044],[]),([10,153612,310616,866672,1163648,1828524,1967616],[])]
noncomputable def k12 : CE := [([10,153612,371184,602208,1163648,1967616,2031132],[]),([10,153612,371184,602208,1163648,2008600,2045536],[2053]),([10,153612,371184,602208,1163648,2031132,2045536],[1797,2050]),([10,153612,372056,602208,1163648,1989604,2074136],[]),([10,153612,458268,602208,1163648,1964528,1967616],[1799,2566]),([10,153612,602208,621028,1427920,2008600,2082688],[]),([10,153612,602208,653820,1427920,2008600,2082688],[]),([10,153612,602208,753644,1427920,2008600,2082688],[]),([10,153612,602208,786428,1427920,2008600,2082688],[]),([10,153612,602208,1048572,1427920,2008600,2082688],[]),([10,153612,602208,1163648,1964528,2008600,2056164],[]),([10,153612,602208,1169892,1427920,2008600,2082688],[]),([10,153612,602208,1178108,1427920,2008600,2082688],[]),([10,153612,602208,1300876,1427920,2008600,2056164],[]),([10,153612,602208,1411536,2008600,2082688],[2116]),([10,153612,602208,1427920,1432052,2008600,2082688],[]),([10,153612,602208,1427920,1440252,2008600,2082688],[4483]),([10,153612,602208,1427920,1499036,2008600,2082688],[3205]),([10,153612,602208,1427920,1507324,2008600,2082688],[3205,4484]),([10,153612,602208,1427920,1558400,2008600],[2116]),([10,153612,602208,1427920,1560476,2008600,2082688],[]),([10,153612,602208,1427920,1560540,2008600,2082688],[]),([10,153612,602208,1427920,1564668,2008600,2082688],[]),([10,153612,602208,1427920,1572860,2008600,2082688],[4484]),([10,153612,602208,1427920,1832876,2008600,2082688],[2948]),([10,153612,602208,1427920,1959920,2008600,2082688],[4481]),([10,153612,602208,1427920,1961968,2008600,2082688],[4481]),([10,153612,602208,1427920,1966068,2008600,2082688],[4481]),([10,153612,602208,1427920,1966076,2008600,2082688],[4481]),([10,153612,602208,1427920,2008600,2082688],[2116]),([10,153612,602208,1427920,2008600,2082688,2084764],[]),([10,153612,602208,1427920,2008600,2082688,2088932],[]),([10,153612,602208,1427920,2008600,2082688,2093052],[]),([10,153612,602208,1427920,2008600,2082688,2097148],[]),([11,0,42009,153612,264529,1700320,2033152],[2564]),([11,0,42009,395600,602208,1163648,1990156],[]),([11,8,107544,153612,264529,1700320,1967616],[6,1284,1796,2564,3588,4868]),([11,4096,42009,153612,264529,1700320,2033152],[2,1284]),([11,4096,42009,219148,264529,1700320,1967616],[3,1284,1793,2561,3585]),([11,4096,42009,264529,743436,1163648,1967616],[1795,3587,4871]),([11,4096,42009,395600,602208,1163648,1990156],[3]),([11,4096,42009,416092,602208,1163648,1974096],[]),([11,4096,42009,751724,1300876,1427920,1967616],[3587,4865]),([11,4096,153612,602208,1427920,2008600,2082688],[2564]),([11,4096,153612,866672,1163648,2008600,2045536],[5,1282,1794,2562,3586,4866]),([11,4096,195612,751724,866672,1163648,1967616],[3,1283,1795,2563,3585,4869]),([11,6144,42009,153612,602208,1950080,1967616],[]),([11,6144,42009,153612,864352,1163648,1967616],[2562,3585,4866]),([11,6144,42009,602208,940044,1163648,1967616],[1795,3585]),([11,6144,42009,751724,866672,1163648,1967616],[3585,4866]),([11,6144,42009,751724,866672,1163648,1973760],[3,1794,2562,3586,4866]),([11,6144,42009,751724,866672,1169792,1967616],[3,1793,2561,3585,4866]),([11,6144,42009,751724,1163648,1964528,1967616],[2563,4866]),([11,6144,48152,751724,866672,1163648,1967616],[]),([11,6144,153612,866672,1163648,2008600,2045536],[5,1282,1794,2562,3586,4866]),([11,6144,195612,602208,1014140,1163648,1967616],[1795,3590,4870]),([11,6144,195612,751724,866672,1163648,1967616],[3,1283,1795,2563,3585,4869]),([11,6144,751724,866672,1163648,1967616,2008600],[2561,3591,4867]),([11,14352,195612,751724,866672,1163648,1967616],[3,1283,2563,3585,4869]),([11,20480,42009,153612,264529,1700320,2033152],[1284]),([11,20480,42009,219148,264529,1700320,1967616],[1,1286,1793,2561,3585]),([11,20480,42009,264529,602208,1163648,1703936],[1286,4868]),([11,20480,42009,264529,602208,1294720,1967616],[1286,4870]),([11,20480,42009,395600,602208,1163648,1967616],[4865]),([11,20480,107544,153612,264529,1700320,1967616],[6,1284,1796,3588,4868]),([11,22528,42009,602208,1014140,1163648,1967616],[]),([11,22528,42009,602208,1163648,1967616,2095612],[3585]),([11,22528,42009,602208,1300876,1427920,1967616],[1795]),([11,22528,42009,602208,1300876,1964528,1967616],[1793]),([11,40960,153612,264529,602208,1163648,1967616],[1286,4868]),([11,42008,65536,153612,264529,1700320,1967616],[1284,2049]),([11,42008,131072,264529,602208,1163648,1990156],[2818]),([11,42008,153612,264528,602208,1163648,1967616],[]),([11,42008,153612,264529,602208,1163648,1967616],[]),([11,42008,153612,264529,602208,1163648,1971712],[]),([11,42008,153612,264529,602208,1163648,2008600],[4]),([11,42008,153612,264529,602208,1163648,2033152],[]),([11,42008,153612,264529,602208,1167744,1967616],[]),([11,42008,153612,264529,602208,1172888,1967616],[2564]),([11,42008,153612,264529,602208,1294720,1967616],[]),([11,42008,153612,268624,602208,1163648,1967616],[]),([11,42008,153612,306520,602208,1163648,1967616],[]),([11,42008,153612,330064,602208,1163648,1967616],[]),([11,42008,153612,395600,602208,1163648,1967616],[]),([11,42008,153612,602208,866672,1163648,1967616],[]),([11,42009,65536,131072,264529,1700320,1990156],[1284,5124]),([11,42009,65536,151552,264529,1700320,1967616],[1284,2049]),([11,42009,65536,153612,264529,1593344,1967616],[1284]),([11,42009,65536,153612,264529,1667168,1967616],[1284,2049]),([11,42009,65536,153612,264529,1700320,1967616],[1284,2049]),([11,42009,65536,153612,264529,1700320,1971712],[1284]),([11,42009,65536,153612,264529,1700320,1988096],[1284]),([11,42009,65536,153612,264529,1700320,2033152],[1284]),([11,42009,65536,153612,264529,1831392,1967616],[1284,2049]),([11,42009,65536,153612,268624,1700320,1967616],[1284,2049]),([11,42009,65536,153612,285008,1700320,1967616],[2049]),([11,42009,65536,153612,330064,1700320,1967616],[2049]),([11,42009,65536,153612,330064,1700320,2033152],[]),([11,42009,65536,153612,330064,1700320,2035536],[]),([11,42009,65536,153612,330064,1964528,1967616],[2049]),([11,42009,65536,153612,395600,1700320,1967616],[2049]),([11,42009,65536,153612,602208,1329488,1967616],[1285,2049]),([11,42009,65536,153612,866672,1427920,1967616],[2049]),([11,42009,65536,153612,866672,1700320,1967616],[2049]),([11,42009,65536,153612,866672,1700320,2033152],[]),([11,42009,65536,153612,1700320,1964528,1967616],[2049]),([11,42009,65536,153612,1700320,1964528,2033152],[]),([11,42009,65536,153612,1833452,1964528,1967616],[1793,2049]),([11,42009,65536,219148,264529,1700320,2033152],[1284]),([11,42009,65536,264529,602208,1294720,1990156],[68,1284,2820,3844,5124]),([11,42009,65536,395600,602208,1163648,1990156],[1284]),([11,42009,65536,481628,602208,1163648,2035536],[]),([11,42009,69632,153612,264529,1687936,1967616],[5122]),([11,42009,69632,153612,264529,1700320,1967616],[1284,2049]),([11,42009,69632,153612,264529,1700320,2037248],[66,1284]),([11,42009,69632,153612,334160,1700320,1967616],[2049]),([11,42009,69632,153612,788816,1163648,1967616],[5122]),([11,42009,69632,153612,866672,1700320,1967616],[2049]),([11,42009,69632,153612,1427920,1700320,1967616],[2051,5122]),([11,42009,69632,153612,1427920,1833452,1967616],[5122]),([11,42009,69632,153612,1700320,1964528,1967616],[2049]),([11,42009,69632,219148,264529,1700320,1967616],[67,1284,2049,2817,3841]),([11,42009,69632,264529,677900,1163648,1967616],[5125]),([11,42009,69632,751724,1300876,1427920,1967616],[3843,5121]),([11,42009,71936,602208,1014140,1163648,1967616],[5121]),([11,42009,71936,751724,866672,1163648,1967616],[3841,5122]),([11,42009,86016,153612,264529,1700320,1967616],[1284,2049]),([11,42009,86016,219148,264529,1700320,1967616],[65,1286,2049,2817,3841]),([11,42009,131072,268624,602208,1163648,1990156],[]),([11,42009,131072,330064,602208,1163648,1990156],[2818]),([11,42009,131072,395264,602208,1163648,1990156],[1284,2818,3074,4868]),([11,42009,131072,395600,602208,1163648,1990156],[1284,2818]),([11,42009,131072,395600,602208,1163648,1990492],[]),([11,42009,131072,395600,602208,1294720,1990156],[1284]),([11,42009,131072,395600,602208,1558992,1990156],[1284]),([11,42009,131072,416092,602208,1163648,1970000],[]),([11,42009,131072,602208,792576,1163648,1990156],[2050,3074,4868]),([11,42009,131072,602208,792912,1163648,1990156],[2050]),([11,42009,131072,602208,866672,1163648,1990156],[2050]),([11,42009,131072,602208,866672,1294720,1990156],[1284]),([11,42009,131072,602208,997744,1163648,1990156],[1284,2050]),([11,42009,131072,602208,1163648,1964528,1990156],[2050]),([11,42009,131072,602208,1294720,1427920,1990156],[1284,2050]),([11,42009,131072,602208,1294720,1558992,1990156],[1284,2050]),([11,42009,131072,602208,1300876,1427920,1990156],[]),([11,42009,131072,602208,1427920,1990156,2088844],[3588]),([11,42009,133120,395600,602208,1163648,1990156],[65,1284,2818]),([11,42009,135168,399696,602208,1163648,1990156],[1284]),([11,42009,135168,602208,866672,1163648,1990156],[2050]),([11,42009,135168,602208,1163648,1427920,1990156],[2050,3842])]
noncomputable def k13 : CE := [([11,42009,135168,866672,1163648,1990156,2045536],[2051,2818]),([11,42009,137216,602208,866672,1163648,1990156],[2050]),([11,42009,137216,751724,866672,1163648,1967616],[1287,3841,5122]),([11,42009,151552,264529,602208,1163648,1967616],[]),([11,42009,151552,264529,602208,1163648,1971712],[2823]),([11,42009,151552,264529,602208,1163648,1988096],[2823,3846]),([11,42009,151552,264529,602208,1163648,1990156],[2821,3844]),([11,42009,151552,264529,602208,1167744,1967616],[2819]),([11,42009,151552,264529,602208,1294720,1967616],[1286,5126]),([11,42009,151552,264529,602208,1298816,1967616],[1286,2817,5126]),([11,42009,151552,416080,602208,1163648,1967616],[1281]),([11,42009,151552,602208,866672,1163648,1967616],[]),([11,42009,151552,602208,1163648,1964528,1967616],[]),([11,42009,151552,602208,1427920,1967616,2082688],[]),([11,42009,153600,602208,866672,1163648,1967616],[]),([11,42009,153600,602208,1163648,1964528,1967616],[6017]),([11,42009,153612,196608,264529,1700320,1967616],[1796,2049]),([11,42009,153612,219148,264529,1700320,1967616],[65,1286,1796,2049]),([11,42009,153612,219148,264529,1700320,2033152],[65,129,1284,1796]),([11,42009,153612,219148,330064,1700320,1967616],[65,1281,2049]),([11,42009,153612,219148,866672,1700320,1967616],[65,1281,2049]),([11,42009,153612,219148,1700320,1964528,1967616],[65,1281,2049,2817]),([11,42009,153612,264529,602208,1163648,1967616],[]),([11,42009,153612,264529,602208,1163648,1971712],[]),([11,42009,153612,264529,602208,1163648,1988096],[]),([11,42009,153612,264529,602208,1163648,2033152],[]),([11,42009,153612,264529,602208,1163648,2037248],[]),([11,42009,153612,264529,602208,1167744,1971712],[]),([11,42009,153612,264529,602208,1167744,1984000],[]),([11,42009,153612,264529,602208,1167744,1988096],[]),([11,42009,153612,264529,602208,1167744,2033152],[]),([11,42009,153612,264529,602208,1167744,2037248],[]),([11,42009,153612,264529,602208,1294720,1984000],[5124]),([11,42009,153612,264529,602208,1294720,1990156],[65,1284,5124]),([11,42009,153612,264529,602208,1294720,2033152],[5124]),([11,42009,153612,264529,602208,1298816,1990156],[65,1284,5124]),([11,42009,153612,264529,602208,1300876,1984000],[]),([11,42009,153612,264529,602208,1300876,1988096],[]),([11,42009,153612,264529,602208,1300876,2049536],[]),([11,42009,153612,264529,602208,1687936,1984000],[]),([11,42009,153612,264529,602208,1700320,2049536],[197,4354]),([11,42009,153612,264529,602208,1819008,2063980],[1284]),([11,42009,153612,264529,618592,1167744,1967616],[]),([11,42009,153612,264529,618592,1294720,1967616],[5125]),([11,42009,153612,264529,618592,1300876,1967616],[]),([11,42009,153612,264529,618592,1300876,1984000],[]),([11,42009,153612,264529,618592,1687936,1967616],[]),([11,42009,153612,264529,733280,1294720,1967616],[5124]),([11,42009,153612,264529,733280,1294720,1990156],[65,1284,5124]),([11,42009,153612,264529,733280,1298816,1967616],[5124]),([11,42009,153612,264529,737280,1700320,1967616],[2564,2817,5634]),([11,42009,153612,264529,743436,1700320,1967616],[65,1286,2564,2817]),([11,42009,153612,264529,749664,1300876,1967616],[]),([11,42009,153612,264529,751724,1687936,2045536],[1287]),([11,42009,153612,264529,751724,1692032,1967616],[]),([11,42009,153612,264529,751724,1700320,2033152],[195,1286]),([11,42009,153612,264529,751724,1700320,2049536],[195,1287,2946]),([11,42009,153612,264529,751724,1819008,2045536],[1287]),([11,42009,153612,264529,1650784,1700320,2082688],[]),([11,42009,153612,264529,1650784,1990156,2082688],[]),([11,42009,153612,264529,1650784,2045536,2082688],[]),([11,42009,153612,264529,1667168,1967616,2088844],[]),([11,42009,153612,264529,1667168,1990156,2082688],[]),([11,42009,153612,264529,1700320,1700320,2033152],[196]),([11,42009,153612,264529,1700320,1833452,2033152],[257,1286]),([11,42009,153612,264529,1700320,1967616,2055692],[3972,4868]),([11,42009,153612,264529,1700320,1990156,2033152],[3588]),([11,42009,153612,264529,1700320,2033152],[97,228,1316,3620]),([11,42009,153612,264529,1700320,2033152,2033152],[3588]),([11,42009,153612,264529,1700320,2033152,2045536],[322,3588]),([11,42009,153612,264529,1700320,2033152,2055692],[3972,4868]),([11,42009,153612,264529,1700320,2033152,2095072],[3588]),([11,42009,153612,264529,1700320,2037248],[97,228,290,1316,3620]),([11,42009,153612,264529,1700320,2045536,2082688],[]),([11,42009,153612,264529,1700320,2045536,2088844],[]),([11,42009,153612,264529,1833452,2045536,2082688],[1286]),([11,42009,153612,268288,602208,1163648,1967616],[3074]),([11,42009,153612,268624,602208,1163648,1967616],[]),([11,42009,153612,268624,602208,1163648,1967872],[]),([11,42009,153612,268624,602208,1163648,1971712],[]),([11,42009,153612,268624,602208,1163648,1971776],[]),([11,42009,153612,268624,602208,1163648,1973760],[]),([11,42009,153612,268624,602208,1163648,1974096],[]),([11,42009,153612,268624,602208,1163648,1984000],[]),([11,42009,153612,268624,602208,1163648,2033152],[]),([11,42009,153612,268624,602208,1167744,1967616],[]),([11,42009,153612,268624,602208,1167744,1971712],[]),([11,42009,153612,268624,602208,1167744,1974096],[]),([11,42009,153612,268624,602208,1167808,1967616],[]),([11,42009,153612,268624,602208,1169792,1967616],[]),([11,42009,153612,268624,602208,1294720,1967616],[]),([11,42009,153612,268624,602208,1425792,1967616],[]),([11,42009,153612,268624,602208,1432016,1967616],[129]),([11,42009,153612,268624,602208,1432016,1971712],[]),([11,42009,153612,268624,602208,1687936,1967616],[]),([11,42009,153612,268624,602464,1163648,1967616],[]),([11,42009,153612,268624,604256,1163648,1967616],[]),([11,42009,153612,268624,618592,1163648,1967616],[]),([11,42009,153612,268624,733280,1163648,1967616],[]),([11,42009,153612,268624,751724,1163648,1967616],[]),([11,42009,153612,268624,751724,1163648,1971712],[]),([11,42009,153612,268624,751724,1163648,1974096],[]),([11,42009,153612,268624,751724,1167744,1967616],[]),([11,42009,153612,268624,751724,1432016,1967616],[]),([11,42009,153612,268624,864352,1163648,1967616],[]),([11,42009,153612,268624,866672,1163648,1967616],[131]),([11,42009,153612,268624,866672,1163648,1971712],[130]),([11,42009,153612,268624,866672,1167744,1967616],[130]),([11,42009,153612,268624,866672,1432016,1967616],[131]),([11,42009,153612,268624,1014140,1163648,1967616],[]),([11,42009,153612,268624,1163648,1650784,1967616],[]),([11,42009,153612,285008,602208,1163648,1967616],[]),([11,42009,153612,285008,602208,1163648,1988096],[]),([11,42009,153612,285008,602208,1163648,1990480],[]),([11,42009,153612,285008,602208,1167744,1967616],[]),([11,42009,153612,285008,602208,1300876,1967616],[]),([11,42009,153612,285008,602208,1432016,1967616],[129]),([11,42009,153612,330064,602208,1163648,1967616],[]),([11,42009,153612,330064,602208,1163648,1969664],[]),([11,42009,153612,330064,602208,1163648,1971712],[]),([11,42009,153612,330064,602208,1163648,2033152],[]),([11,42009,153612,330064,602208,1163648,2033216],[]),([11,42009,153612,330064,602208,1163648,2035536],[]),([11,42009,153612,330064,602208,1165696,1967616],[]),([11,42009,153612,330064,602208,1167744,1967616],[]),([11,42009,153612,330064,602208,1294720,1967616],[]),([11,42009,153612,330064,602208,1427920,2033152],[]),([11,42009,153612,330064,602208,1700320,2033152],[194]),([11,42009,153612,330064,1700320,2033152],[97,2081]),([11,42009,153612,334160,602208,1163648,1967616],[]),([11,42009,153612,334160,602208,1163648,2037248],[]),([11,42009,153612,334160,602208,1163648,2039632],[]),([11,42009,153612,334160,602208,1167744,1967616],[]),([11,42009,153612,334160,751724,1163648,1967616],[]),([11,42009,153612,395264,602208,1163648,1967616],[1286,3074,4868]),([11,42009,153612,395264,602208,1163648,1990156],[65,1284,3074,4868]),([11,42009,153612,395600,602208,1163648,1967616],[]),([11,42009,153612,395600,602208,1163648,1967680],[]),([11,42009,153612,395600,602208,1163648,1969664],[1286]),([11,42009,153612,395600,602208,1163648,1970000],[]),([11,42009,153612,395600,602208,1163648,1971712],[]),([11,42009,153612,395600,602208,1163648,1990156],[65,1284]),([11,42009,153612,395600,602208,1163648,1990492],[]),([11,42009,153612,395600,602208,1163648,2033152],[]),([11,42009,153612,395600,602208,1163712,1967616],[]),([11,42009,153612,395600,602208,1167744,1967616],[]),([11,42009,153612,395600,602208,1294720,1967616],[]),([11,42009,153612,395600,602208,1294720,1970000],[]),([11,42009,153612,395600,602208,1294720,1990156],[65,1284]),([11,42009,153612,395600,602208,1296768,1967616],[1286])]
noncomputable def k14 : CE := [([11,42009,153612,395600,602208,1558992,1967616],[]),([11,42009,153612,395600,602208,1558992,1990156],[1284]),([11,42009,153612,395600,733280,1294720,1967616],[]),([11,42009,153612,395600,733280,1558992,1967616],[]),([11,42009,153612,395600,997744,1558992,1967616],[]),([11,42009,153612,399696,602208,1163648,1967616],[]),([11,42009,153612,399696,602208,1163648,1971712],[]),([11,42009,153612,399696,602208,1163648,1974096],[]),([11,42009,153612,399696,602208,1163648,1990156],[65,1284]),([11,42009,153612,399696,602208,1298816,1967616],[]),([11,42009,153612,399696,602208,1563088,1967616],[129]),([11,42009,153612,399696,733280,1163648,1967616],[]),([11,42009,153612,399696,751724,1163648,1967616],[]),([11,42009,153612,399696,997744,1163648,1967616],[131]),([11,42009,153612,416080,602208,1163648,1967616],[]),([11,42009,153612,416092,602208,1163648,1970000],[]),([11,42009,153612,416092,602208,1163648,1974096],[]),([11,42009,153612,416092,602208,1427920,1967616],[129]),([11,42009,153612,416092,602208,1432016,1967616],[129]),([11,42009,153612,416092,602208,1558992,1967616],[129]),([11,42009,153612,461136,602208,1163648,1967616],[]),([11,42009,153612,481628,602208,1163648,2035536],[]),([11,42009,153612,593920,858448,1163648,1967616],[1797,2051,5378]),([11,42009,153612,593920,1163648,1427920,1967616],[]),([11,42009,153612,593920,1300876,1427920,1967616],[1286]),([11,42009,153612,593920,1427920,1967616,2088844],[]),([11,42009,153612,593984,1163648,1427920,1967616],[]),([11,42009,153612,602208,788816,1163648,1967872],[]),([11,42009,153612,602208,788816,1163648,1969664],[]),([11,42009,153612,602208,788816,1163648,1971712],[]),([11,42009,153612,602208,788816,1163648,1984000],[]),([11,42009,153612,602208,788816,1163648,2033152],[]),([11,42009,153612,602208,788816,1687936,1970000],[2817]),([11,42009,153612,602208,788816,1687936,2045536],[]),([11,42009,153612,602208,792576,1163648,1967616],[3074]),([11,42009,153612,602208,792576,1163648,1973760],[3074]),([11,42009,153612,602208,792576,1163648,2045536],[]),([11,42009,153612,602208,792576,1956224,1967616],[2564,2817]),([11,42009,153612,602208,792912,1163648,1967616],[]),([11,42009,153612,602208,792912,1163648,1971712],[]),([11,42009,153612,602208,792912,1692032,1967616],[]),([11,42009,153612,602208,792912,1956304,1967616],[]),([11,42009,153612,602208,805200,1163648,1967616],[]),([11,42009,153612,602208,854352,1163648,2033152],[]),([11,42009,153612,602208,858368,1163648,1967616],[]),([11,42009,153612,602208,858448,1163648,1967616],[]),([11,42009,153612,602208,866400,1163648,1967616],[130,3074]),([11,42009,153612,602208,866672,1163648,1967616],[]),([11,42009,153612,602208,866672,1163648,1971712],[]),([11,42009,153612,602208,866672,1163648,1973760],[2050]),([11,42009,153612,602208,866672,1163648,1984000],[]),([11,42009,153612,602208,866672,1163648,1988096],[]),([11,42009,153612,602208,866672,1163648,1990144],[2050]),([11,42009,153612,602208,866672,1163648,2033152],[]),([11,42009,153612,602208,866672,1163648,2033408],[]),([11,42009,153612,602208,866672,1163648,2037248],[]),([11,42009,153612,602208,866672,1163648,2039552],[2050,2817]),([11,42009,153612,602208,866672,1163648,2049536],[]),([11,42009,153612,602208,866672,1163648,2049792],[]),([11,42009,153612,602208,866672,1167744,1967616],[]),([11,42009,153612,602208,866672,1167744,1971712],[]),([11,42009,153612,602208,866672,1169792,1967616],[2049]),([11,42009,153612,602208,866672,1169792,1973760],[2050]),([11,42009,153612,602208,866672,1294720,1967616],[]),([11,42009,153612,602208,866672,1294720,1990156],[65,1284,2050]),([11,42009,153612,602208,866672,1298816,1967616],[]),([11,42009,153612,602208,866672,1300864,1967616],[1286,2049]),([11,42009,153612,602208,866672,1300876,1984000],[2051]),([11,42009,153612,602208,866672,1687936,2045536],[]),([11,42009,153612,602208,866672,1687936,2047856],[]),([11,42009,153612,602208,866672,1692032,1967616],[]),([11,42009,153612,602208,866672,1700320,2033152],[]),([11,42009,153612,602208,866672,1700320,2033408],[]),([11,42009,153612,602208,866672,1950080,2045536],[]),([11,42009,153612,602208,866672,1956224,1967616],[2049]),([11,42009,153612,602208,866672,1964528,2033152],[]),([11,42009,153612,602208,883056,1163648,1967616],[]),([11,42009,153612,602208,883056,1163648,1984000],[]),([11,42009,153612,602208,883056,1300876,1967616],[2049]),([11,42009,153612,602208,919888,1163648,1990156],[65,1286,5121]),([11,42009,153612,602208,940380,1952208,1967616],[195]),([11,42009,153612,602208,997744,1163648,1967616],[]),([11,42009,153612,602208,997744,1163648,1990156],[65,1284,2050]),([11,42009,153612,602208,997744,1294720,1967616],[]),([11,42009,153612,602208,1001808,1163648,1967616],[]),([11,42009,153612,602208,1014128,1163648,1967616],[]),([11,42009,153612,602208,1014140,1163648,1973760],[1286]),([11,42009,153612,602208,1014140,1169792,1967616],[1286]),([11,42009,153612,602208,1163648,1857536,1967616],[4098]),([11,42009,153612,602208,1163648,1857872,1967616],[]),([11,42009,153612,602208,1163648,1931360,1967616],[130,4098]),([11,42009,153612,602208,1163648,1931632,1967616],[]),([11,42009,153612,602208,1163648,1964528,1967616],[]),([11,42009,153612,602208,1163648,1964528,1971712],[]),([11,42009,153612,602208,1163648,1964528,1973760],[2050]),([11,42009,153612,602208,1163648,1964528,1988096],[]),([11,42009,153612,602208,1163648,1964528,1990144],[2050,3841]),([11,42009,153612,602208,1163648,1964528,2033152],[]),([11,42009,153612,602208,1163648,1967616,2095600],[]),([11,42009,153612,602208,1165696,1427920,1967616],[]),([11,42009,153612,602208,1165696,1427920,1986048],[]),([11,42009,153612,602208,1165696,1563100,1967616],[1281]),([11,42009,153612,602208,1165696,1964528,1967616],[]),([11,42009,153612,602208,1167744,1427920,1967616],[]),([11,42009,153612,602208,1167744,1427920,1971712],[]),([11,42009,153612,602208,1167744,1432016,1967616],[]),([11,42009,153612,602208,1167744,1432016,1971712],[]),([11,42009,153612,602208,1167744,1964528,1967616],[]),([11,42009,153612,602208,1169792,1427920,1967616],[]),([11,42009,153612,602208,1169792,1964528,1967616],[2051]),([11,42009,153612,602208,1294720,1427920,1967616],[]),([11,42009,153612,602208,1294720,1427920,1990156],[65,1284]),([11,42009,153612,602208,1294720,1558992,1967616],[]),([11,42009,153612,602208,1294720,1558992,1990156],[65,1284]),([11,42009,153612,602208,1294720,1964528,1967616],[]),([11,42009,153612,602208,1294720,1967616,2095600],[]),([11,42009,153612,602208,1296768,1427920,1967616],[1281]),([11,42009,153612,602208,1298816,1427920,1967616],[]),([11,42009,153612,602208,1298816,1563088,1967616],[]),([11,42009,153612,602208,1300876,1329152,1967616],[65,4098]),([11,42009,153612,602208,1300876,1329488,1967616],[]),([11,42009,153612,602208,1300876,1427840,1967616],[193,1281]),([11,42009,153612,602208,1300876,1427920,1967616],[1281]),([11,42009,153612,602208,1300876,1427920,1971712],[1286,2049]),([11,42009,153612,602208,1300876,1427920,1984000],[1284]),([11,42009,153612,602208,1300876,1427920,1986048],[65,1284]),([11,42009,153612,602208,1300876,1427920,2033152],[1286]),([11,42009,153612,602208,1300876,1427920,2033216],[1286]),([11,42009,153612,602208,1300876,1427920,2037248],[1286,2049,3074]),([11,42009,153612,602208,1300876,1432016,1967616],[1286,2051]),([11,42009,153612,602208,1300876,1558992,1967616],[1286]),([11,42009,153612,602208,1300876,1952208,1967616],[1286]),([11,42009,153612,602208,1300876,1964528,1967616],[1286,2049]),([11,42009,153612,602208,1313104,1990156,2082688],[]),([11,42009,153612,602208,1313104,2045536,2082688],[]),([11,42009,153612,602208,1329152,1427840,1967616],[2564,2817,3074]),([11,42009,153612,602208,1329152,1427920,2082688],[2817,3074]),([11,42009,153612,602208,1329152,1967616,2088844],[]),([11,42009,153612,602208,1329152,1990156,2082688],[]),([11,42009,153612,602208,1329488,1427920,1967616],[]),([11,42009,153612,602208,1329488,1967616,2088844],[]),([11,42009,153612,602208,1329488,1990156,2082688],[]),([11,42009,153612,602208,1378640,2045536,2082688],[]),([11,42009,153612,602208,1427840,1427920,1967616],[]),([11,42009,153612,602208,1427840,1967616],[97,3617]),([11,42009,153612,602208,1427840,1967616,1990156],[4868]),([11,42009,153612,602208,1427840,1967616,2088844],[324]),([11,42009,153612,602208,1427920,1464332,2082688],[65,1284,3841]),([11,42009,153612,602208,1427920,1464668,1967616],[257]),([11,42009,153612,602208,1427920,1563020,1967616],[1281])]
noncomputable def k15 : CE := [([11,42009,153612,602208,1427920,1687936,2045536],[]),([11,42009,153612,602208,1427920,1692032,1967616],[]),([11,42009,153612,602208,1427920,1700320,2033152],[130,4098]),([11,42009,153612,602208,1427920,1825164,1967616],[1281]),([11,42009,153612,602208,1427920,1912928,2082688],[130,4098]),([11,42009,153612,602208,1427920,1967616,2088844],[]),([11,42009,153612,602208,1427920,1971712,2082688],[]),([11,42009,153612,602208,1427920,1971712,2086784],[]),([11,42009,153612,602208,1427920,1984000,2082688],[]),([11,42009,153612,602208,1427920,1986048,2082688],[]),([11,42009,153612,602208,1427920,1986048,2084736],[]),([11,42009,153612,602208,1427920,1990156,2082688],[]),([11,42009,153612,602208,1427920,2033152,2082688],[]),([11,42009,153612,602208,1427920,2033216,2082688],[]),([11,42009,153612,602208,1427920,2045536,2082688],[]),([11,42009,153612,602208,1427920,2045536,2088844],[]),([11,42009,153612,602208,1427920,2063980,2082688],[3074]),([11,42009,153612,602208,1432016,1967616,2086784],[3588]),([11,42009,153612,602208,1687936,1952208,2045536],[]),([11,42009,153612,602208,1692032,1956304,1967616],[]),([11,42009,153612,602208,1700320,1964528,2033152],[130]),([11,42009,153612,602208,1956224,1967616],[97,2081,3617,4129]),([11,42009,153612,602208,1956224,1967616,1990156],[2051,4098,4868,5378]),([11,42009,153612,602208,1964528,1967616,2088844],[2049]),([11,42009,153612,602208,1964528,1990156,2082688],[4098]),([11,42009,153612,602208,1964528,2045536,2082688],[130]),([11,42009,153612,604256,866672,1169792,1967616],[2049]),([11,42009,153612,618592,866672,1300876,1967616],[]),([11,42009,153612,618592,883056,1300876,1967616],[2049]),([11,42009,153612,618592,1300876,1427920,1967616],[1283]),([11,42009,153612,618592,1427920,1967616,2082688],[]),([11,42009,153612,620640,1300876,1427920,1967616],[67,1283,2819]),([11,42009,153612,620640,1427920,1967616,2082688],[5763]),([11,42009,153612,733280,866672,1294720,1967616],[]),([11,42009,153612,733280,997744,1294720,1967616],[]),([11,42009,153612,733280,1300876,1427920,1967616],[1281]),([11,42009,153612,749664,1427920,1967616,2082688],[]),([11,42009,153612,751724,1300876,1964528,1967616],[65,1281,2049,2817]),([11,42009,153612,751724,1427920,2045536,2082688],[]),([11,42009,153612,751724,1964528,1967616,2082688],[1283,4098,5121]),([11,42009,153612,866672,1700320,2033152],[97,162]),([11,42009,153612,866672,1700320,2045536,2082688],[]),([11,42009,153612,866672,1950080,2045536],[99,162,290,3106]),([11,42009,153612,866672,1964528,2045536,2082688],[130]),([11,42009,153612,1700320,1964528,2033152],[97]),([11,42009,153612,1700320,1964528,2045536,2082688],[]),([11,42009,153612,1964528,2045536,2082688],[97,226,2882,4290]),([11,42009,219148,264529,1700320,2033152],[97,228,1316,3622]),([11,42009,219148,330064,602208,1163648,2033152],[]),([11,42009,219148,330064,602208,1163648,2035536],[]),([11,42009,219148,602208,866672,1163648,2033152],[]),([11,42009,219212,602208,1163648,1427920,2033216],[]),([11,42009,264529,751724,1300876,2045536,2082688],[]),([11,42009,264529,751724,1700320,1990156,2082688],[3588]),([11,42009,268624,416092,602208,1163648,1971712],[]),([11,42009,268624,602208,751724,1163648,1971712],[]),([11,42009,330064,481628,602208,1163648,2035536],[]),([11,42009,395264,395600,602208,1163648,1990156],[1284,2818,4868]),([11,42009,395264,602208,1163648,1990156],[162,1316,2050,2114,2850,3588,3620]),([11,42009,395600,395600,602208,1163648,1990156],[1284,2818]),([11,42009,395600,416092,602208,1163648,1970000],[]),([11,42009,395600,416092,602208,1163648,1990156],[129,1796,2818]),([11,42009,395600,416092,602208,1163648,1990492],[]),([11,42009,395600,602208,733280,1163648,1990156],[130,194,2050,3074]),([11,42009,395600,602208,751724,1163648,1990156],[195,2050]),([11,42009,395600,602208,997744,1163648,1990156],[197,3074]),([11,42009,395600,602208,1163648,1700320,1990156],[]),([11,42009,395600,602208,1163648,1990156],[162,1316,2114,2850,3620]),([11,42009,395600,602208,1163648,1990156,1990156],[3588]),([11,42009,395600,602208,1163648,1990156,1990492],[2050,4868]),([11,42009,395600,602208,1163648,1990156,2063980],[325,2050,3588,5762]),([11,42009,395600,602208,1163648,1990492],[]),([11,42009,395600,602208,1294720,1990156],[1316,2114,3620]),([11,42009,395600,602208,1558992,1990156],[1316,3620]),([11,42009,399696,602208,1163648,1990156],[1316,2850,3620]),([11,42009,399696,602208,1163648,1990156,2045536],[322,2051]),([11,42009,416092,602208,1163648,1970000],[]),([11,42009,481628,602208,1163648,2035536],[]),([11,42009,602208,677900,866672,1163648,2045536],[66]),([11,42009,602208,677900,866672,1163648,2047856],[]),([11,42009,602208,677900,1163648,1427920,2045536],[]),([11,42009,602208,733280,866672,1163648,1990156],[66,2050,2818]),([11,42009,602208,733280,997744,1163648,1990156],[66,130,2050,2818]),([11,42009,602208,733280,1163648,1427920,1990156],[66,2050,3842]),([11,42009,602208,751724,866672,1163648,1973760],[66,2050,2818]),([11,42009,602208,751724,1427920,1990156,2082688],[3588]),([11,42009,602208,866672,940044,1163648,2047856],[130]),([11,42009,602208,866672,997744,1163648,1990156],[130]),([11,42009,602208,866672,1294720,1990156],[3620,3874]),([11,42009,602208,866672,1300876,1990156,2082688],[3588,3842]),([11,42009,602208,997744,1163648,1990156],[98,165,3620,3874]),([11,42009,602208,1014140,1163648,1990156,2047856],[]),([11,42009,602208,1294720,1427920,1990156],[3620]),([11,42009,602208,1294720,1558992,1990156],[228,3620]),([11,42009,602208,1300876,1427920,1986048],[161,3622]),([11,42009,602208,1300876,1427920,1990156,2082688],[3588]),([11,42009,602208,1300876,1427920,1990156,2084816],[]),([11,42072,153612,280912,602208,1163648,1967616],[]),([11,42072,153612,395600,602208,1163648,1967616],[]),([11,44056,153612,330064,602208,1163648,1967616],[]),([11,44056,153612,602208,788816,1163648,1967616],[]),([11,46104,153612,268624,602208,1163648,1967616],[]),([11,46104,153612,268624,602208,1163648,1971712],[]),([11,46104,153612,268624,602208,1163648,1974096],[]),([11,46104,153612,268624,602208,1163648,2012696],[4]),([11,46104,153612,268624,636024,1163648,1967616],[3588]),([11,46104,153612,268624,751724,1163648,1967616],[]),([11,46104,153612,268624,866672,1163648,1967616],[]),([11,46104,153612,268632,602208,1163648,1967616],[]),([11,46104,153612,276816,602208,1163648,1967616],[]),([11,46104,153612,280912,602208,1163648,1967616],[]),([11,46104,153612,310616,602208,1163648,1967616],[]),([11,46104,153612,310616,602208,1163648,1971712],[]),([11,46104,153612,310616,602208,1163648,2012696],[1284]),([11,46104,153612,310616,602208,1163648,2015064],[]),([11,46104,153612,310616,602208,1167744,1967616],[]),([11,46104,153612,330064,602208,1163648,1967616],[]),([11,46104,153612,395600,602208,1163648,1967616],[]),([11,46104,153612,602208,866672,1163648,1967616],[]),([11,46104,153612,602208,866672,1163648,1971712],[]),([11,46104,153612,602208,866672,1163648,2012696],[4]),([11,46104,153612,602208,866672,1167744,1967616],[]),([11,46104,153612,602208,866672,1176984,1967616],[]),([11,46104,153612,602208,900472,1163648,1967616],[]),([11,46104,153612,602208,1163648,1313104,1967616],[]),([11,46104,153612,602208,1163648,1427920,1967616],[]),([11,46104,153612,602208,1163648,1427920,1971712],[]),([11,46104,153612,602208,1163648,1427920,2012696],[5]),([11,46104,153612,602208,1163648,1432016,1967616],[]),([11,46104,153612,602208,1163648,1441240,1967616],[]),([11,46104,153612,602208,1163648,1964528,1967616],[]),([11,46104,153612,602208,1167744,1427920,1967616],[]),([11,46104,153612,602208,1167744,1432016,1967616],[]),([11,46104,153612,602208,1300876,1427920,1967616],[1281]),([11,46104,153612,602208,1427920,1967616,2082688],[]),([11,46104,153612,751724,866672,1163648,1967616],[1283]),([11,46104,153612,866672,1163648,1967616,2045536],[3586]),([11,46104,195612,310616,602208,1163648,1967616],[4,4868]),([11,46104,195612,602208,866672,1163648,1967616],[6]),([11,46104,195612,602208,1163648,1427920,1967616],[7]),([11,46104,310616,458076,602208,1163648,1967616],[]),([11,46104,310616,602208,751724,1163648,1967616],[]),([11,46104,602208,751724,866672,1163648,1967616],[]),([11,46104,602208,751724,1163648,1427920,1967616],[]),([11,46104,602208,866672,1014140,1163648,1967616],[]),([11,48152,153612,602208,866672,1163648,1967616],[]),([11,48152,153612,602208,866672,1163648,1973760],[]),([11,48152,153612,602208,866672,1163648,2014744],[4]),([11,48152,153612,602208,866672,1169792,1967616],[]),([11,48152,153612,602208,866672,1179032,1967616],[])]
noncomputable def k16 : CE := [([11,48152,153612,602208,1163648,1964528,1967616],[]),([11,48152,153612,604256,866672,1163648,1967616],[]),([11,48152,153612,751724,866672,1163648,1967616],[1283]),([11,48152,153612,866672,1163648,1967616,2045536],[3586]),([11,48152,602208,751724,866672,1163648,1967616],[]),([11,48152,751724,866672,1163648,1967616],[103,3619]),([11,61440,153612,325968,602208,1163648,1967616],[1281]),([11,61440,153612,602208,866672,1163648,1967616],[1286,4868]),([11,61440,153612,602208,1163648,1964528,1967616],[1281]),([11,62488,153612,285008,602208,1163648,1967616],[]),([11,62488,153612,327000,602208,1163648,1967616],[]),([11,62488,153612,602208,866672,1163648,1967616],[]),([11,62488,153612,602208,1163648,1964528,1967616],[]),([11,63504,153612,602208,866672,1163648,1967616],[2050]),([11,63504,153612,602208,1163648,1964528,1967616],[2050]),([11,64536,153612,602208,866672,1163648,1967616],[2050]),([11,64536,153612,602208,1163648,1964528,1967616],[2050]),([11,65536,107544,153612,330064,1700320,1967616],[1793]),([11,65536,107544,153612,372056,1700320,1967616],[1793]),([11,65536,107544,153612,866672,1700320,1967616],[1793]),([11,65536,107544,153612,1700320,1964528,1967616],[1793]),([11,65536,153612,195612,330064,1700320,1967616],[1281]),([11,65536,153612,195612,866672,1700320,1967616],[1281]),([11,65536,153612,195612,1700320,1964528,1967616],[1281,2817]),([11,65536,153612,330064,372056,1700320,1967616],[1281]),([11,65536,153612,602208,1427920,2008600,2082688],[4,1284]),([11,65600,153612,602208,1427920,2008600,2082688],[4,1284]),([11,69632,195612,602208,1300876,1427920,1967616],[1,1281,1793,2561,3590,4870]),([11,73728,107544,153612,866672,1163648,1967616],[1795,3586,4866]),([11,73728,107800,153612,866672,1163648,1967616],[1795,4866]),([11,77824,153612,195612,866672,1163648,1967616],[1287,4866]),([11,107544,153612,330064,602208,1163648,1967616],[]),([11,107544,153612,330064,602208,1163648,2033152],[]),([11,107544,153612,330064,602208,1163648,2035536],[]),([11,107544,153612,330064,602208,1163648,2074136],[4]),([11,107544,153612,330064,602208,1172888,1967616],[]),([11,107544,153612,330064,602208,1427920,1967616],[]),([11,107544,153612,330064,602208,1700320,1967616],[194]),([11,107544,153612,330064,1700320,1967616],[97,228,1345,2081,3617]),([11,107544,153612,338256,602208,1163648,1967616],[]),([11,107544,153612,372056,602208,1163648,1967616],[]),([11,107544,153612,372056,602208,1163648,2033152],[]),([11,107544,153612,372056,602208,1163648,2074136],[1284]),([11,107544,153612,372056,602208,1163648,2076504],[]),([11,107544,153612,372056,602208,1700320,1967616],[]),([11,107544,153612,372056,1700320,1967616],[1345,2081]),([11,107544,153612,395600,602208,1163648,1967616],[5124]),([11,107544,153612,602208,866672,1163648,1967616],[]),([11,107544,153612,602208,866672,1163648,2033152],[]),([11,107544,153612,602208,866672,1163648,2074136],[4]),([11,107544,153612,602208,866672,1172888,1967616],[]),([11,107544,153612,602208,866672,1700320,1967616],[]),([11,107544,153612,602208,866672,1964528,1967616],[197]),([11,107544,153612,602208,900472,1163648,1967616],[]),([11,107544,153612,602208,1163648,1964528,1967616],[]),([11,107544,153612,602208,1300876,1427920,1967616],[1281]),([11,107544,153612,602208,1427920,1700320,1967616],[130,4098]),([11,107544,153612,602208,1700320,1964528,1967616],[130]),([11,107544,153612,866672,1700320,1967616],[97,165,228,1345,3617]),([11,107544,153612,1700320,1964528,1967616],[97,164,228,1345,3617,4129]),([11,107608,153612,330064,602208,1163648,1967616],[]),([11,107608,153612,602208,1163648,1427920,1967616],[]),([11,107608,153612,602208,1163648,1427920,2033216],[]),([11,107608,153612,602208,1163648,1427920,2074200],[]),([11,107608,153612,602208,1300876,1427920,1967616],[1281]),([11,107608,153612,636024,1163648,1427920,1967616],[]),([11,107608,153612,1163648,1427920,1700320,1967616],[]),([11,107608,153612,1163648,1427920,1964528,1967616],[196]),([11,111640,153612,334160,602208,1163648,1967616],[]),([11,111640,153612,376152,602208,1163648,1967616],[]),([11,111640,153612,602208,866672,1163648,1967616],[]),([11,111640,153612,602208,1163648,1427920,1967616],[]),([11,111640,153612,602208,1300876,1427920,1967616],[1281]),([11,111704,153612,602208,1163648,1427920,1967616],[]),([11,113944,153612,602208,866672,1163648,1967616],[]),([11,153612,173080,330064,602208,1163648,1967616],[]),([11,153612,173080,437592,602208,1163648,1967616],[]),([11,153612,173080,437592,602208,1294720,1967616],[4868]),([11,153612,173080,602208,866672,1163648,1967616],[]),([11,153612,173080,602208,866672,1294720,1967616],[4868]),([11,153612,173080,602208,866672,1303960,1967616],[]),([11,153612,173080,602208,997744,1163648,1967616],[4868]),([11,153612,173080,602208,1031544,1163648,1967616],[]),([11,153612,173080,602208,1163648,1964528,1967616],[]),([11,153612,173080,602208,1294720,1427920,1967616],[4868]),([11,153612,173080,602208,1294720,1558992,1967616],[4868]),([11,153612,173080,602208,1300876,1427920,1967616],[1281]),([11,153612,177176,441688,602208,1163648,1967616],[]),([11,153612,177176,602208,866672,1163648,1967616],[]),([11,153612,177176,602208,1163648,1427920,1967616],[]),([11,153612,177176,866672,1163648,1967616,2045536],[3842]),([11,153612,179224,602208,866672,1163648,1967616],[1799]),([11,153612,195612,285008,602208,1163648,1967616],[]),([11,153612,195612,325968,602208,1163648,1967616],[2567,3590]),([11,153612,195612,602208,866672,1163648,1967616],[1795]),([11,153612,195612,602208,866672,1163648,1971712],[1797]),([11,153612,195612,602208,866672,1163648,1973760],[1797,2566]),([11,153612,195612,602208,866672,1163648,1979904],[1797,2050]),([11,153612,195612,602208,866672,1163648,1981968],[1797]),([11,153612,195612,602208,866672,1163648,1984000],[1799]),([11,153612,195612,602208,866672,1163648,2016768],[1799,3588]),([11,153612,195612,602208,866672,1163648,2033152],[1799]),([11,153612,195612,602208,866672,1163648,2033408],[1799]),([11,153612,195612,602208,883056,1163648,1967616],[1799]),([11,153612,195612,602208,915824,1163648,1967616],[1799,3590]),([11,153612,195612,602208,997744,1163648,1967616],[1799,4868]),([11,153612,195612,602208,998768,1163648,1967616],[1799]),([11,153612,195612,602208,1163648,1837392,1967616],[]),([11,153612,195612,602208,1163648,1915248,1967616],[1799]),([11,153612,195612,602208,1163648,1964528,1967616],[1799,2566]),([11,153612,195612,602208,1165696,1427920,1967616],[2561,3585]),([11,153612,195612,602208,1167744,1427920,1967616],[2561]),([11,153612,195612,602208,1167744,1432016,1967616],[2566]),([11,153612,195612,602208,1175936,1427920,1967616],[1795,2566]),([11,153612,195612,602208,1175936,1440208,1967616],[1795,2566]),([11,153612,195612,602208,1294720,1427920,1967616],[2561,4868]),([11,153612,195612,602208,1294720,1558992,1967616],[2566,4868]),([11,153612,195612,602208,1295744,1427920,1967616],[]),([11,153612,195612,602208,1295744,1560016,1967616],[]),([11,153612,195612,602208,1300876,1427920,1967616],[1,1281,2561]),([11,153612,195612,602208,1300876,1964528,1967616],[1,1286,1793,2566]),([11,153612,195612,602208,1425792,1427920,1967616],[2561]),([11,153612,195612,602208,1427920,1687936,1967616],[3585]),([11,153612,195612,602208,1427920,1967616,2082688],[]),([11,153612,195612,602208,1427920,1967616,2088844],[]),([11,153612,195612,602208,1427920,1990156,2082688],[]),([11,153612,195612,602208,1427920,2031132,2082688],[65,4485]),([11,153612,195612,602208,1427920,2045536,2082688],[]),([11,153612,195612,602208,1687936,1952208,1967616],[2566]),([11,153612,195612,602208,1964528,1967616,2082688],[1795]),([11,153612,285008,327000,602208,1163648,1967616],[]),([11,153612,602208,751724,1427920,2008600,2082688],[131,3588]),([11,153612,602208,1163648,1964528,1967616,2031132],[1283,1793,3842]),([11,153612,602208,1163648,1964528,2008600,2045536],[69,2821,5125]),([11,153612,602208,1163648,1964528,2008600,2095072],[]),([11,153612,602208,1300876,1427920,2008600,2045536],[1281,2818,3590]),([11,153612,602208,1300876,1427920,2008600,2082688],[134,3588]),([11,153612,602208,1425792,1427920,2008600,2082688],[132]),([11,153612,602208,1427920,1427920,2008600,2082688],[132]),([11,153612,602208,1427920,1563100,2008600,2082688],[198]),([11,153612,602208,1427920,1700320,2008600,2082688],[196,3076]),([11,153612,602208,1427920,1964528,2008600,2082688],[132,196,3076,4481]),([11,153612,602208,1427920,1990156,2031132,2082688],[]),([11,153612,602208,1427920,2008600,2082688],[33,101,164,2116]),([11,153612,602208,1427920,2008600,2082688,2082688],[]),([11,153612,602208,1427920,2008600,2082688,2084816],[324]),([11,153612,602208,1427920,2008600,2082688,2088844],[324,5252]),([11,153612,602208,1427920,2008600,2082688,2093016],[]),([11,153612,602208,1427920,2031132,2082688],[33,101,164,1316,3237]),([12,0,40984,153612,264529,602208,1163648,1967616],[])]
noncomputable def k17 : CE := [([12,0,42008,153612,264528,602208,1163648,1967616],[]),([12,0,42008,153612,264529,602208,1163648,1967616],[]),([12,0,42008,153612,602208,866672,1163648,1967616],[]),([12,0,42009,65536,153612,264529,1700320,1967616],[2052,3073,3588]),([12,0,42009,77920,153612,866672,1163648,1967616],[]),([12,0,42009,153612,264529,602208,1163648,1967616],[2564]),([12,0,42009,153612,264529,602208,1163648,1971712],[2564]),([12,0,42009,153612,264529,602208,1163648,2033152],[2564]),([12,0,42009,153612,268624,602208,1163648,1967616],[]),([12,0,42009,153612,330064,602208,1163648,1967616],[]),([12,0,42009,153612,342384,602208,1163648,1967616],[]),([12,0,42009,153612,371184,602208,1163648,1967616],[]),([12,0,42009,153612,395600,602208,1163648,1967616],[]),([12,0,42009,153612,602208,800880,1163648,1967616],[]),([12,0,42009,153612,602208,801136,1163648,1967616],[]),([12,0,42009,153612,602208,866672,1163648,1967616],[]),([12,0,42009,153612,602208,1163648,1964528,1967616],[]),([12,0,42009,153612,602208,1300876,1427920,1967616],[2049]),([12,0,42009,153612,602208,1427920,1832876,1967616],[]),([12,0,153612,195612,602208,866672,1163648,1967616],[2819]),([12,8,40984,153612,264529,602208,1163648,1967616],[]),([12,8,42008,153612,264529,602208,1163648,1967616],[]),([12,8,153612,264529,602208,1163648,1877528,1967616],[1286,4870]),([12,8,153612,264529,602208,1163648,1967616,2008600],[1286,6406]),([12,12,42009,153612,602208,866672,1163648,1967616],[2562]),([12,12,42009,153612,602208,1163648,1964528,1967616],[2562]),([12,16,42009,153612,264529,602208,1163648,1967616],[2564]),([12,2048,42009,153612,264272,602208,1163648,1967616],[1284,1796,2564,3588,4868,6404]),([12,2048,42009,153612,264528,602208,1163648,1967616],[1284,1796,2564,3589,4868,6404]),([12,2048,42009,153612,371184,602208,1163648,1967616],[3586]),([12,2048,42009,153612,602208,862576,1163648,1967616],[1793,2561,3585,4865]),([12,2048,42009,153612,602208,866672,1163648,1967616],[2562]),([12,2052,153612,264529,602208,1163648,1967616,2008600],[1286,4868,6406]),([12,2060,42009,153612,264529,602208,1163648,1967616],[1284]),([12,2076,42009,65536,153612,264529,1700320,1967616],[1284]),([12,2076,42009,153612,264529,602208,1163648,1967616],[1284]),([12,2076,42009,153612,602208,866672,1163648,1967616],[]),([12,2076,42009,153612,602208,1163648,1964528,1967616],[]),([12,2076,42009,153612,602208,1427920,1967616,2082688],[]),([12,2076,44060,153612,264529,602208,1163648,1967616],[1284]),([12,2076,153612,195612,264529,602208,1163648,1967616],[1796]),([12,2076,153612,264529,602208,1163648,1967616,2008600],[6406]),([12,2076,153612,264529,602208,1163648,2008600,2045536],[2565,3074,4868]),([12,2076,153612,264529,602208,1163648,2008600,2095072],[2565,3588,4868]),([12,2128,42009,153612,602208,1163648,1427920,1967616],[4866]),([12,2128,42009,153612,602208,1427920,1967616,2082688],[3585]),([12,2384,42009,153612,264528,602208,1163648,1967616],[2564]),([12,2384,42009,153612,395600,602208,1163648,1967616],[]),([12,2384,42009,153612,602208,788816,1163648,1967616],[3585]),([12,4096,40984,153612,264529,602208,1163648,1967616],[1284]),([12,4096,42000,153612,264529,602208,1163648,1967616],[1284,1793,2561,3585,4865,6401]),([12,4096,42008,153612,264529,602208,1163648,1967616],[1284]),([12,4096,42009,77920,153612,866672,1163648,1967616],[]),([12,4096,42009,115072,153612,602208,1427920,1967616],[1794,2562,3586,4866,6402]),([12,4096,42009,149516,264529,598112,1163648,1967616],[]),([12,4096,42009,149516,264529,602208,1163648,1967616],[1285,4869,6405]),([12,4096,42009,149516,264529,602208,1163648,1971712],[1285,2562,3589,4869,6405]),([12,4096,42009,149516,264529,602208,1167744,1967616],[1285,1796,2562,3589,4869,6405]),([12,4096,42009,149516,268624,602208,1163648,1967616],[4866,6402]),([12,4096,42009,149516,602208,866672,1163648,1967616],[4866,6402]),([12,4096,42009,149516,602208,1163648,1427920,1967616],[1794,3586,6402]),([12,4096,42009,153612,264529,602208,1163648,1967616],[1284,4868]),([12,4096,42009,153612,264529,602208,1163648,1971712],[1284]),([12,4096,42009,153612,268368,602208,1163648,1967616],[1284]),([12,4096,42009,153612,268624,598048,1163648,1967616],[1284,1793,2561,4865,6401]),([12,4096,42009,153612,268624,598112,1163648,1967616],[1284,1793,2561,4865,6401]),([12,4096,42009,153612,268624,602208,1163392,1967616],[]),([12,4096,42009,153612,268624,602208,1163648,1967616],[]),([12,4096,42009,153612,342384,602208,1163648,1967616],[]),([12,4096,42009,153612,371184,602208,1163648,1967616],[]),([12,4096,42009,153612,379344,602208,1163648,1967616],[1794,2562,3586,4866,6402]),([12,4096,42009,153612,598112,862576,1163648,1967616],[2561,3585,4865,6401]),([12,4096,42009,153612,598112,866672,1163648,1967616],[1793,3585,4865,6401]),([12,4096,42009,153612,598112,1163648,1427920,1967616],[2562,3585,4865,6401]),([12,4096,42009,153612,602208,800880,1163648,1967616],[]),([12,4096,42009,153612,602208,801136,1163648,1967616],[]),([12,4096,42009,153612,602208,862576,1163648,1967616],[1793,2561,4865]),([12,4096,42009,153612,602208,866672,1163648,1967616],[]),([12,4096,42009,153612,602208,1147264,1427920,1967616],[1795,2563,3585,4867,6403]),([12,4096,42009,153612,602208,1163648,1362320,1967616],[1794,2562,4866,6402]),([12,4096,42009,153612,602208,1163648,1362384,1967616],[1794,2562,4866,6402]),([12,4096,42009,153612,602208,1163648,1411536,1967616],[1795,2563,3587,4866,6402]),([12,4096,42009,153612,602208,1163648,1427920,1967616],[1794,2562,4866,6402]),([12,4096,42009,153612,602208,1427920,1832876,1967616],[]),([12,4096,42009,153612,602208,1432016,1828524,1967616],[1793,2561,3585]),([12,4096,42009,153612,866672,1163648,1828524,1967616],[1795,2563,3586,4866,6402]),([12,4096,42009,153612,866672,1163648,1832684,1967616],[1794,2562,3586,4866,6402]),([12,4096,42009,751724,866672,1163648,1494940,1967616],[3585,4867,6403]),([12,4108,42009,153612,602208,1163648,1427920,1967616],[1794]),([12,4132,153612,602208,1163648,1427920,1967616,2008600],[2561,4869]),([12,6144,42009,77920,153612,866672,1163648,1967616],[]),([12,6144,42009,129532,751724,866672,1163648,1967616],[4866,6402]),([12,6144,42009,147468,602208,866672,1163648,1967616],[6402]),([12,6144,42009,149516,602208,866672,1163648,1967616],[4866,6402]),([12,6144,42009,153612,264464,602208,1163648,1967616],[1285,1797,3589,4869,6405]),([12,6144,42009,153612,342384,602208,1163648,1967616],[]),([12,6144,42009,153612,598112,866672,1163648,1967616],[1793,2562,3585,4865,6401]),([12,6144,42009,153612,602208,800880,1163648,1967616],[2562]),([12,6144,42009,153612,602208,801136,1163648,1967616],[2562]),([12,6144,42009,153612,602208,860528,1163648,1967616],[2561,4865,6401]),([12,6144,42009,153612,602208,866672,1163648,1967616],[2562]),([12,6144,42009,153612,602208,915964,1163648,1967616],[2562]),([12,6144,42009,153612,866672,1163648,1832684,1967616],[1794,2562,3586,4866,6402]),([12,6144,42009,602208,1014140,1163648,1230476,1967616],[6403]),([12,6144,42009,751724,866672,933500,1163648,1967616],[4865,6402]),([12,6144,42009,751724,866672,1163648,1230476,1967616],[3587,4867,6402]),([12,6144,42009,751724,866672,1163648,1345424,1967616],[1287,3587,4867,6403]),([12,6144,42009,751724,866672,1163648,1494940,1967616],[3585,4867,6402]),([12,6144,42009,751724,866672,1163648,1943536,1967616],[3585,6403]),([12,6144,42009,751724,866672,1163648,1967616,2091004],[3587,4867]),([12,6148,153612,264529,602208,1163648,1967616,2008600],[1286,4868,6406]),([12,6156,42009,147456,264529,602208,1163648,1967616],[6405]),([12,6156,42009,153612,264529,602208,1163648,1967616],[1284]),([12,6156,42009,153612,264529,602208,1163648,1984000],[1284,1794]),([12,6156,42009,153612,264529,602208,1294720,1967616],[1284,1796,6404]),([12,6156,42009,153612,602208,866672,1163648,1967616],[2562]),([12,6156,42009,153612,602208,1163648,1427920,1967616],[1794]),([12,6156,42009,153612,602208,1427920,1967616,2082688],[1793]),([12,6156,42009,161916,264529,602208,1163648,1967616],[]),([12,6156,42009,264529,602208,751724,1163648,1967616],[1284]),([12,6156,48156,153612,264529,602208,1163648,1967616],[1284,1796]),([12,6156,153612,195612,264529,602208,1163648,1967616],[1284,1796]),([12,6156,153612,264529,602208,1163648,1967616,2008600],[1286,6406]),([12,6156,153612,264529,602208,1163648,2008600,2082688],[1285,3588,4869]),([12,6244,153612,264529,602208,1163648,1967616,2008600],[4868]),([12,6244,153612,264529,602208,1163648,1967616,2031132],[1286]),([12,6244,153612,264529,602208,1163648,1973860,2008600],[4868]),([12,6244,153612,264529,602208,1163648,2008600,2045536],[2565,6404]),([12,6244,153612,264529,602208,1163648,2008600,2082688],[3588,6405]),([12,6244,153612,602208,866672,1163648,1967616,2008600],[1795,4868]),([12,6244,153612,602208,1163648,1427920,1967616,2008600],[4869]),([12,6480,42009,153612,268624,602208,1163648,1967616],[]),([12,10364,42009,153612,264529,602208,1163648,1967616],[]),([12,10364,42009,153612,264529,602208,1163648,1971712],[]),([12,14364,153612,195612,264529,602208,1163648,1967616],[1796]),([12,14444,42009,153612,264529,602208,1163648,1967616],[]),([12,14460,42008,153612,264529,602208,1163648,1967616],[]),([12,14460,42009,65536,153612,264529,1700320,1967616],[2052]),([12,14460,42009,147456,264529,602208,1163648,1990156],[4100,5380]),([12,14460,42009,153612,264529,602208,1163648,1967616],[]),([12,14460,42009,153612,264529,602208,1163648,1971712],[]),([12,14460,42009,153612,264529,602208,1163648,1984000],[]),([12,14460,42009,153612,264529,602208,1163648,2033152],[]),([12,14460,42009,153612,264529,618592,1163648,1967616],[]),([12,14460,42009,153612,264529,733280,1163648,1967616],[6916]),([12,14460,42009,153612,264529,749664,1163648,1967616],[6916]),([12,14460,42009,153612,264529,1163648,1650784,1967616],[]),([12,14460,42009,153612,264529,1700320,2045536,2082688],[4866]),([12,14460,42009,153612,268624,602208,1163648,1967616],[]),([12,14460,42009,153612,276848,602208,1163648,1967616],[])]
noncomputable def k18 : CE := [([12,14460,42009,153612,280912,602208,1163648,1967616],[]),([12,14460,42009,153612,330064,602208,1163648,1967616],[]),([12,14460,42009,153612,395600,602208,1163648,1967616],[]),([12,14460,42009,153612,411984,602208,1163648,1967616],[]),([12,14460,42009,153612,602208,788816,1163648,1967616],[]),([12,14460,42009,153612,602208,854352,1163648,1967616],[]),([12,14460,42009,153612,602208,866672,1163648,1967616],[]),([12,14460,42009,153612,602208,1163648,1313104,1967616],[]),([12,14460,42009,153612,602208,1163648,1427920,1967616],[]),([12,14460,42009,153612,602208,1163648,1964528,1967616],[]),([12,14460,42009,153612,602208,1300876,1427920,1967616],[1793,2052]),([12,14460,42009,153612,602208,1425792,1427920,1967616],[]),([12,14460,42009,153612,602208,1427920,1967616,2082688],[]),([12,14460,42009,153612,602208,1427920,1967616,2088844],[1793]),([12,14460,42009,153612,602208,1427920,1982076,2082688],[]),([12,14460,42009,153612,602208,1427920,1990156,2082688],[]),([12,14460,42009,153612,602208,1427920,2045536,2082688],[]),([12,14460,42009,153612,602208,1964528,1967616,2082688],[5124]),([12,14460,42009,153612,751724,866672,1163648,1967616],[]),([12,14460,42009,153612,866672,1163648,1967616,2045536],[]),([12,14460,42009,153612,866672,1163648,2045536,2082688],[3586]),([12,14460,153612,195612,602208,866672,1163648,1967616],[]),([12,14460,153612,195612,602208,1163648,1427920,1967616],[3844]),([12,14460,153612,195612,602208,1427920,1967616,2082688],[]),([12,14460,153612,602208,1163648,1427920,1967616,2008600],[]),([12,14460,153612,602208,1163648,1427920,2008600,2082688],[]),([12,14460,153612,602208,1427920,2008600,2082688],[1828,1956,3140,3620,3748]),([12,20480,42009,133132,264529,602208,1163648,1967616],[1284,6404]),([12,20480,42009,137228,264529,602208,1163648,1967616],[1284,3588,6404]),([12,20480,42009,153612,264529,598112,1163648,1967616],[2561,3589,4865,6401]),([12,20480,42009,153612,264529,602208,1163648,1967616],[1284,3589,4868]),([12,20480,153612,264529,437788,602208,1163648,1967616],[1284,2564,3589,4868,6404]),([12,20492,42009,153612,395600,602208,1163648,1967616],[]),([12,22532,131072,173080,264529,602208,1163648,1967616],[1284,3842,6406]),([12,22532,131072,264529,602208,1163648,1967616,2008600],[1284,2818,4870]),([12,22532,131080,264529,602208,1163648,1967616,2008600],[1286,4868]),([12,22532,153612,173080,264529,602208,1163648,1967616],[1284,1796,6404]),([12,22532,153612,264529,602208,1163648,1967616,2008600],[1286,4868,6404]),([12,22532,153612,264529,602208,1163648,1967616,2031132],[1284,6404]),([12,22532,153612,264529,602208,1163648,1990148,2008600],[1284,4868]),([12,22532,153612,264529,602208,1163648,2008600,2045536],[1284,2565,2818,3074,4868,6404]),([12,22532,153612,264529,602208,1163648,2008600,2056164],[1284,6404]),([12,22532,153612,602208,866672,1163648,1967616,2008600],[1281,1795,2050,4868,5378,6404]),([12,22532,219628,264529,602208,1163648,1967616,2008600],[4868,6406]),([12,22532,264529,602208,751724,1163648,1967616,2008600],[2050,4868,5378,6406]),([12,22540,40984,153612,264529,602208,1163648,1967616],[1284]),([12,22540,42008,153612,264529,602208,1163648,1967616],[1284]),([12,22540,42009,65536,153612,264529,1700320,1967616],[1284]),([12,22540,42009,77920,153612,866672,1163648,1967616],[]),([12,22540,42009,77920,264529,751724,1163648,1967616],[1284]),([12,22540,42009,129532,264529,602208,1294720,1967616],[]),([12,22540,42009,129532,395600,602208,1163648,1967616],[]),([12,22540,42009,129532,602208,1300876,1427920,1967616],[]),([12,22540,42009,131072,264529,602208,1163648,1836544],[6404]),([12,22540,42009,131072,264529,602208,1163648,1967616],[4098,6404]),([12,22540,42009,131072,264529,602208,1163648,1990156],[1284,4098,6404]),([12,22540,42009,131072,264529,602208,1294720,1967616],[1796,6404]),([12,22540,42009,131072,395600,602208,1163648,1967616],[4098]),([12,22540,42009,131072,602208,866672,1163648,1967616],[3074]),([12,22540,42009,135168,264529,602208,1163648,1967616],[4098,6404]),([12,22540,42009,153612,264528,602208,1163648,1967616],[1284,1796]),([12,22540,42009,153612,264529,602208,1163648,1967616],[1284]),([12,22540,42009,153612,264529,602208,1163648,1971712],[1284]),([12,22540,42009,153612,264529,602208,1163648,2033152],[1284]),([12,22540,42009,153612,264529,602208,1167744,1967616],[1284,1796]),([12,22540,42009,153612,264529,602208,1294720,1967616],[1284,1796]),([12,22540,42009,153612,264529,602208,1687936,1967616],[1284,1798]),([12,22540,42009,153612,268624,602208,1163648,1967616],[1284]),([12,22540,42009,153612,330064,602208,1163648,1967616],[]),([12,22540,42009,153612,342384,602208,1163648,1967616],[]),([12,22540,42009,153612,395600,602208,1163648,1967616],[]),([12,22540,42009,153612,602208,788816,1163648,1967616],[1286,1793]),([12,22540,42009,153612,602208,866672,1163648,1967616],[2562,3074]),([12,22540,42009,153612,602208,1163648,1964528,1967616],[2562,3074]),([12,22540,42009,153612,602208,1169804,1427920,1967616],[]),([12,22540,42009,153612,602208,1300876,1427920,1967616],[]),([12,22540,42009,153612,602208,1427920,1967616,2082688],[1793]),([12,22540,42009,219148,264529,602208,1163648,1967616],[1286,1793]),([12,22540,42009,227436,264529,602208,1163648,1967616],[1286]),([12,22540,42009,260604,264529,602208,1163648,1967616],[]),([12,22540,42009,260604,602208,866672,1163648,1967616],[]),([12,22540,42009,264529,602208,655360,1163648,1967616],[3585,4354,6406]),([12,22540,42009,264529,602208,677900,1163648,1967616],[1286,3585]),([12,22540,42009,264529,602208,733280,1163648,1967616],[3074,4354,6404]),([12,22540,42009,264529,602208,751724,1163648,1967616],[1286,3074]),([12,22540,42009,264529,602208,784892,1163648,1967616],[]),([12,22540,42009,264529,602208,1163648,1833452,1967616],[1286]),([12,22540,42009,264529,602208,1294720,1966076,1967616],[6404]),([12,22540,42009,264529,602208,1294720,1967616],[4868,4897]),([12,22540,42009,264529,602208,1300876,1700320,1967616],[1286,2561]),([12,22540,42009,264529,602208,1300876,1967616,2082688],[1286,4868]),([12,22540,42009,395600,602208,1163648,1966076,1967616],[]),([12,22540,42009,395600,602208,1163648,1967616],[4130,4897]),([12,22540,42009,602208,751724,866672,1163648,1967616],[3074,4098]),([12,22540,42009,602208,751724,1163648,1427920,1967616],[3585,5378]),([12,22540,42009,602208,866672,1014140,1163648,1967616],[]),([12,22540,42009,602208,1300876,1427920,1967616],[1825,3746,4897]),([12,22540,46104,153612,264529,602208,1163648,1967616],[1284,1796]),([12,22540,63516,153612,264529,602208,1163648,1967616],[1284,1796]),([12,22540,64540,131072,264529,602208,1163648,1967616],[1796,4098,6404]),([12,22540,64540,153612,264529,602208,1163648,1967616],[1284,1796]),([12,22540,64540,153612,602208,866672,1163648,1967616],[2562,3074]),([12,22540,64540,260604,264529,602208,1163648,1967616],[]),([12,22540,64540,264529,602208,751724,1163648,1967616],[1286,3074,3590]),([12,22540,107544,153612,264529,602208,1163648,1967616],[1284,1796]),([12,22540,131072,173080,264529,602208,1163648,1967616],[1284,3842,6404]),([12,22540,131072,195612,264529,602208,1163648,1967616],[1284,3842,6404]),([12,22540,131072,264529,602208,1163648,1967616,2008600],[1286,2818,4870]),([12,22540,131080,264529,602208,1163648,1967616,2008600],[1286]),([12,22540,153612,173080,264529,602208,1163648,1967616],[1284,1796]),([12,22540,153612,195612,264529,602208,1163648,1967616],[1284,1796]),([12,22540,153612,195612,602208,866672,1163648,1967616],[2562,2818]),([12,22540,153612,264529,566296,602208,1163648,1967616],[1286,2564]),([12,22540,153612,264529,602208,1163648,1967616,2008600],[1286,6404]),([12,22540,153612,264529,602208,1163648,1967616,2031132],[1284,6404]),([12,22540,153612,264529,602208,1163648,2008600,2045536],[1284,2565,2818,3074,4868]),([12,22540,153612,602208,866672,1163648,1967616,2008600],[1281,1795,2050,5378,6404]),([12,22540,195612,260604,264529,602208,1163648,1967616],[]),([12,22540,195612,264529,602208,751724,1163648,1967616],[1286,3074,3590]),([12,22540,260604,264529,602208,1163648,1967616,2008600],[]),([12,22540,264529,602208,751724,1163648,1967616,2008600],[2050,5378,6406]),([12,23012,107544,153612,264529,602208,1163648,1967616],[]),([12,23012,153612,264529,602208,1163648,1967616,2008600],[4868]),([12,23012,153612,264529,602208,1163648,1967616,2074136],[4868]),([12,23012,153612,264529,602208,1163648,2033152,2074136],[4868]),([12,30844,42009,153612,264529,602208,1163648,1967616],[]),([12,40960,153612,264529,396828,602208,1163648,1967616],[1286,2564,6404]),([12,40960,153612,264529,437788,602208,1163648,1967616],[1286,2564,3589,4868,6404]),([12,40960,153612,264529,602208,1163648,1700320,1967616],[1286,6404]),([12,40960,153612,264529,602208,1163648,1967616],[1286,1316,1345,2626,4130,4868,4902]),([12,40976,106992,153612,264529,602208,1163648,1967616],[]),([12,40976,153612,195612,264529,602208,1163648,1967616],[1796]),([12,40976,153612,264529,602208,1163648,1967616],[1316,4130,4902]),([12,40976,153612,264529,602208,1163648,1967616,1990156],[1286,4868,6404]),([12,40976,153612,264529,602208,1163648,1967616,2031132],[6404]),([12,40984,40984,153612,264529,602208,1163648,1967616],[]),([12,40984,42008,153612,264529,602208,1163648,1967616],[]),([12,40984,65536,153612,264529,602208,1163648,1967616],[1284]),([12,40984,77920,153612,264529,602208,1163648,1967616],[]),([12,40984,129532,153612,264529,602208,1163648,1967616],[]),([12,40984,129532,153612,602208,866672,1163648,1967616],[]),([12,40984,131072,153612,264529,602208,1163648,1967616],[1284,3842]),([12,40984,131080,153612,264529,602208,1163648,1967616],[1284]),([12,40984,153612,173080,264529,602208,1163648,1967616],[1796]),([12,40984,153612,194588,264529,602208,1163648,1967616],[1796]),([12,40984,153612,260604,264529,602208,1163648,1967616],[]),([12,40984,153612,264529,566296,602208,1163648,1967616],[2566]),([12,40984,153612,264529,602208,635000,1163648,1967616],[]),([12,40984,153612,264529,602208,653820,1163648,1967616],[]),([12,40984,153612,264529,602208,751724,1163648,1967616],[1286,3074])]
noncomputable def k19 : CE := [([12,40984,153612,264529,602208,1163648,1700320,1967616],[]),([12,40984,153612,264529,602208,1163648,1967616],[1316,4130,4902]),([12,40984,153612,264529,602208,1163648,1967616,1967616],[4870]),([12,40984,153612,264529,602208,1163648,1967616,1990156],[1286,6404]),([12,40984,153612,264529,602208,1163648,1967616,2008600],[6406]),([12,40984,153612,264529,602208,1163648,1967616,2031132],[6404]),([12,40984,153612,264529,602208,1163648,1967616,2045536],[3074,4868]),([12,40984,153612,264529,602208,1163648,1967616,2078328],[]),([12,40984,153612,264529,602208,1163648,1967616,2097148],[]),([12,40984,153612,264529,602208,1163648,2008600,2045536],[2565,3074,4868]),([12,40984,153612,602208,866672,1163648,1967616],[2114,4897,5410]),([12,40984,153612,602208,866672,1163648,1967616,2008600],[5378,6401]),([12,41456,42009,153612,264529,602208,1163648,1967616],[]),([12,41456,42009,153612,264529,602208,1163648,2033152],[]),([12,42008,42008,153612,264529,602208,1163648,1967616],[]),([12,42008,46104,153612,264529,602208,1163648,1967616],[1284]),([12,42008,65536,153612,264529,602208,1163648,1967616],[1284,2049]),([12,42008,77920,153612,264529,602208,1163648,1967616],[]),([12,42008,106992,153612,264529,602208,1163648,1967616],[]),([12,42008,107544,153612,264529,602208,1163648,1967616],[1284]),([12,42008,129532,153612,264528,602208,1163648,1967616],[]),([12,42008,129532,153612,264529,602208,1163648,1967616],[]),([12,42008,129532,153612,602208,866672,1163648,1967616],[]),([12,42008,130556,153612,264529,602208,1163648,1967616],[]),([12,42008,131072,153612,264529,602208,1163648,1967616],[1284,3842]),([12,42008,137228,153612,264529,602208,1163648,1967616],[1284,1796]),([12,42008,153612,153612,264529,602208,1163648,1967616],[1284]),([12,42008,153612,173080,264529,602208,1163648,1967616],[1796]),([12,42008,153612,195612,264529,602208,1163648,1967616],[1796]),([12,42008,153612,260604,264529,602208,1163648,1967616],[]),([12,42008,153612,264528,602208,1163648,1967616],[1316,4130,4902]),([12,42008,153612,264529,396828,602208,1163648,1967616],[2564]),([12,42008,153612,264529,602208,602208,1163648,1967616],[]),([12,42008,153612,264529,602208,636024,1163648,1967616],[]),([12,42008,153612,264529,602208,653820,1163648,1967616],[]),([12,42008,153612,264529,602208,751724,1163648,1967616],[1286,3074]),([12,42008,153612,264529,602208,933500,1163648,1967616],[]),([12,42008,153612,264529,602208,949884,1163648,1967616],[]),([12,42008,153612,264529,602208,966268,1163648,1967616],[]),([12,42008,153612,264529,602208,999036,1163648,1967616],[]),([12,42008,153612,264529,602208,1048572,1163648,1967616],[]),([12,42008,153612,264529,602208,1163648,1700320,1967616],[]),([12,42008,153612,264529,602208,1163648,1966076,1967616],[]),([12,42008,153612,264529,602208,1163648,1967616],[1316,4130,4902]),([12,42008,153612,264529,602208,1163648,1967616,1990156],[6404]),([12,42008,153612,264529,602208,1163648,1967616,2031612],[]),([12,42008,153612,264529,602208,1163648,1967616,2055140],[1286,4868,7809]),([12,42008,153612,264529,602208,1163648,1967616,2097148],[]),([12,42008,153612,602208,669228,1163648,1427920,1967616],[]),([12,42008,153612,602208,866672,933500,1163648,1967616],[]),([12,42008,153612,602208,866672,1163648,1494940,1967616],[5765]),([12,42008,153612,602208,866672,1163648,1967616],[2114,4897,5411]),([12,42009,47612,153612,264529,602208,1163648,1967616],[]),([12,42009,47612,153612,264529,602208,1163648,2049536],[]),([12,42009,61612,153612,330064,602208,1163648,1967616],[]),([12,42009,63740,153612,602208,866672,1163648,1967616],[]),([12,42009,63996,65536,153612,264529,1700320,1967616],[1796]),([12,42009,63996,65536,153612,264529,1700320,2033152],[1796]),([12,42009,63996,153612,264529,602208,1163648,1967616],[]),([12,42009,63996,153612,264529,602208,1163648,2033152],[]),([12,42009,63996,153612,264529,602208,1700320,2033152],[3972]),([12,42009,63996,153612,264529,1700320,1967616,2033152],[4868,6404]),([12,42009,63996,153612,264529,1700320,2033152],[1828,4900]),([12,42009,63996,153612,330064,602208,1163648,1967616],[]),([12,42009,63996,153612,330064,602208,1163648,2033152],[]),([12,42009,63996,153612,602208,866672,1163648,1967616],[]),([12,42009,63996,153612,602208,866672,1163648,2033152],[2948]),([12,42009,63996,219148,264529,602208,1163648,1967616],[]),([12,42009,63996,219148,264529,602208,1163648,2033152],[]),([12,42009,65536,65536,153612,264529,1700320,1967616],[1284,2817]),([12,42009,65536,77920,153612,264529,1700320,1967616],[1284]),([12,42009,65536,77920,153612,866672,1163648,1967616],[5378]),([12,42009,65536,106992,153612,264529,1700320,1967616],[1284,2817]),([12,42009,65536,127456,153612,264529,1700320,1967616],[1284]),([12,42009,65536,129532,153612,264529,1700320,1967616],[1284]),([12,42009,65536,129532,153612,264529,1700320,2033152],[1284]),([12,42009,65536,129532,153612,330064,1700320,1967616],[]),([12,42009,65536,129532,153612,866672,1700320,1967616],[]),([12,42009,65536,129532,153612,1700320,1964528,1967616],[]),([12,42009,65536,129532,219148,264529,1700320,1967616],[1286,2177]),([12,42009,65536,132620,153612,1700320,1964528,1967616],[1284,2817]),([12,42009,65536,133132,153612,264529,1700320,1967616],[1284,1796,2564,2820,6660]),([12,42009,65536,137228,153612,264529,1700320,1967616],[1284,1796,2564,2820,6660]),([12,42009,65536,153612,153612,264529,1700320,1967616],[1284,1796]),([12,42009,65536,153612,260604,264529,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,396828,1700320,1967616],[1284,2054,3588,6660]),([12,42009,65536,153612,264529,396828,1700320,2033152],[1284,2052,3588,5124,6660]),([12,42009,65536,153612,264529,417308,1700320,1967616],[1284,2049,3588]),([12,42009,65536,153612,264529,462364,1700320,1967616],[1284,2049,3588]),([12,42009,65536,153612,264529,524284,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,602208,1163648,1967616],[1284,2049]),([12,42009,65536,153612,264529,602208,1163648,2033152],[1284,2052]),([12,42009,65536,153612,264529,602208,1176032,1967616],[1284,2054,4354]),([12,42009,65536,153612,264529,602208,1634784,1967616],[1284,2054,6660]),([12,42009,65536,153612,264529,602208,1700320,1967616],[1284,2054,6660]),([12,42009,65536,153612,264529,653820,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,933500,1700320,1967616],[1284,2054,6660]),([12,42009,65536,153612,264529,933500,1700320,2033152],[1284,2052,5124,6660]),([12,42009,65536,153612,264529,949884,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,999036,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,1048572,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,1634784,1700320,1967616],[1284,2049]),([12,42009,65536,153612,264529,1634784,1967616],[1316,1828,2113,4902]),([12,42009,65536,153612,264529,1634784,1967616,2031612],[]),([12,42009,65536,153612,264529,1700320,1702396,1967616],[1284,2049]),([12,42009,65536,153612,264529,1700320,1966076,1967616],[1284,2049]),([12,42009,65536,153612,264529,1700320,1967616],[1284,1316,1828,2049,2113,4902,5153]),([12,42009,65536,153612,264529,1700320,1967616,2031612],[1284,2049]),([12,42009,65536,153612,264529,1700320,1967616,2097148],[1284,2049]),([12,42009,65536,153612,264529,1700320,2031612,2033152],[1284]),([12,42009,65536,153612,330064,396828,1700320,1967616],[1284,2049,4484]),([12,42009,65536,153612,330064,602208,1163648,1967616],[2049]),([12,42009,65536,153612,330064,933500,1700320,1967616],[2049,4484]),([12,42009,65536,153612,330064,1700320,1767084,1967616],[2049]),([12,42009,65536,153612,330064,1700320,1967616,2031612],[2049,7300]),([12,42009,65536,153612,342384,602208,1163648,1967616],[2049]),([12,42009,65536,153612,371184,602208,1163648,1967616],[2049]),([12,42009,65536,153612,396828,866672,1700320,1967616],[1284,2049,4484]),([12,42009,65536,153612,396828,1700320,1964528,1967616],[1284,2049,5764]),([12,42009,65536,153612,602208,800880,1163648,1967616],[1284,2049]),([12,42009,65536,153612,602208,801136,1163648,1967616],[1284,2049]),([12,42009,65536,153612,602208,866672,1163648,1967616],[2049]),([12,42009,65536,153612,602208,1230476,1964528,1967616],[1285,2049]),([12,42009,65536,153612,602208,1427920,1767084,1967616],[2049]),([12,42009,65536,153612,602208,1427920,1832876,1967616],[2049,4354]),([12,42009,65536,153612,669228,1427920,1700320,1967616],[1284,2049]),([12,42009,65536,153612,866672,933500,1700320,1967616],[2049]),([12,42009,65536,153612,866672,1494940,1700320,1967616],[2049,4485]),([12,42009,65536,153612,866672,1700320,1967616,2031612],[2049]),([12,42009,65536,153612,933500,1700320,1964528,1967616],[2049]),([12,42009,65536,153612,1700320,1964528,1967616,2031612],[2049]),([12,42009,65600,115072,153612,602208,1427920,1967616],[3842,5122]),([12,42009,65600,153612,379344,602208,1163648,1967616],[2818,3842]),([12,42009,65600,153612,602208,1163648,1362320,1967616],[2818,5122]),([12,42009,65600,153612,602208,1163648,1427920,1967616],[2818,5122]),([12,42009,65600,153612,602208,1427920,1832876,1967616],[]),([12,42009,65600,153612,669228,1163648,1964528,1967616],[1284,2818]),([12,42009,67920,153612,330064,602208,1163648,1967616],[]),([12,42009,69632,129532,153612,264529,1700320,1967616],[1284]),([12,42009,69632,149516,264529,602208,1163648,1967616],[1285,2049,5125,6661]),([12,42009,69632,153612,264529,396828,1700320,1967616],[1284,2054,3588,6660]),([12,42009,69632,153612,264529,598112,1163648,1967616],[2817,5121,6657]),([12,42009,69632,153612,264529,602208,1163648,1967616],[1284,2049,5124]),([12,42009,69632,153612,264529,933500,1700320,1967616],[1284,2054,6660]),([12,42009,69632,153612,264529,1494940,1700320,1967616],[1285,2055,6661]),([12,42009,69632,153612,264529,1700320,1943536,1967616],[1284,2049,6657]),([12,42009,69632,153612,264529,1700320,1967616,2027516],[1284,2051,5122]),([12,42009,73824,106992,153612,866672,1163648,1967616],[]),([12,42009,73824,153612,264529,602208,1163648,1967616],[]),([12,42009,73824,153612,264529,602208,1163648,1971712],[])]
noncomputable def k20 : CE := [([12,42009,73824,153612,264529,635376,1163648,1967616],[]),([12,42009,73824,153612,264529,1163648,1700320,1967616],[]),([12,42009,73824,153612,338288,602208,1163648,1967616],[]),([12,42009,73824,153612,371184,602208,1163648,1967616],[]),([12,42009,73824,153612,602208,866672,1163648,1967616],[]),([12,42009,73824,153612,602208,1163648,1427920,1967616],[2818,5122]),([12,42009,73824,153612,866672,1163648,1967616],[4897,5153]),([12,42009,73824,153612,866672,1163648,1967616,1990156],[2051,5122,6658]),([12,42009,74096,153612,602208,866672,1163648,1967616],[]),([12,42009,77856,153612,602208,788816,1163648,1967616],[2817]),([12,42009,77856,153612,788816,1163648,1308332,1967616],[2818]),([12,42009,77856,153612,788816,1163648,1967616],[1830,4902]),([12,42009,77920,77920,153612,866672,1163648,1967616],[]),([12,42009,77920,80240,153612,866672,1163648,1967616],[]),([12,42009,77920,115072,153612,264529,1700320,1967616],[]),([12,42009,77920,115072,153612,602208,1427920,1967616],[3842,5122]),([12,42009,77920,129532,153612,264529,1687936,1967616],[]),([12,42009,77920,129532,153612,788816,1163648,1967616],[]),([12,42009,77920,129532,153612,866672,1163648,1967616],[]),([12,42009,77920,129532,153612,1163648,1964528,1967616],[]),([12,42009,77920,129532,264529,677900,1163648,1967616],[]),([12,42009,77920,131072,153612,866672,1163648,1967616],[]),([12,42009,77920,153612,227436,866672,1163648,1967616],[]),([12,42009,77920,153612,260604,866672,1163648,1967616],[]),([12,42009,77920,153612,264529,602208,1163648,1967616],[]),([12,42009,77920,153612,264529,602208,1163648,1971712],[]),([12,42009,77920,153612,264529,602208,1163648,1984000],[3842]),([12,42009,77920,153612,264529,602208,1163648,2033152],[]),([12,42009,77920,153612,264529,602208,1167744,1967616],[3844]),([12,42009,77920,153612,264529,602208,1294720,1967616],[3844]),([12,42009,77920,153612,264529,602208,1687936,1967616],[3846]),([12,42009,77920,153612,264529,618592,1163648,1967616],[3845]),([12,42009,77920,153612,264529,620652,1163648,1967616],[]),([12,42009,77920,153612,264529,651744,1163648,1967616],[]),([12,42009,77920,153612,264529,653820,1163648,1967616],[]),([12,42009,77920,153612,264529,677900,1163648,1967616],[1796]),([12,42009,77920,153612,264529,733280,1163648,1967616],[3845]),([12,42009,77920,153612,264529,751724,1163648,1967616],[1796]),([12,42009,77920,153612,264529,784892,1163648,1967616],[]),([12,42009,77920,153612,264529,1163648,1650784,1967616],[5127]),([12,42009,77920,153612,264529,1163648,1687936,1967616],[]),([12,42009,77920,153612,264529,1163648,1700320,1967616],[]),([12,42009,77920,153612,264529,1163648,1702396,1967616],[]),([12,42009,77920,153612,264529,1163648,1833452,1967616],[1796]),([12,42009,77920,153612,264529,1300876,1700320,1967616],[1796,2049]),([12,42009,77920,153612,264529,1572860,1687936,1967616],[]),([12,42009,77920,153612,264529,1687936,1967616],[1828,4900]),([12,42009,77920,153612,264529,1700320,1967616,2082688],[4868]),([12,42009,77920,153612,268624,602208,1163648,1967616],[]),([12,42009,77920,153612,280912,602208,1163648,1967616],[3842]),([12,42009,77920,153612,330064,602208,1163648,1967616],[]),([12,42009,77920,153612,342384,602208,1163648,1967616],[]),([12,42009,77920,153612,342384,653820,1163648,1967616],[]),([12,42009,77920,153612,342384,751724,1163648,1967616],[]),([12,42009,77920,153612,342384,866672,1163648,1967616],[]),([12,42009,77920,153612,342384,1163648,1700320,1967616],[]),([12,42009,77920,153612,379344,602208,1163648,1967616],[3842]),([12,42009,77920,153612,395600,602208,1163648,1967616],[]),([12,42009,77920,153612,602208,788816,1163648,1967616],[2817]),([12,42009,77920,153612,602208,866672,1163648,1967616],[]),([12,42009,77920,153612,602208,1163648,1313104,1967616],[2819,5121]),([12,42009,77920,153612,602208,1163648,1427920,1967616],[2818,5122]),([12,42009,77920,153612,602208,1163648,1440240,1967616],[2818,5122]),([12,42009,77920,153612,602208,1163648,1964528,1967616],[]),([12,42009,77920,153612,602208,1300876,1427920,1967616],[2049]),([12,42009,77920,153612,602208,1427920,1967616,2082688],[2817,3841]),([12,42009,77920,153612,653820,866672,1163648,1967616],[]),([12,42009,77920,153612,653820,1163648,1427920,1967616],[]),([12,42009,77920,153612,751724,866672,1163648,1967616],[2818,3842]),([12,42009,77920,153612,751724,1163648,1427920,1967616],[5122]),([12,42009,77920,153612,788816,1163648,1572860,1967616],[]),([12,42009,77920,153612,788816,1163648,1967616],[1830,4902]),([12,42009,77920,153612,866672,866672,1163648,1967616],[]),([12,42009,77920,153612,866672,915964,1163648,1967616],[]),([12,42009,77920,153612,866672,1014140,1163648,1967616],[]),([12,42009,77920,153612,866672,1163648,1176032,1967616],[3970]),([12,42009,77920,153612,866672,1163648,1178108,1967616],[]),([12,42009,77920,153612,866672,1163648,1300876,1967616],[2051]),([12,42009,77920,153612,866672,1163648,1310716,1967616],[]),([12,42009,77920,153612,866672,1163648,1572860,1967616],[]),([12,42009,77920,153612,866672,1163648,1700320,1967616],[]),([12,42009,77920,153612,866672,1163648,1964528,1967616],[]),([12,42009,77920,153612,866672,1163648,1967616],[5155]),([12,42009,77920,153612,866672,1163648,1967616,1990156],[2051,5122,6658]),([12,42009,77920,153612,866672,1163648,1967616,2045536],[2819,6659]),([12,42009,77920,153612,866672,1163648,1967616,2047856],[]),([12,42009,77920,153612,866672,1163648,1967616,2082688],[5122]),([12,42009,77920,153612,866672,1163648,1967616,2097148],[]),([12,42009,77920,153612,1163648,1427920,1700320,1967616],[2946]),([12,42009,77920,153612,1163648,1427920,1964528,1967616],[]),([12,42009,77920,153612,1163648,1700320,1964528,1967616],[]),([12,42009,77920,153612,1163648,1964528,1967616],[5155]),([12,42009,77920,219148,264529,602208,1163648,1967616],[2817,3841,5126]),([12,42009,77920,264529,602208,677900,1163648,1967616],[2049,2817]),([12,42009,77920,264529,602208,1163648,1202188,1967616],[2049,2819]),([12,42009,77920,264529,677900,1163648,1572860,1967616],[]),([12,42009,77920,264529,677900,1163648,1967616],[2596,4900]),([12,42009,77920,264529,751724,1163648,1300876,1967616],[2051,3843]),([12,42009,77920,264529,751724,1163648,1967616,1990156],[2051,5125,5766,6404]),([12,42009,79996,153612,264529,602208,1163648,1967616],[]),([12,42009,80240,153612,342384,602208,1163648,1967616],[]),([12,42009,80240,153612,602208,866672,1163648,1967616],[]),([12,42009,80240,153612,602208,915964,1163648,1967616],[]),([12,42009,80240,153612,602208,1014140,1163648,1967616],[]),([12,42009,80240,153612,602208,1163648,1964528,1967616],[]),([12,42009,80240,153612,751724,866672,1163648,1967616],[3842]),([12,42009,80240,153612,866672,1163648,1967616,2045536],[2819,5761]),([12,42009,88076,153612,264529,602208,1163648,1967616],[1284,2049]),([12,42009,88076,219148,264529,602208,1163648,1967616],[1286,2049]),([12,42009,94304,153612,264529,602208,1163648,1967616],[3845]),([12,42009,94304,153612,264529,618592,1163648,1967616],[3845]),([12,42009,96364,129532,153612,866672,1163648,1967616],[]),([12,42009,96364,153612,264529,602208,1163648,1967616],[]),([12,42009,96364,153612,264529,1163648,1700320,1967616],[3970]),([12,42009,96364,153612,602208,866672,1163648,1967616],[2818]),([12,42009,96364,153612,602208,1163648,1427920,1967616],[]),([12,42009,96364,153612,751724,866672,1163648,1967616],[2178,2818]),([12,42009,96364,153612,866672,1163648,1967616],[5154]),([12,42009,96364,264529,602208,1163648,1300876,1967616],[]),([12,42009,96636,153612,602208,866672,1163648,1967616],[]),([12,42009,106976,153612,264529,602208,1163648,1967616],[]),([12,42009,106992,131072,371184,602208,1163648,1990156],[4098]),([12,42009,106992,131072,395600,602208,1163648,1990156],[4098]),([12,42009,106992,131072,602208,866672,1163648,1990156],[3074]),([12,42009,106992,153612,264529,602208,1163648,1967616],[]),([12,42009,106992,153612,264529,602208,1163648,1971712],[]),([12,42009,106992,153612,264529,602208,1163648,2033152],[]),([12,42009,106992,153612,264529,602208,1167744,1967616],[]),([12,42009,106992,153612,264529,602208,1294720,1967616],[]),([12,42009,106992,153612,264529,602208,1294720,1990156],[1796,2052,2180]),([12,42009,106992,153612,264529,602208,1692032,1967616],[]),([12,42009,106992,153612,268624,602208,1163648,1967616],[]),([12,42009,106992,153612,330064,602208,1163648,1967616],[]),([12,42009,106992,153612,338288,602208,1163648,1967616],[]),([12,42009,106992,153612,371184,602208,1163648,1967616],[]),([12,42009,106992,153612,395600,602208,1163648,1967616],[]),([12,42009,106992,153612,395600,602208,1163648,1990156],[]),([12,42009,106992,153612,602208,792576,1163648,1967616],[3075,4354,7170]),([12,42009,106992,153612,602208,792912,1163648,1967616],[]),([12,42009,106992,153612,602208,866672,1163648,1967616],[]),([12,42009,106992,153612,602208,899568,1163648,1967616],[]),([12,42009,106992,153612,602208,1163648,1964528,1967616],[3970]),([12,42009,106992,153612,602208,1300876,1427920,1967616],[1793,3970]),([12,42009,106992,153612,602208,1427920,1967616,2088844],[6786]),([12,42009,106992,153612,602208,1427920,1990156,2082688],[]),([12,42009,106992,238064,264529,602208,1163648,1990156],[2052]),([12,42009,106992,264529,602208,733280,1163648,1990156],[2821,3074,3844,4354]),([12,42009,106992,264529,602208,1294720,1990156],[2852,3876,4002,4900,5156,5284]),([12,42009,106992,264529,602208,1300876,1990156,2082688],[3846,4868,6660]),([12,42009,106992,395600,602208,1163648,1990156],[3874,4002,4130])]
noncomputable def k21 : CE := [([12,42009,109052,153612,264529,602208,1163648,1967616],[]),([12,42009,109052,153612,264529,602208,1163648,1988096],[]),([12,42009,110764,153612,280912,602208,1163648,1967616],[]),([12,42009,111088,153612,264529,602208,1163648,1967616],[]),([12,42009,111100,153612,602208,1163648,1427920,1967616],[3970]),([12,42009,111100,153612,602208,1163648,1427920,1986048],[3970,5122]),([12,42009,113148,153612,264529,602208,1163648,1967616],[]),([12,42009,113148,153612,264529,602208,1163648,1984000],[]),([12,42009,113148,153612,264529,618592,1163648,1967616],[]),([12,42009,113148,153612,264529,618592,1163648,1984000],[]),([12,42009,113148,153612,280912,602208,1163648,1967616],[]),([12,42009,113148,153612,280912,602208,1163648,1984000],[]),([12,42009,113148,153612,602208,866672,1163648,1967616],[]),([12,42009,113148,153612,602208,866672,1163648,1984000],[]),([12,42009,113148,153612,602208,1163648,1427920,1967616],[3970]),([12,42009,113148,153612,602208,1163648,1427920,1984000],[3970]),([12,42009,127148,153612,395600,602208,1163648,1967616],[4354]),([12,42009,127148,153612,602208,788816,1163648,1967616],[4354]),([12,42009,127456,153612,264529,602208,1163648,1967616],[]),([12,42009,127456,153612,264529,602208,1300876,1967616],[1798]),([12,42009,127456,153612,391664,602208,1163648,1967616],[]),([12,42009,127456,153612,602208,866672,1163648,1967616],[]),([12,42009,127456,153612,602208,1163648,1964528,1967616],[3970]),([12,42009,129516,153612,264529,602208,1163648,1967616],[]),([12,42009,129520,153612,602208,866672,1163648,1967616],[]),([12,42009,129520,153612,602208,1163648,1964528,1967616],[3970]),([12,42009,129532,131072,395600,602208,1163648,1990156],[1796,4098]),([12,42009,129532,131072,602208,866672,1163648,1990156],[3074]),([12,42009,129532,153612,219148,264529,1700320,1967616],[1798,2049,2564]),([12,42009,129532,153612,227436,866672,1163648,1967616],[]),([12,42009,129532,153612,264529,602208,1163648,1967616],[]),([12,42009,129532,153612,264529,602208,1163648,1971712],[]),([12,42009,129532,153612,264529,602208,1163648,1988096],[]),([12,42009,129532,153612,264529,602208,1163648,2033152],[]),([12,42009,129532,153612,264529,602208,1163648,2037248],[]),([12,42009,129532,153612,264529,602208,1167744,1967616],[]),([12,42009,129532,153612,264529,602208,1167744,1971712],[]),([12,42009,129532,153612,264529,602208,1294720,1967616],[]),([12,42009,129532,153612,264529,602208,1294720,1990156],[1796,2052]),([12,42009,129532,153612,264529,602208,1298816,1967616],[]),([12,42009,129532,153612,264529,602208,1687936,1967616],[]),([12,42009,129532,153612,264529,602208,1692032,1967616],[]),([12,42009,129532,153612,264529,602208,1700320,2033152],[]),([12,42009,129532,153612,264529,602208,1819008,1967616],[]),([12,42009,129532,153612,264529,733280,1294720,1967616],[]),([12,42009,129532,153612,264529,1650784,1967616,2082688],[4868,6786]),([12,42009,129532,153612,264529,1700320,1967616,2033152],[4868,6404]),([12,42009,129532,153612,264529,1700320,2033152],[1828,4900]),([12,42009,129532,153612,264529,1700320,2045536,2082688],[]),([12,42009,129532,153612,268624,602208,1163648,1967616],[]),([12,42009,129532,153612,268624,602208,1163648,1971712],[]),([12,42009,129532,153612,268624,602208,1167744,1967616],[]),([12,42009,129532,153612,285008,602208,1163648,1967616],[]),([12,42009,129532,153612,330064,602208,1163648,1967616],[]),([12,42009,129532,153612,330064,602208,1163648,2033152],[]),([12,42009,129532,153612,334160,602208,1163648,1967616],[]),([12,42009,129532,153612,342384,602208,1163648,1967616],[]),([12,42009,129532,153612,342384,751724,1163648,1967616],[]),([12,42009,129532,153612,391664,602208,1163648,1967616],[]),([12,42009,129532,153612,395600,602208,1163648,1967616],[]),([12,42009,129532,153612,395600,602208,1163648,1990156],[1796]),([12,42009,129532,153612,395600,602208,1294720,1967616],[]),([12,42009,129532,153612,399696,602208,1163648,1967616],[]),([12,42009,129532,153612,602208,788816,1163648,1967616],[]),([12,42009,129532,153612,602208,788816,1687936,1967616],[]),([12,42009,129532,153612,602208,792576,1163648,1967616],[4354,7170]),([12,42009,129532,153612,602208,792912,1163648,1967616],[]),([12,42009,129532,153612,602208,854352,1163648,1967616],[]),([12,42009,129532,153612,602208,866672,1163648,1967616],[]),([12,42009,129532,153612,602208,866672,1163648,1971712],[]),([12,42009,129532,153612,602208,866672,1163648,1973760],[3074]),([12,42009,129532,153612,602208,866672,1163648,1984000],[]),([12,42009,129532,153612,602208,866672,1163648,2033152],[]),([12,42009,129532,153612,602208,866672,1167744,1967616],[]),([12,42009,129532,153612,602208,866672,1169792,1967616],[3074]),([12,42009,129532,153612,602208,866672,1294720,1967616],[]),([12,42009,129532,153612,602208,866672,1687936,1967616],[]),([12,42009,129532,153612,602208,866672,1950080,1967616],[]),([12,42009,129532,153612,602208,883056,1163648,1967616],[]),([12,42009,129532,153612,602208,915952,1163648,1967616],[]),([12,42009,129532,153612,602208,919888,1163648,1967616],[]),([12,42009,129532,153612,602208,997744,1163648,1967616],[]),([12,42009,129532,153612,602208,1163648,1837392,1967616],[3970]),([12,42009,129532,153612,602208,1163648,1915248,1967616],[3970]),([12,42009,129532,153612,602208,1163648,1964528,1967616],[3970]),([12,42009,129532,153612,602208,1165696,1427920,1967616],[3970]),([12,42009,129532,153612,602208,1167744,1427920,1967616],[3970]),([12,42009,129532,153612,602208,1167744,1432016,1967616],[3970]),([12,42009,129532,153612,602208,1169804,1427920,1967616],[3970]),([12,42009,129532,153612,602208,1294720,1427920,1967616],[3970]),([12,42009,129532,153612,602208,1294720,1558992,1967616],[3970]),([12,42009,129532,153612,602208,1300876,1427920,1967616],[3970]),([12,42009,129532,153612,602208,1300876,1964528,1967616],[3970]),([12,42009,129532,153612,602208,1313104,1967616,2082688],[4871,6786]),([12,42009,129532,153612,602208,1425792,1427920,1967616],[3970,5250]),([12,42009,129532,153612,602208,1427920,1687936,1967616],[5250]),([12,42009,129532,153612,602208,1427920,1967616,2082688],[6786]),([12,42009,129532,153612,602208,1427920,1967616,2088844],[6786]),([12,42009,129532,153612,602208,1427920,1990156,2082688],[]),([12,42009,129532,153612,602208,1427920,2045536,2082688],[]),([12,42009,129532,153612,602208,1687936,1952208,1967616],[3970]),([12,42009,129532,153612,602208,1964528,1967616,2082688],[6786]),([12,42009,129532,219148,264529,602208,1163648,1967616],[]),([12,42009,129532,219148,264529,602208,1163648,2033152],[]),([12,42009,129532,219148,264529,602208,1700320,1967616],[3841]),([12,42009,129532,219148,264529,1700320,1967616],[1830,2081,3873,4902,5153,5281]),([12,42009,129532,219148,330064,602208,1163648,1967616],[]),([12,42009,129532,219148,602208,866672,1163648,1967616],[]),([12,42009,129532,264529,602208,677900,1163648,1967616],[]),([12,42009,129532,264529,602208,677900,1687936,1967616],[]),([12,42009,129532,264529,602208,733280,1163648,1990156],[2821,3074,4354]),([12,42009,129532,264529,602208,743436,1163648,1967616],[]),([12,42009,129532,264529,602208,1163648,1726476,1967616],[3970]),([12,42009,129532,264529,602208,1202188,1967616,2082688],[4870,6786]),([12,42009,129532,264529,602208,1294720,1967616,1990156],[4870,5124,5252]),([12,42009,129532,264529,602208,1294720,1990156],[2852,3876,4002,4900,5156]),([12,42009,129532,264529,602208,1300876,1990156,2082688],[3846,4868]),([12,42009,129532,264529,751724,1300876,1700320,1967616],[3970]),([12,42009,129532,395600,602208,1163648,1967616,1990156],[4870]),([12,42009,129532,395600,602208,1163648,1990156],[3874,4002,4130,4900]),([12,42009,129532,602208,677900,788816,1163648,1967616],[]),([12,42009,129532,602208,677900,866672,1163648,1967616],[]),([12,42009,129532,602208,677900,1163648,1427920,1967616],[3970]),([12,42009,129532,602208,751724,1300876,1427920,1967616],[3970]),([12,42009,129532,602208,866672,940044,1163648,1967616],[6914]),([12,42009,129532,602208,1300876,1427920,1967616,1990156],[]),([12,42009,131072,153612,342384,602208,1163648,1967616],[]),([12,42009,131072,153612,371184,602208,1163648,1967616],[3842]),([12,42009,131072,153612,371184,602208,1163648,1990156],[1796,3842]),([12,42009,131072,153612,395344,602208,1163648,1967616],[1284]),([12,42009,131072,153612,395600,602144,1163648,1967616],[1284,3842]),([12,42009,131072,153612,395600,602208,1163648,1967616],[1284,3842]),([12,42009,131072,153612,602208,800880,1163648,1967616],[1284,2818]),([12,42009,131072,153612,602208,801136,1163648,1967616],[1284,2818]),([12,42009,131072,153612,602208,866672,1163648,1967616],[2818]),([12,42009,131072,153612,602208,1427920,1832876,1967616],[]),([12,42009,131072,153612,602208,1558992,1701548,1967616],[]),([12,42009,131072,371184,602208,1163648,1990156],[1316,2818,2882,3874,4130,4900,5540]),([12,42009,131072,395600,602208,933500,1163648,1990156],[1284,2818]),([12,42009,131072,395600,602208,1163648,1701548,1990156],[1284,2818,3074,6018]),([12,42009,131072,395600,602208,1163648,1966076,1990156],[1284,2818,5508]),([12,42009,131072,602208,669228,1163648,1427920,1990156],[2050,2946]),([12,42009,131072,602208,866672,933500,1163648,1990156],[2050]),([12,42009,131072,602208,866672,1163648,1494940,1990156],[2050,2818,5765]),([12,42009,131072,602208,866672,1163648,1966076,1990156],[2050]),([12,42009,131084,153612,602208,866672,1163648,1967616],[2818]),([12,42009,131084,153612,602208,1163648,1964528,1967616],[2818]),([12,42009,132620,153612,602208,866672,1163648,1967616],[2818]),([12,42009,132620,153612,602208,1163648,1964528,1967616],[2818]),([12,42009,132620,153612,602208,1296268,1427920,1967616],[])]
noncomputable def k22 : CE := [([12,42009,132620,153612,602208,1296268,1964528,1967616],[]),([12,42009,132620,153612,602208,1300876,1427920,1967616],[1798,2049]),([12,42009,132620,153612,602208,1300876,1964528,1967616],[1798,2049,3073]),([12,42009,133132,153612,602208,866672,1163648,1967616],[1796,2818]),([12,42009,133132,153612,602208,1163648,1964528,1967616],[1796,2818]),([12,42009,135180,153612,280912,602208,1163648,1967616],[1285,2050]),([12,42009,135180,153612,602208,1163648,1427920,1967616],[2050]),([12,42009,135180,153612,602208,1163648,1964528,1967616],[2818]),([12,42009,135180,153612,602208,1298828,1427920,1967616],[]),([12,42009,135180,153612,602208,1300876,1427920,1967616],[1796]),([12,42009,135180,153612,602208,1427920,1832876,1967616],[]),([12,42009,135180,153612,602208,1427920,1967616,2082688],[2049,4868,6657]),([12,42009,135180,602208,687660,1163648,1427920,1967616],[3841]),([12,42009,135180,602208,1163648,1427920,1967616,1990156],[2817,5250]),([12,42009,137228,153612,268624,602208,1163648,1967616],[1284,1796]),([12,42009,137228,153612,280912,602208,1163648,1967616],[1285,1797,2050]),([12,42009,137228,153612,330064,602208,1163648,1967616],[1284,1796]),([12,42009,137228,153612,395600,602208,1163648,1967616],[1284,1796]),([12,42009,137228,153612,602208,788816,1163648,1967616],[1286,1798,2049]),([12,42009,137228,153612,602208,800880,1163648,1967616],[1284,1796,2818]),([12,42009,137228,153612,602208,801136,1163648,1967616],[1284,1796,2818]),([12,42009,137228,153612,602208,866672,1163648,1967616],[1796,2818]),([12,42009,137228,153612,602208,1163648,1313104,1967616],[1287,1799,2051]),([12,42009,137228,153612,602208,1163648,1427920,1967616],[1796,2050]),([12,42009,137228,153612,602208,1163648,1964528,1967616],[1796,2818]),([12,42009,137228,153612,602208,1300876,1427920,1967616],[1796]),([12,42009,137228,153612,602208,1427920,1967616,2082688],[1796,2049,4868]),([12,42009,137228,153612,735340,866672,1163648,1967616],[1796,2050,2818]),([12,42009,137228,153612,751724,866672,1163648,1967616],[1796,2050,2818]),([12,42009,137228,153612,866672,1163648,1967616,2045536],[1796,2051,4868,5122,6659]),([12,42009,137228,602208,751724,866672,1163648,1967616],[1284]),([12,42009,137228,602208,751724,1163648,1427920,1967616],[1287,3841]),([12,42009,137228,602208,866672,949884,1163648,1967616],[]),([12,42009,137228,602208,866672,1163648,1967616,1990156],[2051,6404]),([12,42009,137228,602208,949884,1163648,1427920,1967616],[3841]),([12,42009,137228,602208,1163648,1427920,1967616,1990156],[2817,5250,6404]),([12,42009,137228,751724,866672,933500,1163648,1967616],[1284]),([12,42009,137228,751724,866672,1163648,1967616],[1287,1316,3875,4900,5155]),([12,42009,144940,153612,602208,788816,1163648,1967616],[]),([12,42009,144940,153612,602208,1163648,1427920,1967616],[]),([12,42009,144940,153612,602208,1163648,1952208,1967616],[]),([12,42009,144940,153612,602208,1687936,1952208,1967616],[3841]),([12,42009,147068,153612,602208,866672,1163648,1967616],[]),([12,42009,147068,153612,602208,866672,1950080,1967616],[3972]),([12,42009,151564,153612,330064,602208,1163648,1967616],[1284]),([12,42009,151564,153612,602208,788816,1163648,1967616],[1286,2049]),([12,42009,151564,153612,602208,866672,1163648,1967616],[2818]),([12,42009,151564,153612,602208,1427920,1832876,1967616],[]),([12,42009,153612,153612,264529,602208,1163648,1967616],[1284]),([12,42009,153612,153612,264529,602208,1163648,2033152],[1284]),([12,42009,153612,153612,264529,602208,1687936,1967616],[1284,1542,1670]),([12,42009,153612,153612,330064,602208,1163648,1967616],[1284]),([12,42009,153612,153612,371184,602208,1163648,1967616],[]),([12,42009,153612,153612,602208,788816,1163648,1967616],[1286,1537,1665]),([12,42009,153612,153612,602208,866672,1163648,1967616],[2818]),([12,42009,153612,153628,264529,602208,1163648,1967616],[1796]),([12,42009,153612,155148,602208,866672,1163648,1967616],[1796,2819,3074]),([12,42009,153612,155148,602208,1163648,1964528,1967616],[2819,3074,3841]),([12,42009,153612,161836,602208,1163648,1427920,1967616],[1287,2178,3841]),([12,42009,153612,161900,264529,602208,1163648,1967616],[1286]),([12,42009,153612,161916,264529,602208,1163648,1967616],[]),([12,42009,153612,161916,602208,866672,1163648,1967616],[]),([12,42009,153612,161916,602208,1163648,1427920,1967616],[2178,3841]),([12,42009,153612,161916,602208,1427920,1967616,2082688],[2177,6657]),([12,42009,153612,195068,264529,602208,1163648,1967616],[]),([12,42009,153612,195068,264529,602208,1163648,2033152],[]),([12,42009,153612,202764,264529,602208,1163648,1967616],[1284,1796,2049]),([12,42009,153612,219148,264529,602208,1163648,1967616],[1286,1796,2049]),([12,42009,153612,219148,264529,1700320,1967616,2031612],[1286,1796,2049,6657]),([12,42009,153612,227436,264529,602208,1163648,1967616],[1286]),([12,42009,153612,227436,264529,1163648,1700320,1967616],[1287,3841,4226]),([12,42009,153612,227436,342384,602208,1163648,1967616],[1284]),([12,42009,153612,227436,602208,866672,1163648,1967616],[1286,3074]),([12,42009,153612,227436,602208,1163648,1427920,1967616],[1287,2178,3841]),([12,42009,153612,227436,866672,1163648,1967616],[1287,3875,4899,5155,5410]),([12,42009,153612,227708,602208,866672,1163648,1967616],[]),([12,42009,153612,238064,264529,602208,1163648,1967616],[6660]),([12,42009,153612,238064,264529,602208,1163648,1990156],[1284,2180,6660]),([12,42009,153612,259756,602208,1163648,1837392,1967616],[4226,5634]),([12,42009,153612,260588,264529,602208,1163648,1967616],[1286]),([12,42009,153612,260604,264529,602208,1163648,1967616],[]),([12,42009,153612,260604,264529,602208,1163648,1971712],[]),([12,42009,153612,260604,264529,602208,1163648,2033152],[]),([12,42009,153612,260604,264529,602208,1167744,1967616],[2180]),([12,42009,153612,260604,264529,602208,1294720,1967616],[2180,6660]),([12,42009,153612,260604,264529,602208,1687936,1967616],[2182]),([12,42009,153612,260604,268624,602208,1163648,1967616],[]),([12,42009,153612,260604,330064,602208,1163648,1967616],[]),([12,42009,153612,260604,342384,602208,1163648,1967616],[]),([12,42009,153612,260604,371184,602208,1163648,1967616],[]),([12,42009,153612,260604,395600,602208,1163648,1967616],[]),([12,42009,153612,260604,602208,788816,1163648,1967616],[2177]),([12,42009,153612,260604,602208,866672,1163648,1967616],[]),([12,42009,153612,260604,602208,1163648,1964528,1967616],[4226]),([12,42009,153612,260604,602208,1300876,1427920,1967616],[1286,4226]),([12,42009,153612,260604,602208,1427920,1967616,2082688],[2177,7042]),([12,42009,153612,262140,602208,866672,1163648,1967616],[]),([12,42009,153612,262140,602208,1163648,1964528,1967616],[4226]),([12,42009,153612,264529,393212,602208,1163648,1967616],[]),([12,42009,153612,264529,417292,602208,1163648,1967616],[2564]),([12,42009,153612,264529,417308,602208,1163648,1967616],[2564]),([12,42009,153612,264529,425596,602208,1163648,1967616],[]),([12,42009,153612,264529,425596,602208,1687936,1967616],[2950]),([12,42009,153612,264529,462364,1700320,1967616],[1316,2564,2596,4902,5665]),([12,42009,153612,264529,503804,602208,1163648,1967616],[]),([12,42009,153612,264529,524284,602208,1163648,1967616],[]),([12,42009,153612,264529,524284,602208,1687936,1967616],[2950]),([12,42009,153612,264529,546828,602208,1163648,1967616],[2564,2817]),([12,42009,153612,264529,575900,602208,1163648,1967616],[]),([12,42009,153612,264529,602208,614496,1163648,1967616],[3075,4357]),([12,42009,153612,264529,602208,618592,1163648,1967616],[3074,4357]),([12,42009,153612,264529,602208,620652,1163648,1967616],[3074]),([12,42009,153612,264529,602208,651744,1163648,1967616],[]),([12,42009,153612,264529,602208,651744,1300876,1967616],[1286,2817]),([12,42009,153612,264529,602208,653804,1163648,1967616],[]),([12,42009,153612,264529,602208,653820,1163648,1967616],[]),([12,42009,153612,264529,602208,653820,1163648,1971712],[]),([12,42009,153612,264529,602208,653820,1163648,1984000],[4482]),([12,42009,153612,264529,602208,653820,1163648,2033152],[]),([12,42009,153612,264529,602208,653820,1167744,1967616],[4484]),([12,42009,153612,264529,602208,653820,1294720,1967616],[4484,6660]),([12,42009,153612,264529,602208,653820,1687936,1967616],[4486]),([12,42009,153612,264529,602208,747628,1163648,1967616],[1287,3075]),([12,42009,153612,264529,602208,751724,1163648,1967616],[1286,3074]),([12,42009,153612,264529,602208,751740,1163648,1967616],[]),([12,42009,153612,264529,602208,784876,1163648,1967616],[1286]),([12,42009,153612,264529,602208,784892,1163648,1967616],[]),([12,42009,153612,264529,602208,847868,1163648,1967616],[]),([12,42009,153612,264529,602208,917500,1163648,1967616],[]),([12,42009,153612,264529,602208,917500,1294720,1967616],[4484,6660]),([12,42009,153612,264529,602208,1044476,1163648,1967616],[]),([12,42009,153612,264529,602208,1048572,1163648,1967616],[]),([12,42009,153612,264529,602208,1048572,1163648,1971712],[]),([12,42009,153612,264529,602208,1048572,1163648,1984000],[3970,4482]),([12,42009,153612,264529,602208,1048572,1163648,2033152],[]),([12,42009,153612,264529,602208,1163648,1634784,1967616],[]),([12,42009,153612,264529,602208,1163648,1700320,1967616],[]),([12,42009,153612,264529,602208,1163648,1700336,1967616],[]),([12,42009,153612,264529,602208,1163648,1702380,1967616],[]),([12,42009,153612,264529,602208,1163648,1702396,1967616],[]),([12,42009,153612,264529,602208,1163648,1833452,1967616],[1286]),([12,42009,153612,264529,602208,1163648,1833468,1967616],[]),([12,42009,153612,264529,602208,1163648,1900540,1967616],[]),([12,42009,153612,264529,602208,1163648,1914464,2082688],[3074]),([12,42009,153612,264529,602208,1163648,1947632,1971712],[]),([12,42009,153612,264529,602208,1163648,1947632,1984000],[5762,6019]),([12,42009,153612,264529,602208,1163648,1947632,2033152],[]),([12,42009,153612,264529,602208,1163648,1949692,1984000],[5762,6019]),([12,42009,153612,264529,602208,1163648,1966076,1967616],[]),([12,42009,153612,264529,602208,1163648,1966076,1971712],[])]
noncomputable def k23 : CE := [([12,42009,153612,264529,602208,1163648,1966076,2033152],[]),([12,42009,153612,264529,602208,1163648,1967616],[1316,4130,4902]),([12,42009,153612,264529,602208,1163648,1967616,2097148],[]),([12,42009,153612,264529,602208,1163648,1969692,2045536],[3074,4868]),([12,42009,153612,264529,602208,1163648,1969692,2095072],[4868]),([12,42009,153612,264529,602208,1163648,1971712],[1316,4130,4900]),([12,42009,153612,264529,602208,1163648,1971712,1982076],[]),([12,42009,153612,264529,602208,1163648,1971712,2019228],[6789]),([12,42009,153612,264529,602208,1163648,1971712,2023324],[]),([12,42009,153612,264529,602208,1163648,1971712,2031612],[]),([12,42009,153612,264529,602208,1163648,1971712,2074608],[7297]),([12,42009,153612,264529,602208,1163648,1971712,2078704],[]),([12,42009,153612,264529,602208,1163648,1971712,2080764],[]),([12,42009,153612,264529,602208,1163648,1971712,2093052],[6789,7297]),([12,42009,153612,264529,602208,1163648,1971712,2097148],[]),([12,42009,153612,264529,602208,1163648,1973772,2045536],[2823,3074,4868]),([12,42009,153612,264529,602208,1163648,1973772,2082688],[4869,6789]),([12,42009,153612,264529,602208,1163648,1975920,1990156],[5252]),([12,42009,153612,264529,602208,1163648,1975920,2082688],[]),([12,42009,153612,264529,602208,1163648,1975920,2088844],[]),([12,42009,153612,264529,602208,1163648,1980000,1990156],[2823,5252,6404]),([12,42009,153612,264529,602208,1163648,1980000,2082688],[]),([12,42009,153612,264529,602208,1163648,1982076,2033152],[5764]),([12,42009,153612,264529,602208,1163648,1982076,2082688],[]),([12,42009,153612,264529,602208,1163648,1988096,2076668],[6788,7297,7555]),([12,42009,153612,264529,602208,1163648,1990156,2041440],[3074,4868,6788]),([12,42009,153612,264529,602208,1163648,1990156,2045536],[2821,3074,4868,6788]),([12,42009,153612,264529,602208,1163648,1990156,2074608],[6788]),([12,42009,153612,264529,602208,1163648,1990156,2078704],[2821,6788]),([12,42009,153612,264529,602208,1163648,1998460,2082688],[3844,7810]),([12,42009,153612,264529,602208,1163648,2015228,2049536],[5252,5764,6023]),([12,42009,153612,264529,602208,1163648,2031612,2033152],[5764,6021]),([12,42009,153612,264529,602208,1163648,2033152],[1316,4130,4389,4420,4900]),([12,42009,153612,264529,602208,1163648,2033152,2047612],[]),([12,42009,153612,264529,602208,1163648,2033152,2074608],[]),([12,42009,153612,264529,602208,1163648,2033152,2080764],[]),([12,42009,153612,264529,602208,1163648,2033152,2097148],[]),([12,42009,153612,264529,602208,1163648,2041440,2082688],[3074]),([12,42009,153612,264529,602208,1163648,2045536,2082688],[3074]),([12,42009,153612,264529,602208,1163648,2045536,2084764],[3074]),([12,42009,153612,264529,602208,1165724,2045536,2082688],[3074]),([12,42009,153612,264529,602208,1167744,1971712,2093052],[6789,7297,7812]),([12,42009,153612,264529,602208,1171952,1990156,2082688],[3846,4868]),([12,42009,153612,264529,602208,1178108,1982076,2082688],[]),([12,42009,153612,264529,602208,1178108,1990156,2082688],[3846,4868]),([12,42009,153612,264529,602208,1178108,2045536,2082688],[3074]),([12,42009,153612,264529,602208,1294720,1966076,1990156],[1284,5124,6660]),([12,42009,153612,264529,604284,1700320,1967616,2082688],[4868,5634,7297]),([12,42009,153612,264529,733280,1294720,1966076,1967616],[5764,6021,6660,7809]),([12,42009,153612,264529,751724,1560476,1700320,1967616],[1287,3841,4482]),([12,42009,153612,264529,999036,1560476,1700320,1967616],[]),([12,42009,153612,264529,1700320,2031612,2033152],[1316,4900,6049]),([12,42009,153612,268368,268624,602208,1163648,1967616],[]),([12,42009,153612,268368,602208,933500,1163648,1967616],[]),([12,42009,153612,268368,602208,1163648,1967616],[1316,4130,4900]),([12,42009,153612,268560,602208,866672,1163648,1967616],[2819]),([12,42009,153612,268560,602208,1163648,1494940,1967616],[5250,5509]),([12,42009,153612,268560,602208,1163648,1499036,1967616],[]),([12,42009,153612,268560,602208,1163648,1967616],[1316,2849,4130,4900]),([12,42009,153612,268624,391676,602208,1163648,1967616],[]),([12,42009,153612,268624,396828,602208,1163648,1967616],[2564,3204]),([12,42009,153612,268624,602208,653820,1163648,1967616],[]),([12,42009,153612,268624,602208,929404,1163648,1967616],[4228]),([12,42009,153612,268624,602208,929404,1167744,1967616],[4228]),([12,42009,153612,268624,602208,933500,1163648,1967616],[]),([12,42009,153612,268624,602208,933500,1163648,1971712],[]),([12,42009,153612,268624,602208,933500,1167744,1967616],[]),([12,42009,153612,268624,602208,933756,1163648,1967616],[]),([12,42009,153612,268624,602208,949884,1163648,1967616],[]),([12,42009,153612,268624,602208,999036,1163648,1967616],[]),([12,42009,153612,268624,602208,1048572,1163648,1967616],[]),([12,42009,153612,268624,602208,1163392,1163648,1967616],[4098,5378]),([12,42009,153612,268624,602208,1163392,1828524,1967616],[3075,4097,5761]),([12,42009,153612,268624,602208,1163392,1967616],[1316,3106,4130,4900]),([12,42009,153612,268624,602208,1163648,1163648,1967616],[4098]),([12,42009,153612,268624,602208,1163648,1178108,1967616],[]),([12,42009,153612,268624,602208,1163648,1230476,1967616],[]),([12,42009,153612,268624,602208,1163648,1494940,1967616],[5509]),([12,42009,153612,268624,602208,1163648,1494940,1971712],[5250,5509]),([12,42009,153612,268624,602208,1163648,1499036,1967616],[]),([12,42009,153612,268624,602208,1163648,1499100,1967616],[]),([12,42009,153612,268624,602208,1163648,1560476,1967616],[5509]),([12,42009,153612,268624,602208,1163648,1572860,1967616],[]),([12,42009,153612,268624,602208,1163648,1828524,1967616],[3075,4097,5761]),([12,42009,153612,268624,602208,1163648,1828524,1971712],[3074,5761]),([12,42009,153612,268624,602208,1163648,1828780,1967616],[4097,5761]),([12,42009,153612,268624,602208,1163648,1832620,1967616],[3074]),([12,42009,153612,268624,602208,1163648,1832684,1967616],[3074]),([12,42009,153612,268624,602208,1163648,1834668,1967616],[3074]),([12,42009,153612,268624,602208,1163648,1835004,1967616],[]),([12,42009,153612,268624,602208,1163648,1947632,1967616],[]),([12,42009,153612,268624,602208,1163648,1949680,1967616],[]),([12,42009,153612,268624,602208,1163648,1959920,1967616],[5761]),([12,42009,153612,268624,602208,1163648,1966076,1967616],[]),([12,42009,153612,268624,602208,1163648,1967616],[1316,4130,4900]),([12,42009,153612,268624,602208,1163648,1967616,1982076],[]),([12,42009,153612,268624,602208,1163648,1967616,2019228],[7045]),([12,42009,153612,268624,602208,1163648,1967616,2031612],[]),([12,42009,153612,268624,602208,1163648,1967616,2080764],[]),([12,42009,153612,268624,602208,1163648,1967616,2090668],[3075,4097,7297]),([12,42009,153612,268624,602208,1163648,1967616,2091004],[7297]),([12,42009,153612,268624,602208,1163648,1967616,2092988],[7045,7297]),([12,42009,153612,268624,602208,1163648,1967616,2093052],[7044,7297]),([12,42009,153612,268624,602208,1163648,1967616,2096892],[]),([12,42009,153612,268624,602208,1163648,1967616,2097148],[]),([12,42009,153612,268624,602208,1163648,1971712,2093052],[6786,7044,7297]),([12,42009,153612,268624,602208,1167744,1494940,1967616],[5250,5509]),([12,42009,153612,268624,602208,1167744,1828524,1967616],[3074,4097,5761]),([12,42009,153612,268624,602208,1167744,1967616,2093052],[6786,7044,7297]),([12,42009,153612,268624,602208,1432016,1828524,1967616],[1796,3075,4097]),([12,42009,153612,268624,866672,1163648,1828524,1967616],[3075,4099,5761]),([12,42009,153612,272752,602208,1163648,1300876,1967616],[1286]),([12,42009,153612,272752,602208,1163648,1967616],[1316,4130,4902]),([12,42009,153612,272752,602208,1163648,1967616,1990156],[6404,7044]),([12,42009,153612,272752,602208,1163648,1967616,2088844],[7045]),([12,42009,153612,276848,602208,1163648,1967616],[1316,4130,4900]),([12,42009,153612,276848,602208,1163648,1967616,2082688],[4097,4868]),([12,42009,153612,285008,396828,602208,1163648,1967616],[3204]),([12,42009,153612,285008,602208,933500,1163648,1967616],[]),([12,42009,153612,285008,602208,1163648,1967616,2076668],[7044,7297,7555]),([12,42009,153612,329808,602208,933500,1163648,1967616],[4228,4484]),([12,42009,153612,329808,602208,999036,1163648,1967616],[]),([12,42009,153612,329808,602208,1163648,1427920,1967616],[5378]),([12,42009,153612,329808,602208,1163648,1967616],[1316,4130,4902]),([12,42009,153612,330064,391676,602208,1163648,1967616],[]),([12,42009,153612,330064,396828,602208,1163648,1967616],[2564,3204]),([12,42009,153612,330064,602208,653820,1163648,1967616],[]),([12,42009,153612,330064,602208,669228,1163648,1967616],[]),([12,42009,153612,330064,602208,933500,1163648,1967616],[4228]),([12,42009,153612,330064,602208,933500,1163648,2033152],[4228,4484]),([12,42009,153612,330064,602208,949884,1163648,1967616],[4228]),([12,42009,153612,330064,602208,999036,1163648,1967616],[]),([12,42009,153612,330064,602208,999292,1163648,1967616],[]),([12,42009,153612,330064,602208,1048572,1163648,1967616],[]),([12,42009,153612,330064,602208,1163648,1767084,1967616],[]),([12,42009,153612,330064,602208,1163648,1767084,2033152],[3074,5764,6021]),([12,42009,153612,330064,602208,1163648,1769132,1967616],[]),([12,42009,153612,330064,602208,1163648,1832620,1967616],[3074,6018]),([12,42009,153612,330064,602208,1163648,1832684,1967616],[3074,6018]),([12,42009,153612,330064,602208,1163648,1835004,1967616],[]),([12,42009,153612,330064,602208,1163648,1966076,1967616],[]),([12,42009,153612,330064,602208,1163648,1967616],[1316,4130,4902]),([12,42009,153612,330064,602208,1163648,1967616,2031356],[7044]),([12,42009,153612,330064,602208,1163648,1967616,2031612],[7044]),([12,42009,153612,330064,602208,1163648,1967616,2097148],[]),([12,42009,153612,330064,602208,1163648,2031612,2033152],[5508,5764,6021]),([12,42009,153612,334160,602208,933500,1163648,1967616],[]),([12,42009,153612,334160,602208,1163648,1494940,1967616],[5509]),([12,42009,153612,334160,602208,1163648,1762988,1967616],[]),([12,42009,153612,334160,602208,1163648,1967616,2027516],[7044])]
noncomputable def k24 : CE := [([12,42009,153612,338288,602208,1163648,1967616],[1316,4130,4902]),([12,42009,153612,338288,602208,1163648,1967616,1990156],[6404,7044]),([12,42009,153612,342384,342384,602208,1163648,1967616],[]),([12,42009,153612,342384,391676,602208,1163648,1967616],[]),([12,42009,153612,342384,489852,602208,1163648,1967616],[]),([12,42009,153612,342384,602208,602208,1163648,1967616],[]),([12,42009,153612,342384,602208,653820,1163648,1967616],[]),([12,42009,153612,342384,602208,751724,1163648,1967616],[1284,3074]),([12,42009,153612,342384,602208,866672,1163648,1967616],[]),([12,42009,153612,342384,602208,1163648,1176032,1967616],[5378]),([12,42009,153612,342384,602208,1163648,1178108,1967616],[]),([12,42009,153612,342384,602208,1163648,1300876,1967616],[1284,2819]),([12,42009,153612,342384,602208,1163648,1440240,1967616],[5378]),([12,42009,153612,342384,602208,1163648,1572860,1967616],[]),([12,42009,153612,342384,602208,1163648,1700320,1967616],[]),([12,42009,153612,342384,602208,1163648,1967616],[1316,4130,4900]),([12,42009,153612,342384,602208,1163648,1967616,1990156],[2819,6404]),([12,42009,153612,342384,602208,1163648,1967616,2045536],[3075,4868]),([12,42009,153612,342384,602208,1163648,1967616,2047856],[]),([12,42009,153612,342384,602208,1163648,1967616,2082688],[4097,4868]),([12,42009,153612,342384,602208,1163648,1967616,2097148],[]),([12,42009,153612,342384,751724,1163648,1967616],[1283,3875,4130,4899,5155]),([12,42009,153612,371184,371184,602208,1163648,1967616],[]),([12,42009,153612,371184,522748,602208,1163648,1967616],[]),([12,42009,153612,371184,602208,635376,1163648,1967616],[]),([12,42009,153612,371184,602208,751724,1163648,1967616],[1281,3074]),([12,42009,153612,371184,602208,899568,1163648,1967616],[]),([12,42009,153612,371184,602208,1163648,1700320,1967616],[]),([12,42009,153612,371184,602208,1163648,1967616],[4130,4897]),([12,42009,153612,371184,602208,1163648,1967616,1990156],[7044]),([12,42009,153612,371184,602208,1163648,1967616,2063980],[3074]),([12,42009,153612,371184,602208,1163648,1967616,2097148],[]),([12,42009,153612,371184,602208,1163648,1990156,2045536],[2818,3074]),([12,42009,153612,371184,602208,1163648,1990156,2074608],[]),([12,42009,153612,371184,602208,1163648,1990156,2076656],[]),([12,42009,153612,391664,602208,1163648,1700320,1967616],[]),([12,42009,153612,391664,602208,1163648,1967616],[2882,4130,4897]),([12,42009,153612,395344,395600,602208,1163648,1967616],[]),([12,42009,153612,395344,602208,933500,1163648,1967616],[]),([12,42009,153612,395344,602208,1163648,1967616],[1316,4130,4902,5153]),([12,42009,153612,395600,396828,602208,1163648,1967616],[2564]),([12,42009,153612,395600,522748,602208,1163648,1967616],[]),([12,42009,153612,395600,602144,602208,1163648,1967616],[]),([12,42009,153612,395600,602144,1163648,1701548,1967616],[3074]),([12,42009,153612,395600,602144,1163648,1967616],[1316,4902,5153]),([12,42009,153612,395600,602208,602208,1163648,1967616],[]),([12,42009,153612,395600,602208,653820,1163648,1967616],[]),([12,42009,153612,395600,602208,802428,1163648,1967616],[4228]),([12,42009,153612,395600,602208,802428,1294720,1967616],[4228]),([12,42009,153612,395600,602208,933500,1163648,1967616],[]),([12,42009,153612,395600,602208,933500,1163648,1990156],[1284]),([12,42009,153612,395600,602208,933500,1294720,1967616],[]),([12,42009,153612,395600,602208,933756,1163648,1967616],[]),([12,42009,153612,395600,602208,949884,1163648,1967616],[]),([12,42009,153612,395600,602208,999036,1163648,1967616],[]),([12,42009,153612,395600,602208,1048572,1163648,1967616],[]),([12,42009,153612,395600,602208,1163648,1701548,1967616],[3074,6018]),([12,42009,153612,395600,602208,1163648,1701548,1990156],[1284,3074,6018]),([12,42009,153612,395600,602208,1163648,1701612,1967616],[3074,6018]),([12,42009,153612,395600,602208,1163648,1703932,1967616],[]),([12,42009,153612,395600,602208,1163648,1832620,1967616],[3074,6018]),([12,42009,153612,395600,602208,1163648,1834668,1967616],[1286,3074,6018]),([12,42009,153612,395600,602208,1163648,1966076,1967616],[5508,7809]),([12,42009,153612,395600,602208,1163648,1966076,1990156],[1284]),([12,42009,153612,395600,602208,1163648,1967616],[1316,4130,4902,5153]),([12,42009,153612,395600,602208,1163648,1967616,2031612],[]),([12,42009,153612,395600,602208,1163648,1967616,2096892],[7554]),([12,42009,153612,395600,602208,1163648,1967616,2097148],[]),([12,42009,153612,395600,602208,1294720,1494940,1967616],[5506]),([12,42009,153612,395600,602208,1294720,1701548,1967616],[3074,6018]),([12,42009,153612,395600,602208,1294720,1966076,1967616],[5508,7809]),([12,42009,153612,395600,602208,1558992,1701548,1967616],[1796,6018]),([12,42009,153612,396828,602208,866672,1163648,1967616],[1796,4228]),([12,42009,153612,396828,602208,1163648,1964528,1967616],[1796,5508]),([12,42009,153612,396828,602208,1300876,1427920,1967616],[1286,1796,2049]),([12,42009,153612,396828,602208,1300876,1964528,1967616],[1286,1796,2049,2817]),([12,42009,153612,399452,602208,1163648,1427920,1967616],[5508]),([12,42009,153612,399696,602208,933500,1163648,1967616],[]),([12,42009,153612,399696,602208,1163648,1494940,1967616],[5506]),([12,42009,153612,399696,602208,1163648,1697452,1967616],[3075,4097,5761]),([12,42009,153612,399696,602208,1163648,1961980,1967616],[5508,5761,7809]),([12,42009,153612,409212,602208,866672,1163648,1967616],[]),([12,42009,153612,409212,602208,866672,1687936,1967616],[]),([12,42009,153612,409212,602208,1163648,1427920,1967616],[5508]),([12,42009,153612,409212,602208,1163648,1952208,1967616],[5508]),([12,42009,153612,409212,602208,1427920,1687936,1967616],[4230]),([12,42009,153612,409212,602208,1687936,1952208,1967616],[5510]),([12,42009,153612,415836,602208,1163648,1427920,1967616],[2178,3841,5506]),([12,42009,153612,417308,602208,866672,1163648,1967616],[1796,2819]),([12,42009,153612,417308,602208,1163648,1964528,1967616],[2819,3841]),([12,42009,153612,524284,602208,866672,1163648,1967616],[]),([12,42009,153612,524284,602208,1163648,1964528,1967616],[4226]),([12,42009,153612,602144,602208,1163648,1427920,1967616],[3074]),([12,42009,153612,602144,602208,1427920,1832876,1967616],[]),([12,42009,153612,602144,669228,1163648,1427920,1967616],[]),([12,42009,153612,602144,669228,1427920,1832876,1967616],[]),([12,42009,153612,602144,1163648,1427920,1832876,1967616],[]),([12,42009,153612,602144,1163648,1427920,1967616],[1316,4902,5665]),([12,42009,153612,602144,1427920,1832876,1967616],[1316,4902,5921]),([12,42009,153612,602208,602208,800880,1163648,1967616],[]),([12,42009,153612,602208,602208,801136,1163648,1967616],[]),([12,42009,153612,602208,602208,866672,1163648,1967616],[]),([12,42009,153612,602208,602208,1163648,1427920,1967616],[2306,2434]),([12,42009,153612,602208,602220,1163648,1427920,1967616],[3202,5378]),([12,42009,153612,602208,604284,866672,1163648,1967616],[]),([12,42009,153612,602208,604284,1163648,1427920,1967616],[3202]),([12,42009,153612,602208,604284,1427920,1967616,2082688],[3201,4868]),([12,42009,153612,602208,604528,866672,1163648,1967616],[]),([12,42009,153612,602208,620652,866672,1163648,1967616],[3074,4098]),([12,42009,153612,602208,620652,1163648,1427920,1967616],[3202,3841,5378]),([12,42009,153612,602208,635376,866672,1163648,1967616],[]),([12,42009,153612,602208,635376,899568,1163648,1967616],[]),([12,42009,153612,602208,635376,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,651500,866672,1163648,1967616],[3074,4098]),([12,42009,153612,602208,651744,866672,1163648,1967616],[]),([12,42009,153612,602208,651744,915952,1163648,1967616],[]),([12,42009,153612,602208,651744,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,653808,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,653820,866672,1163648,1967616],[]),([12,42009,153612,602208,653820,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,653820,1163648,1964528,1967616],[4482]),([12,42009,153612,602208,653820,1300876,1427920,1967616],[1286,4482]),([12,42009,153612,602208,653820,1427920,1967616,2082688],[3201]),([12,42009,153612,602208,655356,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,661004,1163648,1427920,1967616],[2565]),([12,42009,153612,602208,667692,1163648,1427920,1967616],[]),([12,42009,153612,602208,669228,1163648,1329152,1967616],[5378,7297]),([12,42009,153612,602208,669228,1163648,1427920,1967616],[]),([12,42009,153612,602208,669228,1163648,1427920,1971712],[]),([12,42009,153612,602208,669228,1163648,1427920,1984000],[]),([12,42009,153612,602208,669228,1163648,1427920,1986048],[5121]),([12,42009,153612,602208,669228,1163648,1427920,2033152],[3204,5378]),([12,42009,153612,602208,669228,1163648,1432016,1967616],[]),([12,42009,153612,602208,669228,1163648,1558992,1967616],[]),([12,42009,153612,602208,669228,1163648,1964528,1967616],[3074]),([12,42009,153612,602208,669228,1165696,1427920,1967616],[]),([12,42009,153612,602208,669228,1167744,1427920,1967616],[]),([12,42009,153612,602208,669228,1294720,1427920,1967616],[]),([12,42009,153612,602208,669228,1298828,1427920,1967616],[2817]),([12,42009,153612,602208,669228,1300876,1427920,1967616],[1286,2817]),([12,42009,153612,602208,669228,1300876,1964528,1967616],[1286,2049,2817]),([12,42009,153612,602208,669228,1427920,1700256,1967616],[]),([12,42009,153612,602208,669228,1427920,1832876,1967616],[]),([12,42009,153612,602208,669228,1427920,1834924,1967616],[]),([12,42009,153612,602208,669228,1427920,1967616,2088844],[]),([12,42009,153612,602208,669228,1427920,1979948,2082688],[]),([12,42009,153612,602208,669228,1427920,1990156,2082688],[4868]),([12,42009,153612,602208,669228,1427920,2045536,2082688],[3204]),([12,42009,153612,602208,669804,866672,1163648,1967616],[1284,3074]),([12,42009,153612,602208,669804,1163648,1427920,1967616],[1284])]
noncomputable def k25 : CE := [([12,42009,153612,602208,671356,1163648,1427920,1967616],[]),([12,42009,153612,602208,671356,1425792,1427920,1967616],[]),([12,42009,153612,602208,671356,1427920,1967616,2082688],[4868]),([12,42009,153612,602208,679436,1163648,1427920,1967616],[2565,2946,3841]),([12,42009,153612,602208,685612,1163648,1427920,1967616],[]),([12,42009,153612,602208,686124,1163648,1427920,1967616],[1287,2946,3841]),([12,42009,153612,602208,686188,801136,1163648,1967616],[1286,3074]),([12,42009,153612,602208,686188,866672,1163648,1967616],[1286,3074]),([12,42009,153612,602208,686188,1163648,1427920,1967616],[1287,2946,3841]),([12,42009,153612,602208,687660,1163648,1427920,1967616],[2946,3841]),([12,42009,153612,602208,687660,1163648,1964528,1967616],[3074,3841]),([12,42009,153612,602208,687660,1300876,1427920,1967616],[1286,2817,3841]),([12,42009,153612,602208,687660,1427920,1832876,1967616],[]),([12,42009,153612,602208,687660,1427920,1834924,1967616],[]),([12,42009,153612,602208,687660,1427920,1967616,2082688],[2945,4868]),([12,42009,153612,602208,720828,1163648,1427920,1967616],[2946]),([12,42009,153612,602208,733292,1163648,1427920,1967616],[3202,5378]),([12,42009,153612,602208,734764,1163648,1427920,1967616],[5378]),([12,42009,153612,602208,734828,866672,1163648,1967616],[3074,4098]),([12,42009,153612,602208,734828,1163648,1427920,1967616],[3202,5378]),([12,42009,153612,602208,734828,1163648,1964528,1967616],[3074,5378]),([12,42009,153612,602208,734828,1300876,1427920,1967616],[1286,2817]),([12,42009,153612,602208,734828,1427920,1832876,1967616],[]),([12,42009,153612,602208,735340,866672,1163648,1967616],[1284,3074,4098]),([12,42009,153612,602208,735340,1163648,1427920,1967616],[1287,3202,5378]),([12,42009,153612,602208,749676,866672,1163648,1967616],[3074,4098]),([12,42009,153612,602208,751724,800880,1163648,1967616],[1286,3074,4098]),([12,42009,153612,602208,751724,801136,1163648,1967616],[1286,3074,4098]),([12,42009,153612,602208,751724,866672,1163648,1967616],[1286,3074,4098]),([12,42009,153612,602208,751724,1163648,1362320,1967616],[1287,2946,3202,3841,5378]),([12,42009,153612,602208,751724,1163648,1362384,1967616],[1287,2946,3202,3841,5378]),([12,42009,153612,602208,751724,1163648,1427920,1967616],[1287,2946,3202,3841,5378]),([12,42009,153612,602208,751724,1427920,1832876,1967616],[1286]),([12,42009,153612,602208,753260,1163648,1427920,1967616],[2946,3202,3841,5378]),([12,42009,153612,602208,767660,1163648,1329488,1967616],[4482,5378]),([12,42009,153612,602208,767996,1163648,1329152,1967616],[3202,4482,5378,7297]),([12,42009,153612,602208,767996,1163648,1427920,1967616],[3202,4482]),([12,42009,153612,602208,784044,1163648,1427920,1967616],[4482]),([12,42009,153612,602208,784044,1163648,1915248,1967616],[3074,3201,4482,5378]),([12,42009,153612,602208,784044,1427920,1967616],[4514,4897,5665]),([12,42009,153612,602208,784892,866672,1163648,1967616],[]),([12,42009,153612,602208,784892,1163648,1427920,1967616],[2946,3202,4482]),([12,42009,153612,602208,786428,1163648,1427920,1967616],[2946,3202,4482]),([12,42009,153612,602208,786428,1163648,1964528,1967616],[4482]),([12,42009,153612,602208,786428,1300876,1427920,1967616],[1286,4482]),([12,42009,153612,602208,786428,1425792,1427920,1967616],[2945,3201,4482,5762]),([12,42009,153612,602208,786428,1427920,1967616,2082688],[2945,3201]),([12,42009,153612,602208,792576,933500,1163648,1967616],[3074]),([12,42009,153612,602208,792576,1163648,1494940,1967616],[3074,5250,5764,7811]),([12,42009,153612,602208,792912,933500,1163648,1967616],[]),([12,42009,153612,602208,792912,1163648,1494940,1967616],[5765]),([12,42009,153612,602208,792912,1163648,1568764,1967616],[5764]),([12,42009,153612,602208,800880,800880,1163648,1967616],[]),([12,42009,153612,602208,800880,801136,1163648,1967616],[]),([12,42009,153612,602208,800880,866416,1163648,1967616],[3204]),([12,42009,153612,602208,800880,866672,1163648,1967616],[]),([12,42009,153612,602208,800880,933500,1163648,1967616],[]),([12,42009,153612,602208,800880,948348,1163648,1967616],[]),([12,42009,153612,602208,800880,949884,1163648,1967616],[]),([12,42009,153612,602208,800880,999036,1163648,1967616],[]),([12,42009,153612,602208,800880,999292,1163648,1967616],[]),([12,42009,153612,602208,800880,1014140,1163648,1967616],[]),([12,42009,153612,602208,800880,1163648,1427920,1967616],[5764]),([12,42009,153612,602208,800880,1163648,1700320,1967616],[3074]),([12,42009,153612,602208,800880,1163648,1964528,1967616],[]),([12,42009,153612,602208,800880,1163648,1967616],[1316,2114,4902,5411]),([12,42009,153612,602208,800880,1163648,1967616,1990156],[2051,5378,6404,6914]),([12,42009,153612,602208,800880,1163648,1967616,2031356],[]),([12,42009,153612,602208,800880,1163648,1967616,2097148],[]),([12,42009,153612,602208,801136,801136,1163648,1967616],[]),([12,42009,153612,602208,801136,866672,1163648,1967616],[]),([12,42009,153612,602208,801136,933500,1163648,1967616],[]),([12,42009,153612,602208,801136,933756,1163648,1967616],[]),([12,42009,153612,602208,801136,948604,1163648,1967616],[]),([12,42009,153612,602208,801136,949884,1163648,1967616],[]),([12,42009,153612,602208,801136,999036,1163648,1967616],[]),([12,42009,153612,602208,801136,1163648,1700320,1967616],[]),([12,42009,153612,602208,801136,1163648,1964528,1967616],[]),([12,42009,153612,602208,801136,1163648,1967616],[1316,2114,4902,5411]),([12,42009,153612,602208,801136,1163648,1967616,1990156],[2051,5378,6404,6914]),([12,42009,153612,602208,801136,1163648,1967616,2031612],[]),([12,42009,153612,602208,801136,1163648,1967616,2097148],[]),([12,42009,153612,602208,802428,866672,1163648,1967616],[]),([12,42009,153612,602208,802428,866672,1294720,1967616],[]),([12,42009,153612,602208,802428,1163648,1427920,1967616],[5764]),([12,42009,153612,602208,802428,1163648,1558992,1967616],[5764]),([12,42009,153612,602208,802428,1294720,1427920,1967616],[5764]),([12,42009,153612,602208,802428,1294720,1558992,1967616],[5764]),([12,42009,153612,602208,866416,866672,1163648,1967616],[]),([12,42009,153612,602208,866416,933500,1163648,1967616],[4228]),([12,42009,153612,602208,866416,999036,1163648,1967616],[]),([12,42009,153612,602208,866416,1163648,1427920,1967616],[3202]),([12,42009,153612,602208,866416,1163648,1967616],[1316,2114,4130,4902,5411]),([12,42009,153612,602208,866672,866672,1163648,1967616],[]),([12,42009,153612,602208,866672,866684,1163648,1967616],[]),([12,42009,153612,602208,866672,883068,1163648,1967616],[]),([12,42009,153612,602208,866672,899568,1163648,1967616],[]),([12,42009,153612,602208,866672,915952,1163648,1967616],[]),([12,42009,153612,602208,866672,915964,1163648,1967616],[]),([12,42009,153612,602208,866672,917500,1163648,1967616],[]),([12,42009,153612,602208,866672,925196,1163648,1967616],[2051,3588,4098,6914]),([12,42009,153612,602208,866672,931964,1163648,1967616],[]),([12,42009,153612,602208,866672,933500,1163648,1967616],[]),([12,42009,153612,602208,866672,933500,1163648,1971712],[]),([12,42009,153612,602208,866672,933500,1163648,1973760],[2050]),([12,42009,153612,602208,866672,933500,1163648,1984000],[]),([12,42009,153612,602208,866672,933500,1163648,2033152],[4228]),([12,42009,153612,602208,866672,933500,1167744,1967616],[]),([12,42009,153612,602208,866672,933500,1169792,1967616],[2049]),([12,42009,153612,602208,866672,933500,1294720,1967616],[]),([12,42009,153612,602208,866672,941580,1163648,1967616],[2051,3588,4098,6914]),([12,42009,153612,602208,866672,948348,1163648,1967616],[]),([12,42009,153612,602208,866672,949884,1163648,1967616],[]),([12,42009,153612,602208,866672,982780,1163648,1967616],[]),([12,42009,153612,602208,866672,983036,1163648,1967616],[]),([12,42009,153612,602208,866672,997756,1163648,1967616],[]),([12,42009,153612,602208,866672,999036,1163648,1967616],[]),([12,42009,153612,602208,866672,999292,1163648,1967616],[]),([12,42009,153612,602208,866672,1014140,1163648,1967616],[]),([12,42009,153612,602208,866672,1015420,1163648,1967616],[]),([12,42009,153612,602208,866672,1015676,1163648,1967616],[]),([12,42009,153612,602208,866672,1032188,1163648,1967616],[]),([12,42009,153612,602208,866672,1047036,1163648,1967616],[]),([12,42009,153612,602208,866672,1048572,1163648,1967616],[]),([12,42009,153612,602208,866672,1163648,1441788,1967616],[]),([12,42009,153612,602208,866672,1163648,1461772,1967616],[4868,5378,5764]),([12,42009,153612,602208,866672,1163648,1465868,1967616],[2051,4868,5378]),([12,42009,153612,602208,866672,1163648,1494684,1967616],[5764]),([12,42009,153612,602208,866672,1163648,1494940,1967616],[5765]),([12,42009,153612,602208,866672,1163648,1494940,1971712],[2051,5250,5765]),([12,42009,153612,602208,866672,1163648,1494940,1973760],[2050,5250,5765]),([12,42009,153612,602208,866672,1163648,1494940,1984000],[5765]),([12,42009,153612,602208,866672,1163648,1494940,2033152],[5765,6021]),([12,42009,153612,602208,866672,1163648,1499036,1967616],[2051]),([12,42009,153612,602208,866672,1163648,1507324,1967616],[]),([12,42009,153612,602208,866672,1163648,1560476,1967616],[5762]),([12,42009,153612,602208,866672,1163648,1564572,1967616],[2051]),([12,42009,153612,602208,866672,1163648,1568764,1967616],[]),([12,42009,153612,602208,866672,1163648,1572860,1967616],[]),([12,42009,153612,602208,866672,1163648,1700064,1967616],[3074,5378,6018]),([12,42009,153612,602208,866672,1163648,1700320,1967616],[]),([12,42009,153612,602208,866672,1163648,1702396,1967616],[]),([12,42009,153612,602208,866672,1163648,1767084,1967616],[5378]),([12,42009,153612,602208,866672,1163648,1832684,1967616],[3074,5378,6018]),([12,42009,153612,602208,866672,1163648,1832940,1967616],[]),([12,42009,153612,602208,866672,1163648,1834732,1967616],[3074,5378,6018]),([12,42009,153612,602208,866672,1163648,1835004,1967616],[]),([12,42009,153612,602208,866672,1163648,1964528,1967616],[]),([12,42009,153612,602208,866672,1163648,1964540,1967616],[]),([12,42009,153612,602208,866672,1163648,1966076,1967616],[])]
noncomputable def k26 : CE := [([12,42009,153612,602208,866672,1163648,1967616],[2114,4897,5411]),([12,42009,153612,602208,866672,1163648,1967616,1990156],[2051,5378,6404,6914]),([12,42009,153612,602208,866672,1163648,1967616,1998460],[]),([12,42009,153612,602208,866672,1163648,1967616,2023052],[2051,5378,6914]),([12,42009,153612,602208,866672,1163648,1967616,2023324],[2051,5378]),([12,42009,153612,602208,866672,1163648,1967616,2031356],[]),([12,42009,153612,602208,866672,1163648,1967616,2031612],[]),([12,42009,153612,602208,866672,1163648,1967616,2096892],[7554]),([12,42009,153612,602208,866672,1163648,1967616,2097148],[]),([12,42009,153612,602208,866672,1163648,1971712,2093052],[6786,7041]),([12,42009,153612,602208,866672,1163648,1973760,2091004],[2051,6786,7041,7297]),([12,42009,153612,602208,866672,1163648,1982076,2082688],[]),([12,42009,153612,602208,866672,1163648,1984000,2080764],[7555]),([12,42009,153612,602208,866672,1163648,1990156,2074608],[2051]),([12,42009,153612,602208,866672,1163648,2016908,2045536],[3074,6914]),([12,42009,153612,602208,866672,1163648,2016908,2047856],[]),([12,42009,153612,602208,866672,1163648,2019228,2045536],[3074,6914]),([12,42009,153612,602208,866672,1163648,2031356,2033408],[]),([12,42009,153612,602208,866672,1163648,2031612,2033152],[5508,6021]),([12,42009,153612,602208,866672,1167744,1230476,1967616],[5378]),([12,42009,153612,602208,866672,1167744,1494940,1967616],[2049,5250,5765]),([12,42009,153612,602208,866672,1167744,1967616,2093052],[6786,7041,7297]),([12,42009,153612,602208,866672,1169792,1230476,1967616],[2051,5378]),([12,42009,153612,602208,866672,1169792,1494940,1967616],[2049,5250,5765]),([12,42009,153612,602208,866672,1169792,1967616,2091004],[2051,7041,7297]),([12,42009,153612,602208,866672,1178108,1967616,2082688],[4868,5378]),([12,42009,153612,602208,866672,1230476,1294720,1967616],[4098]),([12,42009,153612,602208,866672,1294720,1494940,1967616],[5765]),([12,42009,153612,602208,866672,1294720,1966076,1967616],[7809]),([12,42009,153612,602208,866672,1296268,1700320,1967616],[]),([12,42009,153612,602208,866672,1296268,1964528,1967616],[]),([12,42009,153612,602208,866672,1560476,1700320,1967616],[4482]),([12,42009,153612,602208,883056,933500,1163648,1967616],[]),([12,42009,153612,602208,883056,1163648,1494940,1967616],[5762]),([12,42009,153612,602208,883056,1163648,1967616,2080764],[7555]),([12,42009,153612,602208,899568,1163648,1967616],[2114,4897,5411]),([12,42009,153612,602208,899568,1163648,1967616,1990156],[2051,5378,6404,6914]),([12,42009,153612,602208,915952,1163648,1967616],[2114,4897,5411]),([12,42009,153612,602208,915964,1163648,1964528,1967616],[4482]),([12,42009,153612,602208,915964,1163648,1967616,2047856],[]),([12,42009,153612,602208,917500,1300876,1427920,1967616],[1286,4482,5762]),([12,42009,153612,602208,933500,997744,1163648,1967616],[]),([12,42009,153612,602208,933500,1163648,1558992,1967616],[]),([12,42009,153612,602208,933500,1163648,1964528,1967616],[]),([12,42009,153612,602208,933500,1165696,1427920,1967616],[5764]),([12,42009,153612,602208,933500,1167744,1427920,1967616],[5764]),([12,42009,153612,602208,933500,1167744,1432016,1967616],[]),([12,42009,153612,602208,933500,1294720,1427920,1967616],[5764]),([12,42009,153612,602208,933500,1294720,1558992,1967616],[]),([12,42009,153612,602208,933500,1300876,1427920,1967616],[1286,2817]),([12,42009,153612,602208,933500,1300876,1964528,1967616],[1286,2049,2817]),([12,42009,153612,602208,933500,1427920,1967616,2088844],[]),([12,42009,153612,602208,933500,1427920,1982076,2082688],[]),([12,42009,153612,602208,933500,1427920,1990156,2082688],[4868]),([12,42009,153612,602208,933500,1427920,2045536,2082688],[3204]),([12,42009,153612,602208,949884,1163648,1964528,1967616],[3841]),([12,42009,153612,602208,949884,1300876,1427920,1967616],[1286,2817,3841]),([12,42009,153612,602208,949884,1427920,1967616,2082688],[2945,4868]),([12,42009,153612,602208,997744,1163648,1701548,1967616],[3074,5378,6018]),([12,42009,153612,602208,997744,1163648,1966076,1967616],[7809]),([12,42009,153612,602208,999036,1163648,1964528,1967616],[]),([12,42009,153612,602208,999036,1300876,1427920,1967616],[1286,2817]),([12,42009,153612,602208,999292,1163648,1964528,1967616],[]),([12,42009,153612,602208,1048572,1163648,1964528,1967616],[4482]),([12,42009,153612,602208,1048572,1300876,1427920,1967616],[1286,4482,5762]),([12,42009,153612,602208,1048572,1427920,1967616,2082688],[2945,3201]),([12,42009,153612,602208,1163648,1700320,1964528,1967616],[]),([12,42009,153612,602208,1163648,1702396,1964528,1967616],[]),([12,42009,153612,602208,1163648,1832684,1964528,1967616],[4482]),([12,42009,153612,602208,1163648,1832940,1964528,1967616],[]),([12,42009,153612,602208,1163648,1964528,1964540,1967616],[]),([12,42009,153612,602208,1163648,1964528,1966076,1967616],[]),([12,42009,153612,602208,1163648,1964528,1967616],[2114,4897,5411,5665]),([12,42009,153612,602208,1163648,1964528,1967616,2031356],[]),([12,42009,153612,602208,1163648,1964528,1967616,2031612],[]),([12,42009,153612,602208,1163648,1964528,1967616,2097148],[]),([12,42009,153612,602208,1165696,1427920,1494940,1967616],[]),([12,42009,153612,602208,1167744,1427920,1494940,1967616],[5250]),([12,42009,153612,602208,1167744,1427920,1967616,2093052],[6786,7041,7298]),([12,42009,153612,602208,1167744,1432016,1494940,1967616],[5250]),([12,42009,153612,602208,1167744,1432016,1967616,2093052],[6786,7041,7298]),([12,42009,153612,602208,1169804,1427920,1967616],[2081,4897]),([12,42009,153612,602208,1175980,1427920,1967616],[4514,4897,5665]),([12,42009,153612,602208,1175980,1427920,1967616,2084816],[7298]),([12,42009,153612,602208,1178108,1300876,1427920,1967616],[1281]),([12,42009,153612,602208,1178108,1427920,1967616,2082688],[7298]),([12,42009,153612,602208,1230476,1296268,1964528,1967616],[]),([12,42009,153612,602208,1230476,1300876,1964528,1967616],[1287,2051]),([12,42009,153612,602208,1231244,1300876,1427920,1967616],[1285,2946]),([12,42009,153612,602208,1294720,1427920,1494940,1967616],[]),([12,42009,153612,602208,1294720,1427920,1966076,1967616],[5762,7809]),([12,42009,153612,602208,1294720,1494940,1558992,1967616],[]),([12,42009,153612,602208,1294720,1558992,1966076,1967616],[5762,7809]),([12,42009,153612,602208,1296268,1427920,1964528,1967616],[5762]),([12,42009,153612,602208,1296268,1427920,1967616],[4514,4897,5665]),([12,42009,153612,602208,1296268,1700320,1964528,1967616],[]),([12,42009,153612,602208,1296268,1964528,1967616],[2114,4897,5411,5665]),([12,42009,153612,602208,1296780,1427920,1494940,1967616],[1285]),([12,42009,153612,602208,1296780,1427920,1967616],[1281,4897,5153,5665]),([12,42009,153612,602208,1298828,1427920,1967616],[4002,4514,4897,5153,5665]),([12,42009,153612,602208,1300876,1309180,1427920,1967616],[1286]),([12,42009,153612,602208,1300876,1362320,1427920,1967616],[1287,3970,5250]),([12,42009,153612,602208,1300876,1362320,1494940,1967616],[1287,5250]),([12,42009,153612,602208,1300876,1362320,1967616],[1287,1317,2081,4002,4901,5153]),([12,42009,153612,602208,1300876,1362384,1494940,1967616],[1287,5250]),([12,42009,153612,602208,1300876,1362384,1967616],[1287,1317,2081,4002,4901,5153]),([12,42009,153612,602208,1300876,1427920,1440252,1967616],[1281]),([12,42009,153612,602208,1300876,1427920,1494940,1967616],[1287,5250]),([12,42009,153612,602208,1300876,1427920,1499036,1967616],[1286]),([12,42009,153612,602208,1300876,1427920,1560476,1967616],[1281,5250]),([12,42009,153612,602208,1300876,1427920,1560540,1967616],[1281,5250]),([12,42009,153612,602208,1300876,1427920,1564572,1967616],[1281]),([12,42009,153612,602208,1300876,1427920,1572860,1967616],[1281]),([12,42009,153612,602208,1300876,1427920,1832876,1967616],[1281]),([12,42009,153612,602208,1300876,1427920,1834924,1967616],[1286]),([12,42009,153612,602208,1300876,1427920,1961968,1967616],[1281,5250]),([12,42009,153612,602208,1300876,1427920,1966076,1967616],[1281]),([12,42009,153612,602208,1300876,1427920,1967616],[1281,2081,4002,4897,5153]),([12,42009,153612,602208,1300876,1427920,1967616,2019228],[1281,6786]),([12,42009,153612,602208,1300876,1427920,1967616,2027516],[1281,6786]),([12,42009,153612,602208,1300876,1427920,1967616,2031548],[1286]),([12,42009,153612,602208,1300876,1427920,1967616,2031612],[1286]),([12,42009,153612,602208,1300876,1427920,1967616,2093052],[1281,6786]),([12,42009,153612,602208,1300876,1427920,1967616,2097148],[1281]),([12,42009,153612,602208,1300876,1494940,1964528,1967616],[1287,2051,3970]),([12,42009,153612,602208,1308332,1952208,1967616],[4515,4897,5665]),([12,42009,153612,602208,1427920,1427920,1832876,1967616],[5762]),([12,42009,153612,602208,1427920,1494940,1967616,2088844],[3970,6019]),([12,42009,153612,602208,1427920,1494940,1990156,2082688],[3970,4869]),([12,42009,153612,602208,1427920,1494940,2045536,2082688],[3074,6019]),([12,42009,153612,602208,1427920,1560476,1700320,1967616],[4226,6018]),([12,42009,153612,602208,1427920,1563100,1832876,1967616],[]),([12,42009,153612,602208,1427920,1700256,1967616],[4546,4897,5409,5921]),([12,42009,153612,602208,1427920,1700320,1832876,1967616],[]),([12,42009,153612,602208,1427920,1832876,1832876,1967616],[]),([12,42009,153612,602208,1427920,1832876,1832940,1967616],[]),([12,42009,153612,602208,1427920,1832876,1834924,1967616],[]),([12,42009,153612,602208,1427920,1832876,1964528,1967616],[]),([12,42009,153612,602208,1427920,1832876,1967616],[4546,4897,5921]),([12,42009,153612,602208,1427920,1832876,1967616,1990156],[6404]),([12,42009,153612,602208,1427920,1832876,1967616,2097148],[]),([12,42009,153612,602208,1427920,1834924,1967616],[4897]),([12,42009,153612,602208,1427920,1979948,2082688],[4547,6049]),([12,42009,153612,602208,1427920,1982076,2082688],[6049]),([12,42009,153612,602208,1558992,1701548,1967616],[4546,4897,5153,5921]),([12,42009,153612,602208,1560476,1700320,1964528,1967616],[]),([12,42009,395600,602208,933500,1163648,1990156],[3268,4900]),([12,42009,395600,602208,1163648,1701548,1990156],[1316,2050,2114,2850,4418,4482,4514,4546,4900]),([12,42009,395600,602208,1163648,1966076,1990156],[2850,4036,4546,4900]),([12,46104,129532,153612,268624,602208,1163648,1967616],[])]
noncomputable def k27 : CE := [([12,46104,129532,153612,602208,866672,1163648,1967616],[]),([12,46104,129532,153612,602208,1163648,1427920,1967616],[]),([12,46104,153612,268624,602208,1163648,1494940,1967616],[5509]),([12,46104,153612,268624,602208,1163648,1828524,1967616],[5764]),([12,46104,153612,268624,602208,1163648,1967616,2093052],[7044,7300]),([12,46104,153612,310616,602208,1163648,1967616,2051044],[1284,7044]),([12,46104,153612,602208,669228,1163648,1427920,1967616],[]),([12,46104,153612,602208,866672,933500,1163648,1967616],[]),([12,46104,153612,602208,866672,1163648,1230476,1967616],[]),([12,46104,153612,602208,866672,1163648,1494940,1967616],[5765]),([12,46104,153612,602208,866672,1163648,1943536,1967616],[4993]),([12,46104,153612,602208,866672,1163648,1967616,2051044],[1286,4868]),([12,46104,153612,602208,866672,1163648,1967616,2093052],[]),([12,46104,153612,602208,933500,1163648,1427920,1967616],[5764]),([12,46104,153612,602208,1163648,1427920,1494940,1967616],[]),([12,46104,153612,602208,1163648,1427920,1943536,1967616],[4995]),([12,46104,153612,602208,1163648,1427920,1967616,2051044],[1287,4869]),([12,46104,153612,602208,1163648,1427920,1967616,2093052],[6530]),([12,48152,129532,153612,602208,866672,1163648,1967616],[]),([12,48152,153612,602208,866672,933500,1163648,1967616],[]),([12,48152,153612,602208,866672,1163648,1230476,1967616],[]),([12,48152,153612,602208,866672,1163648,1494940,1967616],[5765]),([12,48152,153612,602208,866672,1163648,1943536,1967616],[4993]),([12,48152,153612,602208,866672,1163648,1967616,2048996],[4868]),([12,48152,153612,602208,866672,1163648,1967616,2091004],[]),([12,63516,129532,153612,602208,866672,1163648,1967616],[3074]),([12,63516,153612,195612,602208,866672,1163648,1967616],[2818]),([12,63516,153612,602208,866672,1163648,1967616],[2050,2114,3874,4900,5410]),([12,64540,129532,153612,602208,866672,1163648,1967616],[3074]),([12,64540,153612,602208,866672,1163648,1967616],[2050,2114,3874,4900,5410]),([12,66016,153612,195612,330224,602208,1163648,1967616],[1286,2564]),([12,66016,153612,195612,602208,866672,1163648,1967616],[1286,2819]),([12,66016,153612,330224,602208,1163648,1967616,2031132],[1286,1796,4868]),([12,66016,153612,602208,866672,1163648,1967616,2031132],[1286,2051,2564,4868,5378]),([12,69728,153612,334192,602208,1163648,1967616,2008600],[1796,2564,4868]),([12,69728,153612,602208,866672,1163648,1967616,2008600],[1793,2561,4868]),([12,69728,153612,602208,1163648,1427920,1967616,2008600],[1795,3587,4869]),([12,72032,153612,602208,866672,1163648,1967616,2008600],[2561,4868]),([12,77920,129532,153612,195612,866672,1163648,1967616],[]),([12,77920,129532,153612,866672,1163648,1967616,2008600],[4866]),([12,77920,153612,195612,342384,602208,1163648,1967616],[1284,2564,3588]),([12,77920,153612,195612,602208,866672,1163648,1967616],[1286]),([12,77920,153612,195612,602208,1163648,1427920,1967616],[1287,2562,4866]),([12,77920,153612,195612,866672,1163648,1967616],[1287,4898]),([12,77920,153612,342384,602208,1163648,1967616,2008600],[1796,2564,4868]),([12,77920,153612,602208,866672,1163648,1967616,2008600],[1793,2561,4868]),([12,77920,153612,602208,1163648,1427920,1967616,2008600],[1795,3587,4869]),([12,77920,153612,866672,1163648,1967616,2008600],[1315,3586,3619]),([12,80240,153612,195612,602208,866672,1163648,1967616],[]),([12,80240,153612,602208,866672,1163648,1967616,2008600],[2561]),([12,88548,153612,330064,602208,1163648,1967616,2008600],[4868]),([12,88548,153612,334192,602208,1163648,1967616,2008600],[4868]),([12,88548,153612,395600,602208,1163648,1967616,2008600],[4868]),([12,88548,153612,395608,602208,1163648,1967616,2008600],[4868]),([12,88548,153612,602208,866672,1163648,1967616,2008600],[4868,5378]),([12,88548,153612,602208,866672,1163648,1967616,2031132],[1286,2050,5378]),([12,88548,153612,602208,866672,1163648,2008600,2045536],[1794,3074,6404,6914]),([12,88548,153612,602208,866672,1163648,2008600,2056164],[6404]),([12,88548,153612,602208,866672,1163648,2008600,2082688],[3588,6404]),([12,88548,153612,602208,1163648,1964528,1967616,2008600],[5378]),([12,88548,153612,602208,1300876,1427920,1967616,2008600],[]),([12,88548,153612,602208,1427920,1967616,2008600,2082688],[3588]),([12,88548,153612,602208,1427920,2008600,2082688],[2722,5026]),([12,106992,153612,195612,371184,602208,1163648,1967616],[]),([12,106992,153612,195612,602208,866672,1163648,1967616],[2819]),([12,106992,153612,371184,602208,1163648,1967616,2031132],[]),([12,106992,153612,602208,866672,1163648,1967616,2031132],[2051,2564,5378]),([12,107544,129532,153612,330064,602208,1163648,1967616],[]),([12,107544,129532,153612,602208,866672,1163648,1967616],[]),([12,107544,153612,330064,602208,933500,1163648,1967616],[4228,4484]),([12,107544,153612,330064,602208,1163648,1767084,1967616],[3074,5764,6021]),([12,107544,153612,330064,602208,1163648,1967616,1989604],[1286,4868,7044,7809]),([12,107544,153612,330064,602208,1163648,1967616,2031612],[7044,7300,7557]),([12,107544,153612,372056,602208,1163648,1967616,1989604],[1281,7044]),([12,107544,153612,602208,866672,933500,1163648,1967616],[4228,4484]),([12,107544,153612,602208,866672,1163648,1494940,1967616],[5765,6021]),([12,107544,153612,602208,866672,1163648,1967616,1989604],[1286,4868,6914,7300,7809]),([12,107544,153612,602208,866672,1163648,1967616,2031612],[7044,7300,7557]),([12,107608,153612,602208,1163648,1427920,1967616,2031548],[6530,7044]),([12,129532,153612,173080,602208,866672,1163648,1967616],[]),([12,129532,153612,195612,330064,602208,1163648,1967616],[]),([12,129532,153612,195612,342384,602208,1163648,1967616],[]),([12,129532,153612,195612,602208,866672,1163648,1967616],[2818]),([12,129532,153612,195612,602208,1163648,1964528,1967616],[2818,3714]),([12,129532,153612,195612,602208,1300876,1427920,1967616],[1286,3714]),([12,129532,153612,195612,602208,1427920,1967616,2082688],[6530]),([12,129532,153612,330064,602208,1163648,1967616,2008600],[]),([12,129532,153612,342384,602208,1163648,1967616,2008600],[]),([12,129532,153612,602208,866672,1163648,1967616,2008600],[5378]),([12,129532,153612,602208,866672,1163648,1967616,2031132],[2050,5378]),([12,129532,153612,602208,866672,1163648,2008600,2045536],[1794,3074,6914]),([12,129532,153612,602208,866672,1163648,2008600,2082688],[3588]),([12,129532,153612,602208,1163648,1964528,1967616,2008600],[2690,5378]),([12,129532,153612,602208,1300876,1427920,1967616,2008600],[2690]),([12,129532,153612,602208,1427920,1967616,2008600,2082688],[6530]),([12,129532,153612,602208,1427920,2008600,2082688],[2722,5026]),([12,129532,195612,602208,751724,866672,1163648,1967616],[1795,3074,4098]),([12,129532,195612,602208,751724,1163648,1427920,1967616],[3714,5378]),([12,129532,195612,602208,1300876,1427920,1967616],[1318,1830,2598,2722,3617,3746,4897,5025]),([12,153612,173080,437592,602208,1163648,1924068,1967616],[5508]),([12,153612,173080,602208,866672,1163648,1924068,1967616],[]),([12,153612,173080,602208,866672,1163648,1966076,1967616],[]),([12,153612,173596,602208,866672,1163648,1964528,1967616],[]),([12,153612,173596,602208,866672,1163648,1967616],[1348,1858,5158,5411]),([12,153612,173596,602208,1163648,1700320,1964528,1967616],[]),([12,153612,173596,602208,1163648,1964528,1967616],[1858,5153,5411,5665]),([12,153612,177180,602208,1163648,1427920,1967616],[1346,5159]),([12,153612,179228,602208,866672,1163648,1967616],[1799,1828,5158]),([12,153612,179228,602208,1163648,1427920,1967616],[1346,1831,5159]),([12,153612,195612,260604,602208,866672,1163648,1967616],[2567]),([12,153612,195612,261628,602208,866672,1163648,1967616],[2567]),([12,153612,195612,371184,602208,1163648,1967616],[2593,3619,4130]),([12,153612,195612,371184,602208,1163648,1967616,1990156],[4996,7044]),([12,153612,195612,602208,653820,866672,1163648,1967616],[1795]),([12,153612,195612,602208,653820,1163648,1427920,1967616],[2946,3202,3590,4482]),([12,153612,195612,602208,687660,1163648,1427920,1967616],[2690,3590]),([12,153612,195612,602208,720444,1163648,1427920,1967616],[2690,2946,3590]),([12,153612,195612,602208,734828,1163648,1427920,1967616],[3202,3590,5378]),([12,153612,195612,602208,786428,1163648,1427920,1967616],[2690,2946,3202,3590,4482]),([12,153612,195612,602208,866672,915964,1163648,1967616],[1795]),([12,153612,195612,602208,866672,1048572,1163648,1967616],[1795]),([12,153612,195612,602208,866672,1163648,1499036,1967616],[1799,5764]),([12,153612,195612,602208,866672,1163648,1507228,1967616],[1799,5764]),([12,153612,195612,602208,866672,1163648,1560476,1967616],[1799,4997,5765]),([12,153612,195612,602208,866672,1163648,1572860,1967616],[1799,5764]),([12,153612,195612,602208,866672,1163648,1832684,1967616],[1795,3074,5378,6021]),([12,153612,195612,602208,866672,1163648,1950688,1967616],[1795,3590,4870]),([12,153612,195612,602208,866672,1163648,1959920,1967616],[1795,3590,5250,5505]),([12,153612,195612,602208,866672,1163648,1965052,1967616],[1795]),([12,153612,195612,602208,866672,1163648,1966076,1967616],[1795]),([12,153612,195612,602208,866672,1163648,1967616,2082796],[1795]),([12,153612,195612,602208,866672,1163648,1967616,2084860],[1799,6533,7302]),([12,153612,195612,602208,866672,1163648,1967616,2093052],[1795,6533,6786,7041,7302]),([12,153612,195612,602208,866672,1163648,1967616,2097148],[1795]),([12,153612,195612,602208,1427920,1832876,1967616],[1830,4260,4546,5156]),([12,153612,371184,602208,1163648,1967616,1990156,2031132],[3716,5252,6788]),([12,153612,371184,602208,1163648,1967616,2031132],[1825,2084,2595,2853,4418,5284]),([13,0,42008,153612,264529,602208,1163648,1967616],[]),([13,0,42009,65536,153612,264529,1700320,1967616],[2052,3073,3588]),([13,0,42009,153612,264529,602208,1163648,1967616],[2564]),([13,0,42009,153612,264529,602208,1163648,1971712],[2564]),([13,0,42009,153612,264529,602208,1163648,2033152],[2564]),([13,0,42009,153612,268624,602208,1163648,1967616],[]),([13,0,42009,153612,330064,602208,1163648,1967616],[]),([13,0,42009,153612,395600,602208,1163648,1967616],[]),([13,0,42009,153612,602208,866672,1163648,1967616],[]),([13,8,107544,153612,264529,602208,1163648,1967616],[6,1284,1796,2564,3589,4868,6404]),([13,8,153612,264529,566296,602208,1163648,1967616],[6,1286,1796,2566,3591,4870,6406]),([13,2048,42009,153612,330064,602208,1163648,1967616],[1,3586]),([13,2048,42009,153612,602208,788816,1163648,1967616],[1,1793,2561,3585,4865])]
noncomputable def k28 : CE := [([13,4096,42008,153612,264529,602208,1163648,1967616],[3,1284]),([13,4096,42009,65536,153612,264529,1700320,1967616],[3,1284,2052]),([13,4096,42009,147456,264529,602208,1163648,1967616],[1285,4100,4869,6405]),([13,4096,42009,153612,264529,602208,1163648,1967616],[3,1284,4868]),([13,4096,42009,153612,264529,602208,1163648,1971712],[1284]),([13,4096,42009,153612,264529,602208,1163648,1984000],[2,1284,1794,3586]),([13,4096,42009,153612,264529,602208,1163648,2033152],[2,1284]),([13,4096,42009,153612,264529,602208,1167744,1971712],[1284]),([13,4096,42009,153612,264529,618592,1163648,1967616],[7,1285,1797,3589,6402]),([13,4096,42009,153612,264529,733280,1163648,1967616],[7,1285,1797,3589,4866,6402,6916]),([13,4096,42009,153612,264529,751724,1163648,1967616],[4866,6402]),([13,4096,42009,153612,264529,751724,1163648,1971712],[1285,1794,3586,4866,6402]),([13,4096,42009,153612,264529,751724,1167744,1967616],[1284,1794,3586,4866,6402]),([13,4096,42009,153612,264529,1163648,1650784,1967616],[7,1285,1799,3585,4871,6402]),([13,4096,42009,153612,268624,602208,1163648,1967616],[]),([13,4096,42009,153612,268624,602208,1163648,1971712],[]),([13,4096,42009,153612,268624,602208,1163648,1974096],[]),([13,4096,42009,153612,268624,602208,1167744,1967616],[1284]),([13,4096,42009,153612,268624,602208,1432016,1967616],[1284]),([13,4096,42009,153612,268624,751724,1163648,1967616],[]),([13,4096,42009,153612,268624,866672,1163648,1967616],[]),([13,4096,42009,153612,280912,602208,1163648,1967616],[2,1794,3586,4866,6402]),([13,4096,42009,153612,330064,602208,1163648,1967616],[3]),([13,4096,42009,153612,395600,602208,1163648,1967616],[3]),([13,4096,42009,153612,602208,788816,1163648,1967616],[1,1286,1793,2561,4865]),([13,4096,42009,153612,602208,866672,1163648,1967616],[1]),([13,4096,42009,153612,602208,866672,1163648,1971712],[]),([13,4096,42009,153612,602208,866672,1167744,1967616],[]),([13,4096,42009,153612,602208,1163648,1313104,1967616],[3,1795,2563,3587,4865,6402]),([13,4096,42009,153612,602208,1163648,1427920,1967616],[3,1794,2562,4866,6402]),([13,4096,42009,153612,602208,1163648,1427920,1971712],[2,1794,2562,4866,6402]),([13,4096,42009,153612,602208,1163648,1432016,1967616],[2,1794,2562,4866,6402]),([13,4096,42009,153612,602208,1163648,1964528,1967616],[3]),([13,4096,42009,153612,602208,1167744,1427920,1967616],[]),([13,4096,42009,153612,602208,1167744,1432016,1967616],[]),([13,4096,42009,153612,602208,1300876,1427920,1967616],[2052]),([13,4096,42009,153612,602208,1427920,1967616,2082688],[1,1793,2561,3585,6401]),([13,4096,42009,153612,751724,866672,1163648,1967616],[3,1794,2562,3586,4866,6402]),([13,4096,42009,153612,751724,1163648,1427920,1967616],[3586,4866,6402]),([13,4096,42009,153612,866672,1163648,1967616,2045536],[3,1795,2563,3586,4866,6403]),([13,4096,42009,264529,751724,1163648,1300876,1967616],[1795,3587,6405]),([13,4096,42009,264529,751724,1163648,1700320,1967616],[1287,3587,6407]),([13,4096,42009,268624,416092,602208,1163648,1967616],[1284,4865]),([13,4096,42009,268624,602208,751724,1163648,1967616],[1284,4865]),([13,4096,42009,602208,751724,866672,1163648,1967616],[4865,6401]),([13,4096,42009,602208,751724,1163648,1427920,1967616],[3585,6401]),([13,4096,42009,602208,866672,1014140,1163648,1967616],[4865,6401]),([13,4096,46104,153612,268624,602208,1163648,1967616],[4868]),([13,4096,46104,153612,310616,602208,1163648,1967616],[]),([13,4096,46104,153612,602208,866672,1163648,1967616],[]),([13,4096,46104,153612,602208,1163648,1427920,1967616],[]),([13,4096,153612,195612,602208,866672,1163648,1967616],[4868]),([13,4096,153612,195612,602208,1163648,1427920,1967616],[5,1282,1794,2562,3844,4866,6402]),([13,4096,153612,602208,1163648,1427920,1967616,2008600],[3,1283,1795,2561,3587,4869,6407]),([13,4104,46104,153612,264529,602208,1163648,1967616],[4,1284,1796,4868,6404]),([13,6144,42009,153612,268624,602208,1163648,1967616],[1284]),([13,6144,42009,153612,602208,786432,1163648,1967616],[2561,4865,6401]),([13,6144,42009,153612,602208,866672,1163648,1967616],[3,2562]),([13,6144,42009,153612,602208,866672,1163648,1973760],[2562]),([13,6144,42009,153612,602208,866672,1169792,1967616],[]),([13,6144,42009,153612,602208,1014140,1163648,1967616],[2562]),([13,6144,42009,153612,602208,1163648,1964528,1967616],[3,2562]),([13,6144,42009,153612,604256,866672,1163648,1967616],[3,1794,2562,3586,6402]),([13,6144,42009,153612,751724,866672,1163648,1967616],[3,1794,2562,3586,4866,6402]),([13,6144,42009,153612,866672,1163648,1967616,2045536],[3,1795,2563,3586,4866,6403]),([13,6144,42009,602208,751724,866672,1163648,1967616],[4865]),([13,6144,42009,602208,866672,1014140,1163648,1967616],[6401]),([13,6144,42009,751724,866672,1163648,1967616],[3585,3619,4866,4899]),([13,6144,48152,153612,602208,866672,1163648,1967616],[]),([13,6144,153612,195612,602208,866672,1163648,1967616],[4,2562,4868]),([13,6144,153612,602208,866672,1163648,1967616,2008600],[3,1281,1795,2561,3590,4868,6406]),([13,14352,153612,195612,602208,866672,1163648,1967616],[4868]),([13,20480,42009,65536,153612,264529,1700320,1967616],[1,1284]),([13,20480,42009,131072,264529,602208,1163648,1967616],[1286,4098,6406]),([13,20480,42009,153612,264529,602208,1163648,1967616],[1,1284,3589,4868]),([13,20480,42009,153612,264529,602208,1163648,1988096],[1284,3586]),([13,20480,42009,153612,264529,602208,1167744,1967616],[1,1284,1796,4868]),([13,20480,42009,153612,264529,602208,1300876,1967616],[]),([13,20480,42009,153612,285008,602208,1163648,1967616],[3586]),([13,20480,42009,153612,602208,866672,1163648,1967616],[1,2562]),([13,20480,42009,153612,602208,1163648,1964528,1967616],[1,2562]),([13,20480,42009,264529,602208,751724,1163648,1967616],[1286,4870,6404]),([13,20480,42009,264529,602208,1163648,1833452,1967616],[1286,6406]),([13,20480,42009,264529,602208,1300876,1700320,1967616],[1286,2561,6406]),([13,20480,62488,153612,264529,602208,1163648,1967616],[4,1284,1796,3589,4868,6404]),([13,20480,153612,195612,264529,602208,1163648,1967616],[4,1284,1796,3589,4868,6404]),([13,20480,153612,264529,602208,1163648,1967616,2008600],[6,1286,1793,2567,3590,4868,6406]),([13,22528,42009,153612,602208,866672,1163648,1967616],[1,2562,3074]),([13,22528,42009,153612,602208,1163648,1964528,1967616],[1,2562,3074]),([13,42008,65536,153612,264529,602208,1163648,1967616],[1284,2049]),([13,42008,131072,153612,264529,602208,1163648,1967616],[1284,3842]),([13,42008,153612,264529,602208,1163648,1967616],[97,226,1316,1345,2626,4130,4902]),([13,42009,65536,65536,153612,264529,1700320,1967616],[1284,2817]),([13,42009,65536,131072,153612,264529,1700320,1967616],[1284,1796,2822,6660]),([13,42009,65536,153612,219148,264529,1700320,1967616],[129,193,1284,1798,2049,2177,2564,3073]),([13,42009,65536,153612,264529,602208,1163648,1967616],[68,1284,2049]),([13,42009,65536,153612,264529,602208,1163648,1971712],[1284,2054]),([13,42009,65536,153612,264529,602208,1163648,2033152],[1284,2052]),([13,42009,65536,153612,264529,602208,1167744,1967616],[68,1284,2054,3844,5124]),([13,42009,65536,153612,264529,602208,1294720,1967616],[68,1284,2049,3844,5124]),([13,42009,65536,153612,264529,602208,1700320,1967616],[258,1284,2054,6660]),([13,42009,65536,153612,264529,602208,1700320,2033152],[68,258,1284,2052,3844,5124,6660]),([13,42009,65536,153612,264529,751724,1700320,1967616],[259,1284,1798,2049]),([13,42009,65536,153612,264529,1700320,1700320,1967616],[1284,2049]),([13,42009,65536,153612,264529,1700320,1833452,1967616],[321,1284,1798,2049,7809]),([13,42009,65536,153612,264529,1700320,1967616],[161,1284,1316,1828,2049,2113,4902,5153]),([13,42009,65536,153612,264529,1700320,1967616,1990156],[1284,2049,6404]),([13,42009,65536,153612,264529,1700320,2033152],[161,1284,1316,1828,4900]),([13,42009,65536,153612,268624,602208,1163648,1967616],[1284,2049]),([13,42009,65536,153612,330064,602208,1163648,1967616],[2049]),([13,42009,65536,153612,330064,602208,1163648,2033152],[]),([13,42009,65536,153612,330064,602208,1163648,2035536],[]),([13,42009,65536,153612,330064,602208,1427920,1967616],[2049]),([13,42009,65536,153612,330064,602208,1700320,1967616],[258,2049]),([13,42009,65536,153612,330064,1700320,1967616],[161,2049,2113,3105,4897,5153]),([13,42009,65536,153612,395600,602208,1163648,1967616],[2049]),([13,42009,65536,153612,602208,866672,1163648,1967616],[2049]),([13,42009,65536,153612,602208,866672,1163648,2033152],[]),([13,42009,65536,153612,602208,866672,1700320,1967616],[2049]),([13,42009,65536,153612,602208,866672,1964528,1967616],[2049]),([13,42009,65536,153612,602208,1163648,1964528,1967616],[2049]),([13,42009,65536,153612,602208,1300876,1427920,1967616],[1793,2049]),([13,42009,65536,153612,602208,1427920,1700320,1967616],[194,2049,2946,5634]),([13,42009,65536,153612,602208,1700320,1964528,1967616],[194,2049]),([13,42009,65536,153612,866672,1700320,1967616],[161,226,2049,2113,4897,5153]),([13,42009,65536,153612,1700320,1964528,1967616],[161,2049,2113,4897,5153,5665]),([13,42009,65536,219148,264529,602208,1163648,2033152],[68,1284,2052,3844,5124,6660]),([13,42009,65600,153612,330064,602208,1163648,1967616],[66,2049]),([13,42009,65600,153612,602208,1163648,1427920,1967616],[66,2051,2818,5122,6658]),([13,42009,65600,153612,602208,1163648,1427920,2033216],[66,2818,5122,6658]),([13,42009,65600,153612,602208,1163648,1964528,1967616],[66]),([13,42009,65600,153612,602208,1300876,1427920,1967616],[1793,2049]),([13,42009,65600,153612,1163648,1427920,1700320,1967616],[2051,2946,6658]),([13,42009,65600,153612,1163648,1427920,1964528,1967616],[]),([13,42009,69632,153612,264529,602208,1163648,1967616],[71,1284,2049,5124]),([13,42009,69632,153612,264529,602208,1163648,2037248],[66,1284,2052]),([13,42009,69632,153612,264529,602208,1167744,1967616],[70,1284,2054,3844,5124]),([13,42009,69632,153612,264529,602208,1700320,1967616],[1284,2054,6660]),([13,42009,69632,153612,264529,751724,1163648,1967616],[5122,6658]),([13,42009,69632,153612,264529,1163648,1700320,1967616],[1285,2055,6658]),([13,42009,69632,153612,264529,1163648,1833452,1967616],[6661]),([13,42009,69632,153612,264529,1300876,1700320,1967616],[262,1284,1796,2051,6658]),([13,42009,69632,153612,264529,1700320,1967616],[1284,1316,1828,2049,4900,5153]),([13,42009,69632,153612,334160,602208,1163648,1967616],[2049]),([13,42009,69632,153612,602208,866672,1163648,1967616],[65,2049]),([13,42009,69632,153612,602208,1163648,1427920,1967616],[67,2051,2818,5122,6658]),([13,42009,69632,153612,602208,1300876,1427920,1967616],[2049]),([13,42009,69632,219148,264529,602208,1163648,1967616],[71,1284,2049,2817,3841,5126,6660]),([13,42009,69632,264529,602208,751724,1163648,1967616],[1284,5126,6662]),([13,42009,69632,264529,751724,1163648,1300876,1967616],[2051,3843,6661])]
noncomputable def k29 : CE := [([13,42009,69696,153612,602208,1163648,1427920,1967616],[67,2051,2818,5122,6658]),([13,42009,71936,153612,602208,866672,1163648,1967616],[67,2049]),([13,42009,131072,153612,268624,602208,1163648,1967616],[1284]),([13,42009,131072,153612,330064,602208,1163648,1967616],[3842]),([13,42009,131072,153612,395600,602208,1163648,1967616],[1284,3842]),([13,42009,131072,153612,395600,602208,1163648,1970000],[1284,3842]),([13,42009,131072,153612,395600,602208,1163648,1990156],[129,1284,1796,3842]),([13,42009,131072,153612,395600,602208,1294720,1967616],[1284]),([13,42009,131072,153612,395600,602208,1558992,1967616],[1284]),([13,42009,131072,153612,602208,866672,1163648,1967616],[2818]),([13,42009,131072,153612,602208,866672,1163648,1990156],[129,1796,2818,3074]),([13,42009,131072,153612,602208,866672,1294720,1967616],[]),([13,42009,131072,153612,602208,997744,1163648,1967616],[2818]),([13,42009,131072,153612,602208,1163648,1964528,1967616],[2818]),([13,42009,131072,153612,602208,1294720,1427920,1967616],[2818]),([13,42009,131072,153612,602208,1294720,1558992,1967616],[2818]),([13,42009,131072,153612,602208,1300876,1427920,1967616],[1798]),([13,42009,131072,395600,602208,1163648,1990156],[226,1284,1316,1828,2818,2882,3138,3874,4130,4900]),([13,42009,131072,602208,866672,1163648,1990156],[226,1316,2050,2114,3874,4900,5410]),([13,42009,133120,153612,395600,602208,1163648,1967616],[65,1284,1796,3842]),([13,42009,135168,153612,399696,602208,1163648,1967616],[1284]),([13,42009,135168,153612,602208,866672,1163648,1967616],[65,2818]),([13,42009,135168,153612,602208,1163648,1427920,1967616],[67,2050,2818,5122,6658]),([13,42009,135168,153612,866672,1163648,1967616,2045536],[67,2051,2819,3842,4868,5122,6659]),([13,42009,137216,153612,602208,866672,1163648,1967616],[67,1796,2818]),([13,42009,151552,153612,264529,602208,1163648,1967616],[65,1284,3845,5124]),([13,42009,151552,264529,602208,1163648,1700320,1967616],[7809]),([13,42009,151552,264529,602208,1163648,1967616],[1316,2882,4130,4900]),([13,42009,151552,264529,602208,1163648,1967616,2045536],[3074,4868]),([13,42009,151552,264529,602208,1163648,1967616,2095072],[4868]),([13,42009,153612,153612,264529,602208,1163648,1967616],[65,1284]),([13,42009,153612,153612,264529,602208,1163648,1971712],[65,1284,3842]),([13,42009,153612,153612,264529,602208,1167744,1967616],[65,1284,1540,1668,3842]),([13,42009,153612,153612,264529,602208,1294720,1967616],[65,1284,1540,1668]),([13,42009,153612,153612,268624,602208,1163648,1967616],[65,1284]),([13,42009,153612,153612,395600,602208,1163648,1967616],[65,1284]),([13,42009,153612,153612,602208,866672,1163648,1967616],[65,2818]),([13,42009,153612,153612,602208,1300876,1427920,1967616],[65]),([13,42009,153612,196608,264529,602208,1163648,1967616],[1796,2049,4101,5380,6660]),([13,42009,153612,219148,264529,602208,1163648,1967616],[65,129,1286,1796,2049]),([13,42009,153612,219148,264529,602208,1163648,2033152],[65,129,1284,1796,2052]),([13,42009,153612,219148,264529,602208,1700320,1967616],[65,261,1286,1796,2054,3841]),([13,42009,153612,219148,264529,1700320,1967616],[65,97,161,292,1286,1316,1796,1828,2049,2081,3873,4900,5153,5286]),([13,42009,153612,219148,330064,602208,1163648,1967616],[65,129,1286,1796,2049]),([13,42009,153612,219148,602208,866672,1163648,1967616],[65,129,1286,1796,2049,2819,3074]),([13,42009,153612,219212,602208,1163648,1427920,1967616],[131,1287,1797,2051,2178,3841]),([13,42009,153612,264529,540672,602208,1163648,1967616],[193,2564,2817,4357,5638,7170]),([13,42009,153612,264529,602208,618592,1163648,1967616],[197,263,3074,4357]),([13,42009,153612,264529,602208,618592,1163648,1984000],[197,263,3074,4354,4482]),([13,42009,153612,264529,602208,618592,1300876,1967616],[2817]),([13,42009,153612,264529,602208,737280,1163648,1967616],[257,3588,3841,4357,5894,6660,7426]),([13,42009,153612,264529,602208,743436,1163648,1967616],[65,259,1286,3588,3841,4484]),([13,42009,153612,264529,602208,751724,1163648,1967616],[259,1286,3074]),([13,42009,153612,264529,602208,751724,1163648,1971712],[263,1286,3074,3846,4354]),([13,42009,153612,264529,602208,751724,1163648,1984000],[263,1287,3074,3970,4482,5124]),([13,42009,153612,264529,602208,751724,1163648,2033152],[263,1286,3074]),([13,42009,153612,264529,602208,751724,1163648,2049536],[263,1287,3074,3970,4482,5124,5892]),([13,42009,153612,264529,602208,1163648,1593344,1967616],[4868,5121,5637,5892,6788]),([13,42009,153612,264529,602208,1163648,1650784,2082688],[3074,5637]),([13,42009,153612,264529,602208,1163648,1667168,1967616],[197,325,3074,5637,6021]),([13,42009,153612,264529,602208,1163648,1700320,1967616],[324]),([13,42009,153612,264529,602208,1163648,1700320,1971712],[324,2823]),([13,42009,153612,264529,602208,1163648,1700320,1988096],[324,2823,3846,5126]),([13,42009,153612,264529,602208,1163648,1700320,2033152],[197,260,324,3074,5637,5892]),([13,42009,153612,264529,602208,1163648,1800300,1967616],[323,1286,3074,6021,7809]),([13,42009,153612,264529,602208,1163648,1831392,1967616],[324,6660,7809]),([13,42009,153612,264529,602208,1163648,1833452,1967616],[321,1286,7809]),([13,42009,153612,264529,602208,1163648,1967616],[97,229,292,1316,4130,4902]),([13,42009,153612,264529,602208,1163648,1967616,2097132],[]),([13,42009,153612,264529,602208,1163648,1971712],[97,229,292,354,1316,2854,2882,4130,4900]),([13,42009,153612,264529,602208,1163648,1971712,1971712],[322,4868]),([13,42009,153612,264529,602208,1163648,1971712,1990156],[2823,5252,6404]),([13,42009,153612,264529,602208,1163648,1971712,2045536],[386,2823,3074,4868]),([13,42009,153612,264529,602208,1163648,1971712,2082688],[4869,6789,7297]),([13,42009,153612,264529,602208,1163648,1971712,2086784],[4868,7300]),([13,42009,153612,264529,602208,1163648,1988096],[97,229,292,1316,2852,2882,3877,4130,4900]),([13,42009,153612,264529,602208,1163648,1990156,2033152],[4868,5764,6021,6788]),([13,42009,153612,264529,602208,1163648,1990156,2045536],[2821,3074,4868,6788]),([13,42009,153612,264529,602208,1163648,1990156,2095072],[2821,3844,4868]),([13,42009,153612,264529,602208,1163648,2033152],[97,229,292,1316,4130,4389,4420,4900]),([13,42009,153612,264529,602208,1163648,2033152,2033152],[4868]),([13,42009,153612,264529,602208,1163648,2033152,2045536],[386,3074,4868]),([13,42009,153612,264529,602208,1163648,2033152,2055692],[5252,6404,7300,7557]),([13,42009,153612,264529,602208,1163648,2037248],[97,229,292,354,1316,2854,2882,4130,4386,4420,4900,5796]),([13,42009,153612,264529,602208,1163648,2045536,2082688],[3074]),([13,42009,153612,264529,602208,1163648,2045536,2088844],[2821,3074]),([13,42009,153612,264529,602208,1167744,1971712],[97,229,294,354,1316,2854,2882,4900]),([13,42009,153612,264529,602208,1294720,1990156],[65,97,229,292,1284,1316,2852,2980,3876,4005,4900,5124,5156]),([13,42009,153612,264529,602208,1300876,1984000],[97,1316,2852,4900,5158]),([13,42009,153612,264529,602208,1300876,1990156,2082688],[65,1284,3844,4868,5124]),([13,42009,153612,264529,602208,1300876,2045536,2082688],[1286,3074,5124]),([13,42009,153612,264529,602208,1700320,1990156,2082688],[3846,4868,5634]),([13,42009,153612,264529,618592,1300876,1967616],[97,1316,2849,4900,5153]),([13,42009,153612,264529,733280,1294720,1967616],[97,229,292,1316,4130,4902,5124,5153]),([13,42009,153612,264529,751724,1300876,1700320,1967616],[65,1286,2817,3841,6018]),([13,42009,153612,264529,751724,1700320,1967616,2082688],[1287,4868,5634,6657]),([13,42009,153612,264529,1700320,2033152],[97,228,1316,3620,4068,4577]),([13,42009,153612,264529,1700320,2045536,2082688],[97,228,290,1316,3906,5794,5826,6050]),([13,42009,153612,268624,268624,602208,1163648,1967616],[1796]),([13,42009,153612,268624,416092,602208,1163648,1967616],[193,2564,4098]),([13,42009,153612,268624,602208,602208,1163648,1967616],[]),([13,42009,153612,268624,602208,751724,1163648,1967616],[259,1284,3074]),([13,42009,153612,268624,602208,866672,1163648,1967616],[131]),([13,42009,153612,268624,602208,1163648,1167744,1967616],[5378]),([13,42009,153612,268624,602208,1163648,1300876,1967616],[321,1284,2819]),([13,42009,153612,268624,602208,1163648,1432016,1967616],[131,321,5378]),([13,42009,153612,268624,602208,1163648,1700320,1967616],[]),([13,42009,153612,268624,602208,1163648,1967616],[97,1316,1828,4130,4900]),([13,42009,153612,268624,602208,1163648,1967616,1971712],[386,4868,6404]),([13,42009,153612,268624,602208,1163648,1967616,1974096],[386,3075,4097,6404]),([13,42009,153612,268624,602208,1163648,1967616,1990156],[2819,6404]),([13,42009,153612,268624,602208,1163648,1967616,2045536],[386,3075,4868]),([13,42009,153612,268624,602208,1163648,1967616,2082688],[4097,4868,7297]),([13,42009,153612,268624,602208,1163648,1971712],[97,354,1316,1828,4130,4900]),([13,42009,153612,268624,602208,1163648,1974096],[1316]),([13,42009,153612,268624,602208,1167744,1967616],[97,1316,1828,2081,2849,4900]),([13,42009,153612,268624,602208,1432016,1967616],[129,1316,1828,4900,5409]),([13,42009,153612,268624,751724,1163648,1967616],[99,1316,1828,3875,4130,4900,5155]),([13,42009,153612,268624,866672,1163648,1967616],[131,1316,1828,2114,4900,5411]),([13,42009,153612,285008,602208,1163648,1700320,1967616],[]),([13,42009,153612,285008,602208,1163648,1967616],[97,161,226,2882,3138,4130,4897]),([13,42009,153612,330064,330064,602208,1163648,1967616],[1796,2049]),([13,42009,153612,330064,481628,602208,1163648,1967616],[193,2564,2817]),([13,42009,153612,330064,602208,602208,1163648,1967616],[194]),([13,42009,153612,330064,602208,751724,1163648,1967616],[259,1286,3074]),([13,42009,153612,330064,602208,866672,1163648,1967616],[258]),([13,42009,153612,330064,602208,1163648,1700320,1967616],[]),([13,42009,153612,330064,602208,1163648,1967616],[97,226,1316,1828,2081,4130,4902]),([13,42009,153612,330064,602208,1163648,1967616,1990156],[6404,7044]),([13,42009,153612,330064,602208,1163648,2033152],[97,226,1316,1828,2081,3138,4130,4386,4900]),([13,42009,153612,330064,602208,1163648,2035536],[1316]),([13,42009,153612,334160,602208,1163648,1300876,1967616],[321,1284,2819]),([13,42009,153612,334160,602208,1163648,1967616],[97,1316,1828,4130,4900]),([13,42009,153612,395600,395600,602208,1163648,1967616],[1796,2049,4098]),([13,42009,153612,395600,416092,602208,1163648,1967616],[193,2564,2817,4098]),([13,42009,153612,395600,602208,733280,1163648,1967616],[194,258,3074,4354]),([13,42009,153612,395600,602208,751724,1163648,1967616],[259,1286,3074]),([13,42009,153612,395600,602208,997744,1163648,1967616],[261,4354]),([13,42009,153612,395600,602208,1163648,1700320,1967616],[7809]),([13,42009,153612,395600,602208,1163648,1967616],[97,226,1316,1828,2081,3138,4130,4902,5153]),([13,42009,153612,395600,602208,1163648,1967616,1990156],[65,1286,4868,6404,6657]),([13,42009,153612,395600,602208,1163648,1970000],[1316,5153]),([13,42009,153612,395600,602208,1163648,1990156],[65,97,226,1284,1316,1828,3138,3874,4002,4130,4900]),([13,42009,153612,395600,602208,1294720,1967616],[97,1316,1828,2081,3138,4902,5153]),([13,42009,153612,395600,602208,1558992,1967616],[1316,1828,4902,5153,5409]),([13,42009,153612,399696,602208,1163648,1967616],[97,1316,1828,4130,4900,5153]),([13,42009,153612,399696,602208,1163648,1967616,2045536],[386,3075,4868]),([13,42009,153612,602208,602208,866672,1163648,1967616],[]),([13,42009,153612,602208,602208,1163648,1427920,1967616],[130,2306,2434]),([13,42009,153612,602208,602208,1163648,1964528,1967616],[130])]
noncomputable def k30 : CE := [([13,42009,153612,602208,602464,866672,1163648,1967616],[]),([13,42009,153612,602208,604256,866672,1163648,1967616],[130,195,3074,4098]),([13,42009,153612,602208,618592,866672,1163648,1967616],[130,195,3074,4098]),([13,42009,153612,602208,618592,883056,1163648,1967616],[130,195,3074,4098]),([13,42009,153612,602208,618592,1163648,1427920,1967616],[130,195,3074,3202,5378]),([13,42009,153612,602208,620640,1163648,1427920,1967616],[130,195,3074,3202,3841,5378]),([13,42009,153612,602208,677900,866672,1163648,1967616],[65,195,1286,2051,2564,2817,3074]),([13,42009,153612,602208,677900,1163648,1427920,1967616],[67,195,1287,2565,2819,2946,3841]),([13,42009,153612,602208,733280,866672,1163648,1967616],[130,194,3074,4098]),([13,42009,153612,602208,733280,997744,1163648,1967616],[130,194,3074,4098]),([13,42009,153612,602208,733280,1163648,1427920,1967616],[130,194,3074,3202,5378]),([13,42009,153612,602208,751724,866672,1163648,1967616],[130,195,1286,3074,4098]),([13,42009,153612,602208,751724,1163648,1427920,1967616],[195,1287,2946,3202,3841,5378]),([13,42009,153612,602208,751724,1163648,1964528,1967616],[130,195,1281,3074,3841,5378]),([13,42009,153612,602208,751724,1300876,1427920,1967616],[65,195,1286,2817,3841]),([13,42009,153612,602208,751724,1427920,1967616,2082688],[195,1281,2945,3201,6657]),([13,42009,153612,602208,792576,866672,1163648,1967616],[194,258,2051,2564,2817,3074,6914]),([13,42009,153612,602208,792576,1163648,1967616],[97,226,1316,2081,2114,2596,2849,3074,3106,4386,4902,5411]),([13,42009,153612,602208,792576,1163648,1967616,1990156],[2051,3074,5378,6404,6914]),([13,42009,153612,602208,792912,1163648,1967616],[97,226,1316,2114,2596,3106,4258,4386,4902,5411]),([13,42009,153612,602208,792912,1163648,1967616,1990156],[2051,5378,6404,6914]),([13,42009,153612,602208,866672,866672,1163648,1967616],[194]),([13,42009,153612,602208,866672,883056,1163648,1967616],[194,259]),([13,42009,153612,602208,866672,940044,1163648,1967616],[65,259,1286,2051,3588,3841,4098,6914]),([13,42009,153612,602208,866672,997744,1163648,1967616],[194,261]),([13,42009,153612,602208,866672,1014140,1163648,1967616],[263]),([13,42009,153612,602208,866672,1163648,1700320,1967616],[]),([13,42009,153612,602208,866672,1163648,1833452,1967616],[321,1286,7809]),([13,42009,153612,602208,866672,1163648,1964528,1967616],[194]),([13,42009,153612,602208,866672,1163648,1967616],[97,226,2114,4897,5411]),([13,42009,153612,602208,866672,1163648,1967616,1990156],[2051,5378,6404,6914]),([13,42009,153612,602208,866672,1163648,1967616,2063980],[130,389,3074,6914,7554]),([13,42009,153612,602208,866672,1163648,1967616,2064252],[389,7554]),([13,42009,153612,602208,866672,1163648,1967616,2088844],[388,2051,5378]),([13,42009,153612,602208,866672,1163648,1967616,2095612],[385,7809]),([13,42009,153612,602208,866672,1163648,1971712],[97,226,354,2081,2114,2849,4900,5410]),([13,42009,153612,602208,866672,1163648,1973760],[97,226,354,2050,2114,2849,4900,5410]),([13,42009,153612,602208,866672,1163648,1984000],[99,226,2114,3875,4386,4900,5410]),([13,42009,153612,602208,866672,1163648,1990156,2045536],[130,2050,3074,4868,6914]),([13,42009,153612,602208,866672,1163648,1990156,2047856],[2050]),([13,42009,153612,602208,866672,1163648,1990156,2082688],[2051,4868,5378,6786]),([13,42009,153612,602208,866672,1163648,2033152],[97,226,2114,4130,4900,5410]),([13,42009,153612,602208,866672,1163648,2033408],[2114,4900]),([13,42009,153612,602208,866672,1163648,2045536,2082688],[130,3074,5378]),([13,42009,153612,602208,866672,1163648,2047856,2082688],[7297]),([13,42009,153612,602208,866672,1167744,1967616],[97,289,1316,2081,2114,2849,4902,5410]),([13,42009,153612,602208,866672,1169792,1967616],[97,289,1316,2049,2081,2114,4902,5410,5793]),([13,42009,153612,602208,866672,1294720,1967616],[97,1316,2114,4902,5153,5411]),([13,42009,153612,602208,866672,1300876,1700320,1967616],[1286,2049]),([13,42009,153612,602208,866672,1300876,1964528,1967616],[1286,2049]),([13,42009,153612,602208,866672,1300876,1967616,2082688],[1286,2051,4868,5378]),([13,42009,153612,602208,883056,1163648,1967616],[97,227,2114,4897,5411]),([13,42009,153612,602208,997744,1163648,1967616],[97,162,229,2114,4897,5153,5411]),([13,42009,153612,602208,1014140,1163648,1964528,1967616],[199]),([13,42009,153612,602208,1014140,1163648,1967616,2047856],[]),([13,42009,153612,602208,1163648,1700320,1964528,1967616],[]),([13,42009,153612,602208,1163648,1833452,1964528,1967616],[257,1281,7553]),([13,42009,153612,602208,1163648,1964528,1964528,1967616],[]),([13,42009,153612,602208,1163648,1964528,1967616],[97,162,2114,4897,5411,5665]),([13,42009,153612,602208,1163648,1964528,1967616,1990156],[2051,2817,5378,6914]),([13,42009,153612,602208,1163648,1964528,1967616,2095612],[385,7809]),([13,42009,153612,602208,1165696,1300876,1427920,1967616],[193,257,1281,2946]),([13,42009,153612,602208,1165696,1427920,1967616],[97,225,4897,5665,6051]),([13,42009,153612,602208,1167744,1427920,1967616],[97,225,2081,2114,4514,4897,5665]),([13,42009,153612,602208,1167744,1432016,1967616],[97,225,289,2081,2114,4897]),([13,42009,153612,602208,1294720,1427920,1967616],[97,4514,4897,5153,5665]),([13,42009,153612,602208,1294720,1558992,1967616],[97,292,4897,5153,5665]),([13,42009,153612,602208,1300876,1300876,1427920,1967616],[193,1281]),([13,42009,153612,602208,1300876,1427920,1427920,1967616],[1281,3970]),([13,42009,153612,602208,1300876,1427920,1563100,1967616],[326,1281]),([13,42009,153612,602208,1300876,1427920,1700320,1967616],[1281,2051]),([13,42009,153612,602208,1300876,1427920,1833452,1967616],[321,1286,7809]),([13,42009,153612,602208,1300876,1427920,1964528,1967616],[1281,2051,3970]),([13,42009,153612,602208,1300876,1427920,1967616],[97,225,1281,2081,4002,4897,5153]),([13,42009,153612,602208,1300876,1427920,1967616,1990156],[65,1286,2817,6404,6657]),([13,42009,153612,602208,1300876,1427920,1967616,2082688],[193,1281,2945]),([13,42009,153612,602208,1300876,1427920,1967616,2084816],[388,1281,6786]),([13,42009,153612,602208,1300876,1427920,1967616,2088844],[193,388,1281]),([13,42009,153612,602208,1300876,1700320,1964528,1967616],[1286,2049]),([13,42009,153612,602208,1300876,1964528,1967616],[97,225,1286,2049,2081,4897,5153,5409]),([13,42009,153612,602208,1427920,1967616,1990156,2088844],[4868]),([13,42009,153612,602208,1427920,1967616,2088844],[97,356,2081,3617]),([13,42009,153612,602208,1427920,1990156,2082688],[97,2849,5282]),([13,42009,153612,602208,1427920,2045536,2082688],[97,290,3106,4547,5537]),([13,42009,395600,602208,1163648,1990156],[162,1316,2114,2276,2850,2914,3045,3620,4324,4450,4581]),([13,46104,153612,268624,602208,1163648,1967616],[36,100,292,1316,1348,1828,2084,2852,3652,4164,4900]),([13,46104,153612,310616,602208,1163648,1967616],[]),([13,46104,153612,602208,866672,1163648,1967616],[4902]),([13,46104,153612,602208,1163648,1427920,1967616],[1314,4903]),([13,48152,153612,602208,866672,1163648,1967616],[4902]),([13,65536,107544,153612,330064,602208,1163648,1967616],[1793]),([13,65536,107544,153612,372056,602208,1163648,1967616],[1793]),([13,65536,107544,153612,602208,866672,1163648,1967616],[1793]),([13,65536,153612,195612,330064,602208,1163648,1967616],[4,1286,1796,2564,3588,4868,6404]),([13,65536,153612,195612,602208,866672,1163648,1967616],[4,1286,1796,2819]),([13,65536,153612,330064,372056,602208,1163648,1967616],[1286,1796,2564,3588,4868,6404]),([13,65600,107608,153612,602208,1163648,1427920,1967616],[1793]),([13,65600,153612,195612,602208,1163648,1427920,1967616],[5,1287,1797,2562,3841,4866,6402]),([13,107544,153612,330064,602208,1163648,1967616],[97,226,1316,1345,1828,2081,2626,3138,4130,4386,4902]),([13,107544,153612,372056,602208,1163648,1967616],[1345,2081,4130,4386]),([13,107544,153612,602208,866672,1163648,1967616],[97,229,1316,1345,2114,4130,4902,5411]),([13,107608,153612,602208,1163648,1427920,1967616],[292,1317,1345,2754,4903,5665]),([13,153612,153612,195612,602208,866672,1163648,1967616],[1,2562]),([13,153612,173080,437592,602208,1163648,1967616],[4130]),([13,153612,173080,602208,866672,1163648,1967616],[33,165,229,292,1858,5153,5411]),([13,153612,195612,195612,602208,866672,1163648,1967616],[65,2567]),([13,153612,195612,602208,751724,866672,1163648,1967616],[1,133,195,1286,1795,2566,3074,4098]),([13,153612,195612,602208,751724,1163648,1427920,1967616],[3,199,1287,2567,2690,3202,3590,5378]),([13,153612,195612,602208,785532,866672,1163648,1967616],[195,1799,2180]),([13,153612,195612,602208,785532,1163648,1427920,1967616],[195,2690,2946,3202,3590,4482]),([13,153612,195612,602208,866672,1047932,1163648,1967616],[259,1795]),([13,153612,195612,602208,866672,1163648,1700320,1967616],[324,1795,3590,4870]),([13,153612,195612,602208,866672,1163648,1964528,1967616],[197,324,1795,3590]),([13,153612,195612,602208,866672,1163648,1967616],[33,97,165,229,292,1795,1830,1858,3622,5156,5410]),([13,153612,195612,602208,866672,1163648,1967616,2082688],[1795,3590,5124,5378]),([13,153612,195612,602208,1163648,1700320,1964528,1967616],[260,1799,2566,3585]),([13,153612,195612,602208,1163648,1964528,1967616],[33,97,165,228,292,1799,1825,1858,2566,2595,5410]),([13,153612,195612,602208,1300876,1427920,1967616],[1,33,97,165,230,292,1281,1318,1830,1956,2561,2593,3617,3746,4902,5030,5156]),([13,153612,195612,602208,1427920,1967616,2082688],[33,97,167,228,1825,3878,4547]),([13,153612,602208,1427920,2008600,2082688],[33,101,164,2018,2116,2660,2788,2916,3046,3299,3813,3940,4065,4452,4580]),([14,0,0,42009,153612,264529,602208,1163648,1967616],[3588]),([14,0,4096,42009,153612,264529,602208,1163648,1967616],[2052,3588,6660]),([14,0,14460,42009,153612,264529,602208,1163648,1967616],[3588]),([14,0,22540,42009,153612,264529,602208,1163648,1967616],[2052]),([14,0,42008,129532,153612,264529,602208,1163648,1967616],[]),([14,0,42008,153612,264529,602208,933500,1163648,1967616],[2564]),([14,0,42008,153612,264529,602208,1163648,1967616],[2084,4898,5666,6433,6694]),([14,0,42009,65536,153612,264529,602208,1163648,1967616],[2052,3073,3588]),([14,0,42009,77920,153612,264529,602208,1163648,1967616],[3588]),([14,0,42009,106992,153612,264529,602208,1163648,1967616],[3588]),([14,0,42009,129532,153612,264529,602208,1163648,1967616],[3588]),([14,0,42009,129532,153612,602208,866672,1163648,1967616],[]),([14,0,42009,153612,153612,264529,602208,1163648,1967616],[2052,3588]),([14,0,42009,153612,260604,264529,602208,1163648,1967616],[3588]),([14,0,42009,153612,264529,602208,653820,1163648,1967616],[2564]),([14,0,42009,153612,264529,602208,751724,1163648,1967616],[2054,2564,4354]),([14,0,42009,153612,264529,602208,1048572,1163648,1967616],[2564]),([14,0,42009,153612,264529,602208,1163648,1700320,1967616],[2564]),([14,0,42009,153612,264529,602208,1163648,1966076,1967616],[2564]),([14,0,42009,153612,264529,602208,1163648,1967616],[2084,2564,2628,3620,4901,5666,6433,6694]),([14,0,42009,153612,264529,602208,1163648,1967616,2097148],[2564]),([14,0,42009,153612,602208,669228,1163648,1427920,1967616],[3714]),([14,0,42009,153612,602208,866672,933500,1163648,1967616],[]),([14,0,42009,153612,602208,866672,1163648,1494940,1967616],[7557]),([14,0,42009,153612,602208,866672,1163648,1967616],[3138,4898,6433,6689,7203]),([14,2076,42009,153612,264529,602208,1163648,1700320,1967616],[1284,3589,4868]),([14,2076,42009,153612,264529,602208,1163648,1967616],[1284,3620,4901,5666,6433]),([14,2076,42009,153612,264529,602208,1163648,1967616,2045536],[1284,3589,4354,8198]),([14,2076,42009,153612,264529,602208,1163648,1967616,2095072],[1284,3589,4868]),([14,4096,4096,42009,153612,264529,602208,1163648,1967616],[1796,6404])]
noncomputable def k31 : CE := [([14,4096,14460,42009,153612,264529,602208,1163648,1967616],[1796,6404]),([14,4096,22540,42009,153612,264529,602208,1163648,1967616],[2052]),([14,4096,42009,51612,153612,264529,602208,1163648,1967616],[1285,1794,2562,3586,4866,6402,8194]),([14,4096,42009,77920,153612,264529,602208,1163648,1967616],[1284]),([14,4096,42009,106992,153612,264529,602208,1163648,1967616],[1284]),([14,4096,42009,115072,153612,264529,602208,1163648,1967616],[1285,1794,2562,3586,4866,6402,8194]),([14,4096,42009,125436,153612,264529,602208,1163648,1967616],[1284,2562,3586,4866,6402,8194]),([14,4096,42009,125436,153612,264529,602208,1163648,1971712],[1284,2562,3586,4866,6402,8194]),([14,4096,42009,129532,153612,264529,602208,1163648,1967616],[1284]),([14,4096,42009,129532,153612,264529,602208,1163648,1971712],[1284]),([14,4096,42009,129532,153612,264529,602208,1167744,1967616],[1284,1924]),([14,4096,42009,129532,153612,268624,602208,1163648,1967616],[]),([14,4096,42009,129532,153612,602208,866672,1163648,1967616],[]),([14,4096,42009,129532,153612,602208,1163648,1427920,1967616],[1794,2562,3586,6402,8194]),([14,4096,42009,149516,153612,264529,602208,1163648,1967616],[1285,2052,2565,2820,3586,4869,6405,8197]),([14,4096,42009,149516,264529,602208,1163648,1494940,1967616],[1285,1797,4869,6405,8197]),([14,4096,42009,149516,264529,602208,1163648,1967616],[1285,1348,1829,2084,4869,4901,6405,6437,6692]),([14,4096,42009,149516,264529,602208,1163648,1967616,2093052],[1285,1795,4869,6405]),([14,4096,42009,153612,260604,264529,602208,1163648,1967616],[1284]),([14,4096,42009,153612,264529,602208,653820,1163648,1967616],[1284]),([14,4096,42009,153612,264529,602208,1048572,1163648,1967616],[1284,6404]),([14,4096,42009,153612,264529,602208,1098112,1163648,1967616],[1285,1797,2565,3589,4869,6405,8197]),([14,4096,42009,153612,264529,602208,1147264,1163648,1967616],[1287,1795,2563,3587,4866,6403,8195]),([14,4096,42009,153612,264529,602208,1163648,1163648,1967616],[1285,1797,3589,4866,8197]),([14,4096,42009,153612,264529,602208,1163648,1178108,1967616],[1284,1794,3586,4868,6402,8194]),([14,4096,42009,153612,264529,602208,1163648,1345424,1967616],[1287,1795,2563,3587,4867,6401,8199]),([14,4096,42009,153612,264529,602208,1163648,1494940,1967616],[1285,1797,3589,4869,6405,8197]),([14,4096,42009,153612,264529,602208,1163648,1494940,1971712],[1285,1797,3589,4869,6405,8197]),([14,4096,42009,153612,264529,602208,1163648,1499036,1967616],[1284,1797,3589,4868,6405,8197]),([14,4096,42009,153612,264529,602208,1163648,1560476,1967616],[1285,1797,3589,4868,6405,8197]),([14,4096,42009,153612,264529,602208,1163648,1572860,1967616],[1284,1794,3586,4868,6402,8194]),([14,4096,42009,153612,264529,602208,1163648,1943536,1971712],[1284,1793,2561,3585,4865,7556,8193]),([14,4096,42009,153612,264529,602208,1163648,1959920,1967616],[1284,1795,3587,4868,6401,7556,8194]),([14,4096,42009,153612,264529,602208,1163648,1966076,1967616],[1284,4868]),([14,4096,42009,153612,264529,602208,1163648,1967616],[1284,1348,2084,3620,4868,4898,4932,6438,6692]),([14,4096,42009,153612,264529,602208,1163648,1967616,2093052],[1284,1795,3587,4868,9348]),([14,4096,42009,153612,264529,602208,1163648,1967616,2097148],[1284,4868]),([14,4096,42009,153612,264529,602208,1163648,1971712,2093052],[1284,9348]),([14,4096,42009,153612,264529,751724,1163648,1943536,1967616],[2052,2563,4867,6407,7556,8195]),([14,4096,42009,153612,268624,602208,933500,1163648,1967616],[1284]),([14,4096,42009,153612,268624,602208,1163648,1494940,1967616],[7300]),([14,4096,42009,153612,268624,602208,1163648,1828524,1967616],[]),([14,4096,42009,153612,268624,602208,1163648,1943536,1967616],[1284,1793,2561,3585,4865,8193]),([14,4096,42009,153612,268624,602208,1163648,1967616,2093052],[9092]),([14,4096,42009,153612,602208,669228,1163648,1427920,1967616],[]),([14,4096,42009,153612,602208,866672,933500,1163648,1967616],[]),([14,4096,42009,153612,602208,866672,1163648,1230476,1967616],[1794,2562,3586,6402,8194]),([14,4096,42009,153612,602208,866672,1163648,1494940,1967616],[7556]),([14,4096,42009,153612,602208,866672,1163648,1943536,1967616],[1793,2561,3585,4865,6401,8193]),([14,4096,42009,153612,602208,866672,1163648,1967616,2093052],[1793,2561,3585]),([14,4096,42009,153612,602208,933500,1163648,1427920,1967616],[1794,2562,3586,6402,7556,8194]),([14,4096,42009,153612,602208,1163648,1427920,1494940,1967616],[1794,2562,4866,6402,6530,8194]),([14,4096,42009,153612,602208,1163648,1427920,1943536,1967616],[1795,2563,3585,4867,6401,6530,8193]),([14,4096,42009,153612,602208,1163648,1427920,1967616,2093052],[1795,2563,4866,6402,8194,8322]),([14,6144,42009,129532,153612,602208,866672,1163648,1967616],[3586]),([14,6144,42009,153612,602208,866672,933500,1163648,1967616],[2562]),([14,6144,42009,153612,602208,866672,1163648,1230476,1967616],[1794,2562,3586,6402,8194]),([14,6144,42009,153612,602208,866672,1163648,1494940,1967616],[2562]),([14,6144,42009,153612,602208,866672,1163648,1943536,1967616],[1793,2563,3585,4865,6401,8193]),([14,6144,42009,153612,602208,866672,1163648,1967616,2091004],[1795,2563,3587]),([14,6156,14460,42009,153612,264529,602208,1163648,1967616],[1796]),([14,6156,42009,153612,264529,602208,1163648,1967616],[1284,3620,4898,6438]),([14,6156,42009,153612,264529,602208,1163648,1967616,2082688],[1284,1795,4868,8197]),([14,6244,153612,264529,602208,1163648,1967616,2008600],[1316,2596,2724,3621,3750,4868,4902,5030,6438,6566]),([14,6244,153612,264529,602208,1163648,1967616,2008600,2090904],[3590,4868,6406,8198,8326]),([14,14460,42009,65536,153612,264529,602208,1163648,1967616],[2052,3076]),([14,14460,42009,147456,153612,264529,602208,1163648,1967616],[2052,6916]),([14,14460,42009,153612,161916,264529,602208,1163648,1967616],[]),([14,14460,42009,153612,264529,602208,751724,1163648,1967616],[2052,3716]),([14,14460,42009,153612,264529,602208,1163648,1163648,1967616],[4866]),([14,14460,42009,153612,264529,602208,1163648,1178108,1967616],[6402]),([14,14460,42009,153612,264529,602208,1163648,1300876,1967616],[1793,2052,6402]),([14,14460,42009,153612,264529,602208,1163648,1700320,1967616],[3589,6532]),([14,14460,42009,153612,264529,602208,1163648,1967616],[2084,3620,3748,4898,6438,6692]),([14,14460,42009,153612,264529,602208,1163648,1967616,2082688],[4868,6660]),([14,14460,42009,153612,264529,602208,1163648,1967616,2088844],[1793]),([14,14460,42009,153612,264529,602208,1163648,1967616,2097148],[]),([14,14460,42009,153612,264529,602208,1163648,1982076,2082688],[]),([14,14460,42009,153612,264529,602208,1163648,1990156,2082688],[1796,5380,6660]),([14,14460,42009,153612,264529,602208,1163648,2045536,2082688],[3586,6402]),([14,14460,42009,153612,602208,866672,1163648,1967616],[2724,3748,4898,6433,6692]),([14,14460,42009,153612,602208,866672,1163648,1967616,2082688],[6660]),([14,14460,42009,153612,602208,1163648,1427920,1967616],[2724,3618,3746,4898,6435,6562]),([14,14460,42009,153612,602208,1163648,1427920,1967616,2082688],[3713,6402,8194,8322]),([14,14460,42009,153612,602208,1427920,1967616,2082688],[2724,3617,4897,5025,5156,6083,6433,6561]),([14,20480,42009,129532,153612,264529,602208,1163648,1967616],[1284,4866]),([14,20480,42009,153612,264529,396828,602208,1163648,1967616],[1284,1796,4869,6404,8196]),([14,20480,42009,153612,264529,602208,933500,1163648,1967616],[1284,1796,3588,4868,6404,8196]),([14,20480,42009,153612,264529,602208,1163648,1943536,1967616],[1284,1793,2561,3587,4865,6401,7810,8193]),([14,20480,42009,153612,264529,602208,1163648,1967616,2076668],[1284,1793,3587,4865,9602]),([14,22532,88548,153612,264529,602208,1163648,1967616,2008600],[1284,1796,6404,8196]),([14,22532,153612,264529,602208,1163648,1967616,2008600],[1286,1316,2596,2724,3621,3749,3874,4130,4868,4902,5030,5954,6404,6438,6566]),([14,22540,22540,42009,153612,264529,602208,1163648,1967616],[]),([14,22540,42009,65536,153612,264529,602208,1163648,1967616],[1284]),([14,22540,42009,77920,153612,264529,602208,1163648,1967616],[1284]),([14,22540,42009,129532,131072,264529,602208,1163648,1967616],[5634,8196]),([14,22540,42009,129532,153612,264529,602208,1163648,1967616],[1284]),([14,22540,42009,129532,153612,602208,866672,1163648,1967616],[3586,4354]),([14,22540,42009,129532,260604,264529,602208,1163648,1967616],[]),([14,22540,42009,129532,264529,602208,751724,1163648,1967616],[1286,4354]),([14,22540,42009,131072,153612,264529,602208,1163648,1967616],[1284,2564,5378,8196]),([14,22540,42009,131072,264529,602208,1163648,1966076,1967616],[4098,8196]),([14,22540,42009,131072,264529,602208,1163648,1967616],[1828,4098,4162,5410,5666,6404,6438]),([14,22540,42009,153612,153612,264529,602208,1163648,1967616],[1284]),([14,22540,42009,153612,260604,264529,602208,1163648,1967616],[1284]),([14,22540,42009,153612,264529,602208,620652,1163648,1967616],[1284,4354]),([14,22540,42009,153612,264529,602208,653820,1163648,1967616],[1284]),([14,22540,42009,153612,264529,602208,751724,1163648,1967616],[1284,4354]),([14,22540,42009,153612,264529,602208,1163648,1700320,1967616],[1284,3589,4098,4868]),([14,22540,42009,153612,264529,602208,1163648,1966076,1967616],[1284]),([14,22540,42009,153612,264529,602208,1163648,1967616],[1284,4898,5026,5410,5666,6436]),([14,22540,42009,153612,264529,602208,1163648,1967616,1990156],[1284,1796,8196]),([14,22540,42009,153612,264529,602208,1163648,1967616,2045536],[1286,1793,3589,4098,4354,8196]),([14,22540,42009,153612,264529,602208,1163648,1967616,2097148],[1284]),([14,22540,42009,153612,602208,866672,1163648,1967616],[2562,2626,3074,3138,4898,5026,5410,7202]),([14,22540,42009,260604,264529,602208,1163648,1967616],[5410,5666,6433]),([14,22540,42009,264529,602208,751724,1163648,1967616],[1286,3074,4899,5666,6433,7202]),([14,22540,64540,129532,153612,264529,602208,1163648,1967616],[1284,1796,2564]),([14,22540,64540,153612,264529,602208,1163648,1967616],[1284,1316,1796,1828,3620,3748,4901,5029,5410,5666,6436,6564]),([14,22540,129532,153612,195612,264529,602208,1163648,1967616],[1284,1796,2564]),([14,22540,129532,153612,264529,602208,1163648,1967616,2008600],[1286,1798,8196]),([14,22540,153612,195612,264529,602208,1163648,1967616],[1284,1316,1796,1828,3620,3748,4901,5029,5154,5666,6436,6564]),([14,22540,153612,264529,602208,1163648,1967616,2008600],[1286,1316,2596,2724,3621,3749,3874,4130,4902,5030,5954,6404,6438]),([14,40984,129532,153612,264529,602208,1163648,1967616],[1828,5154,5282,5666,6438]),([14,40984,129532,153612,264529,602208,1163648,1967616,2008600],[1286,8198]),([14,40984,153612,264529,602208,1163648,1967616],[1316,2788,3682,3813,3938,4066,4130,4902,5857,5986,6115]),([14,40984,153612,264529,602208,1163648,1967616,2008600],[1316,2596,2726,3621,3751,4130,4902,5030,5954,6406,6438,7366,7490,7623]),([14,42008,129532,153612,264529,602208,1163648,1967616],[1828,5154,5282,5666,6438]),([14,42008,153612,264529,602208,933500,1163648,1967616],[1316,3780,4548,5410,6438,7457,7585]),([14,42008,153612,264529,602208,1163648,1967616],[1316,2788,3682,3813,3938,4066,4130,4902,4961,5089,5729,5857,5987,6115]),([14,42009,63996,65536,153612,264529,602208,1163648,1967616],[1796]),([14,42009,63996,65536,153612,264529,602208,1163648,2033152],[1796]),([14,42009,63996,153612,264529,602208,1163648,1967616],[1828,4004,5154,5285,5666,6436,6692]),([14,42009,63996,153612,264529,602208,1163648,1967616,2033152],[6404,8196]),([14,42009,63996,153612,264529,602208,1163648,2033152],[1828,4004,5154,5285,5666,5922,6436]),([14,42009,65536,65536,153612,264529,602208,1163648,1967616],[1284,2817]),([14,42009,65536,77920,153612,264529,602208,1163648,1967616],[1284]),([14,42009,65536,106992,153612,264529,602208,1163648,1967616],[1284,2817]),([14,42009,65536,129532,153612,264529,602208,1163648,1967616],[1284]),([14,42009,65536,129532,153612,264529,602208,1163648,2033152],[1284]),([14,42009,65536,129532,153612,264529,602208,1700320,1967616],[1284]),([14,42009,65536,129532,153612,264529,1700320,1967616],[1284,1316,2596,6438]),([14,42009,65536,129532,153612,330064,602208,1163648,1967616],[]),([14,42009,65536,129532,153612,602208,866672,1163648,1967616],[]),([14,42009,65536,129532,219148,264529,602208,1163648,1967616],[1286,2177]),([14,42009,65536,137228,153612,264529,602208,1163648,1967616],[1284,1796,2564,2820,5124,6660,8452]),([14,42009,65536,153612,153612,264529,602208,1163648,1967616],[1284,1796]),([14,42009,65536,153612,260604,264529,602208,1163648,1967616],[1284,2049]),([14,42009,65536,153612,264529,396828,602208,1163648,1967616],[1284,2054,3588,3844,5124,6660,8452]),([14,42009,65536,153612,264529,396828,602208,1700320,1967616],[1284,2054,3588,3844,8452])]
noncomputable def k32 : CE := [([14,42009,65536,153612,264529,396828,1700320,1967616],[1284,1316,1828,2054,2084,2113,3588,3620,3876,6438,6660,6694,7457,7585]),([14,42009,65536,153612,264529,602208,653820,1163648,1967616],[1284,2049]),([14,42009,65536,153612,264529,602208,933500,1163648,1967616],[1284,2054,3844,5124,6020,6660,8452]),([14,42009,65536,153612,264529,602208,933500,1163648,2033152],[1284,2052,3844,5124,6020,6660,8452]),([14,42009,65536,153612,264529,602208,933500,1700320,1967616],[1284,2054,6020,8452]),([14,42009,65536,153612,264529,602208,949884,1163648,1967616],[1284,2049,3844,5124,6020,6660,8452]),([14,42009,65536,153612,264529,602208,999036,1163648,1967616],[1284,2054,3844,5124,6660,8452]),([14,42009,65536,153612,264529,602208,1048572,1163648,1967616],[1284,2049]),([14,42009,65536,153612,264529,602208,1163648,1966076,1967616],[1284,2049]),([14,42009,65536,153612,264529,602208,1163648,1967616],[1284,1316,1828,2049,2113,3876,5157,5666,5922,6438,6689]),([14,42009,65536,153612,264529,602208,1163648,1967616,2031612],[1284,2049,3844,5124,9348,9605]),([14,42009,65536,153612,264529,602208,1163648,1967616,2097148],[1284,2049]),([14,42009,65536,153612,264529,602208,1163648,2031612,2033152],[1284,2052,7556,7813]),([14,42009,65536,153612,264529,602208,1494940,1700320,1967616],[1285,2055,3970,5124,7426,7813,8453]),([14,42009,65536,153612,264529,602208,1700320,1967616,2031612],[1284,2054,6660,9348]),([14,42009,65536,153612,264529,933500,1700320,1967616],[1284,1316,1828,2054,2084,2113,6052,6438,6660,6694,7457,7585]),([14,42009,65536,153612,264529,1700320,1967616,2031612],[1284,1316,1828,2049,2113,4902,5153,7873]),([14,42009,65536,153612,330064,602208,933500,1163648,1967616],[2049,5764,6020]),([14,42009,65536,153612,330064,602208,1163648,1767084,1967616],[2049,4354,7556,7813]),([14,42009,65536,153612,330064,602208,1163648,1967616,2031612],[2049,9092,9348,9605]),([14,42009,65536,153612,602208,669228,1163648,1427920,1967616],[1284,2049,3970,4484,7170]),([14,42009,65536,153612,602208,866672,933500,1163648,1967616],[2049,5764]),([14,42009,65536,153612,602208,866672,1163648,1494940,1967616],[2049,7557,7813]),([14,42009,65536,153612,602208,866672,1163648,1967616,2031612],[2049,9092,9605]),([14,42009,65600,129532,153612,602208,1163648,1427920,1967616],[2050,3842,6658]),([14,42009,65600,153612,602208,669228,1163648,1427920,1967616],[1284,3970,4484]),([14,42009,65600,153612,602208,933500,1163648,1427920,1967616],[2818,3842,3972,4484,6658,7556]),([14,42009,65600,153612,602208,1163648,1427920,1494940,1967616],[2818,5122,6658,6786]),([14,42009,65600,153612,602208,1163648,1427920,1967616,2031548],[2051,2818,5122,6658,8450,8578,9092]),([14,42009,69632,129532,153612,264529,602208,1163648,1967616],[1284]),([14,42009,69632,153612,264529,602208,933500,1163648,1967616],[1284,2054,3844,5124,6020,6660,8452]),([14,42009,69632,153612,264529,602208,1163648,1494940,1967616],[1285,2055,3845,5125,6661,7813,8453]),([14,42009,69632,153612,264529,602208,1163648,1943536,1967616],[1284,2049,2817,3841,5121,6657,8449]),([14,42009,69632,153612,264529,602208,1163648,1967616,2027516],[1284,2055,3847,5126,6658,9350,9605]),([14,42009,73824,106992,153612,264529,602208,1163648,1967616],[]),([14,42009,73824,153612,264529,602208,1163648,1967616],[1828,3876,5157,6438,6689]),([14,42009,73824,153612,264529,602208,1163648,1967616,1990156],[2049,3844,7044,8196,8452,9348]),([14,42009,77920,77920,153612,264529,602208,1163648,1967616],[]),([14,42009,77920,115072,153612,264529,602208,1163648,1967616],[3842,5122,5890,6658]),([14,42009,77920,129532,153612,264529,602208,1163648,1967616],[]),([14,42009,77920,129532,153612,264529,653820,1163648,1967616],[]),([14,42009,77920,129532,153612,264529,751724,1163648,1967616],[2564]),([14,42009,77920,129532,153612,264529,1163648,1700320,1967616],[]),([14,42009,77920,129532,153612,342384,602208,1163648,1967616],[]),([14,42009,77920,129532,153612,602208,866672,1163648,1967616],[]),([14,42009,77920,129532,153612,602208,1163648,1427920,1967616],[2050,3842,6658]),([14,42009,77920,129532,153612,866672,1163648,1967616],[5538,6690]),([14,42009,77920,153612,227436,264529,602208,1163648,1967616],[1796]),([14,42009,77920,153612,260604,264529,602208,1163648,1967616],[]),([14,42009,77920,153612,264529,602208,602208,1163648,1967616],[3844]),([14,42009,77920,153612,264529,602208,653820,1163648,1967616],[]),([14,42009,77920,153612,264529,602208,751724,1163648,1967616],[1796]),([14,42009,77920,153612,264529,602208,1163648,1176032,1967616],[3842,6658]),([14,42009,77920,153612,264529,602208,1163648,1178108,1967616],[3842,6658]),([14,42009,77920,153612,264529,602208,1163648,1300876,1967616],[1796,2049,3842,5124,6658]),([14,42009,77920,153612,264529,602208,1163648,1572860,1967616],[3842,6658]),([14,42009,77920,153612,264529,602208,1163648,1700320,1967616],[]),([14,42009,77920,153612,264529,602208,1163648,1967616],[1828,3876,5154,6436,6689,7590]),([14,42009,77920,153612,264529,602208,1163648,1967616,1990156],[2049,3844,7044,8196,8452,9348]),([14,42009,77920,153612,264529,602208,1163648,1967616,2045536],[3841,6404,8449]),([14,42009,77920,153612,264529,602208,1163648,1967616,2082688],[3843,5124,6404,8449,9345]),([14,42009,77920,153612,264529,602208,1163648,1967616,2097148],[]),([14,42009,77920,153612,264529,653820,1163648,1967616],[1828,6436,6693,7590]),([14,42009,77920,153612,264529,751724,1163648,1967616],[1796,1828,5154,6436,6693,7590]),([14,42009,77920,153612,264529,1163648,1700320,1967616],[1828,4002,6436,6695,7841]),([14,42009,77920,153612,342384,602208,1163648,1967616],[7585]),([14,42009,77920,153612,602208,866672,1163648,1967616],[5154,6689,7329]),([14,42009,77920,153612,602208,1163648,1427920,1967616],[2818,3874,4002,5122,5154,6689,6818,7329]),([14,42009,77920,153612,866672,1163648,1967616],[4322,4578,5155,5857,6115]),([14,42009,80240,129532,153612,602208,866672,1163648,1967616],[]),([14,42009,80240,153612,602208,866672,1163648,1967616],[5154,5282,6689,7585]),([14,42009,96364,129532,153612,264529,602208,1163648,1967616],[]),([14,42009,96364,153612,264529,602208,751724,1163648,1967616],[1798]),([14,42009,96364,153612,264529,602208,1163648,1967616],[1828,5154,5282,6436,6692]),([14,42009,106992,153612,153612,264529,602208,1163648,1967616],[1796]),([14,42009,106992,153612,260604,264529,602208,1163648,1967616],[]),([14,42009,106992,153612,264529,602208,635376,1163648,1967616],[5124]),([14,42009,106992,153612,264529,602208,751724,1163648,1967616],[1798,3845,4354]),([14,42009,106992,153612,264529,602208,1163648,1700320,1967616],[5250]),([14,42009,106992,153612,264529,602208,1163648,1967616],[1828,3876,5157,5282,5666,6438,6689]),([14,42009,106992,153612,264529,602208,1163648,1967616,1990156],[2049,7044,8196]),([14,42009,106992,153612,264529,602208,1163648,1967616,2063980],[3845,4354]),([14,42009,106992,153612,264529,602208,1163648,1967616,2097148],[]),([14,42009,106992,153612,264529,602208,1163648,1990156,2045536],[2054,3842,4098,4354,6404,8836]),([14,42009,106992,153612,264529,602208,1163648,1990156,2074608],[2052,8836]),([14,42009,106992,153612,371184,602208,1163648,1967616],[5154,5282,5666,6433,6689]),([14,42009,106992,153612,371184,602208,1163648,1967616,1990156],[2049,9092]),([14,42009,106992,153612,602208,866672,1163648,1967616],[3138,5154,5282,6433,6689,7203]),([14,42009,106992,153612,602208,866672,1163648,1967616,1990156],[2049,3075,7170,8962]),([14,42009,113148,153612,264529,602208,1163648,1967616],[1828,3876,5154,5282,6436,6689]),([14,42009,113148,153612,264529,602208,1163648,1967616,1984000],[6404,6658,6786,8196]),([14,42009,113148,153612,264529,602208,1163648,1984000],[1828,2082,3876,5154,5282,6436,6690,6818]),([14,42009,127456,129532,153612,264529,602208,1163648,1967616],[]),([14,42009,127456,153612,264529,602208,1163648,1700320,1967616],[5250]),([14,42009,127456,153612,264529,602208,1163648,1967616],[1828,4162,5154,5282,5666,6438,6689]),([14,42009,129532,129532,153612,264529,602208,1163648,1967616],[]),([14,42009,129532,131072,153612,395600,602208,1163648,1967616],[1796,5378]),([14,42009,129532,131072,153612,602208,866672,1163648,1967616],[4098]),([14,42009,129532,153612,153612,264529,602208,1163648,1967616],[1796]),([14,42009,129532,153612,219148,264529,602208,1163648,1967616],[1798,2049,2564]),([14,42009,129532,153612,227436,264529,602208,1163648,1967616],[1798]),([14,42009,129532,153612,260604,264529,602208,1163648,1967616],[]),([14,42009,129532,153612,260604,602208,866672,1163648,1967616],[]),([14,42009,129532,153612,264529,602208,602208,1163648,1967616],[]),([14,42009,129532,153612,264529,602208,618592,1163648,1967616],[3845,4354,5890]),([14,42009,129532,153612,264529,602208,620652,1163648,1967616],[4354]),([14,42009,129532,153612,264529,602208,651744,1163648,1967616],[]),([14,42009,129532,153612,264529,602208,653820,1163648,1967616],[]),([14,42009,129532,153612,264529,602208,677900,1163648,1967616],[1798,2049,4868]),([14,42009,129532,153612,264529,602208,733280,1163648,1967616],[3845,4354,5890]),([14,42009,129532,153612,264529,602208,751724,1163648,1967616],[1798,4354]),([14,42009,129532,153612,264529,602208,784892,1163648,1967616],[]),([14,42009,129532,153612,264529,602208,1163648,1650784,1967616],[3847,4354,5250,7426]),([14,42009,129532,153612,264529,602208,1163648,1700320,1967616],[5250]),([14,42009,129532,153612,264529,602208,1163648,1702396,1967616],[5250]),([14,42009,129532,153612,264529,602208,1163648,1833452,1967616],[1798,5250]),([14,42009,129532,153612,264529,602208,1163648,1967616],[1828,5154,5282,5666,6438]),([14,42009,129532,153612,264529,602208,1163648,1967616,1967616],[6406]),([14,42009,129532,153612,264529,602208,1163648,1967616,1971712],[6404,8198]),([14,42009,129532,153612,264529,602208,1163648,1967616,1990156],[2049,7044,8196]),([14,42009,129532,153612,264529,602208,1163648,1967616,2033152],[6404,8196]),([14,42009,129532,153612,264529,602208,1163648,1967616,2045536],[3845,4354,6404]),([14,42009,129532,153612,264529,602208,1163648,1967616,2063980],[4354]),([14,42009,129532,153612,264529,602208,1163648,1967616,2095072],[6404]),([14,42009,129532,153612,264529,602208,1163648,1967616,2097148],[]),([14,42009,129532,153612,264529,602208,1163648,1971712],[1828,5154,5282,5666,6436]),([14,42009,129532,153612,264529,602208,1163648,1990156,2045536],[2054,3842,4098,4354,6404,8836]),([14,42009,129532,153612,264529,602208,1163648,2033152],[1828,5154,5282,5666,5922,6436]),([14,42009,129532,153612,264529,602208,1163648,2045536,2082688],[3842,4354]),([14,42009,129532,153612,264529,602208,1167744,1967616],[1828,5156,5282,6438,6692,6820]),([14,42009,129532,153612,264529,602208,1178108,1967616,2082688],[5124,6404,8578]),([14,42009,129532,153612,264529,602208,1294720,1967616],[1828,5156,5282,6438,6692,6820]),([14,42009,129532,153612,264529,602208,1300876,1700320,1967616],[1798,5250]),([14,42009,129532,153612,264529,602208,1300876,1967616,2082688],[1798,5126,6404,8578]),([14,42009,129532,153612,264529,602208,1687936,1967616],[1828,5158,5282,6438,6694,6822,7458]),([14,42009,129532,153612,264529,602208,1700320,1967616,2082688],[5124,6404,8578,9345]),([14,42009,129532,153612,268624,602208,1163648,1967616],[1828,5282,5666,6436]),([14,42009,129532,153612,330064,602208,1163648,1967616],[5154,5282,5666]),([14,42009,129532,153612,342384,602208,1163648,1967616],[5282,5666]),([14,42009,129532,153612,395600,602208,1163648,1967616],[1828,5154,5282,5666,6438]),([14,42009,129532,153612,602208,602208,866672,1163648,1967616],[]),([14,42009,129532,153612,602208,653820,866672,1163648,1967616],[]),([14,42009,129532,153612,602208,653820,1163648,1427920,1967616],[3970,4482,5250,6018]),([14,42009,129532,153612,602208,751724,866672,1163648,1967616],[2818,4354,5634]),([14,42009,129532,153612,602208,751724,1163648,1427920,1967616],[4226,4482,5250,7170]),([14,42009,129532,153612,602208,788816,1163648,1967616],[1830,2849,3873,5153,5282,5922,6438,6689,6817,7202]),([14,42009,129532,153612,602208,866672,866672,1163648,1967616],[]),([14,42009,129532,153612,602208,866672,915964,1163648,1967616],[]),([14,42009,129532,153612,602208,866672,1014140,1163648,1967616],[]),([14,42009,129532,153612,602208,866672,1163648,1700320,1967616],[5250])]
noncomputable def k33 : CE := [([14,42009,129532,153612,602208,866672,1163648,1964528,1967616],[5250]),([14,42009,129532,153612,602208,866672,1163648,1967616],[3138,5154,5282,7202]),([14,42009,129532,153612,602208,866672,1163648,1967616,1990156],[2049,3074,7170,8962]),([14,42009,129532,153612,602208,866672,1163648,1967616,2045536],[2818,4354,8962]),([14,42009,129532,153612,602208,866672,1163648,1967616,2047856],[]),([14,42009,129532,153612,602208,866672,1163648,1967616,2082688],[7170,8578]),([14,42009,129532,153612,602208,866672,1163648,1967616,2097148],[]),([14,42009,129532,153612,602208,1163648,1700320,1964528,1967616],[3970]),([14,42009,129532,153612,602208,1163648,1964528,1967616],[3138,3874,3970,4002,4034,7202]),([14,42009,129532,153612,602208,1300876,1427920,1967616],[3970,4002,4034,5282,5538]),([14,42009,129532,153612,602208,1427920,1967616,2082688],[3873,4002,5153,5281,6083,6689,6786,6818,6850]),([14,42009,129532,219148,264529,602208,1163648,1967616],[1830,2081,3873,5155,5282,5666,5922,6438,6689,6817]),([14,42009,129532,260604,264529,602208,1163648,1967616,1990156],[2049,7044]),([14,42009,129532,264529,602208,677900,1163648,1967616],[2849,3622,3873,5155,5282,6438,6689,6817,7202]),([14,42009,129532,264529,602208,751724,1163648,1300876,1967616],[3074,5250,6786]),([14,42009,129532,264529,602208,751724,1163648,1967616,1990156],[3074,3841,7170,7558,8198]),([14,42009,131072,153612,395600,602208,933500,1163648,1967616],[1284,3842]),([14,42009,131072,153612,395600,602208,1163648,1701548,1967616],[1284,3842,4354,7810]),([14,42009,131072,153612,395600,602208,1163648,1966076,1967616],[1284,3842,7300,9857]),([14,42009,131072,153612,602208,669228,1163648,1427920,1967616],[1284,2818,3970]),([14,42009,131072,153612,602208,866672,933500,1163648,1967616],[1284,2818]),([14,42009,131072,153612,602208,866672,1163648,1494940,1967616],[1285,2818,3842,7557]),([14,42009,131072,153612,602208,866672,1163648,1966076,1967616],[2818,9857]),([14,42009,132620,153612,602208,866672,1163648,1964528,1967616],[2818]),([14,42009,132620,153612,602208,866672,1163648,1967616],[1316,1828,2818,2882,3138,5154,6438,6689,6817,7203]),([14,42009,132620,153612,602208,1163648,1700320,1964528,1967616],[2818]),([14,42009,132620,153612,602208,1163648,1964528,1967616],[1316,1828,2818,2882,3138,3874,6438,6689,6817,7203,7457]),([14,42009,135180,153612,602208,669228,1163648,1427920,1967616],[1284]),([14,42009,135180,153612,602208,1163648,1427920,1967616],[1316,1828,2050,2082,3874,4002,5154,5282,5538,6436,6689,6818]),([14,42009,137228,153612,602208,866672,933500,1163648,1967616],[1284,1796,2818]),([14,42009,137228,153612,602208,866672,1163648,1967616],[1316,1796,1828,2818,5154,5538,6436,6689]),([14,42009,137228,153612,602208,933500,1163648,1427920,1967616],[1284,1796,2050,3842,7556]),([14,42009,137228,153612,602208,1163648,1427920,1967616],[1316,1796,1828,2050,2082,3874,4002,4258,5154,5282,5538,6436,6691,6818]),([14,42009,153612,153612,260604,264529,602208,1163648,1967616],[1284]),([14,42009,153612,153612,264529,602208,949884,1163648,1967616],[1284,1540,1668,5124]),([14,42009,153612,153612,264529,602208,1048572,1163648,1967616],[1284]),([14,42009,153612,153612,264529,602208,1163648,1966076,1967616],[1284]),([14,42009,153612,153612,264529,602208,1163648,1967616],[1284,1316,5154,5282,5666,6436,6692,6820]),([14,42009,153612,153612,264529,602208,1163648,1967616,2031612],[1284,1540,1668,8452]),([14,42009,153612,153612,264529,602208,1163648,1967616,2080764],[1284,1537,1665,8580]),([14,42009,153612,153612,264529,602208,1163648,1967616,2097148],[1284]),([14,42009,153612,161916,264529,602208,1163648,1967616],[1316,4260,5153,5410,5538,6436,6689,6948,7076]),([14,42009,153612,161916,264529,602208,1163648,1967616,2082688],[2179,5126,5382,6404,6660,8449,8837]),([14,42009,153612,219148,264529,602208,1163648,1967616,2031612],[1286,1796,2049,2180,8449,9348,9605]),([14,42009,153612,227436,264529,602208,1163648,1967616],[1286,1316,5153,5410,5538,6436,6689,6948,7076]),([14,42009,153612,260604,260604,264529,602208,1163648,1967616],[]),([14,42009,153612,260604,264529,602208,653820,1163648,1967616],[]),([14,42009,153612,260604,264529,602208,751724,1163648,1967616],[1286,4354]),([14,42009,153612,260604,264529,602208,784892,1163648,1967616],[]),([14,42009,153612,260604,264529,602208,1163648,1700320,1967616],[5506]),([14,42009,153612,260604,264529,602208,1163648,1967616],[1316,5410,5538,5666,6438,6689,7076]),([14,42009,153612,260604,264529,602208,1163648,1967616,1990156],[1286,2049,2180,6788,7044,8196,8449]),([14,42009,153612,260604,264529,602208,1163648,1967616,2045536],[2177,4103,4354,6404,6662,8836]),([14,42009,153612,260604,264529,602208,1163648,1967616,2097148],[]),([14,42009,153612,260604,602208,866672,1163648,1967616],[2882,5410,5538,6438,6689,7202]),([14,42009,153612,264529,417308,602208,1163648,1700320,1967616],[2564,3847,4357,5126,5636,6657]),([14,42009,153612,264529,417308,602208,1163648,1967616],[1316,2564,2596,3873,4388,5155,5410,5669,5794,6436,7204,7334]),([14,42009,153612,264529,524284,602208,1163648,1700320,1967616],[5762]),([14,42009,153612,264529,524284,602208,1163648,1967616],[1316,5410,5666,5794,6438,7334]),([14,42009,153612,264529,602208,618592,1163648,1967616,2080764],[3074,4357,4481,8580,8965,9348,9603]),([14,42009,153612,264529,602208,620652,1163648,1967616],[1316,3074,4548,5153,5669,6050,6436,7205,7460,7585]),([14,42009,153612,264529,602208,651744,1163648,1967616],[1316,2885,4548,5794,6050,6438,7205,7457,7585]),([14,42009,153612,264529,602208,653820,653820,1163648,1967616],[]),([14,42009,153612,264529,602208,653820,751724,1163648,1967616],[1286,3074]),([14,42009,153612,264529,602208,653820,784892,1163648,1967616],[]),([14,42009,153612,264529,602208,653820,1163648,1178108,1967616],[4482,6018]),([14,42009,153612,264529,602208,653820,1163648,1300876,1967616],[1287,3970,4482,6018,7554]),([14,42009,153612,264529,602208,653820,1163648,1700320,1967616],[6018]),([14,42009,153612,264529,602208,653820,1163648,1702396,1967616],[6018]),([14,42009,153612,264529,602208,653820,1163648,1967616],[1316,4548,6050,6438,7205,7585]),([14,42009,153612,264529,602208,653820,1163648,1967616,1990156],[3841,4484,6788,7170,8196]),([14,42009,153612,264529,602208,653820,1163648,1967616,2045536],[3074,4357,4481,6404,8965,9348]),([14,42009,153612,264529,602208,653820,1163648,1967616,2082688],[4483,5892,6404,7170,9347]),([14,42009,153612,264529,602208,653820,1163648,1967616,2097148],[]),([14,42009,153612,264529,602208,751724,784892,1163648,1967616],[1286,3074]),([14,42009,153612,264529,602208,751724,1048572,1163648,1967616],[1286,3074]),([14,42009,153612,264529,602208,751724,1163648,1441788,1967616],[1286,3074,3970,4482]),([14,42009,153612,264529,602208,751724,1163648,1572860,1967616],[1286,3074,3970,4482]),([14,42009,153612,264529,602208,751724,1163648,1966076,1967616],[1286,3074]),([14,42009,153612,264529,602208,751724,1163648,1967616],[1286,1316,3074,4548,5153,5669,6050,6436,6689,7205,7460,7590]),([14,42009,153612,264529,602208,751724,1163648,1967616,2093052],[1287,3075,3971,4483]),([14,42009,153612,264529,602208,751724,1163648,1967616,2097148],[1286,3074]),([14,42009,153612,264529,602208,784892,1163648,1967616],[1316,4548,6050,6438,6689,7207,7590]),([14,42009,153612,264529,602208,917500,1163648,1967616],[1316,4548,5410,6050,6438,7585]),([14,42009,153612,264529,602208,1048572,1048572,1163648,1967616],[]),([14,42009,153612,264529,602208,1048572,1163648,1700320,1967616],[6018]),([14,42009,153612,264529,602208,1048572,1163648,1967616],[1316,4548,5410,6050,6438,7590]),([14,42009,153612,264529,602208,1048572,1163648,1967616,2097148],[]),([14,42009,153612,264529,602208,1163648,1700320,1702396,1967616],[]),([14,42009,153612,264529,602208,1163648,1700320,1966076,1967616],[]),([14,42009,153612,264529,602208,1163648,1700320,1967616],[1316,2885,3908,4130,4514,5828,6085,6438,7207,7462,7713,7841]),([14,42009,153612,264529,602208,1163648,1700320,1967616,2031612],[5764,6020]),([14,42009,153612,264529,602208,1163648,1700320,1967616,2097148],[]),([14,42009,153612,264529,602208,1163648,1702396,1967616],[1316,4130,5828,6085,6438,7205,7460,7841]),([14,42009,153612,264529,602208,1163648,1966076,1966076,1967616],[]),([14,42009,153612,264529,602208,1163648,1966076,1967616],[1316,4130,5828,6085,6438,7841]),([14,42009,153612,264529,602208,1163648,1966076,1967616,2097148],[]),([14,42009,153612,264529,602208,1163648,1967616],[1316,3938,4066,4130,4902,5220,5348,5729,5857,5987,6115]),([14,42009,153612,264529,602208,1163648,1967616,2097148],[1316,4130,4902,7364,7621,7873]),([14,42009,153612,264529,602208,1163648,1967616,2097148,2097148],[]),([14,42009,153612,264529,602208,1163648,1971712,2093052],[1316,4130,4900,6789,6821,6853,7297,7329,7361,7621,7843,7878]),([14,42009,153612,264529,602208,1163648,1982076,2082688],[1316,3908,4130,4420,5698,7843,7878]),([14,42009,153612,264529,602208,1163648,1990156,2074608],[1316,2852,3877,4130,4900,6788,6822,6852,7490,7841,7876]),([14,42009,153612,264529,602208,1163648,2031612,2033152],[1316,4130,4389,4420,5764,5796,5828,6021,6053,6085,6436,7841,7876]),([14,42009,153612,268624,602208,933500,1163648,1967616],[1316,4548,5410,6436,7585]),([14,42009,153612,268624,602208,1163648,1494940,1967616],[1316,4130,5314,5509,5541,5573,6085,6436,7843]),([14,42009,153612,268624,602208,1163648,1828524,1967616],[1316,1828,3075,3107,4097,4131,5314,5761,5793,5825,6436,7841]),([14,42009,153612,268624,602208,1163648,1967616,2093052],[1316,3105,4130,4900,6850,7044,7079,7108,7297,7329,7361,7873]),([14,42009,153612,330064,602208,933500,1163648,1967616],[1316,4228,4260,4292,4548,5410,6438,7457,7585]),([14,42009,153612,330064,602208,1163648,1767084,1967616],[1316,1828,4130,5828,5954,6085,6438,7713,7841]),([14,42009,153612,330064,602208,1163648,1967616,2031612],[1316,4130,4902,7044,7076,7108,7364,7621,7873]),([14,42009,153612,342384,602208,1163648,1967616],[1316,4066,4130,4322,4900,5601,5857,6115]),([14,42009,153612,371184,602208,1163648,1967616],[3938,4066,4130,4194,4322,4897,5473,5601,5729,5857,5987,6115]),([14,42009,153612,371184,602208,1163648,1967616,1990156],[2081,2849,3875,4130,4897,5281,5954,7044,7076,7108,7364,7490,7621,7873]),([14,42009,153612,395600,602208,933500,1163648,1967616],[1316,4548,6438,6689,7457,7585]),([14,42009,153612,395600,602208,1163648,1701548,1967616],[1316,1828,3074,3138,4130,5954,6018,6050,6082,6438,6689,7713,7841]),([14,42009,153612,395600,602208,1163648,1966076,1967616],[1316,4130,5508,5540,5572,6082,6438,6689,7809,7841,7873]),([14,42009,153612,396828,602208,866672,1163648,1700320,1967616],[1796,3074,4228]),([14,42009,153612,396828,602208,866672,1163648,1967616],[1316,1796,1828,2882,4228,4260,4292,6438,6945,7073,7203]),([14,42009,153612,396828,602208,1163648,1700320,1964528,1967616],[1796,3074,7044]),([14,42009,153612,396828,602208,1163648,1964528,1967616],[1316,1796,1828,2882,4130,5508,5540,5572,6438,6945,7073,7203,7457]),([14,42009,153612,602208,602208,866672,933500,1163648,1967616],[5508]),([14,42009,153612,602208,602208,866672,1163648,1230476,1967616],[2306,2434,4098]),([14,42009,153612,602208,602208,866672,1163648,1494940,1967616],[7557]),([14,42009,153612,602208,653820,866672,1163648,1967616],[2114,5794,6438,6946,7329]),([14,42009,153612,602208,653820,1163648,1427920,1967616],[3010,3202,4386,4482,4514,4546,5666,5794,6435,6946,7202,7329]),([14,42009,153612,602208,669228,687660,1163648,1427920,1967616],[5121]),([14,42009,153612,602208,669228,734828,1163648,1427920,1967616],[3204,6914]),([14,42009,153612,602208,669228,751724,1163648,1427920,1967616],[1286,3204,5121,6914]),([14,42009,153612,602208,669228,1163648,1300876,1427920,1967616],[1286,2819,5634]),([14,42009,153612,602208,669228,1163648,1427920,1427920,1967616],[5634,5762]),([14,42009,153612,602208,669228,1163648,1427920,1563100,1967616],[2819,5250,7170]),([14,42009,153612,602208,669228,1163648,1427920,1700320,1967616],[3074,7170,7300]),([14,42009,153612,602208,669228,1163648,1427920,1832876,1967616],[7170]),([14,42009,153612,602208,669228,1163648,1427920,1964528,1967616],[3074,7170,7300]),([14,42009,153612,602208,669228,1163648,1427920,1967616],[1316,3268,4386,4514,5666,5794,6438,7201,7329,7457]),([14,42009,153612,602208,669228,1163648,1427920,1967616,1990156],[3841,7297,8196,8962]),([14,42009,153612,602208,669228,1163648,1427920,1967616,2097148],[8962]),([14,42009,153612,602208,669228,1163648,1964528,1967616],[1316,2114,3074,3106,3268,4258,4386,5796,6438,6947,7201,7329,7457]),([14,42009,153612,602208,669228,1300876,1427920,1967616],[1286,1316,2081,2817,2849,3268,5282,6438,6689,7201,7329]),([14,42009,153612,602208,669228,1427920,1832876,1967616],[1316,3268,6438,7201,7329,7713]),([14,42009,153612,602208,687660,1163648,1427920,1967616],[2946,3010,3268,3841,3875,4386,4514,5155,5666,5794,6439,7202,7329]),([14,42009,153612,602208,734828,1163648,1427920,1967616],[3202,4130,4386,4514,5378,5410,5666,6433,7201,7329,7457]),([14,42009,153612,602208,751724,866672,933500,1163648,1967616],[1286,3074,4098,5378,5508]),([14,42009,153612,602208,751724,866672,1163648,1494940,1967616],[1287,3074,4098,6657,6914,7042,7298,7557]),([14,42009,153612,602208,751724,933500,1163648,1427920,1967616],[1286,2946,3202,4228,4354,5121,6914,7556]),([14,42009,153612,602208,751724,1163648,1427920,1494940,1967616],[1287,2946,3202,3841,5378,6659,7170,7298]),([14,42009,153612,602208,786428,1163648,1427920,1967616],[2946,3010,3202,4386,4482,4514,4546,5666,5794,6439,7202,7329]),([14,42009,153612,602208,800880,866672,933500,1163648,1967616],[]),([14,42009,153612,602208,800880,866672,1163648,1967616],[1316,2114,3268,6050,6438,6947,7201,7329,7457,7585])]
noncomputable def k34 : CE := [([14,42009,153612,602208,800880,933500,1163648,1967616],[1316,2114,4292,6438,6947,7457,7585]),([14,42009,153612,602208,800880,1163648,1967616],[1316,2114,3300,3938,4066,4902,5411,5473,5601,5729,5857,5987,6115]),([14,42009,153612,602208,801136,933500,1163648,1967616],[1316,2114,4292,6438,6947,7457,7585]),([14,42009,153612,602208,801136,1163648,1967616],[1316,2114,3300,3938,4066,4581,4902,5411,5473,5601,5729,5857,5987,6115]),([14,42009,153612,602208,866672,866672,933500,1163648,1967616],[]),([14,42009,153612,602208,866672,866672,1163648,1494940,1967616],[7301]),([14,42009,153612,602208,866672,915964,1163648,1967616],[2114,6050,6438,6947,7585]),([14,42009,153612,602208,866672,933500,949884,1163648,1967616],[]),([14,42009,153612,602208,866672,933500,999036,1163648,1967616],[4228]),([14,42009,153612,602208,866672,933500,999292,1163648,1967616],[]),([14,42009,153612,602208,866672,933500,1014140,1163648,1967616],[]),([14,42009,153612,602208,866672,933500,1163648,1700320,1967616],[4098,7556]),([14,42009,153612,602208,866672,933500,1163648,1964528,1967616],[]),([14,42009,153612,602208,866672,933500,1163648,1967616],[1316,2114,4292,6438,6947,7457,7585]),([14,42009,153612,602208,866672,933500,1163648,1967616,1990156],[2051,6914,7553,8196,8706]),([14,42009,153612,602208,866672,933500,1163648,1967616,2097148],[]),([14,42009,153612,602208,866672,949884,1163648,1967616],[1316,2114,4292,5153,6050,6436,6947,7585]),([14,42009,153612,602208,866672,999036,1163648,1967616],[1316,2114,5410,6438,6947,7457,7585]),([14,42009,153612,602208,866672,999292,1163648,1967616],[1316,2114,6050,6438,6947,7457,7585]),([14,42009,153612,602208,866672,1014140,1163648,1494940,1967616],[7301,7554]),([14,42009,153612,602208,866672,1048572,1163648,1967616],[2114,6050,6438,6947,7585]),([14,42009,153612,602208,866672,1163648,1494940,1499036,1967616],[2051,5250,5765]),([14,42009,153612,602208,866672,1163648,1494940,1560476,1967616],[5765,6021,7298]),([14,42009,153612,602208,866672,1163648,1494940,1700320,1967616],[5765,7170,7813]),([14,42009,153612,602208,866672,1163648,1494940,1964528,1967616],[3202,5765,7170,7810]),([14,42009,153612,602208,866672,1163648,1494940,1967616],[1317,2114,4386,5314,5765,5797,5829,6085,6439,6947,7713,7843]),([14,42009,153612,602208,866672,1163648,1494940,1967616,1990156],[2051,5250,5765,6914,7811,8197,8706]),([14,42009,153612,602208,866672,1163648,1494940,1967616,2097148],[5765]),([14,42009,153612,602208,866672,1163648,1499036,1967616],[2051,2081,2114,4386,6085,6438,6946,7843]),([14,42009,153612,602208,866672,1163648,1560476,1967616],[2114,4386,5314,5762,5794,5826,6082,6433,6947,7713,7843]),([14,42009,153612,602208,866672,1163648,1572860,1967616],[2114,4386,6082,6433,6946,7843]),([14,42009,153612,602208,866672,1163648,1832684,1967616],[2114,3074,3106,4130,4258,5378,5410,6018,6050,6082,6433,6947,7073,7713,7841]),([14,42009,153612,602208,866672,1163648,1966076,1967616],[2114,6082,6433,6947,7841]),([14,42009,153612,602208,866672,1163648,1967616,2031356],[1316,2114,4902,5411,7108,7621,7873]),([14,42009,153612,602208,866672,1163648,1967616,2031612],[1316,2114,4902,5411,7108,7621,7873]),([14,42009,153612,602208,866672,1163648,1967616,2097148],[2114,4897,5411,7618,7873]),([14,42009,153612,602208,933500,1163648,1700320,1964528,1967616],[3074,5764]),([14,42009,153612,602208,933500,1163648,1964528,1967616],[1316,2114,3268,6438,6947,7201,7329,7457]),([14,42009,153612,602208,933500,1300876,1427920,1967616],[1286,1316,2081,2817,2849,3268,5282,5796,6438,6689,7201,7329]),([14,42009,153612,602208,1300876,1427920,1494940,1967616],[1287,1317,2081,4002,5250,5282,5314,6437,6689,7843]),([14,42009,153612,602208,1427920,1832876,1967616],[3042,4546,4578,4897,5473,5601,5729,5859,5921,5985,6113]),([14,88548,153612,602208,866672,1163648,1967616,2008600],[1316,1828,2114,2596,3617,3746,4868,4902,5025,5378,5410,6433,6561]),([14,129532,153612,195612,602208,866672,1163648,1967616],[2818,2882,4898,5026,5154,7202]),([14,129532,153612,602208,866672,1163648,1967616,2008600],[1318,1830,2114,2598,3617,3746,4897,5025,5378,5410,6433]),([15,0,4096,42009,153612,264529,602208,1163648,1967616],[67,2052,3588,6660]),([15,0,42009,65536,153612,264529,602208,1163648,1967616],[132,2052,3073,3588]),([15,0,42009,153612,264529,602208,1163648,1967616],[161,293,356,2084,2564,2628,3620,4901,5666,6433,6694]),([15,4096,4096,42009,153612,264529,602208,1163648,1967616],[1796,6404]),([15,4096,16384,42009,153612,264529,602208,1163648,1967616],[5,68,1797,2052,2562,3586,4866,6402,8194]),([15,4096,42009,65536,153612,264529,602208,1163648,1967616],[3,132,1284,2052,3076]),([15,4096,42009,153612,153612,264529,602208,1163648,1967616],[2,132,1284,2052]),([15,4096,42009,153612,264529,602208,751724,1163648,1967616],[1284,1924,2052,5380,6404]),([15,4096,42009,153612,264529,602208,1048576,1163648,1967616],[3,1287,1795,2563,3587,4865,5124,5380,6403,8199]),([15,4096,42009,153612,264529,602208,1163648,1167744,1967616],[2,324,388,1284,1794,3586,4868,4996,6402,7684,8194]),([15,4096,42009,153612,264529,602208,1163648,1300876,1967616],[5,388,1284,1794,2052,3586,4868,6402,8194]),([15,4096,42009,153612,264529,602208,1163648,1700320,1967616],[3,388,1284,4868]),([15,4096,42009,153612,264529,602208,1163648,1967616],[3,164,356,1284,1348,2084,3620,4132,4868,4898,4932,6438,6692]),([15,4096,42009,153612,264529,602208,1163648,1967616,2082688],[3,1284,1795,3587,4868,6660,8195,9348]),([15,4096,42009,153612,264529,602208,1163648,1971712],[356,1284,1348,2084,3620,4132,4898,6692]),([15,4096,42009,153612,264529,751724,1163648,1967616],[1348,2084,4866,4898,6402,6439,6692,6948]),([15,4096,42009,153612,268624,602208,1163648,1967616],[2084,2852,6692]),([15,4096,42009,153612,602208,866672,1163648,1967616],[1,4898,6433,6692]),([15,4096,42009,153612,602208,1163648,1427920,1967616],[3,1794,1826,2562,3618,3746,4866,4898,5026,6402,6433,6562]),([15,6144,42009,153612,602208,866672,1163648,1967616],[3,2562,4898,6433]),([15,20480,42009,153612,264529,602208,1163648,1700320,1967616],[1,1284,3589,4098,4868]),([15,20480,42009,153612,264529,602208,1163648,1967616],[1,290,1284,3589,3650,4162,4868,4898,5026,5410,5666,6438]),([15,42009,65536,65536,153612,264529,602208,1163648,1967616],[1284,2817]),([15,42009,65536,131072,153612,264529,602208,1163648,1967616],[68,1284,1796,2822,5124,5378,6660,8452,8964]),([15,42009,65536,153612,219148,264529,602208,1163648,1967616],[129,193,1284,1798,2049,2177,2564,3073]),([15,42009,65536,153612,264529,602208,602208,1163648,1967616],[68,258,1284,2054,3844,6660,8452]),([15,42009,65536,153612,264529,602208,751724,1163648,1967616],[68,323,1284,1798,2049,4354]),([15,42009,65536,153612,264529,602208,1163648,1700320,1967616],[258,1284,2049,3970,4354,7426]),([15,42009,65536,153612,264529,602208,1163648,1967616],[68,161,290,1284,1316,1828,2049,2113,3876,5157,5666,5922,6438,6689]),([15,42009,65536,153612,264529,602208,1163648,1967616,1990156],[68,1284,2049,3844,5124,7044,8196,8452,9348,9605]),([15,42009,65536,153612,264529,602208,1163648,2033152],[161,290,1284,1316,1828,2052,3876,5157,5666,5922,6436]),([15,42009,65536,153612,264529,602208,1700320,1967616],[161,258,1284,1316,1828,2054,2113,6438,6660,6689,7457,7585]),([15,42009,65536,153612,264529,1700320,1967616],[161,1284,1316,1828,2049,2113,4902,5153,5217,5985,6113]),([15,42009,65536,153612,330064,602208,1163648,1967616],[161,290,2049,2113,3105,4418,5154,5666,5922,6433,6689]),([15,42009,65536,153612,602208,866672,1163648,1967616],[161,290,2049,2113,3138,5154,5666,6433,6689,7203]),([15,42009,65600,153612,602208,1163648,1427920,1967616],[66,161,2051,2113,2210,2818,3874,4002,5122,5154,6433,6658,6689,6818,7457]),([15,42009,69632,153612,264529,602208,1163648,1300876,1967616],[69,390,1284,1796,2051,3842,5124,6658,8450]),([15,42009,69632,153612,264529,602208,1163648,1967616],[71,1284,1316,1828,2049,3876,5124,5154,6436,6689,7590]),([15,42009,131072,153612,395600,602208,1163648,1967616],[161,290,1284,1316,1828,2596,3105,3842,3906,4418,5154,5666,6438,6689,6945]),([15,42009,131072,153612,602208,866672,1163648,1967616],[161,290,1316,1828,2818,2882,3138,5154,6438,6689,6945,7203]),([15,42009,153612,153612,264529,602208,751724,1163648,1967616],[65,327,1284,4354]),([15,42009,153612,153612,264529,602208,1163648,1967616],[65,97,293,356,1284,1316,5154,5282,5666,6436,6692,6820]),([15,42009,153612,153612,264529,602208,1163648,1967616,1990156],[65,1284,1540,1668,6788,8196,8452]),([15,42009,153612,219148,264529,602208,1163648,1967616],[65,97,129,161,293,356,1286,1316,1796,1828,2049,2081,3873,4004,5155,5285,5410,5538,5666,5922,6436,6689,6822,6948,7076]),([15,42009,153612,264529,602208,618592,1163648,1967616],[97,197,229,263,295,356,1316,2885,3074,4357,4389,4548,5153,5669,5794,6050,6436,7205,7329,7457,7585]),([15,42009,153612,264529,602208,751724,751724,1163648,1967616],[259,1286,3074]),([15,42009,153612,264529,602208,751724,1163648,1300876,1967616],[65,263,390,1286,3074,3841,3970,4482,5250,6018,6657]),([15,42009,153612,264529,602208,751724,1163648,1700320,1967616],[197,259,388,1286,3074,4357,5126,6018,7173]),([15,42009,153612,264529,602208,751724,1163648,1833452,1967616],[263,385,1286,3074,6018,9857]),([15,42009,153612,264529,602208,751724,1163648,1967616],[97,229,259,291,356,1286,1316,2980,3074,4548,5153,5669,6050,6436,6689,7205,7460,7590]),([15,42009,153612,264529,602208,751724,1163648,1967616,2082688],[259,1287,3075,3971,4483,5121,5894,6404,6660,7170,7426,8449,8965]),([15,42009,153612,264529,602208,1163648,1700320,1700320,1967616],[324]),([15,42009,153612,264529,602208,1163648,1700320,1833452,1967616],[324,385,1286,9857]),([15,42009,153612,264529,602208,1163648,1700320,1967616],[97,229,292,324,356,1316,2885,3908,4130,4514,5828,6085,6438,7207,7462,7713,7841]),([15,42009,153612,264529,602208,1163648,1700320,1967616,1990156],[324,2819,3841,5121,5764,6020,6788,7170,8196,8965,9220]),([15,42009,153612,264529,602208,1163648,1833452,1967616],[97,229,292,321,353,1286,1316,4130,5828,6085,6438,6689,7207,7462,7809,7841,7873]),([15,42009,153612,264529,602208,1163648,1967616],[97,229,292,1316,3938,4066,4130,4902,5220,5348,5729,5857,5987,6115]),([15,42009,153612,264529,602208,1163648,1971712],[97,229,292,354,1316,2854,2882,3938,4066,4130,4900,5348,5860,6119]),([15,42009,153612,264529,602208,1163648,1990156,2045536],[97,229,292,418,1316,2821,2852,2882,3074,3877,4130,4386,4868,4900,5796,5828,6788,6820,6852]),([15,42009,153612,264529,602208,1163648,2033152],[97,229,292,1316,3938,4066,4130,4389,4420,4900,5348,5857,5986,6115]),([15,42009,153612,264529,602208,1163648,2045536,2082688],[97,229,292,354,1316,2882,3074,4130,4389,4420,5186,6051,6083,7329,7361,7842]),([15,42009,153612,268624,602208,1163648,1967616],[97,1316,1828,3300,4066,4130,4325,4900,5601,5857,6115]),([15,42009,153612,330064,602208,1163648,1967616],[97,226,1316,1828,2081,3938,4066,4130,4194,4322,4902,5473,5601,5729,5857,5987,6115]),([15,42009,153612,395600,602208,1163648,1967616],[97,226,1316,1828,2081,3138,3300,3938,4066,4130,4194,4325,4902,5153,5473,5601,5729,5857,5987,6115]),([15,42009,153612,602208,602208,866672,1163648,1967616],[97,1316,6438,6945,7073]),([15,42009,153612,602208,751724,866672,1163648,1967616],[97,130,195,227,290,1286,2114,3074,3106,4098,4130,5153,5410,5538,5794,6436,6689,6946,7073,7329]),([15,42009,153612,602208,751724,1163648,1427920,1967616],[99,195,227,1287,2946,3010,3202,3841,3875,4130,4386,4514,5155,5378,5410,5666,5794,6435,6691,6946,7202,7329]),([15,42009,153612,602208,866672,866672,1163648,1967616],[97,194,226,1316,2114,5794,6438,6947,7201,7329]),([15,42009,153612,602208,866672,1014140,1163648,1967616],[97,226,263,295,1316,2114,5153,6050,6436,6689,6947,7585]),([15,42009,153612,602208,866672,1163648,1700320,1967616],[97,226,2114,4258,4546,6082,6433,6947,7457,7713,7841]),([15,42009,153612,602208,866672,1163648,1964528,1967616],[97,194,226,2114,4514,4546,6082,6433,6947,7201,7329,7457,7713,7841]),([15,42009,153612,602208,866672,1163648,1967616],[97,226,2114,3938,4066,4578,4897,5411,5473,5601,5729,5857,5987,6115]),([15,42009,153612,602208,866672,1163648,1967616,1990156],[97,226,1316,2051,2081,2114,2849,3873,4902,5281,5378,5411,6404,6436,6914,6946,7108,7621,7873]),([15,42009,153612,602208,1163648,1700320,1964528,1967616],[97,162,2114,3234,4546,6433,6947,7201,7457,7585]),([15,42009,153612,602208,1163648,1964528,1967616],[97,162,2114,2914,3042,4578,4897,5411,5473,5601,5665,5731,5859,5985,6113]),([15,42009,153612,602208,1300876,1427920,1967616],[97,225,1281,2081,4002,4066,4897,5153,5473,5601,5859,6115]),([15,153612,195612,602208,866672,1163648,1967616],[33,97,165,229,292,1795,1830,1858,2276,2660,3172,3300,3622,3682,3810,3938,4069,4578,4964,5092,5156,5220,5350,5410,5478,5606,5734,5857,6115]),([16,0,42009,129532,153612,264529,602208,1163648,1967616],[2852,3588,3652,6434,6946,7074,7458,8486]),([16,0,42009,153612,264529,602208,1163648,1967616],[2084,2564,2628,3620,3684,4901,4965,5474,5602,5666,6433,6497,6694,7012,7140,7521,7649,7779,7907]),([16,4096,42009,129532,153612,264529,602208,1163648,1967616],[1284,1348,2852,6434,8484]),([16,4096,42009,153612,264529,602208,1163648,1494940,1967616],[1285,1348,1797,1829,2084,3589,3621,4132,4869,4901,4932,5029,6405,6437,6565,8197,8231,8357,8484,9764,9892]),([16,4096,42009,153612,264529,602208,1163648,1967616,2093052],[1284,1348,1795,1826,2084,3587,3622,4868,4898,4932,5027,6438,6563,6692,8227,8355,9348,9380,9412,9924]),([16,14460,42009,153612,264529,602208,1163648,1967616],[2084,3620,3684,3748,3812,4898,5602,6438,6500,6692,7012,7140,7524,7654,7907]),([16,14460,42009,153612,264529,602208,1163648,1967616,2082688],[2084,3620,3748,4868,4898,4932,5027,5444,5956,6438,6563,6660,6692,8227,8355,9284,9412,9924]),([16,22540,42009,129532,153612,264529,602208,1163648,1967616],[1284,6434,6562,6946,7074,7202,7458]),([16,22540,42009,153612,264529,602208,1163648,1967616],[1284,4898,4962,5026,5090,5410,5474,5602,5666,6436,7654,7778,7911]),([16,42009,65536,129532,153612,264529,602208,1163648,1967616],[1284,1316,2596,6690,6946,7074,7458,7714,8230]),([16,42009,65536,153612,264529,602208,933500,1163648,1967616],[1284,1316,1828,2054,2084,2113,2212,3844,3876,5124,5156,5284,6020,6052,6084,6660,6692,7202,7458,8230,8452,8486,8612,9505,9633]),([16,42009,65536,153612,264529,602208,1163648,1967616,2031612],[1284,1316,1828,2049,2113,2212,3844,3876,5124,5157,5666,5922,6438,6689,6820,8484,8612,9348,9380,9412,9605,9637,9669,9921]),([16,42009,77920,129532,153612,264529,602208,1163648,1967616],[2596,6690,8228,9638]),([16,42009,77920,153612,264529,602208,1163648,1967616],[1828,3876,5154,5602,6436,6689,7140,7590,7654,7907]),([16,42009,106992,153612,264529,602208,1163648,1967616],[1828,3876,5157,5218,5282,5346,5474,5602,5666,6438,6689,6753,7140,7521,7649,7779,7907]),([16,42009,106992,153612,264529,602208,1163648,1967616,1990156],[1828,2049,2113,2212,3876,4129,5157,5282,5411,5666,6438,6689,6820,7044,7078,7108,7746,8196,8228,8484,8612,9412,9538,9669,9921]),([16,42009,129532,153612,260604,264529,602208,1163648,1967616],[1828,6690,6818,7202,7330,7458,8230,9124]),([16,42009,129532,153612,264529,602208,653820,1163648,1967616],[1828,6818,7842,8230,9250,9638]),([16,42009,129532,153612,264529,602208,751724,1163648,1967616],[1798,1828,4354,6690,6818,7458,7842,8228,9250,9638]),([16,42009,129532,153612,264529,602208,1163648,1700320,1967616],[1828,4162,5154,5250,5282,5314,5666,6050,7874,8230,9250,9889]),([16,42009,129532,153612,264529,602208,1163648,1967616,1990156],[1828,2049,5154,5282,5410,5666,6438,6692,6820,7044,7078,7108,7746,8196,8228,8484,9412,9538,9669]),([16,42009,129532,153612,264529,602208,1163648,1967616,2045536],[1830,3845,3906,4162,4354,5154,5282,5666,5922,6404,6438,6689,6817,7585,8481,8900,9667]),([16,42009,129532,153612,264529,602208,1163648,1967616,2097148],[1828,5154,5282,5666,6438,9666]),([16,42009,129532,153612,602208,866672,1163648,1967616],[3138,5154,5218,5282,5346,5474,5602,6114,7202,7393,7649,7907]),([16,42009,153612,260604,264529,602208,1163648,1967616],[1316,5218,5346,5410,5474,5538,5602,5666,6438,6689,6884,7076,7140,7654,7778,7911]),([16,42009,153612,264529,602208,653820,1163648,1967616],[1316,4548,4580,5346,6050,6114,6438,6884,7205,7398,7585,7654,7907]),([16,42009,153612,264529,602208,1048572,1163648,1967616],[1316,4548,4580,5218,5346,5410,6050,6114,6438,6756,6884,7270,7398,7590,7654,7779,7907]),([16,42009,153612,264529,602208,1163648,1966076,1967616],[1316,3938,4066,4130,5828,5860,6085,6117,6438,6756,6884,7265,7393,7523,7651,7841,7905]),([16,42009,153612,264529,602208,1163648,1967616,2097148],[1316,3938,4066,4130,4902,5220,5348,5729,5857,5987,6115,7364,7396,7621,7653,7873,7905])]
noncomputable def k35 : CE := [([16,42009,153612,602208,669228,1163648,1427920,1967616],[1316,3268,3300,4066,4386,4514,5346,5666,5794,6114,6438,7009,7137,7201,7265,7329,7393,7457,7521,7651,7777,7907]),([16,42009,153612,602208,866672,933500,1163648,1967616],[1316,2114,4292,4324,5218,5346,5858,6438,6947,7009,7137,7265,7393,7457,7521,7585,7649,7779,7907]),([16,42009,153612,602208,866672,1163648,1494940,1967616],[1317,2114,3938,4066,4386,4578,5314,5346,5765,5797,5829,5861,6085,6117,6439,6947,7009,7137,7265,7393,7523,7651,7713,7777,7843,7907]),([17,4096,42009,153612,264529,602208,1163648,1967616],[3,164,356,1284,1348,2084,3620,3684,4132,4868,4898,4932,6438,6500,6692,7012,7140,7524,7652]),([17,42009,65536,153612,264529,602208,1163648,1967616],[68,161,290,1284,1316,1828,2049,2113,3876,5157,5218,5474,5602,5666,5922,6438,6689,6753,7521,7649,7779,7907]),([17,42009,153612,264529,602208,751724,1163648,1967616],[97,229,259,291,356,1286,1316,2980,3074,4548,4580,5153,5346,5669,6050,6114,6436,6689,6756,6884,7205,7268,7398,7460,7524,7590,7654,7907]),([17,42009,153612,264529,602208,1163648,1700320,1967616],[97,229,292,324,356,1316,2885,3908,3938,4066,4130,4514,5828,5860,6085,6117,6438,6884,7207,7265,7393,7462,7523,7651,7713,7777,7841,7905]),([17,42009,153612,602208,866672,1163648,1967616],[97,226,2114,3938,4066,4578,4897,5411,5473,5601,5729,5857,5987,6115]),([18,42009,129532,153612,264529,602208,1163648,1967616],[1828,5154,5218,5282,5346,5474,5602,5666,6438,7140,7654,7778,7911]),([19,42009,153612,264529,602208,1163648,1967616],[97,229,292,1316,3938,4066,4130,4902,5220,5348,5729,5857,5987,6115])]
noncomputable def G3_LL : List CE := [k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35]
noncomputable def G3_L : CE := G3_LL.flatten
noncomputable def G3_T : BinaryTree (List ℕ) := buildBT (G3_L.map Prod.fst)
noncomputable def ok3 (kh : List ℕ × List ℕ) : Bool := stepOK G3_m G3_y G3_nz G3_G G3_T kh.1 kh.2
noncomputable def sl (l : CE) (s : ℕ) : Bool := ((l.drop s).take 30).all ok3
set_option maxRecDepth 200000 in
theorem g0 : k0.all ok3 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g1 : k1.all ok3 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g2 : k2.all ok3 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g3 : k3.all ok3 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g4_0 : sl k4 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g4_1 : sl k4 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g4_2 : sl k4 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g4_3 : sl k4 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g4_4 : sl k4 120 = true := by decide +kernel
theorem g4 : k4.all ok3 = true := all_of_5 (by decide +kernel) g4_0 g4_1 g4_2 g4_3 g4_4
set_option maxRecDepth 200000 in
theorem g5_0 : sl k5 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g5_1 : sl k5 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g5_2 : sl k5 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g5_3 : sl k5 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g5_4 : sl k5 120 = true := by decide +kernel
theorem g5 : k5.all ok3 = true := all_of_5 (by decide +kernel) g5_0 g5_1 g5_2 g5_3 g5_4
set_option maxRecDepth 200000 in
theorem g6_0 : sl k6 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g6_1 : sl k6 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g6_2 : sl k6 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g6_3 : sl k6 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g6_4 : sl k6 120 = true := by decide +kernel
theorem g6 : k6.all ok3 = true := all_of_5 (by decide +kernel) g6_0 g6_1 g6_2 g6_3 g6_4
set_option maxRecDepth 200000 in
theorem g7_0 : sl k7 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g7_1 : sl k7 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g7_2 : sl k7 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g7_3 : sl k7 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g7_4 : sl k7 120 = true := by decide +kernel
theorem g7 : k7.all ok3 = true := all_of_5 (by decide +kernel) g7_0 g7_1 g7_2 g7_3 g7_4
set_option maxRecDepth 200000 in
theorem g8_0 : sl k8 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g8_1 : sl k8 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g8_2 : sl k8 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g8_3 : sl k8 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g8_4 : sl k8 120 = true := by decide +kernel
theorem g8 : k8.all ok3 = true := all_of_5 (by decide +kernel) g8_0 g8_1 g8_2 g8_3 g8_4
set_option maxRecDepth 200000 in
theorem g9_0 : sl k9 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g9_1 : sl k9 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g9_2 : sl k9 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g9_3 : sl k9 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g9_4 : sl k9 120 = true := by decide +kernel
theorem g9 : k9.all ok3 = true := all_of_5 (by decide +kernel) g9_0 g9_1 g9_2 g9_3 g9_4
set_option maxRecDepth 200000 in
theorem g10_0 : sl k10 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g10_1 : sl k10 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g10_2 : sl k10 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g10_3 : sl k10 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g10_4 : sl k10 120 = true := by decide +kernel
theorem g10 : k10.all ok3 = true := all_of_5 (by decide +kernel) g10_0 g10_1 g10_2 g10_3 g10_4
set_option maxRecDepth 200000 in
theorem g11_0 : sl k11 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g11_1 : sl k11 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g11_2 : sl k11 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g11_3 : sl k11 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g11_4 : sl k11 120 = true := by decide +kernel
theorem g11 : k11.all ok3 = true := all_of_5 (by decide +kernel) g11_0 g11_1 g11_2 g11_3 g11_4
set_option maxRecDepth 200000 in
theorem g12_0 : sl k12 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g12_1 : sl k12 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g12_2 : sl k12 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g12_3 : sl k12 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g12_4 : sl k12 120 = true := by decide +kernel
theorem g12 : k12.all ok3 = true := all_of_5 (by decide +kernel) g12_0 g12_1 g12_2 g12_3 g12_4
set_option maxRecDepth 200000 in
theorem g13_0 : sl k13 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g13_1 : sl k13 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g13_2 : sl k13 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g13_3 : sl k13 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g13_4 : sl k13 120 = true := by decide +kernel
theorem g13 : k13.all ok3 = true := all_of_5 (by decide +kernel) g13_0 g13_1 g13_2 g13_3 g13_4
set_option maxRecDepth 200000 in
theorem g14_0 : sl k14 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g14_1 : sl k14 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g14_2 : sl k14 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g14_3 : sl k14 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g14_4 : sl k14 120 = true := by decide +kernel
theorem g14 : k14.all ok3 = true := all_of_5 (by decide +kernel) g14_0 g14_1 g14_2 g14_3 g14_4
set_option maxRecDepth 200000 in
theorem g15_0 : sl k15 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g15_1 : sl k15 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g15_2 : sl k15 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g15_3 : sl k15 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g15_4 : sl k15 120 = true := by decide +kernel
theorem g15 : k15.all ok3 = true := all_of_5 (by decide +kernel) g15_0 g15_1 g15_2 g15_3 g15_4
set_option maxRecDepth 200000 in
theorem g16_0 : sl k16 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g16_1 : sl k16 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g16_2 : sl k16 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g16_3 : sl k16 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g16_4 : sl k16 120 = true := by decide +kernel
theorem g16 : k16.all ok3 = true := all_of_5 (by decide +kernel) g16_0 g16_1 g16_2 g16_3 g16_4
set_option maxRecDepth 200000 in
theorem g17_0 : sl k17 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g17_1 : sl k17 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g17_2 : sl k17 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g17_3 : sl k17 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g17_4 : sl k17 120 = true := by decide +kernel
theorem g17 : k17.all ok3 = true := all_of_5 (by decide +kernel) g17_0 g17_1 g17_2 g17_3 g17_4
set_option maxRecDepth 200000 in
theorem g18_0 : sl k18 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g18_1 : sl k18 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g18_2 : sl k18 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g18_3 : sl k18 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g18_4 : sl k18 120 = true := by decide +kernel
theorem g18 : k18.all ok3 = true := all_of_5 (by decide +kernel) g18_0 g18_1 g18_2 g18_3 g18_4
set_option maxRecDepth 200000 in
theorem g19_0 : sl k19 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g19_1 : sl k19 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g19_2 : sl k19 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g19_3 : sl k19 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g19_4 : sl k19 120 = true := by decide +kernel
theorem g19 : k19.all ok3 = true := all_of_5 (by decide +kernel) g19_0 g19_1 g19_2 g19_3 g19_4
set_option maxRecDepth 200000 in
theorem g20_0 : sl k20 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g20_1 : sl k20 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g20_2 : sl k20 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g20_3 : sl k20 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g20_4 : sl k20 120 = true := by decide +kernel
theorem g20 : k20.all ok3 = true := all_of_5 (by decide +kernel) g20_0 g20_1 g20_2 g20_3 g20_4
set_option maxRecDepth 200000 in
theorem g21_0 : sl k21 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g21_1 : sl k21 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g21_2 : sl k21 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g21_3 : sl k21 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g21_4 : sl k21 120 = true := by decide +kernel
theorem g21 : k21.all ok3 = true := all_of_5 (by decide +kernel) g21_0 g21_1 g21_2 g21_3 g21_4
set_option maxRecDepth 200000 in
theorem g22_0 : sl k22 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g22_1 : sl k22 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g22_2 : sl k22 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g22_3 : sl k22 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g22_4 : sl k22 120 = true := by decide +kernel
theorem g22 : k22.all ok3 = true := all_of_5 (by decide +kernel) g22_0 g22_1 g22_2 g22_3 g22_4
set_option maxRecDepth 200000 in
theorem g23_0 : sl k23 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g23_1 : sl k23 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g23_2 : sl k23 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g23_3 : sl k23 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g23_4 : sl k23 120 = true := by decide +kernel
theorem g23 : k23.all ok3 = true := all_of_5 (by decide +kernel) g23_0 g23_1 g23_2 g23_3 g23_4
set_option maxRecDepth 200000 in
theorem g24_0 : sl k24 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g24_1 : sl k24 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g24_2 : sl k24 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g24_3 : sl k24 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g24_4 : sl k24 120 = true := by decide +kernel
theorem g24 : k24.all ok3 = true := all_of_5 (by decide +kernel) g24_0 g24_1 g24_2 g24_3 g24_4
set_option maxRecDepth 200000 in
theorem g25_0 : sl k25 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g25_1 : sl k25 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g25_2 : sl k25 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g25_3 : sl k25 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g25_4 : sl k25 120 = true := by decide +kernel
theorem g25 : k25.all ok3 = true := all_of_5 (by decide +kernel) g25_0 g25_1 g25_2 g25_3 g25_4
set_option maxRecDepth 200000 in
theorem g26_0 : sl k26 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g26_1 : sl k26 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g26_2 : sl k26 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g26_3 : sl k26 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g26_4 : sl k26 120 = true := by decide +kernel
theorem g26 : k26.all ok3 = true := all_of_5 (by decide +kernel) g26_0 g26_1 g26_2 g26_3 g26_4
set_option maxRecDepth 200000 in
theorem g27_0 : sl k27 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g27_1 : sl k27 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g27_2 : sl k27 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g27_3 : sl k27 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g27_4 : sl k27 120 = true := by decide +kernel
theorem g27 : k27.all ok3 = true := all_of_5 (by decide +kernel) g27_0 g27_1 g27_2 g27_3 g27_4
set_option maxRecDepth 200000 in
theorem g28_0 : sl k28 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g28_1 : sl k28 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g28_2 : sl k28 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g28_3 : sl k28 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g28_4 : sl k28 120 = true := by decide +kernel
theorem g28 : k28.all ok3 = true := all_of_5 (by decide +kernel) g28_0 g28_1 g28_2 g28_3 g28_4
set_option maxRecDepth 200000 in
theorem g29_0 : sl k29 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g29_1 : sl k29 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g29_2 : sl k29 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g29_3 : sl k29 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g29_4 : sl k29 120 = true := by decide +kernel
theorem g29 : k29.all ok3 = true := all_of_5 (by decide +kernel) g29_0 g29_1 g29_2 g29_3 g29_4
set_option maxRecDepth 200000 in
theorem g30_0 : sl k30 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g30_1 : sl k30 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g30_2 : sl k30 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g30_3 : sl k30 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g30_4 : sl k30 120 = true := by decide +kernel
theorem g30 : k30.all ok3 = true := all_of_5 (by decide +kernel) g30_0 g30_1 g30_2 g30_3 g30_4
set_option maxRecDepth 200000 in
theorem g31_0 : sl k31 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g31_1 : sl k31 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g31_2 : sl k31 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g31_3 : sl k31 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g31_4 : sl k31 120 = true := by decide +kernel
theorem g31 : k31.all ok3 = true := all_of_5 (by decide +kernel) g31_0 g31_1 g31_2 g31_3 g31_4
set_option maxRecDepth 200000 in
theorem g32_0 : sl k32 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g32_1 : sl k32 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g32_2 : sl k32 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g32_3 : sl k32 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g32_4 : sl k32 120 = true := by decide +kernel
theorem g32 : k32.all ok3 = true := all_of_5 (by decide +kernel) g32_0 g32_1 g32_2 g32_3 g32_4
set_option maxRecDepth 200000 in
theorem g33_0 : sl k33 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g33_1 : sl k33 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g33_2 : sl k33 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g33_3 : sl k33 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g33_4 : sl k33 120 = true := by decide +kernel
theorem g33 : k33.all ok3 = true := all_of_5 (by decide +kernel) g33_0 g33_1 g33_2 g33_3 g33_4
set_option maxRecDepth 200000 in
theorem g34_0 : sl k34 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g34_1 : sl k34 30 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g34_2 : sl k34 60 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g34_3 : sl k34 90 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem g34_4 : sl k34 120 = true := by decide +kernel
theorem g34 : k34.all ok3 = true := all_of_5 (by decide +kernel) g34_0 g34_1 g34_2 g34_3 g34_4
set_option maxRecDepth 200000 in
theorem g35 : k35.all ok3 = true := by decide +kernel
theorem G3_hL : G3_L.all ok3 = true := by
  apply all_flatten; simp only [G3_LL, List.all_cons, List.all_nil, Bool.and_true, g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15,g16,g17,g18,g19,g20,g21,g22,g23,g24,g25,g26,g27,g28,g29,g30,g31,g32,g33,g34,g35]


def encX : ∀ {n : ℕ}, (Fin n → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, x => Nat.bit (x 0) (encX fun i => x i.succ)

theorem encX_lt : ∀ {n : ℕ} (x : Fin n → Bool), encX x < 2 ^ n
  | 0, _ => by simp [encX]
  | n + 1, x => by
    have ih := encX_lt (fun i : Fin n => x i.succ)
    simp only [encX, Nat.bit_val, Nat.pow_succ]
    cases x 0 <;> (simp; omega)

theorem pt_encX : ∀ {n : ℕ} (x : Fin n → Bool), pt n (encX x) = x
  | 0, x => funext fun i => i.elim0
  | n + 1, x => funext fun i => by
    cases i using Fin.cases with
    | zero => simp [pt, encX]
    | succ j =>
      have ih := congrFun (pt_encX (fun k : Fin n => x k.succ)) j
      simpa [pt, encX, Nat.testBit_bit_succ] using ih

theorem bfn_eq_of_check {n : ℕ} {f g : BFn n}
    (h : (List.range (2 ^ n)).all (fun a => f (pt n a) == g (pt n a)) = true) :
    ∀ x, f x = g x := by
  intro x
  have hm := List.all_eq_true.1 h (encX x) (List.mem_range.2 (encX_lt x))
  rw [pt_encX x] at hm
  exact beq_iff_eq.1 hm

theorem nonConst_of_check {n : ℕ} {f : BFn n}
    (h : ((List.range (2 ^ n)).any fun a => f (pt n a) != f (pt n 0)) = true) : NonConst f := by
  obtain ⟨a, _, ha⟩ := List.any_eq_true.1 h
  exact ⟨pt n a, pt n 0, by simpa using ha⟩

theorem depends_of_check {n : ℕ} {f : BFn n} {i : Fin n}
    (h : ((List.range (2 ^ n)).any fun a =>
      f (Function.update (pt n a) i false) != f (Function.update (pt n a) i true)) = true) :
    Depends f i := by
  obtain ⟨a, _, ha⟩ := List.any_eq_true.1 h
  exact ⟨pt n a, by simpa using ha⟩

theorem all_dep_nc_of_check {n : ℕ} {f : BFn (n + 1)}
    (h : (List.finRange (n + 1)).all (fun i =>
      ((List.range (2 ^ (n + 1))).any fun a =>
        f (Function.update (pt (n + 1) a) i false) != f (Function.update (pt (n + 1) a) i true)) &&
      ((List.range (2 ^ n)).any fun a => restrict i false f (pt n a) != restrict i false f (pt n 0)) &&
      ((List.range (2 ^ n)).any fun a => restrict i true f (pt n a) != restrict i true f (pt n 0))) = true) :
    ∀ i : Fin (n + 1), Depends f i ∧ NonConst (restrict i false f) ∧ NonConst (restrict i true f) := by
  intro i
  have hi := List.all_eq_true.1 h i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at hi
  exact ⟨depends_of_check hi.1.1, nonConst_of_check hi.1.2, nonConst_of_check hi.2⟩

theorem noFalseTwins_of_check {n : ℕ} {f : BFn n}
    (h : (List.finRange n).all (fun u => (List.finRange n).all fun v =>
      (u == v) || (List.range (2 ^ n)).any fun a =>
        (f (Function.update (Function.update (pt n a) u true) v false) !=
          f (Function.update (Function.update (pt n a) u false) v true)) ||
        (f (Function.update (Function.update (pt n a) u true) v false) !=
          f (Function.update (Function.update (pt n a) u true) v true))) = true) :
    NoFalseTwins f := by
  intro u v huv
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h u (List.mem_finRange u)) v (List.mem_finRange v)
  have hne : (u == v) = false := beq_false_of_ne huv
  rw [hne, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨a, _, ha⟩ := h1
  rw [Bool.or_eq_true] at ha
  refine ⟨pt n a, ?_⟩
  rcases ha with ha | ha
  · left; simpa using ha
  · right; simpa using ha

def edgesG : List ℕ :=
  [0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def fG : BFn 7 := fun x =>
  decide (∃ i < edgesG.length / 2,
    (List.ofFn x).getD (edgesG.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgesG.getD (2 * i + 1) 0) false = true)

def fG_b : BFn 7 := fun x =>
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) ||
  (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5) ||
  (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def fK4 : BFn 4 := fun x =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)

theorem fG_eq : ∀ x : Fin 7 → Bool, fG x = fG_b x := bfn_eq_of_check (by decide +kernel)

theorem has1NotBin_congr {n b : ℕ} {f g : BFn n} (hfg : ∀ x, f x = g x)
    (h : Has1NotBin n f b) : Has1NotBin n g b := by
  obtain ⟨gs, o, hcl, hb, hn, ho, hev⟩ := h
  exact ⟨gs, o, hcl, hb, hn, ho, fun x => (hev x).trans (hfg x)⟩

theorem has1NotBin_le {n b1 b2 : ℕ} {f : BFn n} (hle : b1 ≤ b2)
    (h : Has1NotBin n f b1) : Has1NotBin n f b2 := by
  obtain ⟨gs, o, hcl, hb, hn, ho, hev⟩ := h
  exact ⟨gs, o, hcl, hb.trans hle, hn, ho, hev⟩

theorem output_ne_input {n : ℕ} {f : BFn (n + 1)} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, val gs (n + 1) o x = f x) (i : Fin (n + 1))
    (hnc : NonConst (restrict i false f)) : o ≠ i.val := by
  intro heq; obtain ⟨y, y', hne⟩ := hnc; apply hne
  have h1 := hev (insFin i false y); have h2 := hev (insFin i false y')
  rw [heq] at h1 h2
  have hi1 := congrFun (val_input gs (n + 1) i) (insFin i false y)
  have hi2 := congrFun (val_input gs (n + 1) i) (insFin i false y')
  simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
  change f (insFin i false y) = f (insFin i false y')
  rw [← h1, ← h2, hi1, hi2]

theorem output_ne_not_input {n : ℕ} {f : BFn (n + 1)} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x, val gs (n + 1) o x = f x) (i : Fin (n + 1))
    (hnc : NonConst (restrict i false f)) (q : ℕ)
    (hq : gs[q]? = some ⟨GateOp.not, [i.val]⟩) : o ≠ n + 1 + q := by
  intro heq; obtain ⟨y, y', hne⟩ := hnc; apply hne
  have h1 := hev (insFin i false y); have h2 := hev (insFin i false y')
  rw [heq, val_gate (n + 1) gs q _ hq (cleanG_lt (hcl q _ hq))] at h1 h2
  have hi1 := congrFun (val_input gs (n + 1) i) (insFin i false y)
  have hi2 := congrFun (val_input gs (n + 1) i) (insFin i false y')
  simp only [insFin, lt_irrefl, dite_false, dite_true] at hi1 hi2
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at h1 h2
  change f (insFin i false y) = f (insFin i false y')
  rw [← h1, ← h2, hi1, hi2]

theorem K4_hp : prsOK K4_m K4_y K4_nz = true := by decide +kernel
theorem K4_hG : symOK K4_m K4_y K4_G = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem K4_hi : K4_xs.sublists.all (rootOK K4_m K4_y K4_nz K4_G K4_T 6) = true := by decide +kernel
theorem K4_hy : encL fK4 K4_pts = K4_y := by decide +kernel
theorem K4_hxs : (List.ofFn fun i : Fin 4 => packW (if i.val ∈ (∅ : Finset ℕ) then 1 else 0,
    encL (fun x : Fin 4 → Bool => x i) K4_pts)) = K4_xs := by
  simp only [Finset.notMem_empty, ite_false]
  decide +kernel

theorem no_k4 : ¬ Has1NotBin 4 fK4 6 := by
  rintro ⟨gs, o, hcl, hb, hn, ho, hev⟩
  exact lb_cert_tagged fK4 ∅ K4_pts K4_m K4_y K4_nz K4_xs K4_G K4_L 6
    (by decide) K4_hy (by simp) K4_hxs K4_hp K4_hG K4_hL K4_hi
    gs o hcl hb hn ho hev (by simp) (by simp) (by simp)

def fG0 : BFn 6 := restrict 0 false fG_b
def fG1 : BFn 6 := restrict 1 false fG_b
def fG2 : BFn 6 := restrict 2 false fG_b
def fG3 : BFn 6 := restrict 3 false fG_b

theorem G3_hp : prsOK G3_m G3_y G3_nz = true := by decide +kernel
theorem G3_hG : symOK G3_m G3_y G3_G = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem G3_hi : G3_xs.sublists.all (rootOK G3_m G3_y G3_nz G3_G G3_T 9) = true := by decide +kernel
theorem G3_hy : encL fG3 G3_pts = G3_y := by decide +kernel
theorem G3_hxs : (List.ofFn fun i : Fin 6 => packW (if i.val ∈ ({1, 2} : Finset ℕ) then 1 else 0,
    encL (fun x : Fin 6 → Bool => x i) G3_pts)) = G3_xs := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  decide +kernel

theorem no_g3 : ¬ Has1NotBin 6 fG3 9 := by
  rintro ⟨gs, o, hcl, hb, hn, ho, hev⟩
  have h1 := elim_two_or_once hcl hb hn ho hev 1
    (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel))
  have honce1 : OnceProp 6 gs o 1 := by
    rcases h1 with ⟨_, h1f⟩ | ⟨hO, _⟩
    · exfalso
      have h1k := elim_one 1 false (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) h1f
      exact no_k4 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) h1k.2)
    · exact hO
  have h2 := elim_two_or_once hcl hb hn ho hev 2
    (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel))
  have honce2 : OnceProp 6 gs o 2 := by
    rcases h2 with ⟨_, h2f⟩ | ⟨hO, _⟩
    · exfalso
      have h2k := elim_one 1 false (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) h2f
      exact no_k4 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) h2k.2)
    · exact hO
  exact lb_cert_tagged fG3 ({1, 2} : Finset ℕ) G3_pts G3_m G3_y G3_nz G3_xs G3_G G3_L 9
    (by decide) G3_hy
    (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> omega)
    G3_hxs G3_hp G3_hG G3_hL G3_hi gs o hcl hb hn ho hev
    (by intro w hw; simp at hw; rcases hw with rfl | rfl
        · exact output_ne_input hev 1 (nonConst_of_check (by decide +kernel))
        · exact output_ne_input hev 2 (nonConst_of_check (by decide +kernel)))
    (by intro q w hw hq; simp at hw; rcases hw with rfl | rfl
        · exact output_ne_not_input hcl hev 1 (nonConst_of_check (by decide +kernel)) q hq
        · exact output_ne_not_input hcl hev 2 (nonConst_of_check (by decide +kernel)) q hq)
    (by intro w hw; simp at hw; rcases hw with rfl | rfl
        · exact honce1
        · exact honce2)

theorem no_g0 : ¬ Has1NotBin 6 fG0 9 := by
  rintro ⟨gs, o, hcl, hb, hn, ho, hev⟩
  rcases elim_two_or_once hcl hb hn ho hev 1
    (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) with
    ⟨_, h0f⟩ | ⟨_, _, h0t⟩
  · have hk := elim_one 0 false (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) h0f
    exact no_k4 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) hk.2)
  · have hk := elim_one 4 false (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) h0t
    exact no_k4 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) hk.2)

theorem no_g6 : ¬ Has1NotBin 6 (restrict 6 false fG_b) 9 := by
  intro h
  let p : Fin 6 → Fin 6 := fun i => ⟨(i.val + 5) % 6, Nat.mod_lt _ (by omega)⟩
  exact no_g0 (perm_has1NotBin p (bfn_eq_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) h)

theorem elim_k4_of_5 {f : BFn 5} (i : Fin 5)
    (hd : Depends f i) (hnc : NonConst (restrict i false f))
    (heq : ∀ x, restrict i false f x = fK4 x) : ¬ Has1NotBin 5 f 7 := fun h =>
  no_k4 (has1NotBin_congr heq (elim_one i false hd hnc h).2)

theorem no_g1 : ¬ Has1NotBin 6 fG1 9 := by
  intro h
  obtain ⟨w, _, hw⟩ := elim_two_no_false_twins (all_dep_nc_of_check (by decide +kernel)) (noFalseTwins_of_check (by decide +kernel)) h
  fin_cases w
  · exact elim_k4_of_5 0 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 0 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw

theorem no_g2 : ¬ Has1NotBin 6 fG2 9 := by
  intro h
  obtain ⟨w, _, hw⟩ := elim_two_no_false_twins (all_dep_nc_of_check (by decide +kernel)) (noFalseTwins_of_check (by decide +kernel)) h
  fin_cases w
  · exact elim_k4_of_5 0 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 0 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw
  · exact elim_k4_of_5 1 (depends_of_check (by decide +kernel)) (nonConst_of_check (by decide +kernel)) (bfn_eq_of_check (by decide +kernel)) hw

theorem no_fG : ¬ Has1NotBin 7 fG_b 11 := by
  intro h
  obtain ⟨v, _, hv⟩ := elim_two_no_false_twins (all_dep_nc_of_check (by decide +kernel)) (noFalseTwins_of_check (by decide +kernel)) h
  fin_cases v
  · exact no_g0 hv
  · exact no_g1 hv
  · exact no_g2 hv
  · exact no_g3 hv
  · exact no_g3 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) hv)
  · exact no_g3 (has1NotBin_congr (bfn_eq_of_check (by decide +kernel)) hv)
  · exact no_g6 hv

def W13 : List Gate :=
  [⟨.or, [0, 6]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [9, 5]⟩,
   ⟨.and, [3, 4]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [13, 10]⟩,
   ⟨.and, [7, 2]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 15]⟩]

theorem W13_ok : ∀ g ∈ W13, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [W13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem W13_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨W13, 19⟩ (List.ofFn x) = fG x :=
  bfn_eq_of_check (by decide +kernel)

theorem notCount_le_one_of_unique : ∀ (gates : List Gate),
    (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j) → notCount gates ≤ 1
  | [], _ => by simp [notCount]
  | g :: gs, huniq => by
    rw [notCount_cons]
    cases hgn : isNotOp g.op with
    | false =>
      simp only [Bool.toNat_false, zero_add]
      exact notCount_le_one_of_unique gs (fun i j hi hj =>
        Fin.succ_inj.1 (huniq i.succ j.succ hi hj))
    | true =>
      have hgop : g.op = GateOp.not := (isNotOp_eq_true g.op).1 hgn
      have hzero : notCount gs = 0 := by
        by_contra hne
        have hlen : 0 < (gs.filter fun g' => isNotOp g'.op).length := by unfold notCount at hne; omega
        obtain ⟨g', hg'f⟩ := List.exists_mem_of_length_pos hlen
        obtain ⟨hg'm, hg'n⟩ := List.mem_filter.1 hg'f
        obtain ⟨k, hk⟩ := List.mem_iff_get.1 hg'm
        have hk' : (g :: gs).get k.succ = g' := hk
        have h0eq : (0 : Fin (g :: gs).length) = k.succ :=
          huniq 0 k.succ hgop (by rw [hk']; exact (isNotOp_eq_true g'.op).1 hg'n)
        exact Fin.succ_ne_zero k h0eq.symm
      simp [hzero]

theorem main_aux (gates : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gates, Ok g)
    (huniq : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (heval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = fG x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = fG x := by
  by_cases hnot0 : notCount gates = 0
  · refine ⟨gates, o, ?_, le_rfl, heval⟩
    intro g hg
    have hokg := hok g hg
    refine ⟨?_, hokg.2⟩
    rcases hokg.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hfil : gates.filter (fun g' => isNotOp g'.op) = [] :=
        List.eq_nil_of_length_eq_zero hnot0
      have hmem : g ∈ gates.filter (fun g' => isNotOp g'.op) :=
        List.mem_filter.2 ⟨hg, by simp [isNotOp, h]⟩
      rw [hfil] at hmem; simp at hmem
  · have hnot1 : notCount gates ≤ 1 := notCount_le_one_of_unique gates huniq
    have hnot_eq : notCount gates = 1 := by omega
    have hsum : binCount gates + notCount gates = gates.length := binCount_add_notCount gates hok
    have hhas : Has1NotBin 7 fG_b (binCount gates) :=
      of_raw_1not 7 fG_b (nonConst_of_check (by decide +kernel)) gates o hok hnot1
        (fun x => (heval x).trans (fG_eq x))
    have hge13 : 13 ≤ gates.length := by
      by_contra hlt
      have hble : binCount gates ≤ 11 := by omega
      exact no_fG (has1NotBin_le hble hhas)
    exact ⟨W13, 19, W13_ok, by simpa [W13] using hge13, W13_eval⟩

end PEqualNP.Outside.L_meta_10608_aux

theorem PEqualNP.Outside.L_meta_10608 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10608_aux.main_aux
