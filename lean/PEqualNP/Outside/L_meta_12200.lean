import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_12200.Bridge

-- Simplification engine from L-meta-4725, PR #9152.
namespace CircuitProof

open PEqualNP.CircuitLowerBounds

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
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
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
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

end PEqualNP.Outside.L_meta_12200.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12200.Bridge.CircuitProof

namespace PEqualNP.Outside.L_meta_12200.Bridge

private def hits (g : Gate) (marked : List Bool) : Bool :=
  g.inputs.any fun i => marked.getD i false

private def nextMarked (g : Gate) (marked : List Bool) : List Bool :=
  marked ++ [isNotGate g.op && hits g marked]

private def entry (g : Gate) (marked : List Bool) : Nat :=
  if !isNotGate g.op && hits g marked then 1 else 0

-- Counts binary gates reached from marked inputs by paths with no earlier binary gate.
def entries (marked : List Bool) : List Gate → Nat
  | [] => 0
  | g :: gs => entry g marked + entries (nextMarked g marked) gs

private def MarksConstants (marked : List Bool) (stats : List Stat) : Prop :=
  marked.length = stats.length ∧ ∀ i, marked.getD i false = true →
    ∃ b, stats.getD i (.inl false) = .inl b

private lemma hits_const (g : Gate) (marked : List Bool) (stats : List Stat)
    (hc : MarksConstants marked stats) (h : hits g marked = true) :
    ∃ b, (.inl b : Stat) ∈ g.inputs.map (fun i => stats.getD i (.inl false)) := by
  obtain ⟨i, hi, hmark⟩ := List.any_eq_true.mp h
  obtain ⟨b, hb⟩ := hc.2 i hmark
  exact ⟨b, List.mem_map.mpr ⟨i, hi, hb⟩⟩

private lemma extend_marks (n : Nat) (g : Gate) (marked : List Bool)
    (acc : List Stat × List Gate) (hc : MarksConstants marked acc.1)
    (hg : NOk g) : MarksConstants (nextMarked g marked) (elimStep n acc g).1 := by
  refine ⟨by simpa [nextMarked, elimStep] using hc.1, ?_⟩
  intro i hi
  by_cases hnew : i = marked.length
  · have hstats : i = acc.1.length := hnew.trans hc.1
    rw [nextMarked, getD_snoc_len _ _ _ _ hnew.symm, Bool.and_eq_true] at hi
    rcases g with ⟨op, ins⟩
    have hnot : op = .not := by cases op <;> simp_all [isNotGate]
    subst op
    have hlen := hg.2 rfl
    cases ins with
    | nil => simp [hits] at hi
    | cons i' rest =>
      have hrest : rest = [] := by simpa using hlen
      subst rest
      have hmarked : marked.getD i' false = true := by simpa [hits] using hi.2
      obtain ⟨b,hb⟩ := hc.2 i' hmarked
      refine ⟨!b, ?_⟩
      rw [elimStep, getD_snoc_len _ _ _ _ hstats.symm]
      change (simplify .not _ [acc.1.getD i' (.inl false)]).2 = _
      rw [hb]
      rfl
  · have hstats : i ≠ acc.1.length := fun he => hnew (he.trans hc.1.symm)
    rw [nextMarked, getD_snoc_ne _ _ _ _ hnew] at hi
    obtain ⟨b, hb⟩ := hc.2 i hi
    exact ⟨b, by simpa only [elimStep, getD_snoc_ne _ _ _ _ hstats] using hb⟩

private lemma count_step (n : Nat) (g : Gate) (marked : List Bool)
    (acc : List Stat × List Gate) (hc : MarksConstants marked acc.1) (hg : NOk g) :
    nonNotCount (elimStep n acc g).2 + entry g marked ≤
      nonNotCount acc.2 + (if !isNotGate g.op then 1 else 0) := by
  have bound := simplify_opCount_le (fun op => !isNotGate op) g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (.inl false))
  change nonNotCount (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList ≤ _ at bound
  by_cases h : ((!isNotGate g.op) && hits g marked) = true
  · obtain ⟨hbin, hh⟩ := Bool.and_eq_true_iff.mp h
    have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1.1
    have hn := simplify_count g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false)) hop
      (by simpa using hg.1.2) (fun he => by simpa using hg.2 he) (hits_const g marked acc.1 hc hh)
    change nonNotCount (acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList) + entry g marked ≤ _
    rw [hn]
    simp [entry, hbin, hh]
  · have hz : entry g marked = 0 := ite_eq_right h
    rw [hz, Nat.add_zero]
    change opCount (fun op => !isNotGate op) (acc.2 ++
      (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList) ≤ _
    rw [opCount_append]
    exact Nat.add_le_add_left bound _

-- Each marked binary entry saves one binary gate in constant simplification.
theorem eliminate_entries (n : Nat) (gs : List Gate) (marked : List Bool)
    (acc : List Stat × List Gate) (hc : MarksConstants marked acc.1)
    (legal : ∀ g ∈ gs, NOk g) :
    nonNotCount (elim n gs acc).2 + entries marked gs ≤ nonNotCount acc.2 + nonNotCount gs := by
  induction gs generalizing marked acc with
  | nil => simp [elim, entries, nonNotCount]
  | cons g gs ih =>
    have hg := legal g List.mem_cons_self
    have later := ih (nextMarked g marked) (elimStep n acc g) (extend_marks n g marked acc hc hg)
      (fun k hk => legal k (List.mem_cons_of_mem _ hk))
    have first := count_step n g marked acc hc hg
    change nonNotCount (elim n gs (elimStep n acc g)).2 +
      (entry g marked + entries (nextMarked g marked) gs) ≤
      nonNotCount acc.2 + opCount (fun op => !isNotGate op) (g :: gs)
    rw [opCount_cons]
    change _ ≤ nonNotCount acc.2 + (nonNotCount gs + _)
    omega

private lemma legal_elim (n : Nat) (gs : List Gate) (acc : List Stat × List Gate)
    (hacc : ∀ g ∈ acc.2, Ok g) : ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    apply ih (elimStep n acc g)
    intro q hq
    change q ∈ acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList at hq
    rcases List.mem_append.mp hq with hm | hm
    · exact hacc _ hm
    · exact simplify_ok _ _ _ q (by simpa using hm)

private def remap (initial : List Stat) (y : List Bool) : List Bool :=
  initial.map (Stat.val y)

private lemma init_inv (n : Nat) (initial : List Stat) (y : List Bool)
    (valid : ∀ s ∈ initial, s.Valid n) : Inv n y (remap initial y) (initial, []) := by
  refine ⟨by simp [remap], ?_⟩
  intro i
  simp only [wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
  simp only [remap, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases e : initial[i]? with
  | none => simp [Stat.val, Stat.Valid]
  | some s => simpa using valid s (List.mem_iff_getElem?.mpr ⟨i,e⟩)

-- Restrict and remap the input vector while deleting at least the marked binary entries.
theorem remap_removes_entries (n : Nat) (C : Circuit) (initial : List Stat) (marked : List Bool)
    (hc : MarksConstants marked initial) (valid : ∀ s ∈ initial, s.Valid n)
    (legal : ∀ g ∈ C.gates, NOk g)
    (nonconstant : ∃ a b : Fin n → Bool,
      C.eval (remap initial (List.ofFn a)) ≠ C.eval (remap initial (List.ofFn b))) :
    ∃ D : Circuit, FanInTwo D ∧ nonNotCount D.gates + entries marked C.gates ≤ nonNotCount C.gates ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (remap initial (List.ofFn y)) := by
  let run := elim n C.gates (initial, [])
  have eq (y : Fin n → Bool) : (run.1.getD C.output (.inl false)).val
      (wiresFrom run.2 (List.ofFn y)) = C.eval (remap initial (List.ofFn y)) :=
    (inv_elim n (List.ofFn y) (by simp) C.gates _ _ (fun g hg => (legal g hg).1)
      (init_inv n initial (List.ofFn y) valid)).2 C.output |>.2
  cases h : run.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨u,v,huv⟩ := nonconstant
    have hu := eq u
    have hv := eq v
    rw [h] at hu hv
    exact False.elim (huv (hu.symm.trans hv))
  | inr o =>
    refine ⟨⟨run.2, o⟩, legal_elim n C.gates (initial, []) (by simp), ?_, ?_⟩
    · simpa only [nonNotCount, List.countP_nil, Nat.zero_add] using
        eliminate_entries n C.gates marked (initial, []) hc legal
    · intro y
      have he := eq y
      rw [h] at he
      exact he

private def agreeUnmarked (marked w w' : List Bool) : Prop :=
  marked.length = w.length ∧ w.length = w'.length ∧
    ∀ i, marked.getD i false = false → w.getD i false = w'.getD i false

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def agreesAtEntries : List Gate → List Bool → List Bool → List Bool → Prop
  | [], _, _, _ => True
  | g :: gs, marked, w, w' =>
      (entry g marked = 1 → gateValue g w = gateValue g w') ∧
      agreesAtEntries gs (nextMarked g marked) (w ++ [gateValue g w]) (w' ++ [gateValue g w'])

private lemma gate_eq_of_no_hit (g : Gate) (marked w w' : List Bool)
    (h : agreeUnmarked marked w w') (hm : hits g marked = false) :
    gateValue g w = gateValue g w' := by
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro i hi
  apply h.2.2
  cases he : marked.getD i false with
  | false => rfl
  | true =>
    have ht : hits g marked = true := List.any_eq_true.mpr ⟨i, hi, he⟩
    simp [hm] at ht

-- If two evaluations agree at every binary entry, any remaining differences are on marked NOT paths.
theorem factor_at_entries (gs : List Gate) (marked w w' : List Bool)
    (h : agreeUnmarked marked w w') (enter : agreesAtEntries gs marked w w') :
    ∀ o, ((gs.foldl (fun a g => nextMarked g a) marked).getD o false = false) →
      (wiresFrom gs w).getD o false = (wiresFrom gs w').getD o false := by
  induction gs generalizing marked w w' with
  | nil => exact h.2.2
  | cons g gs ih =>
    change ∀ o, (List.foldl (fun a g => nextMarked g a) (nextMarked g marked) gs).getD o false = false →
      (wiresFrom gs (w ++ [gateValue g w])).getD o false =
        (wiresFrom gs (w' ++ [gateValue g w'])).getD o false
    apply ih _ _ _ _ enter.2
    refine ⟨by simp [nextMarked, h.1], by simp [h.2.1], ?_⟩
    intro i hi
    by_cases hnew : i = marked.length
    · have hw : i = w.length := hnew.trans h.1
      have hw' := hw.trans h.2.1
      rw [nextMarked, getD_snoc_len _ _ _ _ hnew.symm] at hi
      rw [getD_snoc_len _ _ _ _ hw.symm, getD_snoc_len _ _ _ _ hw'.symm]
      cases hh : hits g marked with
      | false => exact gate_eq_of_no_hit g marked w w' h hh
      | true =>
        have hn : isNotGate g.op = false := by simpa [hh] using hi
        exact enter.1 (by simp [entry, hn, hh])
    · have hw : i ≠ w.length := fun he => hnew (he.trans h.1.symm)
      have hw' : i ≠ w'.length := fun he => hw (he.trans h.2.1.symm)
      rw [nextMarked, getD_snoc_ne _ _ _ _ hnew] at hi
      simpa only [getD_snoc_ne _ _ _ _ hw, getD_snoc_ne _ _ _ _ hw'] using h.2.2 i hi


end PEqualNP.Outside.L_meta_12200.Bridge
namespace PEqualNP.Outside.L_meta_12200.Bridge
open CircuitProof PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma folded_marks (n : Nat) (gs : List Gate) (marked : List Bool)
    (acc : List Stat × List Gate) (hc : MarksConstants marked acc.1)
    (legal : ∀ g ∈ gs, NOk g) :
    MarksConstants (gs.foldl (fun a g => nextMarked g a) marked) (elim n gs acc).1 := by
  induction gs generalizing marked acc with
  | nil => exact hc
  | cons g gs ih =>
    exact ih _ _ (extend_marks n g marked acc hc (legal g (by simp)))
      (fun h hh => legal h (by simp [hh]))

lemma zero_agrees (gs : List Gate) (marked w w' : List Bool)
    (z : entries marked gs = 0) : agreesAtEntries gs marked w w' := by
  induction gs generalizing marked w w' with
  | nil => trivial
  | cons g gs ih =>
    change entry g marked + entries (nextMarked g marked) gs = 0 at z
    change (entry g marked = 1 → gateValue g w = gateValue g w') ∧ _
    exact ⟨fun h => by omega, ih _ _ _ (by omega)⟩

def remapInputs {m n : ℕ} (μ : Fin m → Option (Fin n)) (b : Bool)
    (y : Fin n → Bool) (i : Fin m) : Bool :=
  (μ i).elim b y

private def remapMask {m n : ℕ} (μ : Fin m → Option (Fin n)) : List Bool :=
  List.ofFn fun i => (μ i).isNone

private def remapStats {m n : ℕ} (μ : Fin m → Option (Fin n)) (b : Bool) : List Stat :=
  List.ofFn fun i => (μ i).elim (.inl b) (fun j => .inr j.val)

private lemma remapStats_valid {m n : ℕ} (μ : Fin m → Option (Fin n)) (b : Bool) :
    ∀ s ∈ remapStats μ b, s.Valid n := by
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  cases h : μ i with
  | none => trivial
  | some j => simp [h, Stat.Valid]

private lemma getD_ofFn_in {α : Type*} {m i : ℕ} (f : Fin m → α) (d : α) (h : i < m) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  have hi : i < (List.ofFn f).length := by simpa using h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem_ofFn]

private lemma getD_ofFn_out {α : Type*} {m i : ℕ} (f : Fin m → α) (d : α) (h : ¬ i < m) :
    (List.ofFn f).getD i d = d := by
  simp [List.getD_eq_getElem?_getD, h]

private lemma remapStats_marks {m n : ℕ} (μ : Fin m → Option (Fin n)) (b : Bool) :
    MarksConstants (remapMask μ) (remapStats μ b) := by
  refine ⟨by simp [remapMask, remapStats], ?_⟩
  intro i mark
  unfold remapMask at mark
  by_cases hi : i < m
  · rw [getD_ofFn_in _ _ hi] at mark
    refine ⟨b, ?_⟩
    rw [remapStats, getD_ofFn_in _ _ hi]
    simp [Option.isNone_iff_eq_none.mp mark]
  · rw [getD_ofFn_out _ _ hi] at mark
    contradiction

private lemma remapStats_eval {m n : ℕ} (μ : Fin m → Option (Fin n)) (b : Bool)
    (y : Fin n → Bool) :
    remap (remapStats μ b) (List.ofFn y) = List.ofFn (remapInputs μ b y) := by
  apply List.ext_getElem
  · simp [remap, remapStats]
  · intro i hi hi'
    simp only [remap, remapStats, List.getElem_map, List.getElem_ofFn, remapInputs]
    cases μ ⟨i, by simpa using hi'⟩ <;> simp [Stat.val]

private lemma remapInputs_agree {m n : ℕ} (μ : Fin m → Option (Fin n)) (y : Fin n → Bool) :
    agreeUnmarked (remapMask μ) (List.ofFn (remapInputs μ false y))
      (List.ofFn (remapInputs μ true y)) := by
  refine ⟨by simp [remapMask], by simp, ?_⟩
  intro i hi
  unfold remapMask at hi
  by_cases ht : i < m
  · rw [getD_ofFn_in _ _ ht] at hi
    rw [getD_ofFn_in _ _ ht, getD_ofFn_in _ _ ht]
    cases he : μ ⟨i, ht⟩ with
    | none => simp [he] at hi
    | some j => simp [remapInputs, he]
  · simp [ht]

private lemma simplify_nok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, NOk g := by
  intro g hg
  refine ⟨simplify_ok op m ins g hg, ?_⟩
  intro hn
  have hop : op = .not := (simplify_same_op op m ins g hg).symm.trans hn
  subst op
  rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
    simp [simplify, simpNot] at hg
  subst g
  simp

private lemma nok_elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hacc : ∀ g ∈ acc.2, NOk g) : ∀ g ∈ (elim n gs acc).2, NOk g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    apply ih (elimStep n acc g)
    intro q hq
    change q ∈ acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList at hq
    rcases List.mem_append.mp hq with hm | hm
    · exact hacc _ hm
    · exact simplify_nok _ _ _ q (by simpa using hm)

theorem reduceAtValue {m n : ℕ} (μ : Fin m → Option (Fin n)) (fixed : Bool) (C : Circuit)
    (legal : ∀ g ∈ C.gates, NOk g)
    (essential : ∃ y : Fin n → Bool,
      C.eval (List.ofFn (remapInputs μ false y)) ≠ C.eval (List.ofFn (remapInputs μ true y)))
    (varies : ∃ u v : Fin n → Bool,
      C.eval (List.ofFn (remapInputs μ fixed u)) ≠ C.eval (List.ofFn (remapInputs μ fixed v))) :
    ∃ D : Circuit, (∀ g ∈ D.gates, NOk g) ∧
      nonNotCount D.gates + 1 ≤ nonNotCount C.gates ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (remapInputs μ fixed y)) := by
  let marks := remapMask μ
  let stats := remapStats μ fixed
  let run := elim n C.gates (stats, [])
  have rel (y : Fin n → Bool) : (run.1.getD C.output (.inl false)).val
      (wiresFrom run.2 (List.ofFn y)) = C.eval (List.ofFn (remapInputs μ fixed y)) := by
    rw [← remapStats_eval]
    exact (inv_elim n (List.ofFn y) (by simp) C.gates _ _ (fun g hg => (legal g hg).1)
      (init_inv n stats _ (remapStats_valid μ fixed))).2 C.output |>.2
  have outputUnmarked :
      (C.gates.foldl (fun a g => nextMarked g a) marks).getD C.output false = false := by
    by_contra! hn
    obtain ⟨b, hb⟩ := (folded_marks n C.gates marks (stats, [])
      (remapStats_marks μ fixed) legal).2 _ (Bool.eq_true_of_not_eq_false hn)
    obtain ⟨u,v,ne⟩ := varies
    have a := rel u
    have c := rel v
    change run.1.getD C.output (.inl false) = .inl b at hb
    rw [hb] at a c
    exact ne (a.symm.trans c)
  have lower : 1 ≤ entries marks C.gates := by
    by_contra! hz
    have ez : entries marks C.gates = 0 := by omega
    obtain ⟨y,ne⟩ := essential
    have eq := factor_at_entries C.gates marks _ _ (remapInputs_agree μ y)
      (zero_agrees _ _ _ _ ez) C.output outputUnmarked
    exact ne eq
  cases h : run.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨u,v,ne⟩ := varies
    have a := rel u
    have c := rel v
    rw [h] at a c
    exact False.elim (ne (a.symm.trans c))
  | inr o =>
    refine ⟨⟨run.2,o⟩, nok_elim n C.gates (stats, []) (by simp), ?_, ?_⟩
    · have save := eliminate_entries n C.gates marks (stats, []) (remapStats_marks μ fixed) legal
      change nonNotCount run.2 + entries marks C.gates ≤ nonNotCount ([] : List Gate) + _ at save
      rw [show nonNotCount ([] : List Gate) = 0 from rfl, Nat.zero_add] at save
      change nonNotCount run.2 + 1 ≤ _
      omega
    · intro y
      have eq := rel y
      rw [h] at eq
      exact eq

def trim (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

lemma trim_op (g : Gate) : (trim g).op = g.op := by
  rcases g with ⟨o,l⟩
  cases o <;> rfl

lemma trim_legal (g : Gate) (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2) : NOk (trim g) := by
  rcases g with ⟨o,l⟩
  rcases legal with ⟨h, len⟩
  change o = .and ∨ o = .or ∨ o = .not at h
  rcases h with rfl|rfl|rfl <;> simp [trim, NOk, Ok, len]

lemma trim_eval (g : Gate) (w : List Bool) : gateValue (trim g) w = gateValue g w := by
  rcases g with ⟨o,l⟩
  cases o <;> try rfl
  cases l <;> rfl

lemma trim_wires (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map trim) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom (gs.map trim) (w ++ [gateValue (trim g) w]) =
      wiresFrom gs (w ++ [gateValue g w])
    rw [trim_eval, ih]

lemma trim_counts (f : GateOp → Bool) (gs : List Gate) :
    opCount f (gs.map trim) = opCount f gs := by
  induction gs <;> simp_all [opCount_cons, trim_op, List.map_cons]

lemma not_true (o : GateOp) : isNotGate o = true ↔ o = .not := by
  cases o <;> simp [isNotGate]

lemma not_false (o : GateOp) : isNotGate o = false ↔ o ≠ .not := by
  cases o <;> simp [isNotGate]

lemma partition_counts (gs : List Gate) :
    nonNotCount gs + opCount isNotGate gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change opCount (fun o => !isNotGate o) (g :: gs) + opCount isNotGate (g :: gs) = _
    rw [opCount_cons, opCount_cons]
    cases isNotGate g.op <;> simp_all [nonNotCount, opCount] <;> omega

end PEqualNP.Outside.L_meta_12200.Bridge

-- The signed live-wire calculus is adapted from k-sandhu's L-meta-8719 (PR 12896).
namespace PEqualNP.Outside.L_meta_12200.Threshold

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 64
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def targetFun (T : ℕ) (x : Fin 4 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 4, if x i then 2 ^ (i : ℕ) else 0)

-- Every AND or OR costs at most one binary step. Signs and constants are free.
theorem bound_from_search (T : ℕ) (inputs : List W) (width : inputs.length = 4)
    (nd : inputs.Nodup) (reject : search 6 inputs = false)
    (sample : ∀ k : Fin 64,
      targetFun T (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 4 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun T x) :
    6 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 4) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 6 inputs nd (lift low run)))


def raw0 : W := 0x38661770ff7fd3fc

def raw1 : W := 0x130ac69793adfeff

def raw2 : W := 0x41d531296fd77fdf

def raw3 : W := 0xacb90806fcffed33

def rows : List W := [raw0, raw1, raw2, raw3]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_1 : dispatch 3 (optimized 5) raw0 raw1 [raw2, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_2 : dispatch 3 (optimized 5) raw0 raw2 [raw1, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_3 : dispatch 3 (optimized 5) raw0 raw3 [raw1, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_2 : dispatch 3 (optimized 5) raw1 raw2 [raw0, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_3 : dispatch 3 (optimized 5) raw1 raw3 [raw0, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_2_3 : dispatch 3 (optimized 5) raw2 raw3 [raw0, raw1] = false := by
  decide +kernel

private theorem whole : optimized 6 3 rows = false := by
  change ((rows == [goal] || rows == [~~~goal]) ||
    (pairs rows).any fun (a,b,r) => dispatch 3 (optimized 5) a b r) = false
  have longer : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
  rw [longer]
  simp only [Bool.false_or, rows, pairs, singles, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.any_cons, List.any_nil]
  simp only [first_0_1, first_0_2, first_0_3, first_1_2, first_1_3, first_2_3, Bool.false_or]

private theorem proper : ∀ ws ∈ rows.sublists, ws ≠ rows → cuts ws ≠ -1 := by
  decide +kernel

theorem reject : search 6 rows = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hw
  by_cases full : ws = rows
  · subst ws
    have room : 6 + 1 - rows.length = 3 := rfl
    simp [room, whole]
  · have bad : (cuts ws == -1) = false :=
      Bool.eq_false_iff.mpr (fun h => proper ws hw full (beq_iff_eq.mp h))
    rw [bad]
    simp

theorem lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 4 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun 0xe880 x) :
    7 ≤ binaryCost gs :=
  bound_from_search 0xe880 rows rfl (by decide) reject (by decide +kernel) gs o hg he

end PEqualNP.Outside.L_meta_12200.Threshold

namespace PEqualNP.Outside.L_meta_12200.Bridge

open CircuitProof PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3900735616 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)

def witness : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.and,[0,1]⟩, ⟨.and,[6,2]⟩, ⟨.or,[7,8]⟩, ⟨.and,[7,2]⟩,
    ⟨.or,[3,5]⟩, ⟨.and,[3,4]⟩, ⟨.and,[10,11]⟩, ⟨.and,[9,12]⟩, ⟨.or,[13,14]⟩],15⟩

theorem witness_legal : Monotone2 witness := by simp [Monotone2, witness]

set_option maxRecDepth 16000 in
theorem witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

def cutOne : Fin 6 → Option (Fin 5) :=
  ![some 0, some 1, some 2, some 3, some 4, none]

def cutTwo : Fin 5 → Option (Fin 4) :=
  ![some 0, some 1, some 2, none, some 3]

def middle (x : Fin 5 → Bool) : Bool := target (remapInputs cutOne false x)

theorem cutOne_essential : ∃ y : Fin 5 → Bool,
    target (remapInputs cutOne false y) ≠ target (remapInputs cutOne true y) :=
  ⟨![true,true,true,false,false], by decide⟩

theorem cutOne_varies : ∃ y z : Fin 5 → Bool,
    target (remapInputs cutOne false y) ≠ target (remapInputs cutOne false z) :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem cutTwo_essential : ∃ y : Fin 4 → Bool,
    middle (remapInputs cutTwo false y) ≠ middle (remapInputs cutTwo true y) :=
  ⟨fun _ => true, by decide⟩

theorem cutTwo_varies : ∃ y z : Fin 4 → Bool,
    middle (remapInputs cutTwo true y) ≠ middle (remapInputs cutTwo true z) :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem threshold_equiv : ∀ y : Fin 4 → Bool,
    middle (remapInputs cutTwo true y) = Threshold.targetFun 0xe880 y := by
  decide +kernel

theorem binary_eq (gs : List Gate) (legal : ∀ g ∈ gs, NOk g) :
    Threshold.binaryCost gs = nonNotCount gs := by
  change (gs.filter Threshold.isBinary).length = gs.countP (fun g => !isNotGate g.op)
  rw [List.countP_eq_length_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro g hg
  unfold Threshold.isBinary isNotGate
  rcases (legal g hg).1.1 with hop | hop | hop <;> rw [hop] <;> rfl

theorem replacement (s : Nat) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨A, fit, size, correct⟩ := h
  by_cases big : 10 ≤ s
  · exact ⟨witness, witness_legal, big, witness_correct⟩
  by_cases plain : ∀ g ∈ A.gates, g.op ≠ .not
  · refine ⟨A, ?_, size, correct⟩
    intro g hg
    refine ⟨?_, (fit g hg).2⟩
    rcases (fit g hg).1 with he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · exact False.elim (plain g hg he)
  exfalso
  push Not at plain
  obtain ⟨g, hg, hn⟩ := plain
  have present : 1 ≤ opCount isNotGate A.gates := by
    by_contra! no
    have z : opCount isNotGate A.gates = 0 := by omega
    have falseGate := List.countP_eq_zero.mp z g hg
    rw [(not_true _).mpr hn] at falseGate
    contradiction
  have partition := partition_counts A.gates
  let C : Circuit := ⟨A.gates.map trim, A.output⟩
  have legal : ∀ g ∈ C.gates, NOk g := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact trim_legal a (fit a ha)
  have computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
    intro x
    change (wiresFrom (A.gates.map trim) (List.ofFn x)).getD A.output false = target x
    rw [trim_wires]
    exact correct x
  obtain ⟨D, Dlegal, saveOne, computesOne⟩ := reduceAtValue cutOne false C legal
    (by simpa only [computes] using cutOne_essential)
    (by simpa only [computes] using cutOne_varies)
  have computesD : ∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = middle x := by
    intro x
    exact (computesOne x).trans (computes _)
  obtain ⟨E, Eleg, saveTwo, computesTwo⟩ := reduceAtValue cutTwo true D Dlegal
    (by simpa only [computesD] using cutTwo_essential)
    (by simpa only [computesD] using cutTwo_varies)
  have computesE : ∀ x : Fin 4 → Bool,
      E.eval (List.ofFn x) = Threshold.targetFun 0xe880 x := by
    intro x
    exact (computesTwo x).trans ((computesD _).trans (threshold_equiv x))
  have lower := Threshold.lower E.gates E.output (fun g hg => (Eleg g hg).1) computesE
  rw [binary_eq _ Eleg] at lower
  have sameBinary : nonNotCount C.gates = nonNotCount A.gates :=
    trim_counts (fun a => !isNotGate a) A.gates
  rw [sameBinary] at saveOne
  change A.gates.length ≤ s at size
  omega

end PEqualNP.Outside.L_meta_12200.Bridge

theorem PEqualNP.Outside.L_meta_12200 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900735616 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900735616 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_12200.Bridge.replacement
