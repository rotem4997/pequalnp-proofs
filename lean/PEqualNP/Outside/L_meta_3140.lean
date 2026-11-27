import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3140

-- Constant propagation adapts the verified construction in L-meta-2165.
namespace Erase

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

end Erase

namespace Erase

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end Erase

namespace Erase

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

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
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
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
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
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
       (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end Erase

namespace Erase

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩



end Erase


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Wire evaluation lemmas adapt L-meta-1717.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

theorem gateActual (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk

theorem realGate {n : ℕ} (C : Circuit) (back : ReadsBack n C)
    (x : Fin n → Bool) (i : ℕ) (hi : i < C.gates.length) :
    value C x (n+i) = (gateAt C i).op.eval
      ((gateAt C i).inputs.map fun w => value C x w) := by
  have h := gate_value C x (n+i) (by omega) (by change n+i < n+C.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [gateActual C i hi]
  rw [h]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hb : w < n+i := back i hi w (by rwa [gateActual C i hi])
  simp only [hb,ite_true]

def falseGate : Gate := ⟨.or,[]⟩

def mask (C : Circuit) (K : Finset ℕ) : Circuit :=
  ⟨C.gates.mapIdx (fun i g => if i ∈ K then falseGate else g),C.output⟩

theorem maskLen (C : Circuit) (K : Finset ℕ) :
    (mask C K).gates.length = C.gates.length := by simp [mask]

theorem maskAt (C : Circuit) (K : Finset ℕ) (i : ℕ) (hi : i < C.gates.length) :
    gateAt (mask C K) i = if i ∈ K then falseGate else gateAt C i := by
  have hic : i < (mask C K).gates.length := by rwa [maskLen]
  rw [gateActual _ _ hic,gateActual _ _ hi]
  change i < (C.gates.mapIdx _).length at hic
  change (C.gates.mapIdx _)[i] = _
  rw [List.getElem_mapIdx]

theorem maskBack {n : ℕ} (C : Circuit) (K : Finset ℕ) (back : ReadsBack n C) :
    ReadsBack n (mask C K) := by
  intro i hi w hw
  rw [maskLen] at hi
  rw [maskAt _ _ _ hi] at hw
  by_cases cut : i ∈ K
  · simp [cut,falseGate] at hw
  · exact back i hi w (by simpa only [cut,ite_false] using hw)

theorem maskValue {n : ℕ} (C : Circuit) (K : Finset ℕ) (back : ReadsBack n C)
    (x : Fin n → Bool) (i : ℕ) (hi : i < C.gates.length) (cut : i ∈ K) :
    value (mask C K) x (n+i) = false := by
  rw [realGate _ (maskBack _ _ back) _ _ (by rwa [maskLen]), maskAt _ _ _ hi,ite_eq_left cut]
  rfl

set_option maxHeartbeats 2500000 in
theorem mask_agree {n : ℕ} (C : Circuit) (K : Finset ℕ) (j : ℕ)
    (back : ReadsBack n C) (jK : j ∈ K)
    (exit : ∀ i < C.gates.length, i ∉ K → ∀ w ∈ (gateAt C i).inputs,
      n ≤ w → w-n ∈ K → w = n+j)
    (x : Fin n → Bool) (w : ℕ)
    (outside : n ≤ w → w-n ∈ K → w = n+j) :
    value (mask C K) x w = value (mask C {j}) x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let v : Fin n := ⟨w,raw⟩
      exact (input_value _ _ v).trans (input_value _ _ v).symm
    · let i := w-n
      have wi : n+i = w := by dsimp [i]; omega
      by_cases lost : i < C.gates.length
      · by_cases inside : i ∈ K
        · have same := outside (by omega) inside
          have eq : i = j := by omega
          subst j
          simp only [← wi]
          rw [maskValue _ _ back _ _ lost inside,maskValue _ _ back _ _ lost (by simp)]
        · have notSingle : i ∉ ({j} : Finset ℕ) := by
            intro reads
            exact inside ((Finset.mem_singleton.mp reads).symm ▸ jK)
          rw [← wi,realGate _ (maskBack _ _ back) _ _ (by rwa [maskLen]),
            realGate _ (maskBack _ _ back) _ _ (by rwa [maskLen]),
            maskAt _ _ _ lost,maskAt _ _ _ lost,ite_eq_right inside,ite_eq_right notSingle]
          congr 1
          apply List.map_congr_left
          intro q hq
          have qlt := back i lost q hq
          exact ih q (wi ▸ qlt) (exit i lost inside q hq)
      · have absent (T : Finset ℕ) : n + (mask C T).size ≤ w := by
          change n + (mask C T).gates.length ≤ w
          rw [maskLen]
          omega
        rw [missing_value _ _ _ (absent K),missing_value _ _ _ (absent {j})]

set_option maxHeartbeats 2500000 in
theorem unchangedIfFalse {n : ℕ} (C : Circuit) (j : ℕ) (back : ReadsBack n C)
    (x : Fin n → Bool) (hf : value C x (n+j) = false) :
    ∀ w, value C x w = value (mask C {j}) x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let v : Fin n := ⟨w,raw⟩
      exact (input_value _ _ v).trans (input_value _ _ v).symm
    · let i := w-n
      have wi : n+i = w := by dsimp [i]; omega
      by_cases hi : i < C.gates.length
      · rw [← wi]
        by_cases changeAt : i = j
        · subst j
          rw [hf, maskValue _ _ back _ _ hi (by simp)]
        · have ne : i ∉ ({j} : Finset ℕ) := by simpa only [Finset.mem_singleton] using changeAt
          rw [realGate _ back _ _ hi,realGate _ (maskBack _ _ back) _ _ (by rwa [maskLen]),
            maskAt _ _ _ hi,ite_eq_right ne]
          congr 1
          exact List.map_congr_left (fun q hq => ih q (wi ▸ back i hi q hq))
      · have absent : n + C.size ≤ w := by change n+C.gates.length ≤ w; omega
        have absent' : n + (mask C {j}).size ≤ w := by
          change n + (mask C {j}).gates.length ≤ w
          rw [maskLen]
          exact absent
        rw [missing_value _ _ _ absent,missing_value _ _ _ absent']

theorem mask_single_set (C : Circuit) (j : ℕ) :
    (mask C {j}).gates = C.gates.set j falseGate := by
  apply List.ext_getElem (by simp [mask])
  intro i hi h'
  change i < (C.gates.mapIdx _).length at hi
  change (C.gates.mapIdx _)[i] = _
  rw [List.getElem_mapIdx]
  by_cases h : i = j
  · subst i
    simp
  · simp [h,Ne.symm h]




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def slots (C : Circuit) (K : Finset ℕ) : Finset ℕ :=
  (K ×ˢ (Finset.univ : Finset (Fin 2))).image
    (fun x => (gateAt C x.1).inputs.getD x.2.val 0)

def rawSlots (n : ℕ) (C : Circuit) (K : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val ∈ slots C K

theorem records (C : Circuit) (K : Finset ℕ) (i w : ℕ)
    (hi : i ∈ K) (binary : (gateAt C i).inputs.length = 2)
    (hw : w ∈ (gateAt C i).inputs) : w ∈ slots C K := by
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hw
  have h2 : j < 2 := by rwa [← binary]
  refine Finset.mem_image.mpr ⟨(i,⟨j,h2⟩),Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,?_⟩
  rw [List.getD_eq_getElem _ _ hj]
  exact eq

set_option maxHeartbeats 1500000 in
theorem slotBudget (n : ℕ) (C : Circuit) (K : Finset ℕ) (j : ℕ)
    (hj : j ∈ K) (binary : ∀ i ∈ K, (gateAt C i).inputs.length = 2)
    (used : ∀ i ∈ K, i ≠ j → ∃ k ∈ K, n+i ∈ (gateAt C k).inputs) :
    (rawSlots n C K).card ≤ K.card+1 := by
  let raw := (rawSlots n C K).image (fun i => i.val)
  let inner := (K.erase j).image (fun i => n+i)
  have rawIncluded : raw ⊆ slots C K := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hi).2
  have innerIncluded : inner ⊆ slots C K := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
    obtain ⟨k,hk,read⟩ := used i mem ne
    exact records C K k (n+i) hk (binary k hk) read
  have disj : Disjoint raw inner := by
    apply Finset.disjoint_left.mpr
    intro w wr wi
    obtain ⟨r,_,er⟩ := Finset.mem_image.mp wr
    obtain ⟨i,_,ei⟩ := Finset.mem_image.mp wi
    have lt := r.isLt
    omega
  have total := Finset.card_le_card (Finset.union_subset rawIncluded innerIncluded)
  have slotsBound : (slots C K).card ≤ 2*K.card := by
    unfold slots
    apply Finset.card_image_le.trans
    simp [Finset.card_product,Nat.mul_comm]
  have rawCount : raw.card = (rawSlots n C K).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have innerCount : inner.card = K.card-1 := by
    dsimp [inner]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact Nat.add_left_cancel h),Finset.card_erase_of_mem hj]
  rw [Finset.card_union_of_disjoint disj,rawCount,innerCount] at total
  have nonzero : 0 < K.card := Finset.card_pos.mpr ⟨j,hj⟩
  omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2500000 in
theorem coneAgreement {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (back : ReadsBack n C) (binary : ∀ i ∈ K, (gateAt C i).inputs.length = 2)
    (closed : ∀ i ∈ K, ∀ w ∈ (gateAt C i).inputs, n ≤ w → w-n ∈ K)
    (x y : Fin n → Bool) (same : ∀ v ∈ rawSlots n C K, x v = y v) :
    ∀ i ∈ K, i<C.gates.length → value C x (n+i) = value C y (n+i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro his hit
    rw [realGate C back x i hit,realGate C back y i hit]
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases raw : w<n
    · let v : Fin n := ⟨w,raw⟩
      have found : v ∈ rawSlots n C K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,records C K i w his (binary i his) hw⟩
      exact (input_value C x v).trans ((same v found).trans (input_value C y v).symm)
    · have h := back i hit w hw
      have lt : w-n < i := by omega
      have eq : n+(w-n)=w := by omega
      exact eq ▸ ih _ lt (closed i his w hw (by omega)) (lt.trans hit)

def oneHot {n : ℕ} (v : Fin n) (u : Fin n) : Bool := decide (u = v)

def edgeInput {a b : ℕ} (p : Fin a) (l : Fin b) (v : Fin (a+b)) : Bool :=
  decide (v = Fin.castAdd b p ∨ v = Fin.natAdd a l)

set_option maxHeartbeats 2500000 in
theorem endpoints {a b : ℕ} (C : Circuit) (K : Finset ℕ) (j : ℕ)
    (back : ReadsBack (a+b) C) (binary : ∀ i ∈ K, (gateAt C i).inputs.length = 2)
    (closed : ∀ i ∈ K, ∀ w ∈ (gateAt C i).inputs, a+b ≤ w → w-(a+b) ∈ K)
    (jK : j ∈ K) (hj : j<C.gates.length)
    (zero : ∀ i : Fin (a+b), value C (oneHot i) (a+b+j) = false)
    (p : Fin a) (l : Fin b)
    (before : value C (edgeInput p l) C.output = true)
    (after : value (mask C {j}) (edgeInput p l) C.output = false) :
    Fin.castAdd b p ∈ rawSlots (a+b) C K ∧ Fin.natAdd a l ∈ rawSlots (a+b) C K := by
  let x := edgeInput p l
  let u := Fin.castAdd b p
  let v := Fin.natAdd a l
  have high : value C x (a+b+j) = true := by
    cases h : value C x (a+b+j)
    · have same := unchangedIfFalse C j back x h C.output
      change value C x C.output = true at before
      change value (mask C {j}) x C.output = false at after
      rw [before,after] at same
      cases same
    · rfl
  constructor
  · by_contra absent
    have agree (w : Fin (a+b)) (hw : w ∈ rawSlots (a+b) C K) : x w = oneHot v w := by
      have no : w ≠ u := fun e => absent (by simpa only [e] using hw)
      change decide (w = u ∨ w = v) = decide (w = v)
      simp [no]
    have same := coneAgreement C K back binary closed x (oneHot v) agree j jK hj
    rw [high,zero] at same
    cases same
  · by_contra absent
    have agree (w : Fin (a+b)) (hw : w ∈ rawSlots (a+b) C K) : x w = oneHot u w := by
      have no : w ≠ v := fun e => absent (by simpa only [e] using hw)
      change decide (w = u ∨ w = v) = decide (w = u)
      simp [no]
    have same := coneAgreement C K back binary closed x (oneHot u) agree j jK hj
    rw [high,zero] at same
    cases same



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

theorem separates {a b : ℕ} (p : Fin a) (l : Fin b) :
    Fin.castAdd b p ≠ Fin.natAdd a l := by
  intro h
  have v := congrArg Fin.val h
  change p.val = a + l.val at v
  omega

set_option maxHeartbeats 1500000 in
theorem stars {a b : ℕ} (E : Finset (Fin a × Fin b))
    (noFork : ∀ (p p' : Fin a) (l l' : Fin b),
      (p,l) ∈ E → (p',l) ∈ E → (p,l') ∈ E → p' = p ∨ l' = l)
    (W : Finset (Fin (a+b)))
    (allEndpoints : ∀ p l, (p,l) ∈ E → Fin.castAdd b p ∈ W ∧ Fin.natAdd a l ∈ W) :
    ∃ center leaf : Fin a × Fin b → Fin (a+b),
      (∀ p l, (p,l) ∈ E →
        (center (p,l) = Fin.castAdd b p ∧ leaf (p,l) = Fin.natAdd a l) ∨
        (center (p,l) = Fin.natAdd a l ∧ leaf (p,l) = Fin.castAdd b p)) ∧
      Set.InjOn leaf (↑E : Set (Fin a × Fin b)) ∧
      Disjoint (E.image center) (E.image leaf) ∧
      E.card + (E.image center).card ≤ W.card := by
  classical
  let high (p : Fin a) : Prop :=
    ∃ l l' : Fin b, l ≠ l' ∧ (p,l) ∈ E ∧ (p,l') ∈ E
  let center (e : Fin a × Fin b) : Fin (a+b) :=
    if high e.1 then Fin.castAdd b e.1 else Fin.natAdd a e.2
  let leaf (e : Fin a × Fin b) : Fin (a+b) :=
    if high e.1 then Fin.natAdd a e.2 else Fin.castAdd b e.1
  have sameLine (p p' : Fin a) (l : Fin b) (hp : high p) (e : (p,l) ∈ E)
      (e' : (p',l) ∈ E) : p' = p := by
    obtain ⟨u,v,ne,hu,hv⟩ := hp
    by_cases h : u = l
    · exact (noFork p p' l v e e' hv).resolve_right (by intro eq; exact ne (h.trans eq.symm))
    · exact (noFork p p' l u e e' hu).resolve_right h
  have samePoint (p : Fin a) (l l' : Fin b) (hp : ¬ high p) (e : (p,l) ∈ E)
      (e' : (p,l') ∈ E) : l = l' := by
    by_contra h
    exact hp ⟨l,l',h,e,e'⟩
  have shape (p : Fin a) (l : Fin b) :
      (center (p,l) = Fin.castAdd b p ∧ leaf (p,l) = Fin.natAdd a l) ∨
      (center (p,l) = Fin.natAdd a l ∧ leaf (p,l) = Fin.castAdd b p) := by
    by_cases hp : high p <;> simp [center,leaf,hp]
  have leafInj : Set.InjOn leaf (↑E : Set (Fin a × Fin b)) := by
    rintro ⟨p,l⟩ he ⟨p',l'⟩ he' same
    change (p,l) ∈ E at he
    change (p',l') ∈ E at he'
    by_cases hp : high p <;> by_cases hp' : high p'
    · have eql : l=l' := by simpa [leaf,hp,hp'] using same
      subst l'
      have eqp := sameLine p p' l hp he he'
      subst p'
      rfl
    · exact False.elim ((separates p' l) (by simpa [leaf,hp,hp'] using same.symm))
    · exact False.elim ((separates p l') (by simpa [leaf,hp,hp'] using same))
    · have eqp : p=p' := by simpa [leaf,hp,hp'] using same
      subst p'
      have eql := samePoint p l l' hp he he'
      subst l'
      rfl
  have disjoint : Disjoint (E.image center) (E.image leaf) := by
    apply Finset.disjoint_left.mpr
    intro w hc hlf
    obtain ⟨⟨p,l⟩,he,hc⟩ := Finset.mem_image.mp hc
    obtain ⟨⟨p',l'⟩,he',hlf⟩ := Finset.mem_image.mp hlf
    have same := hc.trans hlf.symm
    by_cases hp : high p <;> by_cases hp' : high p'
    · exact separates p l' (by simpa [center,leaf,hp,hp'] using same)
    · have eqp : p=p' := by simpa [center,leaf,hp,hp'] using same
      exact hp' (eqp ▸ hp)
    · have eql : l=l' := by simpa [center,leaf,hp,hp'] using same
      subst l'
      have eqp := sameLine p' p l hp' he' he
      exact hp (eqp ▸ hp')
    · exact separates p' l (by simpa [center,leaf,hp,hp'] using same.symm)
  have below : E.image center ∪ E.image leaf ⊆ W := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨⟨p,l⟩,he,rfl⟩ := Finset.mem_image.mp hw
      rcases shape p l with h | h <;> rw [h.1]
      · exact (allEndpoints p l he).1
      · exact (allEndpoints p l he).2
    · obtain ⟨⟨p,l⟩,he,rfl⟩ := Finset.mem_image.mp hw
      rcases shape p l with h | h <;> rw [h.2]
      · exact (allEndpoints p l he).2
      · exact (allEndpoints p l he).1
  refine ⟨center,leaf,fun p l _ => shape p l,leafInj,disjoint,?_⟩
  have budget := Finset.card_le_card below
  rw [Finset.card_union_of_disjoint disjoint,Finset.card_image_of_injOn leafInj] at budget
  omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- The builder and star expression adapt the construction in L-meta-1975.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

def StrictGate (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


theorem readsBack_append (m : ℕ) {gs hs : List Gate} {i j o : ℕ}
    (left : ReadsBack m ⟨gs,i⟩) (right : ReadsBack (m+gs.length) ⟨hs,j⟩) :
    ReadsBack m ⟨gs ++ hs,o⟩ := by
  intro k hk w hw
  change k < (gs ++ hs).length at hk
  simp only [List.length_append] at hk
  by_cases h : k < gs.length
  · have eq : gateAt ⟨gs ++ hs,o⟩ k = gateAt ⟨gs,i⟩ k := by
      simp only [gateAt,List.getD_append _ _ _ _ h]
    rw [eq] at hw
    exact left k h w hw
  · have eq : gateAt ⟨gs ++ hs,o⟩ k = gateAt ⟨hs,j⟩ (k-gs.length) := by
      simp only [gateAt,List.getD_append_right _ _ _ _ (by omega : gs.length ≤ k)]
    rw [eq] at hw
    have lim : k-gs.length < hs.length := by omega
    have lt := right (k-gs.length) lim w hw
    omega

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, StrictGate g) ∧ ReadsBack m ⟨gs,out⟩ ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, back, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, back, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, back, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, back, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp [ReadsBack], le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, read1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, read2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; exact ⟨hop,rfl⟩
  · apply readsBack_append _ (j := 0)
      (readsBack_append _ (o := 0) read1 read2)
    intro j hj w hw
    have j0 : j = 0 := by simp at hj; omega
    subst j
    change w ∈ ([o1,o2] : List ℕ) at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    change w < m+(gs1++gs2).length+0
    simp only [List.length_append,Nat.add_zero]
    rcases hw with rfl | rfl <;> omega
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩

    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

open Classical in
set_option maxHeartbeats 2000000 in
theorem starBuild {a b : ℕ} (E : Finset (Fin a × Fin b)) (W : Finset (Fin (a+b)))
    (present : E.Nonempty)
    (noFork : ∀ p p' l l', (p,l) ∈ E → (p',l) ∈ E → (p,l') ∈ E → p'=p ∨ l'=l)
    (vertices : ∀ p l, (p,l) ∈ E → Fin.castAdd b p ∈ W ∧ Fin.natAdd a l ∈ W) :
    Bld (a+b) (fun z => decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd b p) = true ∧
      z (Fin.natAdd a l) = true)) (W.card-1) := by
  obtain ⟨center,leaf,shape,_,_,budget⟩ := stars E noFork W vertices
  let pair (e : Fin a × Fin b) : Sym2 (Fin (a+b)) :=
    s(Fin.castAdd b e.1,Fin.natAdd a e.2)
  let edges := E.image pair
  let centers := E.image center
  have edgesPresent : edges.Nonempty := present.image pair
  have cover : ∀ e ∈ edges, ∃ t ∈ centers, t ∈ e := by
    intro e he
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp he
    refine ⟨center (p,l),Finset.mem_image.mpr ⟨(p,l),hp,rfl⟩,?_⟩
    rcases shape p l hp with h | h <;> rw [h.1]
    · exact Sym2.mem_mk_left _ _
    · exact Sym2.mem_mk_right _ _
  have card : edges.card + centers.card - 1 ≤ W.card-1 := by
    have smaller : edges.card ≤ E.card := Finset.card_image_le
    change E.card + centers.card ≤ W.card at budget
    omega
  refine bld_congr (bld_mono (bld_edges (a+b) centers edges edgesPresent cover) card) ?_
  intro x
  rw [Bool.eq_iff_iff,decide_eq_true_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨e,he,test⟩
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp he
    exact ⟨p,l,hp,test _ (Sym2.mem_mk_left _ _),test _ (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨p,l,hp,hx,hy⟩
    refine ⟨pair (p,l),Finset.mem_image.mpr ⟨(p,l),hp,rfl⟩,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open Erase

theorem elim_append (n : ℕ) (xs ys : List Gate) (st : List Stat × List Gate) :
    elim n (xs++ys) st = elim n ys (elim n xs st) := by simp only [elim,List.foldl_append]

theorem statLen (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) :
    (elim n gs st).1.length = st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    change (elim n gs (elimStep n st g)).1.length = _
    rw [ih]
    simp [elimStep]
    omega

theorem elimAdd (n : ℕ) (g : Gate) (st : List Stat × List Gate) :
    (elimStep n st g).2.length ≤ st.2.length+1 := by
  simp only [elimStep,List.length_append]
  have h := toList_length_le (simplify g.op (n+st.2.length)
    (g.inputs.map fun k => st.1.getD k (.const false))).1
  omega

theorem dropReader (n : ℕ) (w : ℕ) (st : List Stat × List Gate) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (binary : g.inputs.length = 2)
    (read : w ∈ g.inputs) (zero : st.1.getD w (.const false) = .const false) :
    (elimStep n st g).2.length = st.2.length := by
  obtain ⟨a,b,h⟩ := List.length_eq_two.mp binary
  rw [h] at read
  simp only [List.mem_cons,List.not_mem_nil,or_false] at read
  have rule : ∀ x : Stat, ∀ v : GateOp, v = .and ∨ v = .or →
      (simplify v (n+st.2.length) [.const false,x]).1 = none ∧
      (simplify v (n+st.2.length) [x,.const false]).1 = none := by
    intro x v hv
    rcases hv with rfl | rfl <;>
      cases x with
      | const c => cases c <;> exact ⟨rfl,rfl⟩
      | wire _ => exact ⟨rfl,rfl⟩
  change (st.2 ++ (simplify g.op (n+st.2.length)
    (g.inputs.map fun k => st.1.getD k (.const false))).1.toList).length = _
  rw [h]
  simp only [List.map_cons,List.map_nil]
  rcases read with rfl | rfl
  · rw [zero,(rule _ g.op op).1]
    simp
  · rw [zero,(rule _ g.op op).2]
    simp

set_option maxHeartbeats 4000000 in
theorem shrinkBudget (n : ℕ) (C : Circuit) (K : Finset ℕ) (j k k' : ℕ)
    (hj : j < C.gates.length) (jK : j ∈ K)
    (bounds : ∀ i ∈ K, i ≤ j)
    (back : ReadsBack n C)
    (valid : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2)
    (ne : k ≠ k') (hk : k < C.gates.length) (hk' : k' < C.gates.length)
    (hread : n+j ∈ (gateAt C k).inputs) (hread' : n+j ∈ (gateAt C k').inputs) :
    (elim n (mask C K).gates (idStats n,[])).2.length + K.card + 2 ≤ C.gates.length := by
  let M := mask C K
  let R := insert k (insert k' K)
  have jlt : j < k := by have h := back k hk (n+j) hread; omega
  have jlt' : j < k' := by have h := back k' hk' (n+j) hread'; omega
  have kOut : k ∉ K := fun h => (Nat.not_le_of_lt jlt) (bounds k h)
  have kOut' : k' ∉ K := fun h => (Nat.not_le_of_lt jlt') (bounds k' h)
  have rSize : R.card = K.card+2 := by
    dsimp [R]
    rw [Finset.card_insert_of_notMem (by simp [ne,kOut]),Finset.card_insert_of_notMem kOut']
  let st (i : ℕ) := elim n (M.gates.take i) (idStats n,[])
  have next (i : ℕ) (hi : i < C.gates.length) :
      st (i+1) = elimStep n (st i) (gateAt M i) := by
    have h : i<M.gates.length := by rw [maskLen]; exact hi
    dsimp only [st]
    rw [List.take_succ_eq_append_getElem h,elim_append,gateActual _ _ h]
    rfl
  have stLen (i : ℕ) (hi : i ≤ C.gates.length) : (st i).1.length = n+i := by
    change (elim n (M.gates.take i) (idStats n,[])).1.length = _
    have hl : i ≤ M.gates.length := by rw [maskLen]; exact hi
    simp [statLen,idStats,Nat.min_eq_left hl]
  have markedFalse (i : ℕ) :
      j < i → i ≤ C.gates.length → (st i).1.getD (n+j) (.const false) = .const false := by
    induction i with
    | zero => omega
    | succ i ih =>
      intro later bound
      have before : i < C.gates.length := by omega
      rw [next i before]
      by_cases equal : i=j
      · subst i
        rw [maskAt _ _ _ hj,ite_eq_left jK]
        change ((st j).1 ++ [Stat.const false]).getD (n+j) (Stat.const false) = _
        apply getD_snoc_len
        exact stLen j (by omega)
      · have inner : n+j < (st i).1.length := by rw [stLen i (by omega)]; omega
        change ((st i).1 ++ [_]).getD (n+j) (.const false) = _
        rw [List.getD_append _ _ _ _ inner]
        exact ih (by omega) (by omega)
  have saved (i : ℕ) (hi : i < C.gates.length) (entry : i ∈ R) :
      (st (i+1)).2.length = (st i).2.length := by
    rw [next i hi,maskAt _ _ _ hi]
    by_cases inside : i ∈ K
    · rw [ite_eq_left inside]
      change ((st i).2 ++ []).length = _
      simp
    · rw [ite_eq_right inside]
      have op := valid (gateAt C i) (by rw [gateActual C i hi]; exact List.getElem_mem hi)
      have atReader : i=k ∨ i=k' := by
        simpa [R,inside] using entry
      rcases atReader with rfl | rfl
      · exact dropReader _ _ _ _ op.1 op.2 hread (markedFalse i jlt (by omega))
      · exact dropReader _ _ _ _ op.1 op.2 hread' (markedFalse i jlt' (by omega))
  let count (i : ℕ) := (R.filter (fun d => d < i)).card
  have grow (i : ℕ) : count (i+1) = count i + if i ∈ R then 1 else 0 := by
    by_cases inside : i ∈ R
    · have eq : R.filter (fun d => d < i+1) = insert i (R.filter fun d => d < i) := by
        ext d
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨hd,lt⟩
          by_cases h : d=i
          · exact Or.inl h
          · exact Or.inr ⟨hd,by omega⟩
        · rintro (rfl | ⟨hd,lt⟩)
          · exact ⟨inside,by omega⟩
          · exact ⟨hd,by omega⟩
      change (R.filter (fun d => d < i+1)).card = _ + _
      rw [eq,Finset.card_insert_of_notMem (by simp)]
      simp [count,inside]
    · have eq : R.filter (fun d => d < i+1) = R.filter (fun d => d < i) := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hd,lt⟩
          have ne : d≠i := fun eq => inside (eq ▸ hd)
          exact ⟨hd,by omega⟩
        · rintro ⟨hd,lt⟩
          exact ⟨hd,by omega⟩
      change (R.filter (fun d => d < i+1)).card = _ + _
      rw [eq]
      simp [count,inside]
  have prefixBudget : ∀ i ≤ C.gates.length, (st i).2.length + count i ≤ i := by
    intro i
    induction i with
    | zero => intro _; simp [st,count,elim]
    | succ i ih =>
      intro b
      have prev := ih (by omega)
      rw [grow]
      by_cases entry : i ∈ R
      · rw [saved i (by omega) entry,ite_eq_left entry]
        omega
      · rw [next i (by omega),ite_eq_right entry]
        have le := elimAdd n (gateAt M i) (st i)
        omega
  have endState : st C.gates.length = elim n M.gates (idStats n,[]) := by
    dsimp only [st]
    rw [List.take_of_length_le (by rw [maskLen])]
  have endCount : count C.gates.length = R.card := by
    change (R.filter (fun i => i < C.gates.length)).card = R.card
    congr 1
    apply Finset.filter_eq_self.mpr
    intro i hi
    simp only [R,Finset.mem_insert] at hi
    rcases hi with rfl | rfl | v
    · exact hk
    · exact hk'
    · exact (bounds i v).trans_lt hj
  have budget := prefixBudget C.gates.length le_rfl
  rw [endState,endCount,rSize] at budget
  omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Erase

theorem opsMask (C : Circuit) (K : Finset ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2) :
    ∀ g ∈ (mask C K).gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp hg
  have bound : i < C.gates.length := by rwa [maskLen] at hi
  have eg : gateAt (mask C K) i = g := (gateActual _ i hi).trans e
  rw [maskAt _ _ _ bound] at eg
  by_cases cut : i ∈ K
  · rw [ite_eq_left cut] at eg
    rw [← eg]
    simp [falseGate]
  · rw [ite_eq_right cut] at eg
    rw [← eg]
    have record := legal (gateAt C i) (by rw [gateActual C i bound]; exact List.getElem_mem bound)
    exact ⟨record.1,record.2.le⟩

theorem portLe (g : Gate) (legal : g.op = .and ∨ g.op = .or)
    (x y : ℕ → Bool) (up : ∀ v ∈ g.inputs, x v = true → y v = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases legal with h | h
  · simp only [h,GateOp.eval,List.all_eq_true,id_eq]
    intro yes b hb
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
    exact up v hv (yes _ (List.mem_map.mpr ⟨v,hv,rfl⟩))
  · simp only [h,GateOp.eval,List.any_eq_true,id_eq]
    rintro ⟨b,hb,rfl⟩
    obtain ⟨v,hv,ht⟩ := List.mem_map.mp hb
    exact ⟨_,List.mem_map.mpr ⟨v,hv,rfl⟩,up v hv ht⟩

set_option maxHeartbeats 2500000 in
theorem comparison {n : ℕ} (C D : Circuit)
    (bc : ReadsBack n C) (bd : ReadsBack n D)
    (size : D.gates.length = C.gates.length)
    (legal : ∀ i < C.gates.length, (gateAt C i).op = .and ∨ (gateAt C i).op = .or)
    (contained : ∀ i < C.gates.length, gateAt D i = gateAt C i ∨ gateAt D i = falseGate)
    (x y : Fin n → Bool) (xy : ∀ v, x v = true → y v = true) :
    ∀ w, value D x w = true → value C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let v : Fin n := ⟨w,raw⟩
      change value D x v.val = true → value C y v.val = true
      rw [input_value D x v,input_value C y v]
      exact xy v
    · let i := w-n
      have wi : n+i=w := by dsimp [i]; omega
      by_cases hit : i<C.gates.length
      · have dh : i<D.gates.length := by rwa [size]
        rw [← wi,realGate D bd x i dh]
        rcases contained i hit with same | dropped
        · rw [same,realGate C bc y i hit]
          exact portLe _ (legal i hit) _ _
            (fun q hq => ih q (wi ▸ bc i hit q hq))
        · rw [dropped]
          simp [falseGate,GateOp.eval]
      · have absent : n + D.size ≤ w := by
          change n+D.gates.length ≤ w
          rw [size]
          omega
        rw [missing_value D x w absent]
        simp

theorem maskBelow {n : ℕ} (C : Circuit) (K : Finset ℕ) (back : ReadsBack n C)
    (legal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2)
    (x : Fin n → Bool) :
    value (mask C K) x C.output = true → value C x C.output = true := by
  apply comparison C (mask C K) back (maskBack C K back) (maskLen C K)
  · intro i hi
    exact (legal (gateAt C i) (by rw [gateActual C i hi]; exact List.getElem_mem hi)).1
  · intro i hi
    rw [maskAt _ _ _ hi]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact fun _ h => h

theorem maskMono {n : ℕ} (C : Circuit) (K : Finset ℕ) (back : ReadsBack n C)
    (legal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2)
    (x y : Fin n → Bool) (xy : ∀ v, x v = true → y v = true) :
    value (mask C K) x C.output = true → value (mask C K) y C.output = true := by
  let M := mask C K
  have backM := maskBack C K back
  apply comparison M M backM backM rfl
  · intro i hi
    exact (opsMask C K legal (gateAt M i) (by rw [gateActual M i hi]; exact List.getElem_mem hi)).1
  · exact fun _ _ => Or.inl rfl
  · exact xy

set_option maxHeartbeats 3000000 in
theorem normalize {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2) :
    let st := elim n (mask C K).gates (idStats n,[])
    let state := st.1.getD C.output (Stat.const false)
    (∀ g ∈ st.2, StrictGate g) ∧ (∀ o, ReadsBack n ⟨st.2,o⟩) ∧
    state.Valid (n+st.2.length) ∧
    ∀ x : Fin n → Bool, state.val (wiresFrom st.2 (List.ofFn x)) =
      value (mask C K) x C.output := by
  let gs := (mask C K).gates
  let st := elim n gs (idStats n,[])
  let state := st.1.getD C.output (Stat.const false)
  have allow := opsMask C K legal
  have ok : ∀ g ∈ gs, Ok g := by
    intro g hg
    obtain ⟨hop,hlen⟩ := allow g hg
    refine ⟨?_,hlen⟩
    rcases hop with h | h <;> simp [h]
  let z : Fin n → Bool := fun _ => false
  have clean : CleanL n st.2 := clean_elim n (List.ofFn z) (by simp) gs _ (idStats n,[])
    ok (inv_id n z) (by intro i g atI; simp at atI)
  have noNot : opCount isNotGate gs = 0 := by
    apply List.countP_eq_zero.mpr
    intro g hg
    rcases (allow g hg).1 with h | h <;> simp [h,isNotGate]
  have notCount := elim_opCount_le isNotGate n gs (idStats n,[])
  rw [noNot] at notCount
  have none : opCount isNotGate st.2 = 0 := by
    change opCount isNotGate st.2 ≤ 0 at notCount
    omega
  have propagated (x : Fin n → Bool) :=
    inv_elim n (List.ofFn x) (by simp) gs _ (idStats n,[]) ok (inv_id n x)
  refine ⟨?_,?_,?_,fun x => ((propagated x).2 C.output).2⟩
  · intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    rcases clean i g hi with ⟨notOp,_,_,_⟩ | ⟨hOp,p,q,_,_,hPins⟩
    · exact False.elim (List.countP_eq_zero.mp none g hg (by simp [notOp,isNotGate]))
    · exact ⟨hOp,by simp [hPins]⟩
  · intro o i hi w hw
    have e : st.2[i]? = some (gateAt ⟨st.2,o⟩ i) := by
      rw [gateActual _ i hi]
      exact List.getElem?_eq_getElem hi
    exact (clean i _ e).lt w hw
  · have h := ((propagated z).2 C.output).1
    simpa only [length_wiresFrom,List.length_ofFn] using h



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem builderCircuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (good : Bld n F s) :
    ∃ D : Circuit, (∀ g ∈ D.gates, StrictGate g) ∧ ReadsBack n D ∧ D.size ≤ s ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  obtain ⟨gs,o,strict,back,len,_,run⟩ := good n le_rfl
  refine ⟨⟨gs,o⟩,strict,back,len,?_⟩
  intro x
  change (wiresFrom gs (List.ofFn x)).getD o false = _
  rw [run _ (by simp)]
  congr
  funext i
  exact getD_ofFn x i

set_option maxHeartbeats 2000000 in
theorem appendOR {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (C : Circuit)
    (strict : ∀ g ∈ C.gates, StrictGate g) (back : ReadsBack n C)
    (live : C.output < n+C.size) (good : Bld n F s) :
    ∃ D : Circuit, (∀ g ∈ D.gates, StrictGate g) ∧ ReadsBack n D ∧
      D.size ≤ C.size+s+1 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = (C.eval (List.ofFn x) || F x) := by
  let gs := C.gates
  let m := n+gs.length
  obtain ⟨hs,o,strictH,backH,foot,liveH,runH⟩ := good m (by dsimp [m]; omega)
  let last : Gate := ⟨.or,[C.output,o]⟩
  let D : Circuit := ⟨gs++hs++[last],m+hs.length⟩
  have backJoin : ReadsBack n ⟨gs++hs,0⟩ := readsBack_append n back backH
  have backLast : ReadsBack (n+(gs++hs).length) ⟨[last],0⟩ := by
    intro i hi w hw
    have i0 : i=0 := by change i<1 at hi; omega
    subst i
    change w ∈ ([C.output,o] : List ℕ) at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    change w < n+(gs++hs).length+0
    simp only [List.length_append,Nat.add_zero]
    change C.output < n+gs.length at live
    change o < n+gs.length+hs.length at liveH
    rcases hw with rfl | rfl <;> omega
  refine ⟨D,?_,readsBack_append n backJoin backLast,?_,?_⟩
  · intro g hg
    change g ∈ gs++hs++[last] at hg
    rcases List.mem_append.mp hg with hg | gLast
    · rcases List.mem_append.mp hg with hg | hg
      · exact strict g hg
      · exact strictH g hg
    · have e := List.mem_singleton.mp gLast
      subst g
      exact ⟨Or.inr rfl,rfl⟩
  · change (gs++hs++[last]).length ≤ gs.length+s+1
    simp only [List.length_append,List.length_singleton]
    omega
  · intro x
    let w := List.ofFn x
    let v := wiresFrom gs w
    let u := wiresFrom hs v
    have vlen : v.length = m := by simp [v,m,w,length_wiresFrom]
    have ulen : u.length = m+hs.length := by rw [show u=wiresFrom hs v from rfl,length_wiresFrom,vlen]
    have oldValue : u.getD C.output false = C.eval w := by
      change (wiresFrom hs v).getD C.output false = v.getD C.output false
      exact getD_wiresFrom _ _ _ (by rw [vlen]; exact live)
    have after : u.getD o false = F x := by
      change (wiresFrom hs v).getD o false = _
      rw [runH _ vlen]
      congr
      funext i
      rw [show v = wiresFrom gs w from rfl,getD_wiresFrom _ _ _ (by simp [w])]
      exact getD_ofFn x i
    change (wiresFrom (gs++hs++[last]) w).getD (m+hs.length) false = _
    rw [wiresFrom_append,wiresFrom_append]
    change (u++[(u.getD C.output false || (u.getD o false || false))]).getD (m+hs.length) false = _
    rw [← ulen,getD_snoc_eq,oldValue,after,Bool.or_false]

end PEqualNP.Outside.L_meta_3140

open PEqualNP.Outside.L_meta_3140

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3140.Erase

set_option maxHeartbeats 7500000 in
theorem PEqualNP.Outside.L_meta_3140 : ∀ (a b : ℕ) (I : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (K : Finset ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C → (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) → j < C.gates.length → (∀ v : Fin (a + b), (C.wires (List.ofFn (fun u : Fin (a + b) => decide (u = v)))).getD (a + b + j) false = false) → (∃ k k' : ℕ, k ≠ k' ∧ k < C.gates.length ∧ k' < C.gates.length ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs) → j ∈ K → (∀ i ∈ K, i ≤ j) → (∀ i ∈ K, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, a + b ≤ w → w - (a + b) ∈ K) → (∀ i ∈ K, i ≠ j → ∃ k ∈ K, a + b + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → (∀ k < C.gates.length, k ∉ K → ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, a + b ≤ w → w - (a + b) ∈ K → w = a + b + j) → ¬ (a + b ≤ C.output ∧ C.output - (a + b) ∈ K) → (∀ (p p' : Fin a) (l l' : Fin b), (I p l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e1 : Fin (a + b) => decide (e1 = Fin.castAdd b p ∨ e1 = Fin.natAdd a l)) = false) → (I p' l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e2 : Fin (a + b) => decide (e2 = Fin.castAdd b p' ∨ e2 = Fin.natAdd a l)) = false) → (I p l' ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e3 : Fin (a + b) => decide (e3 = Fin.castAdd b p ∨ e3 = Fin.natAdd a l')) = false) → p' = p ∨ l' = l) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C'.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C' ∧ C'.size < C.size ∧ (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C' z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
  intro a b I C j K _ strict back computes hj off readers jK bounds closed privateReaders exit outside noFork
  classical
  let n := a+b
  let M := mask C K
  let single := mask C {j}
  let E : Finset (Fin a × Fin b) :=
    Finset.univ.filter fun e => I e.1 e.2 ∧ value single (edgeInput e.1 e.2) C.output = false
  let W := rawSlots n C K
  let G (x : Fin n → Bool) : Bool :=
    decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)
  let Target (x : Fin n → Bool) : Prop :=
    ∃ p l, I p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true
  have maskEq (x : Fin n → Bool) : value M x C.output = value single x C.output :=
    mask_agree C K j back jK exit x C.output (fun beyond inside => False.elim (outside ⟨beyond,inside⟩))
  have added (p : Fin a) (l : Fin b) :
      (p,l) ∈ E ↔ I p l ∧ value single (edgeInput p l) C.output = false := by simp [E]
  have presents (p : Fin a) (l : Fin b) (h : I p l) :
      value C (edgeInput p l) C.output = true := by
    apply (computes _).mpr
    exact ⟨p,l,h,by simp [edgeInput],by simp [edgeInput]⟩
  have arities (i : ℕ) (h : i ∈ K) : (gateAt C i).inputs.length = 2 := by
    have hi : i<C.gates.length := (bounds i h).trans_lt hj
    exact (strict (gateAt C i) (by rw [gateActual C i hi]; exact List.getElem_mem hi)).2
  have supports (p : Fin a) (l : Fin b) (h : (p,l) ∈ E) :
      Fin.castAdd b p ∈ W ∧ Fin.natAdd a l ∈ W :=
    endpoints C K j back arities closed jK hj off p l
      (presents p l ((added p l).mp h).1) ((added p l).mp h).2
  have cutEdges (p : Fin a) (l : Fin b) (h : (p,l) ∈ E) :
      I p l ∧ circuitFun n ⟨C.gates.set j falseGate,C.output⟩ (edgeInput p l) = false := by
    have hx := (added p l).mp h
    refine ⟨hx.1,?_⟩
    rw [← mask_single_set C j]
    exact hx.2
  have forest : ∀ p p' l l', (p,l) ∈ E → (p',l) ∈ E → (p,l') ∈ E → p'=p ∨ l'=l := by
    intro p p' l l' hp hq hr
    exact noFork p p' l l' (cutEdges _ _ hp) (cutEdges _ _ hq) (cutEdges _ _ hr)
  have replace (x : Fin n → Bool) : (value M x C.output || G x) = true ↔ Target x := by
    rw [Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact (computes x).mp (maskBelow C K back strict x h)
      · change decide _ = true at h
        obtain ⟨p,l,e,hp,hl⟩ := of_decide_eq_true h
        exact ⟨p,l,((added p l).mp e).1,hp,hl⟩
    · rintro ⟨p,l,e,hp,hl⟩
      cases yes : value single (edgeInput p l) C.output
      · right
        apply decide_eq_true
        exact ⟨p,l,(added p l).mpr ⟨e,yes⟩,hp,hl⟩
      · left
        have up (u : Fin n) : edgeInput p l u = true → x u = true := by
          intro h
          rcases of_decide_eq_true h with rfl | rfl <;> assumption
        have okay : value M (edgeInput p l) C.output = true :=
          (maskEq _).trans yes
        exact maskMono C K back strict _ x up okay
  have cardW : W.card ≤ K.card+1 := slotBudget n C K j jK arities privateReaders
  let st := elim n M.gates (idStats n,[])
  let kept := st.2
  let state := st.1.getD C.output (Stat.const false)
  obtain ⟨k,k',ne,hk,hk',ed,ed'⟩ := readers
  have cut : kept.length + K.card + 2 ≤ C.gates.length :=
    shrinkBudget n C K j k k' hj jK bounds back strict ne hk hk' ed ed'
  have lostBuild (someEdge : E.Nonempty) : Bld n G (W.card-1) :=
    starBuild E W someEdge forest supports
  have noAdd (empty : ¬ E.Nonempty) (x : Fin n → Bool) : G x = false := by
    have z := Finset.not_nonempty_iff_eq_empty.mp empty
    simp [G,z]
  obtain ⟨norm,proper,live,same⟩ := normalize (n:=n) C K strict
  change (∀ g ∈ kept, StrictGate g) at norm
  change (∀ o, ReadsBack n ⟨kept,o⟩) at proper
  change state.Valid (n+kept.length) at live
  change (∀ x : Fin n → Bool, state.val (PEqualNP.Outside.L_meta_3140.wiresFrom kept (List.ofFn x)) =
    value M x C.output) at same
  cases actual : state with
  | const v =>
    have fixed (x : Fin n → Bool) : value M x C.output = v := by
      have h := same x
      rw [actual] at h
      exact h.symm
    have isFalse : v = false := by
      cases hv : v
      · rfl
      · let z : Fin n → Bool := fun _ => false
        have yes : value M z C.output = true := (fixed z).trans hv
        obtain ⟨p,l,_,hp,_⟩ := (computes z).mp (maskBelow C K back strict z yes)
        exact False.elim (by cases hp)
    by_cases present : E.Nonempty
    · obtain ⟨D,dModel,dBack,dLen,dEval⟩ := builderCircuit (lostBuild present)
      refine ⟨D,dModel,dBack,?_,fun x => ?_⟩
      · change D.size < C.gates.length
        omega
      · change D.eval (List.ofFn x) = true ↔ Target x
        rw [dEval]
        have test := replace x
        rw [fixed x,isFalse,Bool.false_or] at test
        exact test
    · let D : Circuit := ⟨[],n⟩
      refine ⟨D,by simp [D],by simp [D,ReadsBack],?_,fun x => ?_⟩
      · change 0 < C.gates.length
        omega
      · change (List.ofFn x).getD n false = true ↔ Target x
        have absent : (List.ofFn x).getD n false = false :=
          List.getD_eq_default _ _ (by simp [n])
        rw [absent]
        have test := replace x
        rw [fixed x,isFalse,Bool.false_or,noAdd present x] at test
        exact test
  | wire w =>
    let D0 : Circuit := ⟨kept,w⟩
    rw [actual] at live
    have existsWire : D0.output < n+D0.size := live
    have eval0 (x : Fin n → Bool) : D0.eval (List.ofFn x) = value M x C.output := by
      have h := same x
      rw [actual] at h
      exact h
    by_cases present : E.Nonempty
    · obtain ⟨D,dm,db,ds,de⟩ := appendOR D0 norm (proper w) existsWire (lostBuild present)
      refine ⟨D,dm,db,?_,fun x => ?_⟩
      · change D.size ≤ kept.length+(W.card-1)+1 at ds
        change D.size < C.gates.length
        omega
      · change D.eval (List.ofFn x) = true ↔ Target x
        rw [de,eval0]
        exact replace x
    · refine ⟨D0,norm,proper w,?_,fun x => ?_⟩
      · change kept.length < C.gates.length
        omega
      · change D0.eval (List.ofFn x) = true ↔ Target x
        rw [eval0]
        have test := replace x
        rw [noAdd present x,Bool.or_false] at test
        exact test
