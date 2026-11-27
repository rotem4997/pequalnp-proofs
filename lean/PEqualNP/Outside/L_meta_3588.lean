import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3588_aux

-- The gate simplifier below is adapted from L_meta_2535. The wiring for
-- duplicate inputs and the fixed input, and the reduction proof, are new.
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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

def sval (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def svalid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
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
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, svalid w.length s) :
    svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (sval w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, svalid, sval, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

theorem svalid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem sval_append (w t : List Bool) : ∀ s : Bool ⊕ ℕ, svalid w.length s →
    sval (w ++ t) s = sval w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    svalid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    sval (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
    have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨svalid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, sval_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


theorem elim_count1 (n k : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    acc.1.getD k (Sum.inl false) = Sum.inl false →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hlen hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hl : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
    have hk' : (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hk
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by omega) hk'
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨false, List.mem_map.2 ⟨k, hg, hk⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem agree_except (affected : ℕ → Prop) (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
    (∀ j, ¬ affected j → w.getD j false = w'.getD j false) →
    (∀ g ∈ gs, ∀ j ∈ g.inputs, ¬ affected j) →
    ∀ j, ¬ affected j → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ h _ j hj; exact h j hj
  | cons g gs ih =>
    intro w w' hl hag hgs
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hag a (hgs g List.mem_cons_self a ha)
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (by simp [hl]) _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = w.length
    · subst hjl
      rw [getD_snoc_eq, hl, getD_snoc_eq, hv]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact hag j hj

theorem getD_ofFn_lt {α : Type} {n : ℕ} (x : Fin n → α) (d : α) (j : ℕ) (h : j < n) :
    (List.ofFn x).getD j d = x ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ofFn_ge {α : Type} {n : ℕ} (x : Fin n → α) (d : α) (j : ℕ) (h : n ≤ j) :
    (List.ofFn x).getD j d = d :=
  List.getD_eq_default _ _ (by simp; omega)

def baseInput (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 4]

def input (sel : Fin 11) (x : Fin 9 → Bool) : List Bool :=
  baseInput x ++ [(baseInput x).getD sel.val false]

def baseRefs : List (Bool ⊕ ℕ) :=
  [.inr 0, .inr 1, .inr 2, .inr 3, .inl false, .inr 4, .inr 5, .inr 6, .inr 7, .inr 0]

def refs (sel : Fin 11) : List (Bool ⊕ ℕ) :=
  baseRefs ++ [baseRefs.getD sel.val (.inl false)]

def insertFalse (x : Fin 8 → Bool) : Fin 9 → Bool :=
  ![x 0, x 1, x 2, x 3, false, x 4, x 5, x 6, x 7]

def affected (sel : Fin 11) (j : ℕ) : Prop :=
  j = 4 ∨ (sel.val = 4 ∧ j = 10)

theorem getD_snoc_at {α : Type} (L : List α) (v d : α) (j : ℕ) (hj : j = L.length) :
    (L ++ [v]).getD j d = v := hj.symm ▸ getD_snoc_eq L v d

theorem baseRefs_sound (y : Fin 8 → Bool) (j : ℕ) :
    svalid 8 (baseRefs.getD j (.inl false)) ∧
      sval (List.ofFn y) (baseRefs.getD j (.inl false)) =
        (baseInput (insertFalse y)).getD j false := by
  by_cases hj : j < 10
  · interval_cases j
    all_goals constructor
    all_goals first
      | (change True; trivial)
      | (change _ < 8; decide)
      | rfl
      | (change y 0 = (y 0 || false); simp)
  · have hleft : baseRefs.getD j (.inl false) = .inl false :=
      List.getD_eq_default _ _ (by simpa [baseRefs] using Nat.le_of_not_gt hj)
    have hright : (baseInput (insertFalse y)).getD j false = false :=
      List.getD_eq_default _ _ (by simpa [baseInput] using Nat.le_of_not_gt hj)
    rw [hleft, hright]
    exact ⟨trivial, rfl⟩

theorem init_inv (sel : Fin 11) (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (input sel (insertFalse y)) (refs sel, []) := by
  refine ⟨by simp [refs, baseRefs, input, baseInput], ?_⟩
  intro j
  by_cases hj : j = 10
  · subst j
    change svalid 8 ((refs sel).getD 10 (.inl false)) ∧
      sval (List.ofFn y) ((refs sel).getD 10 (.inl false)) =
        (input sel (insertFalse y)).getD 10 false
    unfold refs input
    rw [getD_snoc_at baseRefs _ _ 10 rfl,
      getD_snoc_at (baseInput (insertFalse y)) _ _ 10 (by simp [baseInput])]
    exact baseRefs_sound y sel.val
  · simpa only [refs, input, getD_snoc_ne _ _ _ _ (show j ≠ baseRefs.length from hj),
      getD_snoc_ne _ _ _ _ (show j ≠ (baseInput (insertFalse y)).length by
        simpa [baseInput] using hj), wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
      using baseRefs_sound y j

theorem refs_affected (sel : Fin 11) (j : ℕ) (h : affected sel j) :
    j < (refs sel).length ∧ (refs sel).getD j (.inl false) = .inl false := by
  rcases h with rfl | ⟨hsel, rfl⟩
  · exact ⟨by simp [refs, baseRefs], rfl⟩
  · constructor
    · simp [refs, baseRefs]
    · unfold refs
      rw [show (10 : ℕ) = baseRefs.length by rfl, getD_snoc_eq, hsel]
      rfl

theorem base_agree (x : Fin 9 → Bool) (hx0 : x 0 = true) (j : ℕ) (hj : j ≠ 4) :
    (baseInput x).getD j false =
      (baseInput (Function.update x (4 : Fin 9) true)).getD j false := by
  by_cases h9 : j = 9
  · subst j
    change (List.ofFn x ++ [x 0 || x 4]).getD 9 false =
      (List.ofFn (Function.update x (4 : Fin 9) true) ++
        [Function.update x (4 : Fin 9) true 0 || Function.update x (4 : Fin 9) true 4]).getD 9 false
    rw [getD_snoc_at (List.ofFn x) _ _ 9 (by simp),
      getD_snoc_at (List.ofFn (Function.update x (4 : Fin 9) true)) _ _ 9 (by simp)]
    simp [Function.update_of_ne (show (0 : Fin 9) ≠ 4 by decide), hx0]
  · unfold baseInput
    rw [getD_snoc_ne _ _ _ _ (by simpa using h9), getD_snoc_ne _ _ _ _ (by simpa using h9)]
    by_cases hlt : j < 9
    · rw [getD_ofFn_lt _ _ _ hlt, getD_ofFn_lt _ _ _ hlt]
      exact (Function.update_of_ne (show (⟨j, hlt⟩ : Fin 9) ≠ 4 from
        fun eq => hj (congrArg Fin.val eq)) true x).symm
    · rw [getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]

theorem input_agree (sel : Fin 11) (x : Fin 9 → Bool) (hx0 : x 0 = true) (j : ℕ)
    (hj : ¬ affected sel j) :
    (input sel x).getD j false =
      (input sel (Function.update x (4 : Fin 9) true)).getD j false := by
  by_cases he : j = 10
  · subst j
    have hs : sel.val ≠ 4 := fun hs => hj (Or.inr ⟨hs, rfl⟩)
    unfold input
    rw [getD_snoc_at (baseInput x) _ _ 10 (by simp [baseInput]),
      getD_snoc_at (baseInput (Function.update x (4 : Fin 9) true)) _ _ 10 (by simp [baseInput])]
    exact base_agree x hx0 sel.val hs
  · unfold input
    rw [getD_snoc_ne _ _ _ _ (by simpa [baseInput] using he),
      getD_snoc_ne _ _ _ _ (by simpa [baseInput] using he)]
    exact base_agree x hx0 j (fun h => hj (Or.inl h))

theorem main (C : Circuit) (sel : Fin 11) (f : (Fin 9 → Bool) → Bool)
    (hfan : FanInTwo C) (hcomp : ∀ x, C.eval (input sel x) = f x)
    (hdep : ∃ x : Fin 9 → Bool, x 0 = true ∧ x 4 = false ∧
      f x ≠ f (Function.update x (4 : Fin 9) true))
    (hnc : ∃ x y : Fin 8 → Bool, f (insertFalse x) ≠ f (insertFalse y)) :
    HasCircuitSize 8 (fun y => f (insertFalse y)) (C.size - 1) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hfan g0 hg0)
  have hevg : ∀ x, (wiresFrom gs (input sel x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hcomp x]
    rfl
  set acc := elim 8 gs (refs sel, []) with hacc
  have hval : ∀ y : Fin 8 → Bool,
      sval (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (.inl false)) =
        f (insertFalse y) := by
    intro y
    have hi := inv_elim 8 (List.ofFn y) (by simp) gs _ _
      (fun g hg => (hnok g hg).1) (init_inv sel y)
    rw [hacc, (hi.2 C.output).2, hevg]
  have hout : ¬ affected sel C.output := by
    intro ho
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hevg, ← hevg, getD_wiresFrom _ _ _ (by
      have := (refs_affected sel C.output ho).1
      simpa [refs, baseRefs, input, baseInput] using this),
      getD_wiresFrom _ _ _ (by
      have := (refs_affected sel C.output ho).1
      simpa [refs, baseRefs, input, baseInput] using this)]
    have hx := (init_inv sel x).2 C.output
    have hy := (init_inv sel y).2 C.output
    rw [(refs_affected sel C.output ho).2] at hx hy
    exact hx.2.symm.trans hy.2
  have hread : ∃ g ∈ gs, ∃ j ∈ g.inputs, affected sel j := by
    by_contra hn
    obtain ⟨x, hx0, _, hx⟩ := hdep
    apply hx
    rw [← hevg, ← hevg]
    exact agree_except (affected sel) gs _ _ (by simp [input, baseInput])
      (input_agree sel x hx0)
      (fun g hg j hj h => hn ⟨g, hg, j, hj, h⟩) C.output hout
  obtain ⟨g, hg, j, hj, ht⟩ := hread
  obtain ⟨hjlt, hjfalse⟩ := refs_affected sel j ht
  have hcount := elim_count1 8 j gs (refs sel, []) hnok hjlt hjfalse
  rw [← hacc] at hcount
  have hpos : 0 < gs.countP (fun g => decide (j ∈ g.inputs)) :=
    List.countP_pos_iff.2 ⟨g, hg, by simpa using hj⟩
  have hlen : gs.length = C.size := by rw [hgs, List.length_map]; rfl
  cases hs : acc.1.getD C.output (.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, fun g hg => elim_ok 8 gs _ (by simp) g hg, ?_, ?_⟩
    · show acc.2.length ≤ C.size - 1
      simp only [List.length_nil, zero_add] at hcount
      omega
    · intro y
      have h := hval y
      rw [hs] at h
      exact h

end PEqualNP.Outside.L_meta_3588_aux

theorem PEqualNP.Outside.L_meta_3588 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : (Fin (9 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))];         x1.eval (x6 ++ [x6.getD (↑x2) Bool.false]) = x3 x5) →       (∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.true ∧ x6 (4 : Fin (9 : ℕ)) = Bool.false ∧ x3 x6 ≠ x3 (Function.update x6 (4 : Fin (9 : ℕ)) Bool.true)) →         have x7 : (Fin (8 : ℕ) → Bool) → Bool := fun (x7 : Fin (8 : ℕ) → Bool) => x3 ![x7 (0 : Fin (8 : ℕ)), x7 (1 : Fin (8 : ℕ)), x7 (2 : Fin (8 : ℕ)), x7 (3 : Fin (8 : ℕ)), Bool.false, x7 (4 : Fin (8 : ℕ)), x7 (5 : Fin (8 : ℕ)), x7 (6 : Fin (8 : ℕ)), x7 (7 : Fin (8 : ℕ))];         (∃ (x8 : Fin (8 : ℕ) → Bool) (x9 : Fin (8 : ℕ) → Bool), x7 x8 ≠ x7 x9) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x7 (x1.size - (1 : ℕ)) := by
  intro C sel f hfan hcomp hdep reduced hnc
  exact PEqualNP.Outside.L_meta_3588_aux.main C sel f hfan hcomp hdep hnc
