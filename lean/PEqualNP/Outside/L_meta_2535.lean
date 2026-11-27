import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2535_aux

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

theorem agree_off (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    (∀ g ∈ gs, k ∉ g.inputs) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ h _ j hj; exact h j hj
  | cons g gs ih =>
    intro w w' hl hag hgs
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hag a (fun e => hgs g List.mem_cons_self (e ▸ ha))
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

def initStats (n : ℕ) (i : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun j : Fin n => if j = i then (Sum.inl false : Bool ⊕ ℕ) else Sum.inr j.val)

theorem inv_init1 (n : ℕ) (i : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y i false)) (initStats n i, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro j
  by_cases hj : j < n
  · show svalid (n + 0) ((initStats n i).getD j (Sum.inl false)) ∧
      sval (wiresFrom [] (List.ofFn y)) ((initStats n i).getD j (Sum.inl false)) = _
    rw [initStats, getD_ofFn_lt _ _ _ hj, getD_ofFn_lt _ _ _ hj]
    by_cases hji : (⟨j, hj⟩ : Fin n) = i
    · rw [if_pos hji, ← hji, Function.update_self]
      exact ⟨trivial, rfl⟩
    · rw [if_neg hji, Function.update_of_ne hji]
      refine ⟨show j < n + 0 by omega, ?_⟩
      show (wiresFrom [] (List.ofFn y)).getD j false = y ⟨j, hj⟩
      exact getD_ofFn_lt _ _ _ hj
  · show svalid (n + 0) ((initStats n i).getD j (Sum.inl false)) ∧
      sval (wiresFrom [] (List.ofFn y)) ((initStats n i).getD j (Sum.inl false)) = _
    rw [initStats, getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]
    exact ⟨trivial, rfl⟩

theorem main (n s : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (h : HasCircuitSize n f s)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update y i false)) :
    HasCircuitSize n (fun z => f (Function.update z i false)) (s - 1) := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hfan g0 hg0)
  have hevg : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]
    rfl
  have hout : C.output ≠ i.val := by
    intro ho
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hevg, ← hevg, ho, getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp),
      getD_ofFn_lt _ _ _ i.isLt, getD_ofFn_lt _ _ _ i.isLt]
    simp
  have hread : ∃ g ∈ gs, i.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx⟩ := hdep
    apply hx
    rw [← hevg, ← hevg]
    refine agree_off i.val gs _ _ (by simp) ?_ hno C.output hout
    intro j hj
    by_cases hjn : j < n
    · rw [getD_ofFn_lt _ _ _ hjn, getD_ofFn_lt _ _ _ hjn]
      have hne : (⟨j, hjn⟩ : Fin n) ≠ i := fun e => hj (by rw [← e])
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rw [getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Function.update y i false)))
        (elim n gs (initStats n i, [])) := fun y =>
    inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init1 n i y)
  set acc := elim n gs (initStats n i, []) with hacc
  have hval : ∀ y : Fin n → Bool,
      sval (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Function.update y i false) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hk : (initStats n i).getD i.val (Sum.inl false) = Sum.inl false := by
    rw [initStats, getD_ofFn_lt _ _ _ i.isLt]
    simp
  have hcount := elim_count1 n i.val gs (initStats n i, []) hnok (by simp [initStats]) hk
  rw [← hacc] at hcount
  have hpos : 0 < gs.countP (fun g => decide (i.val ∈ g.inputs)) :=
    List.countP_pos_iff.2 ⟨g, hg, by simpa using hgi⟩
  have hlen : gs.length = C.size := by
    rw [hgs, List.length_map]; rfl
  have hsz' : C.size ≤ s := hsz
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, fun g hg => elim_ok n gs _ (by simp) g hg, ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      simp only [List.length_nil, zero_add] at hcount
      omega
    · intro y
      have e := hval y
      rw [hs] at e
      exact e

end PEqualNP.Outside.L_meta_2535_aux

theorem PEqualNP.Outside.L_meta_2535 : ∀ (x1 x2 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x4 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x2 → (∃ (x6 : Fin x1 → Bool), x3 (Function.update x6 x4 Bool.false) ≠ x3 (Function.update x6 x4 Bool.true)) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x3 (Function.update x7 x4 Bool.false) ≠ x3 (Function.update x8 x4 Bool.false)) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x3 (Function.update x8 x4 Bool.false)) (x2 - (1 : ℕ)) :=
  fun n s f i h hdep hnc => PEqualNP.Outside.L_meta_2535_aux.main n s f i h hdep hnc
