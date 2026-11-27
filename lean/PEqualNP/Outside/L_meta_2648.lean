import Mathlib
import PEqualNP.Defs

-- The cleaning lemmas follow those of the merged file L_meta_1680.lean of this repository, without NOT
-- and with equal operands collapsed. New are simplify_shape, elim_head, normal and the final theorem.

namespace PEqualNP.Outside.L_meta_2648

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def MOk (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

-- What an emitted gate looks like: AND or OR of two distinct valid wires.
def Shape (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, g.inputs = [j, k] ∧ j < m ∧ k < m ∧ j ≠ k

theorem simplify_shape (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, Shape m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    rename_i j k
    by_cases h : j = k
    · simp [h] at hg
    · simp [h] at hg
      subst hg
      exact ⟨Or.inl rfl, j, k, rfl, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), h⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    rename_i j k
    by_cases h : j = k
    · simp [h] at hg
    · simp [h] at hg
      subst hg
      exact ⟨Or.inr rfl, j, k, rfl, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), h⟩
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with e | k
      · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases e <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · by_cases h : j = k
        · subst h
          simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with e | k
      · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases e <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · by_cases h : j = k
        · subst h
          simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, MOk g) → Inv n y w acc →
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


-- Every status stays valid, so every emitted gate has the wanted shape.
def Head (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, MOk g) ∧ ∀ g, gs.head? = some g → Shape n g

theorem elim_head (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ i, (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length)) →
    (∀ g ∈ gs, MOk g) → Head n acc.2 → Head n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ h; exact h
  | cons g gs ih =>
    intro acc hv hok h
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hiv : ∀ s ∈ ins, s.Valid (n + acc.2.length) := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact hv a
    have hg := hok g List.mem_cons_self
    have hsh := simplify_shape g.op (n + acc.2.length) ins hiv
    have hval : ((simplify g.op (n + acc.2.length) ins).2).Valid
        (n + acc.2.length + (simplify g.op (n + acc.2.length) ins).1.toList.length) := by
      have := (simplify_sound g.op hg.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hg.2) (by simpa using hiv)).1
      simpa using this
    apply ih (elimStep n acc g) ?_ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_
    · intro i
      show ((acc.1 ++ [(simplify g.op (n + acc.2.length) ins).2]).getD i (Sum.inl false)).Valid
        (n + (acc.2 ++ (simplify g.op (n + acc.2.length) ins).1.toList).length)
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · rw [hil, getD_snoc_eq]; exact hval
      · rw [getD_snoc_ne _ _ _ _ hil]; exact Stat.valid_mono (by omega) _ (hv i)
    · show Head n (acc.2 ++ (simplify g.op (n + acc.2.length) ins).1.toList)
      refine ⟨?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.1 hg' with h1 | h1
        · exact h.1 g' h1
        · obtain ⟨hop, j, k, hjk, _⟩ := hsh g' (by simpa using h1)
          exact ⟨hop, by simp [hjk]⟩
      · intro g' hg'
        rcases hacc : acc.2 with _ | ⟨a, l⟩
        · rw [hacc] at hg' hsh
          have : g' ∈ (simplify g.op (n + 0) ins).1 := by
            simp only [List.nil_append, List.length_nil] at hg'
            rcases ho : (simplify g.op (n + 0) ins).1 with _ | b
            · rw [ho] at hg'; simp at hg'
            · rw [ho] at hg'; simp at hg'; simp [hg']
          simpa using hsh g' (by simpa using this)
        · apply h.2
          rw [hacc] at hg' ⊢
          simpa using hg'

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i.val)

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem id_valid (n i : ℕ) : ((idStats n).getD i (Sum.inl false)).Valid n := by
  by_cases h : i < n
  · have : (idStats n).getD i (Sum.inl false) = Sum.inr i := getD_ofFn' n _ _ ⟨i, h⟩
    rw [this]; exact h
  · have : (idStats n).getD i (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by simp [idStats]; omega)
    rw [this]; trivial

theorem id_inv (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  refine ⟨by simpa using id_valid n i, ?_⟩
  by_cases h : i < n
  · have e1 : (idStats n).getD i (Sum.inl false) = Sum.inr i := getD_ofFn' n _ _ ⟨i, h⟩
    show ((idStats n).getD i (Sum.inl false)).val _ = _
    rw [e1]; rfl
  · have e1 : (idStats n).getD i (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by simp [idStats]; omega)
    show ((idStats n).getD i (Sum.inl false)).val _ = _
    rw [e1, List.getD_eq_default _ _ (by simp; omega)]; rfl

theorem normal (n : ℕ) (P : (Fin n → Bool) → Prop) (C : Circuit) (hC : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ P x)
    (hconst : ∀ c : Bool, ∃ x, ¬ (c = true ↔ P x))
    (hvar : ∀ j : Fin n, ∃ x, ¬ (x j = true ↔ P x)) :
    ∃ D : Circuit, Monotone2 D ∧ (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ P x) ∧
      D.size ≤ C.size ∧ ∃ (op : GateOp) (gs : List Gate) (a b : ℕ),
        D.gates = ⟨op, [a, b]⟩ :: gs ∧ a < n ∧ b < n ∧ a ≠ b := by
  have hok : ∀ g ∈ C.gates, MOk g := fun g hg => by
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  let r := elim n C.gates (idStats n, [])
  have hhead : Head n r.2 := elim_head n C.gates (idStats n, []) (by simpa using id_valid n) hok
    ⟨by simp, by simp⟩
  have hinv : ∀ x : Fin n → Bool, Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) r :=
    fun x => inv_elim n (List.ofFn x) (by simp) C.gates _ _ hok (id_inv n x)
  have hval : ∀ x : Fin n → Bool,
      ((r.1.getD C.output (Sum.inl false)).val (wiresFrom r.2 (List.ofFn x)) = true ↔ P x) := by
    intro x
    rw [((hinv x).2 C.output).2]
    exact he x
  have hlen : r.2.length ≤ C.gates.length := by
    have := elim_len n C.gates (idStats n, [])
    simpa using this
  rcases hst : r.1.getD C.output (Sum.inl false) with c | j
  · exfalso
    obtain ⟨x, hx⟩ := hconst c
    have := hval x
    rw [hst] at this
    exact hx this
  · have hD : ∀ x : Fin n → Bool, (Circuit.eval ⟨r.2, j⟩ (List.ofFn x) = true ↔ P x) := by
      intro x
      have := hval x
      rw [hst] at this
      exact this
    refine ⟨⟨r.2, j⟩, ?_, hD, hlen, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := hhead.1 g hg
      exact ⟨by simpa using h1, h2⟩
    · rcases hr : r.2 with _ | ⟨g, gs⟩
      · exfalso
        have hv := ((hinv (fun _ => false)).2 C.output).1
        rw [hst, hr] at hv
        have hjn : j < n := by simpa [Stat.Valid] using hv
        obtain ⟨x, hx⟩ := hvar ⟨j, hjn⟩
        apply hx
        rw [← hD x, hr]
        show (x ⟨j, hjn⟩ = true) ↔ (List.ofFn x).getD j false = true
        rw [getD_ofFn' n x false ⟨j, hjn⟩]
      · obtain ⟨hop, a, b, hab, ha, hb, hne⟩ := hhead.2 g (by rw [hr]; rfl)
        obtain ⟨op, inp⟩ := g
        exact ⟨op, gs, a, b, by simp only at hab; rw [hab], ha, hb, hne⟩

end PEqualNP.Outside.L_meta_2648

theorem PEqualNP.Outside.L_meta_2648 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ x2 x5) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin (14 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ x2 x7) ∧ x6.size ≤ x3.size ∧ ∃ (x7 : PEqualNP.CircuitLowerBounds.GateOp) (x8 : List PEqualNP.CircuitLowerBounds.Gate) (x9 : ℕ) (x10 : ℕ), x6.gates = { op := x7, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } :: x8 ∧ x9 < (14 : ℕ) ∧ x10 < (14 : ℕ) ∧ x9 ≠ x10 := by
  intro E f C hC he
  refine PEqualNP.Outside.L_meta_2648.normal 14 f C hC he ?_ ?_
  · intro c
    cases c
    · refine ⟨fun _ => true, ?_⟩
      intro h
      exact absurd (h.2 ⟨0, 7, by decide, rfl, rfl⟩) (by decide)
    · refine ⟨fun _ => false, ?_⟩
      intro h
      obtain ⟨a, b, _, h1, _⟩ := h.1 rfl
      exact absurd h1 Bool.false_ne_true
  · intro j
    refine ⟨fun i => decide (i = j), ?_⟩
    intro h
    obtain ⟨a, b, hab, h1, h2⟩ := h.1 (by simp)
    have ea : a = j := by simpa using h1
    have eb : b = j := by simpa using h2
    subst ea
    subst eb
    revert hab
    fin_cases b <;> decide
