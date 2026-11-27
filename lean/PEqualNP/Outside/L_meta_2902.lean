import Mathlib
import PEqualNP.Defs

-- The cleaning lemmas follow those of the merged file L_meta_1680.lean of this repository, without NOT
-- and with equal operands collapsed.

namespace PEqualNP.Outside.L_meta_2902

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


theorem simplify_mok (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, MOk g := by
  intro g hg
  obtain ⟨hop, j, k, hjk, _⟩ := simplify_shape op m ins hv g hg
  exact ⟨hop, by simp [hjk]⟩

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) : (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + (gs.filter fun g => decide (k ∈ g.inputs)).length
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.filter_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hg := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count _ _ _ hg.1 (by simpa using hg.2)
        exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true, List.length_cons]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem elim_mok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ i, (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length)) →
    (∀ g ∈ gs, MOk g) → (∀ g ∈ acc.2, MOk g) → ∀ g ∈ (elim n gs acc).2, MOk g := by
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
    · intro g' hg'
      rcases List.mem_append.1 hg' with h1 | h1
      · exact h g' h1
      · exact simplify_mok _ _ _ hiv g' (Option.mem_toList.1 h1)

theorem gate_mono (g : Gate) (hg : MOk g) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  obtain ⟨op, inp⟩ := g
  rcases hg.1 with e | e
  · have e : op = GateOp.and := e
    subst e
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H a ha => h a (H a ha)
  · have e : op = GateOp.or := e
    subst e
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨a, ha, H⟩ => ⟨a, ha, h a H⟩

theorem wires_mono (gs : List Gate) : ∀ w w' : List Bool, (∀ g ∈ gs, MOk g) →
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hok hl h
    refine ih (w ++ [_]) (w' ++ [_]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [hl]) ?_
    intro i
    by_cases hil : i = w.length
    · rw [hil, getD_snoc_eq, hl, getD_snoc_eq]
      exact gate_mono g (hok g List.mem_cons_self) w w' h
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      exact h i

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

def ext (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 4]

theorem ext_len (x : Fin 9 → Bool) : (ext x).length = 10 := by simp [ext]

theorem ext_lo (x : Fin 9 → Bool) (i : Fin 9) : (ext x).getD i.val false = x i := by
  unfold ext
  rw [List.getD_append _ _ _ _ (by simp), getD_ofFn']

theorem ext_hi (x : Fin 9 → Bool) : (ext x).getD 9 false = (x 0 || x 4) := by
  have h := getD_snoc_eq (List.ofFn x) (x 0 || x 4) false
  have l : (List.ofFn x).length = 9 := by simp
  rw [l] at h
  exact h

theorem ext_out (x : Fin 9 → Bool) (i : ℕ) (h : 10 ≤ i) : (ext x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [ext_len]; omega)

theorem ext_mono (x y : Fin 9 → Bool) (h : ∀ i, x i = true → y i = true) (i : ℕ) :
    (ext x).getD i false = true → (ext y).getD i false = true := by
  by_cases h9 : i < 9
  · have a := ext_lo x ⟨i, h9⟩
    have b := ext_lo y ⟨i, h9⟩
    simp only at a b
    rw [a, b]; exact h ⟨i, h9⟩
  · by_cases h10 : i = 9
    · subst h10
      rw [ext_hi, ext_hi]
      intro H
      rcases Bool.or_eq_true _ _ |>.mp H with H | H
      · rw [h 0 H]; rfl
      · rw [h 4 H]; simp
    · rw [ext_out x i (by omega)]; intro H; exact absurd H (by decide)

def yes : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
def all : List ℕ := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261,
  264, 276, 288, 320, 385, 402]

def bits (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i

def F9 (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

theorem below : ∀ x : Fin 9 → Bool, F9 x = true →
    ∃ m ∈ yes, ∀ i, bits m i = true → x i = true := by decide +kernel

theorem above : ∀ x : Fin 9 → Bool, F9 x = false →
    ∃ m ∈ all, m ∉ yes ∧ ∀ i, x i = true → bits m i = true := by decide +kernel

theorem yes_all : ∀ m ∈ yes, m ∈ all := by decide

theorem agrees (C : Circuit) (hok : ∀ g ∈ C.gates, MOk g)
    (hs : ∀ m ∈ all, C.eval (ext (bits m)) = decide (m ∈ yes)) (x : Fin 9 → Bool) :
    C.eval (ext x) = F9 x := by
  have mono : ∀ a b : Fin 9 → Bool, (∀ i, a i = true → b i = true) →
      C.eval (ext a) = true → C.eval (ext b) = true := fun a b h =>
    wires_mono C.gates (ext a) (ext b) hok (by rw [ext_len, ext_len]) (ext_mono a b h) C.output
  cases hF : F9 x
  · obtain ⟨m, hm, hn, hle⟩ := above x hF
    cases hC : C.eval (ext x)
    · rfl
    · have h1 := mono x (bits m) hle hC
      rw [hs m hm] at h1
      simp [hn] at h1
  · obtain ⟨m, hm, hle⟩ := below x hF
    apply mono (bits m) x hle
    rw [hs m (yes_all m hm)]
    simp [hm]

def drop (x : Fin 9 → Bool) (v : Fin 9) : Fin 9 → Bool := fun i => if i = v then false else x i

theorem main (C : Circuit) (hC : Monotone2 C)
    (hs : ∀ m ∈ all, C.eval (ext (bits m)) = decide (m ∈ yes)) (v : Fin 9) (h0 : (0 : Fin 9) ≠ v)
    (h4 : (4 : Fin 9) ≠ v)
    (hne : ∃ x y, F9 (drop x v) ≠ F9 (drop y v))
    (hcount : 4 ≤ (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 4 ≤ C.size ∧
      ∀ x : Fin 9 → Bool, D.eval (ext x) = F9 (drop x v) := by
  have hok : ∀ g ∈ C.gates, MOk g := fun g hg => by
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  let st : List Stat := List.ofFn (fun i : Fin 10 => if i.val = v.val then Sum.inl false else Sum.inr i.val)
  have stget : ∀ i : ℕ, st.getD i (Sum.inl false)
      = if i < 10 ∧ i ≠ v.val then Sum.inr i else Sum.inl false := by
    intro i
    by_cases h : i < 10
    · have e : st.getD i (Sum.inl false)
          = if i = v.val then (Sum.inl false : Stat) else Sum.inr i :=
        getD_ofFn' 10 (fun i : Fin 10 => if i.val = v.val then (Sum.inl false : Stat)
          else Sum.inr i.val) (Sum.inl false) ⟨i, h⟩
      rw [e]
      by_cases hv : i = v.val
      · simp [hv]
      · simp [h, hv]
    · rw [List.getD_eq_default _ _ (by simp [st]; omega)]
      simp [h]
  have hvalid : ∀ i, (st.getD i (Sum.inl false)).Valid 10 := by
    intro i
    rw [stget]
    split
    · next h => exact h.1
    · trivial
  let r := elim 10 C.gates (st, [])
  have hinv : ∀ x : Fin 9 → Bool, Inv 10 (ext x) (wiresFrom C.gates (ext (drop x v))) r := by
    intro x
    refine inv_elim 10 (ext x) (ext_len x) C.gates _ (st, []) hok ⟨by simp [st, ext_len], ?_⟩
    intro i
    refine ⟨by simpa using hvalid i, ?_⟩
    show (st.getD i (Sum.inl false)).val (ext x) = (ext (drop x v)).getD i false
    rw [stget]
    by_cases h9 : i < 9
    · have b := ext_lo (drop x v) ⟨i, h9⟩
      have a := ext_lo x ⟨i, h9⟩
      simp only at a b
      rw [b]
      by_cases hv : i = v.val
      · have hv' : (⟨i, h9⟩ : Fin 9) = v := Fin.ext hv
        simp [hv, drop, hv', Stat.val]
      · have hv' : (⟨i, h9⟩ : Fin 9) ≠ v := fun e => hv (congrArg Fin.val e)
        have h10 : i < 10 := by omega
        simp only [h10, hv, ne_eq, not_false_eq_true, and_self, if_true, Stat.val, drop, hv', if_false]
        exact a
    · by_cases h10 : i = 9
      · subst h10
        have hv : (9 : ℕ) ≠ v.val := by have := v.isLt; omega
        rw [ext_hi]
        simp only [hv, ne_eq, not_false_eq_true, and_true, Stat.val, drop, h0, h4, if_false]
        simpa using ext_hi x
      · have hn : ¬ (i < 10 ∧ i ≠ v.val) := by omega
        rw [if_neg hn, ext_out _ i (by omega)]
        rfl
  have hval : ∀ x : Fin 9 → Bool,
      (r.1.getD C.output (Sum.inl false)).val (wiresFrom r.2 (ext x)) = F9 (drop x v) := by
    intro x
    rw [((hinv x).2 C.output).2, ← agrees C hok hs]
    rfl
  have hlen : r.2.length + 4 ≤ C.gates.length := by
    have h := elim_count 10 v.val C.gates (st, []) hok (by simp [st]; have := v.isLt; omega)
      ⟨false, by
        show st.getD v.val (Sum.inl false) = _
        rw [stget]; simp⟩
    have h' : r.2.length + (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length
        ≤ C.gates.length := by simpa using h
    omega
  rcases hst : r.1.getD C.output (Sum.inl false) with c | j
  · exfalso
    obtain ⟨x, y, hxy⟩ := hne
    have h1 := hval x
    have h2 := hval y
    rw [hst] at h1 h2
    exact hxy (h1.symm.trans h2)
  · refine ⟨⟨r.2, j⟩, ?_, hlen, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := elim_mok 10 C.gates (st, []) (by simpa using hvalid) hok (by simp) g hg
      exact ⟨by simpa using h1, h2⟩
    · intro x
      have := hval x
      rw [hst] at this
      exact this

def G (v : Fin 9) (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7),
    (3, 8), (5, 8), (6, 8)].any fun e => e.1 != v && e.2 != v && x e.1 && x e.2

theorem G_eq : ∀ v ∈ [(1 : Fin 9), 2, 3, 5, 8], ∀ x : Fin 9 → Bool, F9 (drop x v) = G v x := by
  decide +kernel

theorem nonconst : ∀ v : Fin 9, ∃ x y, F9 (drop x v) ≠ F9 (drop y v) := by
  intro v
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  revert v
  decide

theorem fin (C : Circuit) (hC : Monotone2 C)
    (hs : ∀ m ∈ all, C.eval (ext (bits m)) = decide (m ∈ yes)) (v : Fin 9)
    (hv : v ∈ [(1 : Fin 9), 2, 3, 5, 8])
    (hcount : 4 ≤ (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 4 ≤ C.size ∧
      ∀ x : Fin 9 → Bool, D.eval (ext x) = G v x := by
  obtain ⟨D, h1, h2, h3⟩ := main C hC hs v (by clear hcount; revert v; decide) (by clear hcount; revert v; decide)
    (nonconst v) hcount
  exact ⟨D, h1, h2, fun x => (h3 x).trans (G_eq v hv x)⟩

end PEqualNP.Outside.L_meta_2902

theorem PEqualNP.Outside.L_meta_2902 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ x4 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], (4 : ℕ) ≤ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x4 ∈ x6.inputs)) x1.gates).length → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size + (4 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9.1 != x4 && x9.2 != x4 && x8 x9.1 && x8 x9.2 := by
  intro C hC hs v hv hcount
  exact PEqualNP.Outside.L_meta_2902.fin C hC hs v hv hcount
