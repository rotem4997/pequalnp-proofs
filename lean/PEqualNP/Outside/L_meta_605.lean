import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_605_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

section
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

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
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

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

abbrev Stat : Type := Sum Bool ℕ

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
      simp [simpAnd] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; (subst hg; simp [Ok])
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with (_ | _) | j <;> rcases b with (_ | _) | k <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with (_ | _) | j <;> rcases b with (_ | _) | k <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)) ++ [Sum.inl b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, statValid m s) :
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Sum.inl b) (fun k : Fin n => (Sum.inr k.val : Stat)) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Sum.inl false) = Sum.inl b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Sum.inl false) = Sum.inr k.val := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      statValid (n + 0) ((statAt n i b).getD j (Sum.inl false)) ∧
      statVal (List.ofFn y) ((statAt n i b).getD j (Sum.inl false))
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show statValid (n + 0) ((statAt n i b).getD j (Sum.inl false)) ∧
      statVal (List.ofFn y) ((statAt n i b).getD j (Sum.inl false))
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Sum.inl false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Sum.inl b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Sum.inl false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Sum.inl c

theorem elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]

def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Sum.inl true else Sum.inr i

theorem startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Sum.inl false) =
      if i < m then (if i = h then Sum.inl true else Sum.inr i) else Sum.inl false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Sum.inl c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Sum.inl c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inl c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Sum.inr q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inr q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Sum.inl c) : ∃ c, (simplify op t ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Sum.inl c) :
    (simplify g.op t (g.inputs.map F)).2 = Sum.inr t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Sum.inl c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Sum.inr q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Sum.inl (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Sum.inl c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem rc_input {n : ℕ} {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {n : ℕ} {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

theorem isC_reader {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1

def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩

def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i
def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩

def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅

def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)

theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega

theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]

theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]

theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]

theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩

theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)

theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]

theorem vl_and_true {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = true) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]

theorem exch_startStats_length (m h : ℕ) : (startStats m h).length = m := by
  simp [startStats]

theorem exch_clean_take (N k : ℕ) (gs : List Gate) (hcl : CleanL N gs) :
    CleanL N (gs.take k) := by
  intro p g hp
  rw [List.getElem?_take] at hp
  by_cases hpk : p < k
  · simp [hpk] at hp; exact hcl p g hp
  · simp [hpk] at hp

theorem exch_const_reader (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g)
    (hop : g.op = GateOp.or ∨ g.op = GateOp.not) (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Sum.inl false) = Sum.inl true) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') true
  · intro h'; rcases hop with h2 | h2 <;> rw [h2] at h' <;> cases h'
  · intro _; rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst

theorem andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x

theorem vl_dfree {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {h : ℕ} (hD : DFree D gs h)
    (u u' : Fin N → Bool) (hu : ∀ i, i ∉ D → u i = u' i) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h (fun i hi =>
    hu i (fun hiD => hD i hiD hi))

theorem vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x

theorem front_suppsFrom_prefix {m : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin m)), ∃ T, suppsFrom gs L = L ++ T := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨T, hT⟩ := ih (L ++ [gateSupp L g])
    exact ⟨[gateSupp L g] ++ T, by
      show suppsFrom gs (L ++ [gateSupp L g]) = _
      rw [hT, List.append_assoc]⟩

theorem front_supp_input {m : ℕ} (gs : List Gate) (i : ℕ) (hi : i < m) :
    (suppsFrom gs (inputSupps m)).getD i ∅ = {(⟨i, hi⟩ : Fin m)} := by
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix gs (inputSupps m)
  rw [hT, List.getD_append _ _ _ _ (by simp [inputSupps]; exact hi)]
  simp [inputSupps, hi]

theorem front_supp_beyond {m : ℕ} (gs : List Gate) (w : ℕ) (hw : m + gs.length ≤ w) :
    (suppsFrom gs (inputSupps m)).getD w ∅ = ∅ :=
  List.getD_eq_default _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)

theorem front_supp_gate {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (i : Fin m) :
    i ∈ (suppsFrom gs (inputSupps m)).getD (m + p) ∅ ↔
      ∃ a ∈ g.inputs, i ∈ (suppsFrom gs (inputSupps m)).getD a ∅ := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  set L0 := suppsFrom pre (inputSupps m) with hL0
  have hl0 : L0.length = m + pre.length := by rw [hL0, length_suppsFrom]; simp [inputSupps]
  have e : suppsFrom (pre ++ g :: post) (inputSupps m)
      = suppsFrom post (L0 ++ [gateSupp L0 g]) := by
    rw [suppsFrom_append]; rfl
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix post (L0 ++ [gateSupp L0 g])
  have full : ∀ j, j < m + pre.length →
      (suppsFrom (pre ++ g :: post) (inputSupps m)).getD j ∅ = L0.getD j ∅ := by
    intro j hj
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (suppsFrom (pre ++ g :: post) (inputSupps m)).getD (m + pre.length) ∅
      = gateSupp L0 g := by
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]), ← hl0, getD_snoc_eq]
  rw [top, mem_gateSupp]
  constructor
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [full a (hlt a ha)]; exact hia⟩
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [← full a (hlt a ha)]; exact hia⟩

theorem vl_bin {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) :
    (g.op = GateOp.or → vl gs x (N + p) = (vl gs x l || vl gs x h)) ∧
    (g.op = GateOp.and → vl gs x (N + p) = (vl gs x l && vl gs x h)) := by
  rw [vl_gate gs hcl x p g hg]
  constructor <;> intro hop <;> rw [hop] <;>
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm, Bool.and_comm]


def HasSize2 (m : ℕ) (F1 F2 : (Fin m → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
    ∃ o1 o2 : ℕ, ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD o1 false = F1 x ∧
      (C.wires (List.ofFn x)).getD o2 false = F2 x

def HasClean2 (m : ℕ) (F1 F2 : (Fin m → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o1 o2 : ℕ), CleanL m gs ∧ gs.length ≤ s ∧
    ∀ x : Fin m → Bool, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x

theorem has2_of_clean (k : ℕ) (gs : List Gate) (o1 o2 : ℕ) (hcl : CleanL k gs) :
    HasSize2 k (fun y => vl gs y o1) (fun y => vl gs y o2) gs.length := by
  refine ⟨⟨gs, 0⟩, ?_, le_refl _, o1, o2, fun y => ⟨rfl, rfl⟩⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem renum_size2 {n m : ℕ} (π : Fin n → Fin m) (F1 F2 : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasSize2 n F1 F2 s) : HasSize2 m (fun x => F1 (x ∘ π)) (fun x => F2 (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, o1, o2, hev⟩ := hc
  refine ⟨⟨C.gates.map (relGate n m π), 0⟩, ?_, ?_, wmap n m π o1, wmap n m π o2, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [Circuit.size] using hsz
  · intro x
    dsimp only
    have hrel := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2
    exact ⟨by rw [← (hev (x ∘ π)).1]; exact hrel o1,
      by rw [← (hev (x ∘ π)).2]; exact hrel o2⟩

theorem clean_of2 (n : ℕ) (F1 F2 : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc1 : ∃ y y' : Fin n → Bool, F1 y ≠ F1 y')
    (hnc2 : ∃ y y' : Fin n → Bool, F2 y ≠ F2 y')
    (h : HasSize2 n F1 F2 s) : HasClean2 n F1 F2 s := by
  obtain ⟨C, ok, hsz, o1, o2, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval1 : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD o1 (Sum.inl false)) = F1 y := by
    intro y; rw [((hinv y).2 o1).2, ← (hev y).1]; rfl
  have hval2 : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD o2 (Sum.inl false)) = F2 y := by
    intro y; rw [((hinv y).2 o2).2, ← (hev y).2]; rfl
  cases hst1 : acc.1.getD o1 (Sum.inl false) with
  | inl c =>
    exfalso; obtain ⟨y, y', hne⟩ := hnc1; apply hne
    rw [← hval1 y, ← hval1 y', hst1]; rfl
  | inr j1 =>
    cases hst2 : acc.1.getD o2 (Sum.inl false) with
    | inl c =>
      exfalso; obtain ⟨y, y', hne⟩ := hnc2; apply hne
      rw [← hval2 y, ← hval2 y', hst2]; rfl
    | inr j2 =>
      refine ⟨acc.2, j1, j2, ?_, ?_, ?_⟩
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
      · have := elim_len n C.gates (idStats n, [])
        rw [← hacc] at this
        simp only [List.length_nil, zero_add] at this
        omega
      · intro y
        have h1 := hval1 y; rw [hst1] at h1
        have h2 := hval2 y; rw [hst2] at h2
        exact ⟨h1, h2⟩

def Drop2 {m : ℕ} (F1 F2 : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧
    HasSize2 m (fun x => F1 (Function.update x y b)) (fun x => F2 (Function.update x y b)) s'

theorem Drop2.mono {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool}
    {k s k' s' : ℕ} (h : Drop2 F1 F2 y b k s) (hk : k' ≤ k) (hs : s ≤ s') :
    Drop2 F1 F2 y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

def Pays2 {m : ℕ} (F1 F2 : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop2 F1 F2 y false 3 s ∧ Drop2 F1 F2 y true 3 s) ∨
  (Drop2 F1 F2 y false 4 s ∧ Drop2 F1 F2 y true 2 s) ∨
  (Drop2 F1 F2 y false 2 s ∧ Drop2 F1 F2 y true 4 s)

def Least2 (m : ℕ) (F1 F2 : (Fin m → Bool) → Bool) (gs : List Gate) (o1 o2 : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x) ∧
    ∀ (gs' : List Gate) (o1' o2' : ℕ), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o1' = F1 x ∧ vl gs' x o2' = F2 x) →
      gs.length ≤ gs'.length

theorem Least2.hcl {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) : CleanL m gs := L.1

theorem Least2.hev {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) :
    ∀ x : Fin m → Bool, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x := L.2.1

theorem Least2.hev1 {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) (x : Fin m → Bool) : vl gs x o1 = F1 x := (L.2.1 x).1

theorem Least2.hev2 {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) (x : Fin m → Bool) : vl gs x o2 = F2 x := (L.2.1 x).2

theorem Least2.hmin {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) :
    ∀ (gs' : List Gate) (o1' o2' : ℕ), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o1' = F1 x ∧ vl gs' x o2' = F2 x) →
      gs.length ≤ gs'.length := L.2.2

theorem least2_len {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs gs' : List Gate} {o1 o2 o1' o2' : ℕ}
    (L : Least2 m F1 F2 gs o1 o2) (L' : Least2 m F1 F2 gs' o1' o2') : gs.length = gs'.length :=
  le_antisymm (L.hmin gs' o1' o2' L'.hcl L'.hev) (L'.hmin gs o1 o2 L.hcl L.hev)

theorem least2_of {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs gs0 : List Gate} {o1 o2 o10 o20 : ℕ}
    (h0 : Least2 m F1 F2 gs0 o10 o20) (hcl : CleanL m gs)
    (hev : ∀ x, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x) (hle : gs.length ≤ gs0.length) :
    Least2 m F1 F2 gs o1 o2 :=
  ⟨hcl, hev, fun gs' o1' o2' hc he => le_trans hle (h0.hmin gs' o1' o2' hc he)⟩

theorem exists_least2 (m : ℕ) (F1 F2 : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y)
    (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y) (h : HasSize2 m F1 F2 s) :
    ∃ (gs : List Gate) (o1 o2 : ℕ), Least2 m F1 F2 gs o1 o2 ∧ gs.length ≤ s := by
  classical
  have hc := clean_of2 m F1 F2 s hnc1 hnc2 h
  have hex : ∃ t, HasClean2 m F1 F2 t := ⟨s, hc⟩
  obtain ⟨gs, o1, o2, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o1, o2, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o1' o2' hc' he'
  have := Nat.find_min' hex ⟨gs', o1', o2', hc', le_refl _, he'⟩
  omega

theorem drop_core2 (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o1 o2 : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, statValid (k + (elim k pre (idStats k, [])).2.length) S ∧
      statVal (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) S
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc1 : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o1 ≠ vl (pre ++ g :: post) y' o1)
    (hnc2 : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o2 ≠ vl (pre ++ g :: post) y' o2) :
    ∃ gs' o1' o2', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool,
        vl gs' y o1' = vl (pre ++ g :: post) y o1 ∧
        vl gs' y o2' = vl (pre ++ g :: post) y o2 := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show statValid (k + (elim k pre (idStats k, [])).2.length)
        (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)) ∧
      statVal (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  set acc3 := elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) with hacc3
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y)) acc3 := by
    intro y; rw [hfull]; exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k acc3.2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : acc3.2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : acc3.2.length ≤ (elim k pre (idStats k, [])).2.length + post.length :=
      elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval1 : ∀ y : Fin k → Bool,
      statVal (wiresFrom acc3.2 (List.ofFn y)) (acc3.1.getD o1 (Sum.inl false))
      = vl (pre ++ g :: post) y o1 := fun y => ((inv3 y).2 o1).2
  have hval2 : ∀ y : Fin k → Bool,
      statVal (wiresFrom acc3.2 (List.ofFn y)) (acc3.1.getD o2 (Sum.inl false))
      = vl (pre ++ g :: post) y o2 := fun y => ((inv3 y).2 o2).2
  cases hst1 : acc3.1.getD o1 (Sum.inl false) with
  | inl c =>
    exfalso; obtain ⟨y, y', hne⟩ := hnc1; apply hne
    rw [← hval1 y, ← hval1 y', hst1]; rfl
  | inr j1 =>
    cases hst2 : acc3.1.getD o2 (Sum.inl false) with
    | inl c =>
      exfalso; obtain ⟨y, y', hne⟩ := hnc2; apply hne
      rw [← hval2 y, ← hval2 y', hst2]; rfl
    | inr j2 =>
      refine ⟨acc3.2, j1, j2, hc3, hlen, fun y => ?_⟩
      have h1 := hval1 y; rw [hst1] at h1
      have h2 := hval2 y; rw [hst2] at h2
      exact ⟨h1, h2⟩

theorem drop_alias2 (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o1 o2 p j : ℕ)
    (hp : p < gs.length) (hj : j < k + p)
    (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc1 : ∃ y y' : Fin k → Bool, vl gs y o1 ≠ vl gs y' o1)
    (hnc2 : ∃ y y' : Fin k → Bool, vl gs y o2 ≠ vl gs y' o2) :
    ∃ gs' o1' o2', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o1' = vl gs y o1 ∧ vl gs' y o2' = vl gs y o2 := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core2 k pre g post hcl o1 o2 ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc1 hnc2
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const2 (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o1 o2 p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc1 : ∃ y y' : Fin k → Bool, vl gs y o1 ≠ vl gs y' o1)
    (hnc2 : ∃ y y' : Fin k → Bool, vl gs y o2 ≠ vl gs y' o2) :
    ∃ gs' o1' o2', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o1' = vl gs y o1 ∧ vl gs' y o2' = vl gs y o2 := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core2 k pre g post hcl o1 o2 (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc1 hnc2

theorem drop_dead2 (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o1 o2 p : ℕ) (hp : p < gs.length)
    (ho1 : o1 ≠ k + p) (ho2 : o2 ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc1 : ∃ y y' : Fin k → Bool, vl gs y o1 ≠ vl gs y' o1)
    (hnc2 : ∃ y y' : Fin k → Bool, vl gs y o2 ≠ vl gs y' o2) :
    ∃ gs' o1' o2', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o1' = vl gs y o1 ∧ vl gs' y o2' = vl gs y o2 := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr; simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp; rw [hget_p] at hr'; cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'; exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y; rw [vl_gate gs' hcl' y p g0 hget_p]; simp [g0, GateOp.eval]
  have hnc1' : ∃ y y' : Fin k → Bool, vl gs' y o1 ≠ vl gs' y' o1 := by
    obtain ⟨y, y', h⟩ := hnc1
    exact ⟨y, y', by rw [hagree y o1 ho1, hagree y' o1 ho1]; exact h⟩
  have hnc2' : ∃ y y' : Fin k → Bool, vl gs' y o2 ≠ vl gs' y' o2 := by
    obtain ⟨y, y', h⟩ := hnc2
    exact ⟨y, y', by rw [hagree y o2 ho2, hagree y' o2 ho2]; exact h⟩
  obtain ⟨gs'', o1'', o2'', hc'', hl'', he''⟩ :=
    drop_alias2 k gs' hcl' o1 o2 p 0 (by omega) hpos halias hnc1' hnc2'
  exact ⟨gs'', o1'', o2'', hc'', by omega, fun y =>
    ⟨by rw [(he'' y).1, hagree y o1 ho1], by rw [(he'' y).2, hagree y o2 ho2]⟩⟩

section
variable {m : ℕ} {F1 F2 : (Fin m → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}

theorem Least2.ncv1 (L : Least2 m F1 F2 gs o1 o2) (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y) :
    ∃ y y' : Fin m → Bool, vl gs y o1 ≠ vl gs y' o1 := by
  obtain ⟨x, y, h⟩ := hnc1; exact ⟨x, y, by rw [L.hev1, L.hev1]; exact h⟩

theorem Least2.ncv2 (L : Least2 m F1 F2 gs o1 o2) (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y) :
    ∃ y y' : Fin m → Bool, vl gs y o2 ≠ vl gs y' o2 := by
  obtain ⟨x, y, h⟩ := hnc2; exact ⟨x, y, by rw [L.hev2, L.hev2]; exact h⟩

theorem Least2.no_const (L : Least2 m F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y)
    (p : ℕ) (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o1', o2', hc', hl', he'⟩ :=
    drop_const2 m gs L.hcl o1 o2 p c hp hall (L.ncv1 hnc1) (L.ncv2 hnc2)
  have := L.hmin gs' o1' o2' hc' (fun x => ⟨by rw [(he' x).1]; exact L.hev1 x,
    by rw [(he' x).2]; exact L.hev2 x⟩)
  omega

theorem Least2.no_alias (L : Least2 m F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y)
    (p : ℕ) (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o1', o2', hc', hl', he'⟩ :=
    drop_alias2 m gs L.hcl o1 o2 p j hp hj hall (L.ncv1 hnc1) (L.ncv2 hnc2)
  have := L.hmin gs' o1' o2' hc' (fun x => ⟨by rw [(he' x).1]; exact L.hev1 x,
    by rw [(he' x).2]; exact L.hev2 x⟩)
  omega

theorem Least2.live (L : Least2 m F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y)
    (p : ℕ) (hp : p < gs.length) (ho1 : o1 ≠ m + p) (ho2 : o2 ≠ m + p) :
    ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq; omega
  obtain ⟨gs', o1', o2', hc', hl', he'⟩ :=
    drop_dead2 m gs L.hcl o1 o2 p hp ho1 ho2 hno' (L.ncv1 hnc1) (L.ncv2 hnc2)
  have := L.hmin gs' o1' o2' hc' (fun x => ⟨by rw [(he' x).1]; exact L.hev1 x,
    by rw [(he' x).2]; exact L.hev2 x⟩)
  omega

theorem Least2.no_tri (L : Least2 m F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin m → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin m → Bool, F2 x ≠ F2 y)
    (p q a : ℕ) (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq; simp at hpq; omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc1 hnc2 q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc1 hnc2 q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc1 hnc2 q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc1 hnc2 q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc1 hnc2 q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc1 hnc2 q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

theorem save2_gen (n : ℕ) (F1 F2 : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o1 o2 : ℕ)
    (hcl : CleanL (n + 1) gs)
    (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop2 F1 F2 i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]; exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst1 : stF n gs i b o1 with
  | inl c =>
    exfalso; obtain ⟨x, y, hxy⟩ := hnc1
    exact hxy ((restr_const hcl (fun u => (hev u).1) i b c hst1 x).trans
      (restr_const hcl (fun u => (hev u).1) i b c hst1 y).symm)
  | inr j1 =>
    cases hst2 : stF n gs i b o2 with
    | inl c =>
      exfalso; obtain ⟨x, y, hxy⟩ := hnc2
      exact hxy ((restr_const hcl (fun u => (hev u).2) i b c hst2 x).trans
        (restr_const hcl (fun u => (hev u).2) i b c hst2 y).symm)
    | inr j2 =>
      have hc : CleanL n (passG n gs i b) :=
        clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
          (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
      have h2 := renum_size2 (Fin.succAbove i) _ _ _ (has2_of_clean n (passG n gs i b) j1 j2 hc)
      have e1 : (fun x : Fin (n + 1) → Bool => F1 (Function.update x i b))
          = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j1 := by
        funext x; rw [upd_ins, ← (hev _).1, st_val_wire n gs hcl i b o1 j1 hst1]; rfl
      have e2 : (fun x : Fin (n + 1) → Bool => F2 (Function.update x i b))
          = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j2 := by
        funext x; rw [upd_ins, ← (hev _).2, st_val_wire n gs hcl i b o2 j2 hst2]; rfl
      refine ⟨(passG n gs i b).length, hcount, ?_⟩
      rw [e1, e2]; exact h2

section
variable {n : ℕ} {F1 F2 : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o1 o2 : ℕ}

theorem Least2.save (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop2 F1 F2 i b S.card gs.length :=
  save2_gen n F1 F2 gs o1 o2 L.hcl L.hev i b hnc1 hnc2 S hS

theorem Least2.save2 (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop2 F1 F2 i b 2 gs.length := by
  have := L.save i b hnc1 hnc2 {p1, p2} (by
    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least2.save3 (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop2 F1 F2 i b 3 gs.length := by
  have := L.save i b hnc1 hnc2 {p1, p2, p3} (by
    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least2.save4 (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop2 F1 F2 i b 4 gs.length := by
  have := L.save i b hnc1 hnc2 {p1, p2, p3, p4} (by
    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem Least2.next (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc1 : ∃ x y : Fin (n + 1) → Bool, F1 x ≠ F1 y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hfnc2 : ∃ x y : Fin (n + 1) → Bool, F2 x ≠ F2 y := by
    obtain ⟨x, y, h⟩ := hnc2; exact ⟨_, _, h⟩
  have ho1 : o1 ≠ n + 1 + p := by
    intro e; obtain ⟨c, hc'⟩ := hc; obtain ⟨x, y, hxy⟩ := hnc1; rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev1 i b c hc' x).trans
      (restr_const L.hcl L.hev1 i b c hc' y).symm)
  have ho2 : o2 ≠ n + 1 + p := by
    intro e; obtain ⟨c, hc'⟩ := hc; obtain ⟨x, y, hxy⟩ := hnc2; rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev2 i b c hc' x).trans
      (restr_const L.hcl L.hev2 i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc1 hfnc2 p hp ho1 ho2
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

theorem Least2.third (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop2 F1 F2 i b 3 gs.length := by
  have hfnc1 : ∃ x y : Fin (n + 1) → Bool, F1 x ≠ F1 y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hfnc2 : ∃ x y : Fin (n + 1) → Bool, F2 x ≠ F2 y := by
    obtain ⟨x, y, h⟩ := hnc2; exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc1 hnc2 p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl; exact L.no_tri hfnc1 hfnc2 p J i hp hq hJr
  exact L.save3 i b hnc1 hnc2 p q J hpq (by omega) (Ne.symm hJq)
    (rc_input b hp) (rc_input b hq) hJrc

theorem Least2.fourth (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1)) (b : Bool)
    (hnc1 : ∃ x y : Fin (n + 1) → Bool, F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∃ x y : Fin (n + 1) → Bool, F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop2 F1 F2 i b 4 gs.length := by
  have hfnc1 : ∃ x y : Fin (n + 1) → Bool, F1 x ≠ F1 y := by
    obtain ⟨x, y, h⟩ := hnc1; exact ⟨_, _, h⟩
  have hfnc2 : ∃ x y : Fin (n + 1) → Bool, F2 x ≠ F2 y := by
    obtain ⟨x, y, h⟩ := hnc2; exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc1 hnc2 p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc1 hnc2 q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl; exact L.no_tri hfnc1 hfnc2 p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl; exact L.no_tri hfnc1 hfnc2 q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ :=
      L.next i b hnc1 hnc2 J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc1 hnc2 p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega)
      (by omega) (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc1 hnc2 p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega)
      h12 (rc_input b hp) (rc_input b hq) h1rc h2rc

theorem Least2.two_readers (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1))
    (hnc1 : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) :
    Pays2 F1 F2 i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc1 false) (hnc2 false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc1 true) (hnc2 true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc1 false) (hnc2 false) q p (Ne.symm hpq) hq hp
        (cq false (Or.inl hnq)),
      L.third i true (hnc1 true) (hnc2 true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc1 false) (hnc2 false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc1 true) (hnc2 true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc1 false) (hnc2 false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc1 true) (hnc2 true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop2 F1 F2 i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc1 b) (hnc2 b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc1 b) (hnc2 b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

theorem Least2.not_two_readers (L : Least2 (n + 1) F1 F2 gs o1 o2) (i : Fin (n + 1))
    (hnc1 : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      F1 (Function.update x i b) ≠ F1 (Function.update y i b))
    (hnc2 : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      F2 (Function.update x i b) ≠ F2 (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) :
    Drop2 F1 F2 i false 3 gs.length ∧ Drop2 F1 F2 i true 3 gs.length := by
  have key : ∀ b, Drop2 F1 F2 i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc1 b) (hnc2 b) r p q (by omega) (by omega) hpq
      (rc_input b ⟨g, hr, hin⟩) (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

def DeepHyp' {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop :=
  (∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)) ∧
  (∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y') ∧
  (∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true) ∧
  (∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true) ∧
  (∃ z : Fin N → Bool, (∀ y ∈ D, z y = false) ∧ F z = false)

theorem DeepHyp'.nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b) := H.1

theorem DeepHyp'.nf {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y' := H.2.1

theorem DeepHyp'.win {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true := H.2.2.1

theorem DeepHyp'.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true := H.2.2.2.1

theorem DeepHyp'.zero {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∃ z : Fin N → Bool, (∀ y ∈ D, z y = false) ∧ F z = false := H.2.2.2.2

theorem deepHyp'_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp' F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩

theorem deepHyp'_zero_ex {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp' F D) : ∃ z : Fin N → Bool, F (zeroOn D z) = false := by
  obtain ⟨z, hz, hFz⟩ := hD.zero
  refine ⟨z, ?_⟩
  have e : zeroOn D z = z := by
    funext i
    unfold zeroOn
    split_ifs with hi
    · exact (hz i hi).symm
    · rfl
  rw [e]; exact hFz

theorem deepHyp'_dep {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp' F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  obtain ⟨z, h0⟩ := deepHyp'_zero_ex hD
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy z h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp

theorem deepHyp'_supp {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o : ℕ} (DH : DeepHyp' F D)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) {y : Fin N} (hy : y ∈ D) :
    y ∈ (suppsFrom gs (inputSupps N)).getD o ∅ := by
  obtain ⟨z, h0⟩ := deepHyp'_zero_ex DH
  obtain ⟨x', -, -, hF0, hF1⟩ := DH.win y hy z h0
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x' y true) x' gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  have e : F (Function.update x' y true) = F x' := by
    rw [← hev, ← hev]; exact hag
  rw [hF0, hF1] at e; cases e

theorem out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

def TailOK2 (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧
      ((∀ x : Fin N → Bool, vl gs x (N + j) = true → F1 x = true) ∨
       (∀ x : Fin N → Bool, vl gs x (N + j) = true → F2 x = true))))

def TailGE2 (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK2 N F1 F2 gs j

theorem TailGE2.zero (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) :
    TailGE2 N F1 F2 gs 0 :=
  ⟨Nat.zero_le _, fun _ h1 h2 => absurd h2 (by omega)⟩

theorem TailGE2.mono {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {gs : List Gate} {t t' : ℕ}
    (h : TailGE2 N F1 F2 gs t) (ht : t' ≤ t) : TailGE2 N F1 F2 gs t' :=
  ⟨le_trans ht h.1, fun j h1 h2 => h.2 j (by omega) h2⟩

theorem TailGE2.lt_of_not {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE2 N F1 F2 gs t) (hp : p < gs.length) (hn : ¬ TailOK2 N F1 F2 gs p) :
    p + t < gs.length := by
  by_contra hc; exact hn (h.2 p (by omega) hp)

theorem not_tailOK2_and {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {gs : List Gate} {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) (hop : g.op = GateOp.and) : ¬ TailOK2 N F1 F2 gs j := by
  rintro ⟨g0, hg0, h | ⟨h, _⟩⟩ <;>
  · rw [hg] at hg0; cases hg0; rw [hop] at h; cases h

theorem tailGE2_rdel_any (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE2 N F1 F2 gs t)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a)
    (hF : ∀ x, ¬ S x → F1 x = true ∧ F2 x = true) :
    TailGE2 N F1 F2 (rdel N p a gs) (if p + t < gs.length then t else t - 1) := by
  have hlen := rdel_length N p a gs hp
  have ht' : (if p + t < gs.length then t else t - 1) ≤ (rdel N p a gs).length := by
    have := ht.1; split_ifs <;> omega
  refine ⟨ht', ?_⟩
  intro j h1 h2
  by_cases hjp : j < p
  · have hj_in : gs.length ≤ j + t := by
      split_ifs at h1 <;> omega
    obtain ⟨g, hg, hop⟩ := ht.2 j hj_in (by omega)
    have hj' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hjp, hg]
    refine ⟨g, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, ?_⟩
      rcases hbel with h1' | h2'
      · left; intro x hx
        rw [rdel_prefix N p a gs hcl hp ha x (N + j) (by omega)] at hx
        exact h1' x hx
      · right; intro x hx
        rw [rdel_prefix N p a gs hcl hp ha x (N + j) (by omega)] at hx
        exact h2' x hx
  · have hj_in : gs.length ≤ (j + 1) + t := by
      split_ifs at h1 <;> omega
    obtain ⟨g, hg, hop⟩ := ht.2 (j + 1) hj_in (by omega)
    have hj' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, ?_⟩
      rcases hbel with h1' | h2'
      · left; intro x hx
        by_cases hSx : S x
        · apply h1' x
          rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
            rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega]
          exact hx
        · exact (hF x hSx).1
      · right; intro x hx
        by_cases hSx : S x
        · apply h2' x
          rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
            rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega]
          exact hx
        · exact (hF x hSx).2

theorem tailGE2_append (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs new : List Gate) (t : ℕ)
    (ht : TailGE2 N F1 F2 gs t)
    (hnew : ∀ i, i < new.length → TailOK2 N F1 F2 (gs ++ new) (gs.length + i)) :
    TailGE2 N F1 F2 (gs ++ new) (t + new.length) := by
  have h1 := ht.1
  refine ⟨by simp; omega, ?_⟩
  intro j hj1 hj2
  simp only [List.length_append] at hj1 hj2
  by_cases hlt : j < gs.length
  · obtain ⟨g, hg, hop⟩ := ht.2 j (by omega) hlt
    have hj' : (gs ++ new)[j]? = some g := by rw [List.getElem?_append_left hlt, hg]
    refine ⟨g, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, ?_⟩
      rcases hbel with hbel | hbel
      · left; intro x hx
        rw [vl_append_lt gs new x (N + j) (by omega)] at hx
        exact hbel x hx
      · right; intro x hx
        rw [vl_append_lt gs new x (N + j) (by omega)] at hx
        exact hbel x hx
  · have := hnew (j - gs.length) (by omega)
    rwa [show gs.length + (j - gs.length) = j by omega] at this

theorem vl_or_false {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = false) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]

def startStatsB (m h : ℕ) (b : Bool) : List Stat :=
  (List.range m).map fun i => if i = h then Sum.inl b else Sum.inr i

theorem startStatsB_length (m h : ℕ) (b : Bool) : (startStatsB m h b).length = m := by
  simp [startStatsB]

theorem startStatsB_getD (m h : ℕ) (b : Bool) (i : ℕ) :
    (startStatsB m h b).getD i (Sum.inl false) =
      if i < m then (if i = h then Sum.inl b else Sum.inr i) else Sum.inl false := by
  unfold startStatsB
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem inv_startB (n h : ℕ) (b : Bool) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = b) :
    Inv n y (wiresFrom pre y) (startStatsB (n + pre.length) h b, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStatsB, lw], ?_⟩
  intro i
  rw [startStatsB_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩

theorem exch_const_readerB (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g) (b : Bool)
    (hop : (b = false ∧ (g.op = GateOp.and ∨ g.op = GateOp.not)) ∨
           (b = true ∧ (g.op = GateOp.or ∨ g.op = GateOp.not)))
    (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Sum.inl false) = Sum.inl b) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') b
  · intro h'; rcases hop with ⟨rfl, _⟩ | ⟨rfl, h2 | h2⟩
    · rfl
    · rw [h2] at h'; cases h'
    · rw [h2] at h'; cases h'
  · intro h'; rcases hop with ⟨rfl, h2 | h2⟩ | ⟨rfl, _⟩
    · rw [h2] at h'; cases h'
    · rw [h2] at h'; cases h'
    · rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst

theorem clean_append_or {N : ℕ} {gs : List Gate} (hcl : CleanL N gs) {a b : ℕ}
    (ha : a < N + gs.length) (hb : b < N + gs.length) :
    CleanL N (gs ++ [⟨GateOp.or, [a, b]⟩]) := by
  intro p g hp
  by_cases hlt : p < gs.length
  · rw [List.getElem?_append_left hlt] at hp; exact hcl p g hp
  · rw [List.getElem?_append_right (by omega)] at hp
    have h0 : p - gs.length = 0 := by
      by_contra hne; simp [hne] at hp
    simp [h0] at hp; cases hp
    have hpl : p = gs.length := by omega
    rw [hpl]; exact Or.inr ⟨Or.inr rfl, a, b, ha, hb, rfl⟩

theorem clean_append_not {N : ℕ} {gs : List Gate} (hcl : CleanL N gs) {a : ℕ}
    (ha : a < N + gs.length) : CleanL N (gs ++ [⟨GateOp.not, [a]⟩]) := by
  intro p g hp
  by_cases hlt : p < gs.length
  · rw [List.getElem?_append_left hlt] at hp; exact hcl p g hp
  · rw [List.getElem?_append_right (by omega)] at hp
    have h0 : p - gs.length = 0 := by
      by_contra hne; simp [hne] at hp
    simp [h0] at hp; cases hp
    have hpl : p = gs.length := by omega
    rw [hpl]; exact Or.inl ⟨rfl, a, ha, rfl⟩

theorem vl_append_or {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (a b : ℕ)
    (ha : a < N + gs.length) (hb : b < N + gs.length) (x : Fin N → Bool) :
    vl (gs ++ [⟨GateOp.or, [a, b]⟩]) x (N + gs.length) = (vl gs x a || vl gs x b) := by
  have hcl' := clean_append_or hcl ha hb
  have hlast : (gs ++ [⟨GateOp.or, [a, b]⟩])[gs.length]? = some ⟨GateOp.or, [a, b]⟩ := by simp
  rw [vl_gate _ hcl' x gs.length _ hlast]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
    vl_append_lt gs _ x a ha, vl_append_lt gs _ x b hb]

theorem vl_append_not {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (a : ℕ)
    (ha : a < N + gs.length) (x : Fin N → Bool) :
    vl (gs ++ [⟨GateOp.not, [a]⟩]) x (N + gs.length) = !vl gs x a := by
  have hcl' := clean_append_not hcl ha
  have hlast : (gs ++ [⟨GateOp.not, [a]⟩])[gs.length]? = some ⟨GateOp.not, [a]⟩ := by simp
  rw [vl_gate _ hcl' x gs.length _ hlast]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
    vl_append_lt gs _ x a ha]

theorem append_or_out {N : ℕ} {F : (Fin N → Bool) → Bool} (gs : List Gate) (hcl : CleanL N gs)
    (r : ℕ) (hr : r < N + gs.length) (s : Stat) (hs : statValid (N + gs.length) s)
    (hnc : ∃ x y : Fin N → Bool, F x ≠ F y)
    (hcov : ∀ x : Fin N → Bool, vl gs x r = true → F x = true)
    (hval : ∀ x : Fin N → Bool, vl gs x r = false → statVal (wiresFrom gs (List.ofFn x)) s = F x) :
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ gs'.length ≤ gs.length + 1 ∧
      (∀ x : Fin N → Bool, ∀ w < N + gs.length, vl gs' x w = vl gs x w) ∧
      (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      (gs'.length = gs.length ∨
        ∃ j < N + gs.length, gs' = gs ++ [⟨GateOp.or, [j, r]⟩] ∧ o' = N + gs.length) := by
  cases s with
  | inl c =>
    cases c with
    | true =>
      exfalso; obtain ⟨x, y, hxy⟩ := hnc
      have key : ∀ z, F z = true := fun z => by
        cases hz : vl gs z r
        · rw [← hval z hz]; rfl
        · exact hcov z hz
      exact hxy (by rw [key x, key y])
    | false =>
      refine ⟨gs, r, hcl, by omega, fun _ _ _ => rfl, ?_, Or.inl rfl⟩
      intro x
      cases hx : vl gs x r
      · rw [← hval x hx]; rfl
      · rw [hcov x hx]
  | inr j =>
    have hj : j < N + gs.length := hs
    refine ⟨gs ++ [⟨GateOp.or, [j, r]⟩], N + gs.length, clean_append_or hcl hj hr,
      by simp, fun x w hw => vl_append_lt gs _ x w hw, ?_, Or.inr ⟨j, hj, rfl, rfl⟩⟩
    intro x
    rw [vl_append_or gs hcl j r hj hr x]
    cases hx : vl gs x r
    · rw [← hval x hx]; simp [statVal, vl]
    · rw [hcov x hx]; simp

theorem exch2_gen (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (o1 o2 h : ℕ)
    (b : Bool) (T : Finset ℕ) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o1 = F1 x ∧ vl gs x o2 = F2 x)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y)
    (hcov : ∀ x : Fin N → Bool, vl gs x h = !b → F1 x = true ∧ F2 x = true)
    (hT : ∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      ((b = false ∧ (g.op = GateOp.and ∨ g.op = GateOp.not)) ∨
       (b = true ∧ (g.op = GateOp.or ∨ g.op = GateOp.not))) ∧
      Reads gs r h ∧ Reads gs t (N + r)) :
    ∃ (gs' : List Gate) (o1' o2' : ℕ), CleanL N gs' ∧
      (∀ x : Fin N → Bool, vl gs' x o1' = F1 x ∧ vl gs' x o2' = F2 x) ∧
      gs'.length + T.card ≤ gs.length + (if b then 3 else 2) := by
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp
  have hnotT1 : ¬ ∀ x : Fin N → Bool, F1 x = true := by
    intro hT'; obtain ⟨x, y, hxy⟩ := hnc1; exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = b := by
    by_contra hne; push Not at hne
    exact hnotT1 fun x => (hcov x (by cases hb : b <;> have := hne x <;> cases hv : vl gs x h <;> simp_all)).1
  obtain ⟨x0, hx0⟩ := hex
  by_cases hTe : T = ∅
  · subst hTe
    refine ⟨gs, o1, o2, hcl, hev, ?_⟩
    simp only [Finset.card_empty, add_zero]
    omega
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hTe
  obtain ⟨t0, ht0⟩ := hTne
  have hhs : h < N + gs.length := by
    rcases hT t0 ht0 with hr | ⟨r, _, _, _, hrh, _⟩
    · have := reads_lt hcl hr; have := reads_len hr; omega
    · have := reads_lt hcl hrh; have := reads_len hrh; omega
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y; rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x; show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc0 : List Stat × List Gate := (startStatsB (N + pre.length) h b, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by rw [hacc0, startStatsB_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = b →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx; rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_startB N h b pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := elim_prefix N post acc0
  rw [← hacc] at htl
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_startB N h b pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre
  have hsth0 : acc0.1.getD h (Sum.inl false) = Sum.inl b := by
    rw [hacc0, startStatsB_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Sum.inl false) = Sum.inl b := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0
  have hTk : ∀ t ∈ T, k ≤ t := by
    intro t ht
    rcases hT t ht with hr | ⟨r, _, _, _, hrh, htr⟩
    · have := reads_lt hcl hr; omega
    · have := reads_lt hcl hrh; have := reads_lt hcl htr; omega
  have hcount := elim_count N acc0 post hnokpost (T.image fun t => t - k) (by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    have htk := hTk t ht
    have hpt : post[t - k]? = gs[t]? := by rw [hpost, List.getElem?_drop]; congr 1; omega
    rcases hT t ht with ⟨g, hg, hhg⟩ | ⟨r, g', hg', hop, hrh, ⟨g, hg, hrg⟩⟩
    · refine ⟨g, by rw [hpt]; exact hg, h, hhg, ?_, b, ?_⟩
      · have := (hcl t g hg).lt h hhg; omega
      · rw [← hacc]; exact hsth
    · refine ⟨g, by rw [hpt]; exact hg, N + r, hrg, ?_, ?_⟩
      · have := (hcl t g hg).lt _ hrg; omega
      · have hrk : k ≤ r := by have := reads_lt hcl hrh; omega
        obtain ⟨g'', hg'', hhg''⟩ := hrh
        rw [hg'] at hg''; cases hg''
        have hpr : post[r - k]? = some g' := by
          rw [hpost, List.getElem?_drop]
          rw [show k + (r - k) = r by omega]; exact hg'
        obtain ⟨c, hc⟩ := exch_const_readerB N post acc0 hnokpost h (r - k) g' hpr b hop hhg''
          (by omega) hsth0
        refine ⟨c, ?_⟩
        rw [show acc0.1.length + (r - k) = N + r by omega] at hc; exact hc)
  have hcard : (T.image fun t => t - k).card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b' hb' hab
    have := hTk a ha; have := hTk b' hb'
    simp only at hab; omega
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + T.card ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega
  have hwhA : ∀ x : Fin N → Bool, vl acc.2 x h = vl gs x h := by
    intro x; rw [hwh x]; unfold vl
    rw [htl, wiresFrom_append, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hval1 : ∀ x : Fin N → Bool, vl gs x h = b →
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o1 (Sum.inl false)) = F1 x := by
    intro x hx; rw [((hinv x hx).2 o1).2, ← (hev x).1]; rfl
  have hval2 : ∀ x : Fin N → Bool, vl gs x h = b →
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o2 (Sum.inl false)) = F2 x := by
    intro x hx; rw [((hinv x hx).2 o2).2, ← (hev x).2]; rfl
  have hv1 : statValid (N + acc.2.length) (acc.1.getD o1 (Sum.inl false)) := ((hinv x0 hx0).2 o1).1
  have hv2 : statValid (N + acc.2.length) (acc.1.getD o2 (Sum.inl false)) := ((hinv x0 hx0).2 o2).1
  have hbase : ∃ (gs0 : List Gate) (r : ℕ), CleanL N gs0 ∧
      gs0.length = acc.2.length + (if b then 1 else 0) ∧ r < N + gs0.length ∧
      (∀ (x : Fin N → Bool) (w : ℕ), w < N + acc.2.length → vl gs0 x w = vl acc.2 x w) ∧
      (∀ (x : Fin N → Bool), vl gs0 x r = (vl gs x h == !b)) := by
    cases hb : b
    · refine ⟨acc.2, h, hclacc, by simp, by omega, fun _ _ _ => rfl, fun x => ?_⟩
      rw [hwhA x]; simp
    · refine ⟨acc.2 ++ [⟨GateOp.not, [h]⟩], N + acc.2.length, clean_append_not hclacc (by omega),
        by simp, by simp, fun x w hw => vl_append_lt acc.2 _ x w hw, fun x => ?_⟩
      rw [vl_append_not acc.2 hclacc h (by omega) x, hwhA x]; simp
  obtain ⟨gs0, r, hcl0, hlen0, hr0, hag0, hrval⟩ := hbase
  have hst0 : ∀ (s : Stat) (x : Fin N → Bool), statValid (N + acc.2.length) s →
      statVal (wiresFrom gs0 (List.ofFn x)) s = statVal (wiresFrom acc.2 (List.ofFn x)) s := by
    intro s x hs
    cases s with
    | inl c => rfl
    | inr j => exact hag0 x j hs
  have hlen0_ge : acc.2.length ≤ gs0.length := by cases b <;> simp at hlen0 <;> omega
  obtain ⟨gs1, o1', hcl1, hlen1, hag1, hev1', hkind1⟩ :=
    append_or_out gs0 hcl0 r hr0 (acc.1.getD o1 (Sum.inl false))
      (statValid_mono (by omega) _ hv1) hnc1
      (fun x hx => (hcov x (by rw [hrval x] at hx; simpa using hx)).1)
      (fun x hx => by
        rw [hst0 _ x hv1]
        have hx' : vl gs x h = b := by
          have := hrval x; rw [hx] at this
          cases b <;> cases hv : vl gs x h <;> rw [hv] at this <;> simp at this
        exact hval1 x hx')
  have hge0 : gs0.length ≤ gs1.length := by
    rcases hkind1 with h | ⟨_, _, h, _⟩
    · omega
    · rw [h]; simp
  have hst1 : ∀ (s : Stat) (x : Fin N → Bool), statValid (N + acc.2.length) s →
      statVal (wiresFrom gs1 (List.ofFn x)) s = statVal (wiresFrom acc.2 (List.ofFn x)) s := by
    intro s x hs
    cases s with
    | inl c => rfl
    | inr j =>
      have hj : j < N + acc.2.length := hs
      show vl gs1 x j = vl acc.2 x j
      rw [hag1 x j (by omega), hag0 x j hj]
  obtain ⟨gs2, o2', hcl2, hlen2, hag2, hev2', _⟩ :=
    append_or_out gs1 hcl1 r (by omega) (acc.1.getD o2 (Sum.inl false))
      (statValid_mono (by omega) _ hv2) hnc2
      (fun x hx => (hcov x (by rw [hag1 x r hr0, hrval x] at hx; simpa using hx)).2)
      (fun x hx => by
        rw [hst1 _ x hv2]
        have hx' : vl gs x h = b := by
          have := hrval x; rw [hag1 x r hr0] at hx; rw [hx] at this
          cases b <;> cases hv : vl gs x h <;> rw [hv] at this <;> simp at this
        exact hval2 x hx')
  have ho1lt : o1' < N + gs1.length := out_lt_of_nc hev1' hnc1
  refine ⟨gs2, o1', o2', hcl2, fun x => ⟨by rw [hag2 x o1' ho1lt, hev1' x], hev2' x⟩, ?_⟩
  cases b <;> simp at hlen0 ⊢ <;> omega

theorem lift2_or (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (o1 o2 p r l q h : ℕ)
    (gp gr : Gate) (L : Least2 N F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y)
    (hpr : p ≠ r) (hgp : gs[p]? = some gp) (hopp : gp.op = GateOp.or)
    (hinp : gp.inputs = [l, h] ∨ gp.inputs = [h, l])
    (hgr : gs[r]? = some gr) (hopr : gr.op = GateOp.or)
    (hinr : gr.inputs = [q, h] ∨ gr.inputs = [h, q])
    (hbel : ∀ x : Fin N → Bool, vl gs x h = true → F1 x = true ∧ F2 x = true)
    (hnt : ¬ TailOK2 N F1 F2 gs p) :
    ∃ (gs' : List Gate) (o1' o2' : ℕ), Least2 N F1 F2 gs' o1' o2' ∧
      ∀ t, TailGE2 N F1 F2 gs t → TailGE2 N F1 F2 gs' (t + 1) := by
  have aux : ∀ (p1 p2 l1 l2 : ℕ) (g1 g2 : Gate), p1 < p2 →
      gs[p1]? = some g1 → g1.op = GateOp.or → (g1.inputs = [l1, h] ∨ g1.inputs = [h, l1]) →
      gs[p2]? = some g2 → g2.op = GateOp.or → (g2.inputs = [l2, h] ∨ g2.inputs = [h, l2]) →
      (¬ TailOK2 N F1 F2 gs p1 ∨ ¬ TailOK2 N F1 F2 gs p2) →
      ∃ (gs' : List Gate) (o1' o2' : ℕ), Least2 N F1 F2 gs' o1' o2' ∧
        ∀ t, TailGE2 N F1 F2 gs t → TailGE2 N F1 F2 gs' (t + 1) := by
    intro p1 p2 l1 l2 g1 g2 h12 hg1 hop1 hin1 hg2 hop2 hin2 hnt12
    have hcl := L.hcl
    have hp2 : p2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hl1 : l1 < N + p1 := (hcl p1 g1 hg1).lt l1 (by rcases hin1 with e | e <;> simp [e])
    have hh1 : h < N + p1 := (hcl p1 g1 hg1).lt h (by rcases hin1 with e | e <;> simp [e])
    have hl2 : l2 < N + p2 := (hcl p2 g2 hg2).lt l2 (by rcases hin2 with e | e <;> simp [e])
    have ho1 := out_lt_of_nc L.hev1 hnc1
    have ho2 := out_lt_of_nc L.hev2 hnc2
    have hcl1 := rdel_clean N p2 l2 gs hcl hp2 hl2
    have hlen1 := rdel_length N p2 l2 gs hp2
    have hp1' : p1 < (rdel N p2 l2 gs).length := by omega
    have hcl2 := rdel_clean N p1 l1 (rdel N p2 l2 gs) hcl1 hp1' hl1
    set gs2 := rdel N p1 l1 (rdel N p2 l2 gs) with hgs2
    have hlen2 : gs2.length + 1 = (rdel N p2 l2 gs).length := rdel_length N p1 l1 (rdel N p2 l2 gs) hp1'
    set o1' := rd N p1 l1 (rd N p2 l2 o1) with ho1def
    set o2' := rd N p1 l1 (rd N p2 l2 o2) with ho2def
    have ho1lt : o1' < N + gs2.length := by
      rw [ho1def]; unfold rd; split_ifs <;> omega
    have ho2lt : o2' < N + gs2.length := by
      rw [ho2def]; unfold rd; split_ifs <;> omega
    have hh2 : h < N + gs2.length := by omega
    have hS2 : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p2) = vl gs x l2 :=
      fun x hx => vl_or_false gs hcl x p2 l2 h g2 hg2 hop2 hin2 hx
    have hS1 : ∀ x : Fin N → Bool, vl gs x h = false →
        vl (rdel N p2 l2 gs) x (N + p1) = vl (rdel N p2 l2 gs) x l1 := by
      intro x hx
      rw [rdel_prefix N p2 l2 gs hcl hp2 hl2 x (N + p1) (by omega),
        rdel_prefix N p2 l2 gs hcl hp2 hl2 x l1 (by omega)]
      exact vl_or_false gs hcl x p1 l1 h g1 hg1 hop1 hin1 hx
    have hgood : ∀ x : Fin N → Bool, vl gs x h = false →
        vl gs2 x o1' = F1 x ∧ vl gs2 x o2' = F2 x := by
      intro x hx
      exact ⟨by rw [hgs2, ho1def, rdel_all N p1 l1 _ hcl1 hp1' hl1 x (hS1 x hx),
          rdel_all N p2 l2 gs hcl hp2 hl2 x (hS2 x hx), L.hev1 x],
        by rw [hgs2, ho2def, rdel_all N p1 l1 _ hcl1 hp1' hl1 x (hS1 x hx),
          rdel_all N p2 l2 gs hcl hp2 hl2 x (hS2 x hx), L.hev2 x]⟩
    have hh_eq : ∀ x : Fin N → Bool, vl gs2 x h = vl gs x h := by
      intro x
      rw [hgs2, rdel_prefix N p1 l1 _ hcl1 hp1' hl1 x h hh1,
        rdel_prefix N p2 l2 gs hcl hp2 hl2 x h (by omega)]
    set gs3 := gs2 ++ [⟨GateOp.or, [o1', h]⟩] with hgs3
    have hcl3 : CleanL N gs3 := clean_append_or hcl2 ho1lt hh2
    have hlen3 : gs3.length = gs2.length + 1 := by simp [hgs3]
    set gs4 := gs3 ++ [⟨GateOp.or, [o2', h]⟩] with hgs4
    have hcl4 : CleanL N gs4 := clean_append_or hcl3 (by omega) (by omega)
    have hv1 : ∀ x : Fin N → Bool, vl gs3 x (N + gs2.length) = F1 x := by
      intro x; rw [hgs3, vl_append_or gs2 hcl2 o1' h ho1lt hh2 x, hh_eq x]
      cases hx : vl gs x h
      · rw [(hgood x hx).1]; simp
      · rw [(hbel x hx).1]; simp
    have hv2 : ∀ x : Fin N → Bool, vl gs4 x (N + gs3.length) = F2 x := by
      intro x; rw [hgs4, vl_append_or gs3 hcl3 o2' h (by simp [hgs3]; omega) (by simp [hgs3]; omega) x,
        hgs3, vl_append_lt gs2 _ x o2' ho2lt, vl_append_lt gs2 _ x h hh2, hh_eq x]
      cases hx : vl gs x h
      · rw [(hgood x hx).2]; simp
      · rw [(hbel x hx).2]; simp
    have hv : ∀ x : Fin N → Bool, vl gs4 x (N + gs2.length) = F1 x ∧
        vl gs4 x (N + gs3.length) = F2 x := by
      intro x
      refine ⟨?_, hv2 x⟩
      rw [hgs4, vl_append_lt gs3 _ x (N + gs2.length) (by simp [hgs3]), hv1 x]
    have hlen4 : gs4.length = gs.length := by simp [hgs4, hgs3]; omega
    refine ⟨gs4, N + gs2.length, N + gs3.length, least2_of L hcl4 hv (le_of_eq hlen4), ?_⟩
    intro t ht
    have ht1 := tailGE2_rdel_any N F1 F2 gs p2 l2 t (fun x => vl gs x h = false) hcl hp2 hl2 ht
      hS2 (fun x hx => hbel x (by simpa using hx))
    set t1 := if p2 + t < gs.length then t else t - 1 with ht1def
    have ht2 := tailGE2_rdel_any N F1 F2 (rdel N p2 l2 gs) p1 l1 t1 (fun x => vl gs x h = false)
      hcl1 hp1' hl1 ht1 hS1 (fun x hx => hbel x (by simpa using hx))
    set t2 := if p1 + t1 < (rdel N p2 l2 gs).length then t1 else t1 - 1 with ht2def
    have ht2_ge : t - 1 ≤ t2 := by
      rcases hnt12 with hn1 | hn2
      · have h1 := ht.lt_of_not (by omega) hn1
        have hcond : p1 + t1 < (rdel N p2 l2 gs).length := by
          unfold t1; split_ifs <;> omega
        rw [ht2def, ite_eq_left_iff.2 (fun hc => absurd hcond hc)]; unfold t1; split_ifs <;> omega
      · have h2 := ht.lt_of_not hp2 hn2
        have ht1eq : t1 = t := by rw [ht1def, ite_eq_left_iff.2 (fun hc => absurd h2 hc)]
        rw [ht2def, ht1eq]; split_ifs <;> omega
    have hge_app : TailGE2 N F1 F2 gs4 (t2 + 2) := by
      have e : gs4 = gs2 ++ [⟨GateOp.or, [o1', h]⟩, ⟨GateOp.or, [o2', h]⟩] := by
        simp [hgs4, hgs3]
      rw [e]
      refine tailGE2_append N F1 F2 gs2 [⟨GateOp.or, [o1', h]⟩, ⟨GateOp.or, [o2', h]⟩] t2 ht2 ?_
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · refine ⟨⟨GateOp.or, [o1', h]⟩, by simp, Or.inr ⟨rfl, Or.inl fun x hx => ?_⟩⟩
        rw [← e] at hx; rw [← (hv x).1]; simpa using hx
      · refine ⟨⟨GateOp.or, [o2', h]⟩, by simp, Or.inr ⟨rfl, Or.inr fun x hx => ?_⟩⟩
        rw [← e] at hx
        have hlen3 : gs3.length = gs2.length + 1 := by simp [hgs3]
        rw [← (hv x).2, hlen3]; exact hx
    exact hge_app.mono (by omega)
  rcases lt_or_gt_of_ne hpr with hlt | hlt
  · exact aux p r l q gp gr hlt hgp hopp hinp hgr hopr hinr (Or.inl hnt)
  · exact aux r p q l gr gp hlt hgr hopr hinr hgp hopp hinp (Or.inr hnt)

theorem xmove3_and (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (o1 o2 : ℕ)
    (p1 p2 p3 l1 l2 l3 h : ℕ) (g1 g2 g3 : Gate) (L : Least2 N F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y)
    (h12 : p1 < p2) (h23 : p2 < p3)
    (hg1 : gs[p1]? = some g1) (hop1 : g1.op = GateOp.and) (hin1 : g1.inputs = [l1, h] ∨ g1.inputs = [h, l1])
    (hg2 : gs[p2]? = some g2) (hop2 : g2.op = GateOp.and) (hin2 : g2.inputs = [l2, h] ∨ g2.inputs = [h, l2])
    (hg3 : gs[p3]? = some g3) (hop3 : g3.op = GateOp.and) (hin3 : g3.inputs = [l3, h] ∨ g3.inputs = [h, l3])
    (hbel : ∀ x : Fin N → Bool, vl gs x h = false → F1 x = true ∧ F2 x = true) :
    ∃ (gs' : List Gate) (o1' o2' : ℕ), Least2 N F1 F2 gs' o1' o2' ∧
      ∀ t, TailGE2 N F1 F2 gs t → TailGE2 N F1 F2 gs' (t + 3) := by
  have hcl := L.hcl
  have hp3 : p3 < gs.length := (List.getElem?_eq_some_iff.1 hg3).1
  have hl1 : l1 < N + p1 := (hcl p1 g1 hg1).lt l1 (by rcases hin1 with e | e <;> simp [e])
  have hh1 : h < N + p1 := (hcl p1 g1 hg1).lt h (by rcases hin1 with e | e <;> simp [e])
  have hl2 : l2 < N + p2 := (hcl p2 g2 hg2).lt l2 (by rcases hin2 with e | e <;> simp [e])
  have hl3 : l3 < N + p3 := (hcl p3 g3 hg3).lt l3 (by rcases hin3 with e | e <;> simp [e])
  have ho1 := out_lt_of_nc L.hev1 hnc1
  have ho2 := out_lt_of_nc L.hev2 hnc2
  set gsA := rdel N p3 l3 gs with hgsA
  have hclA := rdel_clean N p3 l3 gs hcl hp3 hl3
  have hlenA : gsA.length + 1 = gs.length := rdel_length N p3 l3 gs hp3
  have hp2A : p2 < gsA.length := by omega
  set gsB := rdel N p2 l2 gsA with hgsB
  have hclB := rdel_clean N p2 l2 gsA hclA hp2A hl2
  have hlenB : gsB.length + 1 = gsA.length := rdel_length N p2 l2 gsA hp2A
  have hp1B : p1 < gsB.length := by omega
  set gsC := rdel N p1 l1 gsB with hgsC
  have hclC := rdel_clean N p1 l1 gsB hclB hp1B hl1
  have hlenC : gsC.length + 1 = gsB.length := rdel_length N p1 l1 gsB hp1B
  set o1' := rd N p1 l1 (rd N p2 l2 (rd N p3 l3 o1)) with ho1def
  set o2' := rd N p1 l1 (rd N p2 l2 (rd N p3 l3 o2)) with ho2def
  have hrd_lt : ∀ w, w < N + gs.length → rd N p1 l1 (rd N p2 l2 (rd N p3 l3 w)) < N + gsC.length := by
    intro w hw; unfold rd; split_ifs <;> omega
  have ho1lt : o1' < N + gsC.length := hrd_lt o1 ho1
  have ho2lt : o2' < N + gsC.length := hrd_lt o2 ho2
  have hhC : h < N + gsC.length := by omega
  have hS3 : ∀ x : Fin N → Bool, vl gs x h = true → vl gs x (N + p3) = vl gs x l3 :=
    fun x hx => vl_and_true gs hcl x p3 l3 h g3 hg3 hop3 hin3 hx
  have hS2 : ∀ x : Fin N → Bool, vl gs x h = true → vl gsA x (N + p2) = vl gsA x l2 := by
    intro x hx
    rw [hgsA, rdel_prefix N p3 l3 gs hcl hp3 hl3 x (N + p2) (by omega),
      rdel_prefix N p3 l3 gs hcl hp3 hl3 x l2 (by omega)]
    exact vl_and_true gs hcl x p2 l2 h g2 hg2 hop2 hin2 hx
  have hS1 : ∀ x : Fin N → Bool, vl gs x h = true → vl gsB x (N + p1) = vl gsB x l1 := by
    intro x hx
    rw [hgsB, rdel_prefix N p2 l2 gsA hclA hp2A hl2 x (N + p1) (by omega),
      rdel_prefix N p2 l2 gsA hclA hp2A hl2 x l1 (by omega),
      hgsA, rdel_prefix N p3 l3 gs hcl hp3 hl3 x (N + p1) (by omega),
      rdel_prefix N p3 l3 gs hcl hp3 hl3 x l1 (by omega)]
    exact vl_and_true gs hcl x p1 l1 h g1 hg1 hop1 hin1 hx
  have hgood : ∀ x : Fin N → Bool, vl gs x h = true →
      vl gsC x o1' = F1 x ∧ vl gsC x o2' = F2 x := by
    intro x hx
    exact ⟨by rw [hgsC, ho1def, rdel_all N p1 l1 gsB hclB hp1B hl1 x (hS1 x hx),
        rdel_all N p2 l2 gsA hclA hp2A hl2 x (hS2 x hx),
        rdel_all N p3 l3 gs hcl hp3 hl3 x (hS3 x hx), L.hev1 x],
      by rw [hgsC, ho2def, rdel_all N p1 l1 gsB hclB hp1B hl1 x (hS1 x hx),
        rdel_all N p2 l2 gsA hclA hp2A hl2 x (hS2 x hx),
        rdel_all N p3 l3 gs hcl hp3 hl3 x (hS3 x hx), L.hev2 x]⟩
  have hh_eq : ∀ x : Fin N → Bool, vl gsC x h = vl gs x h := by
    intro x
    rw [hgsC, rdel_prefix N p1 l1 gsB hclB hp1B hl1 x h hh1,
      hgsB, rdel_prefix N p2 l2 gsA hclA hp2A hl2 x h (by omega),
      hgsA, rdel_prefix N p3 l3 gs hcl hp3 hl3 x h (by omega)]
  set gsD := gsC ++ [⟨GateOp.not, [h]⟩] with hgsD
  have hclD : CleanL N gsD := clean_append_not hclC hhC
  have hlenD : gsD.length = gsC.length + 1 := by simp [hgsD]
  set gsE := gsD ++ [⟨GateOp.or, [o1', N + gsC.length]⟩] with hgsE
  have hclE : CleanL N gsE := clean_append_or hclD (by omega) (by omega)
  have hlenE : gsE.length = gsD.length + 1 := by simp [hgsE]
  set gsF := gsE ++ [⟨GateOp.or, [o2', N + gsC.length]⟩] with hgsF
  have hclF : CleanL N gsF := clean_append_or hclE (by omega) (by omega)
  have hv0 : ∀ x : Fin N → Bool, vl gsD x (N + gsC.length) = !vl gs x h := by
    intro x; rw [hgsD, vl_append_not gsC hclC h hhC x, hh_eq x]
  have hv1 : ∀ x : Fin N → Bool, vl gsE x (N + gsD.length) = F1 x := by
    intro x
    rw [hgsE, vl_append_or gsD hclD o1' (N + gsC.length) (by simp [hgsD]; omega) (by simp [hgsD]) x,
      hv0 x, hgsD, vl_append_lt gsC _ x o1' ho1lt]
    cases hx : vl gs x h
    · rw [(hbel x hx).1]; simp
    · rw [(hgood x hx).1]; simp
  have hv2 : ∀ x : Fin N → Bool, vl gsF x (N + gsE.length) = F2 x := by
    intro x
    rw [hgsF, vl_append_or gsE hclE o2' (N + gsC.length) (by simp [hgsE, hgsD]; omega) (by simp [hgsE, hgsD]) x,
      hgsE, vl_append_lt gsD _ x o2' (by simp [hgsD]; omega),
      vl_append_lt gsD _ x (N + gsC.length) (by simp [hgsD]), hv0 x,
      hgsD, vl_append_lt gsC _ x o2' ho2lt]
    cases hx : vl gs x h
    · rw [(hbel x hx).2]; simp
    · rw [(hgood x hx).2]; simp
  have hv : ∀ x : Fin N → Bool, vl gsF x (N + gsD.length) = F1 x ∧
      vl gsF x (N + gsE.length) = F2 x := by
    intro x
    refine ⟨?_, hv2 x⟩
    rw [hgsF, vl_append_lt gsE _ x (N + gsD.length) (by simp [hgsE]), hv1 x]
  have hlenF : gsF.length = gs.length := by simp [hgsF, hgsE, hgsD]; omega
  refine ⟨gsF, N + gsD.length, N + gsE.length, least2_of L hclF hv (le_of_eq hlenF), ?_⟩
  intro t ht
  have hp3t := ht.lt_of_not hp3 (not_tailOK2_and hg3 hop3)
  have htA : TailGE2 N F1 F2 gsA t := by
    have := tailGE2_rdel_any N F1 F2 gs p3 l3 t (fun x => vl gs x h = true) hcl hp3 hl3 ht
      hS3 (fun x hx => hbel x (by simpa using hx))
    rwa [ite_eq_left_iff.2 (fun hc => absurd hp3t hc)] at this
  have htB : TailGE2 N F1 F2 gsB t := by
    have := tailGE2_rdel_any N F1 F2 gsA p2 l2 t (fun x => vl gs x h = true) hclA hp2A hl2 htA
      hS2 (fun x hx => hbel x (by simpa using hx))
    rwa [ite_eq_left_iff.2 (fun hc => absurd (by omega : p2 + t < gsA.length) hc)] at this
  have htC : TailGE2 N F1 F2 gsC t := by
    have := tailGE2_rdel_any N F1 F2 gsB p1 l1 t (fun x => vl gs x h = true) hclB hp1B hl1 htB
      hS1 (fun x hx => hbel x (by simpa using hx))
    rwa [ite_eq_left_iff.2 (fun hc => absurd (by omega : p1 + t < gsB.length) hc)] at this
  have e : gsF = gsC ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [o1', N + gsC.length]⟩,
      ⟨GateOp.or, [o2', N + gsC.length]⟩] := by simp [hgsF, hgsE, hgsD]
  rw [e]
  refine tailGE2_append N F1 F2 gsC _ t htC ?_
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact ⟨⟨GateOp.not, [h]⟩, by simp, Or.inl rfl⟩
  · refine ⟨⟨GateOp.or, [o1', N + gsC.length]⟩, by simp, Or.inr ⟨rfl, Or.inl fun x hx => ?_⟩⟩
    rw [← e] at hx
    have hlD : gsD.length = gsC.length + 1 := by simp [hgsD]
    rw [← (hv x).1, hlD]; exact hx
  · refine ⟨⟨GateOp.or, [o2', N + gsC.length]⟩, by simp, Or.inr ⟨rfl, Or.inr fun x hx => ?_⟩⟩
    rw [← e] at hx
    have hlE : gsE.length = gsC.length + 2 := by simp [hgsE, hgsD]
    rw [← (hv x).2, hlE]; exact hx

theorem simplify_op_eq (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (hg : (simplify op m ins).1 = some g) : g.op = op := by
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg; subst hg; rfl
  · simp at hg
  · simp at hg

theorem simplify_val_eq (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (hg : (simplify op m ins).1 = some g) : (simplify op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; simp [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; simp [simplify, simpOr]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg; simp [simplify, simpNot]
  · simp at hg
  · simp at hg

theorem elim_tail_ok (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (S : (Fin N → Bool) → Prop)
    (hF : ∀ x, ¬ S x → F1 x = true ∧ F2 x = true) (tail : List Gate) :
    ∀ (W : (Fin N → Bool) → List Bool) (acc : List Stat × List Gate),
    (∀ g ∈ tail, Ok g) →
    (∀ x, S x → Inv N (List.ofFn x) (W x) acc) →
    (∀ (q : ℕ) (g : Gate), tail[q]? = some g →
      g.op = GateOp.not ∨ (g.op = GateOp.or ∧
        ((∀ x, S x → (wiresFrom tail (W x)).getD ((W x).length + q) false = true → F1 x = true) ∨
         (∀ x, S x → (wiresFrom tail (W x)).getD ((W x).length + q) false = true → F2 x = true)))) →
    ∀ j, acc.2.length ≤ j → j < (elim N tail acc).2.length →
      TailOK2 N F1 F2 (elim N tail acc).2 j := by
  induction tail with
  | nil => intro W acc _ _ _ j hj1 hj2; simp [elim] at hj2; omega
  | cons g tail ih =>
    intro W acc hok hinv htok j hj1 hj2
    set acc1 := elimStep N acc g with hacc1
    have hstep : elim N (g :: tail) acc = elim N tail acc1 := rfl
    rw [hstep] at hj2 ⊢
    set W1 : (Fin N → Bool) → List Bool := fun x =>
      W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)] with hW1
    have hinv1 : ∀ x, S x → Inv N (List.ofFn x) (W1 x) acc1 := fun x hx =>
      inv_elim N (List.ofFn x) (by simp) [g] (W x) acc
        (fun g' hg' => by simp at hg'; subst hg'; exact hok g' List.mem_cons_self) (hinv x hx)
    have htok_tail : ∀ (q : ℕ) (g' : Gate), tail[q]? = some g' →
        g'.op = GateOp.not ∨ (g'.op = GateOp.or ∧
          ((∀ x, S x → (wiresFrom tail (W1 x)).getD ((W1 x).length + q) false = true → F1 x = true) ∨
           (∀ x, S x → (wiresFrom tail (W1 x)).getD ((W1 x).length + q) false = true → F2 x = true))) := by
      intro q g' hq
      have hq' : (g :: tail)[q + 1]? = some g' := hq
      rcases htok (q + 1) g' hq' with h | ⟨h, h1 | h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, Or.inl fun x hx hv => h1 x hx ?_⟩
        have e1 : (W1 x).length + q = (W x).length + (q + 1) := by simp [hW1]; omega
        rw [← e1]; exact hv
      · refine Or.inr ⟨h, Or.inr fun x hx hv => h2 x hx ?_⟩
        have e1 : (W1 x).length + q = (W x).length + (q + 1) := by simp [hW1]; omega
        rw [← e1]; exact hv
    by_cases hj1' : acc1.2.length ≤ j
    · exact ih W1 acc1 (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv1 htok_tail j hj1' hj2
    · set r := simplify g.op (N + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
      cases hr1 : r.1 with
      | none =>
        have : acc1.2.length = acc.2.length := by show (acc.2 ++ r.1.toList).length = _; rw [hr1]; simp
        omega
      | some gnew =>
        have hlen1 : acc1.2.length = acc.2.length + 1 := by
          show (acc.2 ++ r.1.toList).length = _; rw [hr1]; simp
        have hjeq : j = acc.2.length := by omega
        subst hjeq
        obtain ⟨tl, htl⟩ := elim_prefix N tail acc1
        have hget : (elim N tail acc1).2[acc.2.length]? = some gnew := by
          rw [htl, List.getElem?_append_left (by omega)]
          show (acc.2 ++ r.1.toList)[acc.2.length]? = some gnew
          rw [hr1]; simp
        have hop_eq : gnew.op = g.op := simplify_op_eq _ _ _ gnew hr1
        have hval_eq : r.2 = Sum.inr (N + acc.2.length) := simplify_val_eq _ _ _ gnew hr1
        refine ⟨gnew, hget, ?_⟩
        rcases htok 0 g rfl with h | ⟨h, h1 | h2⟩
        · exact Or.inl (hop_eq.trans h)
        · refine Or.inr ⟨hop_eq.trans h, Or.inl fun x hv => ?_⟩
          by_cases hx : S x
          · apply h1 x hx
            have hinv_x := hinv1 x hx
            have he0 := (hinv_x.2 acc.1.length).2
            have hlW : acc.1.length = (W x).length := (hinv x hx).1
            have hstat : acc1.1.getD acc.1.length (Sum.inl false) = Sum.inr (N + acc.2.length) := by
              show (acc.1 ++ [r.2]).getD acc.1.length (Sum.inl false) = _; rw [getD_snoc_eq, hval_eq]
            rw [hstat] at he0
            have hW1g : (W1 x).getD (W x).length false =
                (wiresFrom (g :: tail) (W x)).getD ((W x).length + 0) false := by
              rw [Nat.add_zero]
              show (W1 x).getD (W x).length false = (wiresFrom tail (W1 x)).getD (W x).length false
              rw [getD_wiresFrom tail (W1 x) (W x).length (by simp [hW1])]
            rw [← hW1g, ← hlW, ← he0]
            show (wiresFrom acc1.2 (List.ofFn x)).getD (N + acc.2.length) false = true
            rw [← hv]; unfold vl; rw [htl, wiresFrom_append, getD_wiresFrom tl _ _ (by
              rw [length_wiresFrom]; simp [hlen1])]
          · exact (hF x hx).1
        · refine Or.inr ⟨hop_eq.trans h, Or.inr fun x hv => ?_⟩
          by_cases hx : S x
          · apply h2 x hx
            have hinv_x := hinv1 x hx
            have he0 := (hinv_x.2 acc.1.length).2
            have hlW : acc.1.length = (W x).length := (hinv x hx).1
            have hstat : acc1.1.getD acc.1.length (Sum.inl false) = Sum.inr (N + acc.2.length) := by
              show (acc.1 ++ [r.2]).getD acc.1.length (Sum.inl false) = _; rw [getD_snoc_eq, hval_eq]
            rw [hstat] at he0
            have hW1g : (W1 x).getD (W x).length false =
                (wiresFrom (g :: tail) (W x)).getD ((W x).length + 0) false := by
              rw [Nat.add_zero]
              show (W1 x).getD (W x).length false = (wiresFrom tail (W1 x)).getD (W x).length false
              rw [getD_wiresFrom tail (W1 x) (W x).length (by simp [hW1])]
            rw [← hW1g, ← hlW, ← he0]
            show (wiresFrom acc1.2 (List.ofFn x)).getD (N + acc.2.length) false = true
            rw [← hv]; unfold vl; rw [htl, wiresFrom_append, getD_wiresFrom tl _ _ (by
              rw [length_wiresFrom]; simp [hlen1])]
          · exact (hF x hx).2

theorem exch2_and_tail (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs : List Gate) (o1 o2 h p r t : ℕ)
    (gp gr : Gate) (L : Least2 N F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y) (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y)
    (hcov : ∀ x : Fin N → Bool, vl gs x h = false → F1 x = true ∧ F2 x = true)
    (hpr : p ≠ r) (hpt : p ≠ t) (hrt : r ≠ t)
    (hgp : gs[p]? = some gp) (hopp : gp.op = GateOp.and) (hph : h ∈ gp.inputs)
    (hgr : gs[r]? = some gr) (hopr : gr.op = GateOp.or ∨ gr.op = GateOp.not) (hrh : h ∈ gr.inputs)
    (htr : Reads gs t (N + r)) :
    ∃ (gs' : List Gate) (o1' o2' : ℕ), Least2 N F1 F2 gs' o1' o2' ∧
      ∀ M, TailGE2 N F1 F2 gs M → TailGE2 N F1 F2 gs' (M + 1) := by
  have hcl := L.hcl
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp
  have hnotT1 : ¬ ∀ x : Fin N → Bool, F1 x = true := by
    intro hT'; obtain ⟨x, y, hxy⟩ := hnc1; exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = true := by
    by_contra hne; push Not at hne
    exact hnotT1 fun x => (hcov x (by simpa using hne x)).1
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < N + gs.length := by
    have := (hcl p gp hgp).lt h hph; have := (List.getElem?_eq_some_iff.1 hgp).1; omega
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y; rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x; show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc0 : List Stat × List Gate := (startStatsB (N + pre.length) h true, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by rw [hacc0, startStatsB_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = true →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx; rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_startB N h true pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := elim_prefix N post acc0
  rw [← hacc] at htl
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_startB N h true pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre
  have hsth0 : acc0.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc0, startStatsB_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Sum.inl false) = Sum.inl true := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0
  have hpk : k ≤ p := by have := (hcl p gp hgp).lt h hph; omega
  have hrk : k ≤ r := by have := (hcl r gr hgr).lt h hrh; omega
  have htk : k ≤ t := by have := reads_lt hcl htr; omega
  have hcount := elim_count N acc0 post hnokpost {p - k, r - k, t - k} (by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · have hpt : post[p - k]? = some gp := by rw [hpost, List.getElem?_drop, show k + (p - k) = p by omega]; exact hgp
      refine ⟨gp, hpt, h, hph, by have := (hcl p gp hgp).lt h hph; omega, true, by rw [← hacc]; exact hsth⟩
    · have hpt : post[r - k]? = some gr := by rw [hpost, List.getElem?_drop, show k + (r - k) = r by omega]; exact hgr
      refine ⟨gr, hpt, h, hrh, by have := (hcl r gr hgr).lt h hrh; omega, true, by rw [← hacc]; exact hsth⟩
    · obtain ⟨gt, hgt, hrtm⟩ := htr
      have hpt : post[t - k]? = some gt := by rw [hpost, List.getElem?_drop, show k + (t - k) = t by omega]; exact hgt
      have hpr : post[r - k]? = some gr := by rw [hpost, List.getElem?_drop, show k + (r - k) = r by omega]; exact hgr
      obtain ⟨c, hc⟩ := exch_const_readerB N post acc0 hnokpost h (r - k) gr hpr true
        (Or.inr ⟨rfl, hopr⟩) hrh (by omega) hsth0
      refine ⟨gt, hpt, N + r, hrtm, by have := (hcl t gt hgt).lt _ hrtm; omega, c, ?_⟩
      rw [show acc0.1.length + (r - k) = N + r by omega] at hc; exact hc)
  have hcard : ({p - k, r - k, t - k} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p - k, r - k, t - k, by omega, by omega, by omega, rfl⟩
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + 3 ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega
  have hwhA : ∀ x : Fin N → Bool, vl acc.2 x h = vl gs x h := by
    intro x; rw [hwh x]; unfold vl
    rw [htl, wiresFrom_append, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hval1 : ∀ x : Fin N → Bool, vl gs x h = true →
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o1 (Sum.inl false)) = F1 x := by
    intro x hx; rw [((hinv x hx).2 o1).2, ← L.hev1 x]; rfl
  have hval2 : ∀ x : Fin N → Bool, vl gs x h = true →
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o2 (Sum.inl false)) = F2 x := by
    intro x hx; rw [((hinv x hx).2 o2).2, ← L.hev2 x]; rfl
  have hv1 : statValid (N + acc.2.length) (acc.1.getD o1 (Sum.inl false)) := ((hinv x0 hx0).2 o1).1
  have hv2 : statValid (N + acc.2.length) (acc.1.getD o2 (Sum.inl false)) := ((hinv x0 hx0).2 o2).1
  set gs0 := acc.2 ++ [⟨GateOp.not, [h]⟩] with hgs0
  have hcl0 : CleanL N gs0 := clean_append_not hclacc (by omega)
  have hr0 : N + acc.2.length < N + gs0.length := by simp [hgs0]
  have hrval : ∀ x : Fin N → Bool, vl gs0 x (N + acc.2.length) = !vl gs x h := by
    intro x; rw [hgs0, vl_append_not acc.2 hclacc h (by omega) x, hwhA x]
  have hst0 : ∀ (s : Stat) (x : Fin N → Bool), statValid (N + acc.2.length) s →
      statVal (wiresFrom gs0 (List.ofFn x)) s = statVal (wiresFrom acc.2 (List.ofFn x)) s := by
    intro s x hs; cases s with
    | inl c => rfl
    | inr j => exact vl_append_lt acc.2 _ x j hs
  obtain ⟨gs1, o1', hcl1, hlen1, hag1, hev1', hkind1⟩ :=
    append_or_out gs0 hcl0 (N + acc.2.length) hr0 (acc.1.getD o1 (Sum.inl false))
      (statValid_mono (by simp [hgs0]) _ hv1) hnc1
      (fun x hx => (hcov x (by rw [hrval x] at hx; simpa using hx)).1)
      (fun x hx => by
        rw [hst0 _ x hv1]
        exact hval1 x (by rw [hrval x] at hx; simpa using hx))
  have hlen0 : gs0.length = acc.2.length + 1 := by simp [hgs0]
  have hge0 : gs0.length ≤ gs1.length := by
    rcases hkind1 with h | ⟨j, _, h, _⟩
    · omega
    · rw [h]; simp
  have hst1 : ∀ (s : Stat) (x : Fin N → Bool), statValid (N + acc.2.length) s →
      statVal (wiresFrom gs1 (List.ofFn x)) s = statVal (wiresFrom acc.2 (List.ofFn x)) s := by
    intro s x hs; cases s with
    | inl c => rfl
    | inr j =>
      have hj : j < N + acc.2.length := hs
      show vl gs1 x j = vl acc.2 x j
      rw [hag1 x j (by omega), hgs0, vl_append_lt acc.2 _ x j hj]
  obtain ⟨gs2, o2', hcl2, hlen2, hag2, hev2', hkind2⟩ :=
    append_or_out gs1 hcl1 (N + acc.2.length) (by omega) (acc.1.getD o2 (Sum.inl false))
      (statValid_mono (by omega) _ hv2) hnc2
      (fun x hx => (hcov x (by rw [hag1 x _ hr0, hrval x] at hx; simpa using hx)).2)
      (fun x hx => by
        rw [hst1 _ x hv2]
        exact hval2 x (by rw [hag1 x _ hr0, hrval x] at hx; simpa using hx))
  have ho1lt : o1' < N + gs1.length := out_lt_of_nc hev1' hnc1
  have hev_final : ∀ x : Fin N → Bool, vl gs2 x o1' = F1 x ∧ vl gs2 x o2' = F2 x :=
    fun x => ⟨by rw [hag2 x o1' ho1lt, hev1' x], hev2' x⟩
  have hmin_le : gs.length ≤ gs2.length := L.hmin gs2 o1' o2' hcl2 hev_final
  have hlen_acc : acc.2.length + 3 = gs.length := by omega
  have hlen_gs2 : gs2.length = gs.length := by omega
  have hlen_gs1 : gs1.length = gs0.length + 1 := by omega
  have hlen_gs2' : gs2.length = gs1.length + 1 := by omega
  obtain ⟨j1, hj1, hgs1_eq, ho1_eq⟩ : ∃ j1 < N + gs0.length,
      gs1 = gs0 ++ [⟨GateOp.or, [j1, N + acc.2.length]⟩] ∧ o1' = N + gs0.length := by
    rcases hkind1 with h | h
    · omega
    · exact h
  obtain ⟨j2, hj2, hgs2_eq, ho2_eq⟩ : ∃ j2 < N + gs1.length,
      gs2 = gs1 ++ [⟨GateOp.or, [j2, N + acc.2.length]⟩] ∧ o2' = N + gs1.length := by
    rcases hkind2 with h | h
    · omega
    · exact h
  refine ⟨gs2, o1', o2', least2_of L hcl2 hev_final (le_of_eq hlen_gs2), ?_⟩
  intro M hM
  have hpM := hM.lt_of_not (List.getElem?_eq_some_iff.1 hgp).1 (not_tailOK2_and hgp hopp)
  have hgs2_app : gs2 = acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j1, N + acc.2.length]⟩,
      ⟨GateOp.or, [j2, N + acc.2.length]⟩] := by simp [hgs2_eq, hgs1_eq, hgs0]
  have hnew3 : ∀ i < 3, TailOK2 N F1 F2 gs2 (acc.2.length + i) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact ⟨⟨GateOp.not, [h]⟩, by rw [hgs2_app]; simp, Or.inl rfl⟩
    · refine ⟨⟨GateOp.or, [j1, N + acc.2.length]⟩, by rw [hgs2_app]; simp, Or.inr ⟨rfl, Or.inl fun x hx => ?_⟩⟩
      have e : N + (acc.2.length + 1) = o1' := by rw [ho1_eq, hlen0]
      rw [e, (hev_final x).1] at hx; exact hx
    · refine ⟨⟨GateOp.or, [j2, N + acc.2.length]⟩, by rw [hgs2_app]; simp, Or.inr ⟨rfl, Or.inr fun x hx => ?_⟩⟩
      have e : N + (acc.2.length + 2) = o2' := by rw [ho2_eq, hlen_gs1, hlen0]
      rw [e, (hev_final x).2] at hx; exact hx
  by_cases hM2 : M ≤ 2
  · rw [hgs2_app]
    exact (tailGE2_append N F1 F2 acc.2 _ 0 (TailGE2.zero N F1 F2 acc.2) (fun i hi => by
      rw [← hgs2_app]; exact hnew3 i (by simpa using hi))).mono (by simp; omega)
  · set B := gs.length - M - k with hB
    have hBp : p - k < B := by omega
    have hBlen : B ≤ post.length := by omega
    set post1 := post.take B with hpost1
    set post2 := post.drop B with hpost2
    have hpost_eq : post = post1 ++ post2 := (List.take_append_drop B post).symm
    set acc1 := elim N post1 acc0 with hacc1
    have hacc_eq : acc = elim N post2 acc1 := by rw [hacc, hpost_eq, elim_append]
    have hacc1_len : acc1.2.length + 1 ≤ k + B := by
      have hc1 := elim_count N acc0 post1 (fun g hg => hnokpost g (List.mem_of_mem_take hg))
        {p - k} (by
          intro q hq; rw [Finset.mem_singleton] at hq; subst hq
          have hq1 : post1[p - k]? = some gp := by
            rw [hpost1, List.getElem?_take_of_lt hBp, hpost, List.getElem?_drop,
              show k + (p - k) = p by omega]; exact hgp
          have hst1' : (elim N post1 acc0).1.getD h (Sum.inl false) = Sum.inl true := by
            rw [elim_getD N h _ post1 acc0 (by omega)]; exact hsth0
          exact ⟨gp, hq1, h, hph, by have := (hcl p gp hgp).lt h hph; omega, true, hst1'⟩)
      rw [Finset.card_singleton, ← hacc1] at hc1
      have : acc0.2.length = k := by simp [hacc0, hlpre]
      have : post1.length = B := by simp [hpost1]; omega
      omega
    have htail_acc : TailGE2 N F1 F2 acc.2 (M - 2) := by
      refine ⟨by omega, ?_⟩
      intro j hj1 hj2
      have hja : acc1.2.length ≤ j := by omega
      rw [hacc_eq] at hj2 ⊢
      refine elim_tail_ok N F1 F2 (fun x => vl gs x h = true)
        (fun x hx => hcov x (by simpa using hx)) post2
        (fun x => wiresFrom post1 (wiresFrom pre (List.ofFn x))) acc1
        (fun g hg => (hnokpost g (List.mem_of_mem_drop hg)).1)
        (fun x hx => inv_elim N _ (hyl x) post1 _ _
          (fun g hg => (hnokpost g (List.mem_of_mem_take hg)).1)
          (inv_startB N h true pre _ (hyl x) (by rw [← hwh]; exact hx)))
        ?_ j hja hj2
      intro q g hq
      have hqg : gs[k + B + q]? = some g := by
        rw [hpost2, List.getElem?_drop, hpost, List.getElem?_drop] at hq
        rwa [← Nat.add_assoc] at hq
      have hlen_w : ∀ x : Fin N → Bool,
          (wiresFrom post1 (wiresFrom pre (List.ofFn x))).length = N + (k + B) := by
        intro x; rw [length_wiresFrom, length_wiresFrom, hyl, hlpre]; simp [hpost1]; omega
      have hfull_w : ∀ x : Fin N → Bool,
          wiresFrom post2 (wiresFrom post1 (wiresFrom pre (List.ofFn x))) =
          wiresFrom gs (List.ofFn x) := by
        intro x; rw [← wiresFrom_append, ← hpost_eq, ← hwg]
      obtain ⟨g', hg', hop'⟩ := hM.2 (k + B + q) (by omega)
        ((List.getElem?_eq_some_iff.1 hqg).1)
      rw [hqg] at hg'; cases hg'
      rcases hop' with hop' | ⟨hop', h1 | h2⟩
      · exact Or.inl hop'
      · refine Or.inr ⟨hop', Or.inl fun x _ hv => h1 x ?_⟩
        rw [hfull_w x, hlen_w x] at hv
        show (wiresFrom gs (List.ofFn x)).getD (N + (k + B + q)) false = true
        rw [← Nat.add_assoc]; exact hv
      · refine Or.inr ⟨hop', Or.inr fun x _ hv => h2 x ?_⟩
        rw [hfull_w x, hlen_w x] at hv
        show (wiresFrom gs (List.ofFn x)).getD (N + (k + B + q)) false = true
        rw [← Nat.add_assoc]; exact hv
    rw [hgs2_app]
    exact (tailGE2_append N F1 F2 acc.2 _ (M - 2) htail_acc (fun i hi => by
      rw [← hgs2_app]; exact hnew3 i (by simpa using hi))).mono (by simp; omega)

def ExtProps2 (n : ℕ) (F1 F2 : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1)))
    (gs : List Gate) : Prop :=
  (∀ (h p : ℕ) (gp : Gate), DFree D gs h → gs[p]? = some gp → gp.op = GateOp.or →
    h ∈ gp.inputs → ¬ TailOK2 (n + 1) F1 F2 gs p →
    (∀ x : Fin (n + 1) → Bool, vl gs x h = true → F1 x = true ∧ F2 x = true) →
    ∀ t, Reads gs t h → t = p) ∧
  (∀ (h p : ℕ) (gp : Gate), DFree D gs h → gs[p]? = some gp → gp.op = GateOp.and →
    h ∈ gp.inputs →
    (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F1 x = true ∧ F2 x = true) →
    (∀ t, Reads gs t h → t = p) ∨
    ∃ (r : ℕ) (gr : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some gr ∧ gr.op = GateOp.and ∧
      (gr.inputs = [q, h] ∨ gr.inputs = [h, q]) ∧ ∀ t, Reads gs t h → t = p ∨ t = r)

theorem stmtExt2 (n s : ℕ) (F1 F2 : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1)))
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D) (hne : D.Nonempty)
    (hs : HasSize2 (n + 1) F1 F2 s) :
    ∃ (gs : List Gate) (o1 o2 : ℕ), Least2 (n + 1) F1 F2 gs o1 o2 ∧ gs.length ≤ s ∧
      ExtProps2 n F1 F2 D gs := by
  classical
  have hnc1 := deepHyp'_nc H1 hne
  have hnc2 := deepHyp'_nc H2 hne
  obtain ⟨gs0, o10, o20, L0, hl0⟩ := exists_least2 (n + 1) F1 F2 s hnc1 hnc2 hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o1 o2 : ℕ),
    Least2 (n + 1) F1 F2 gs o1 o2 ∧ TailGE2 (n + 1) F1 F2 gs t
  have hP0 : P 0 := ⟨gs0, o10, o20, L0, TailGE2.zero _ _ _ _⟩
  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o1, o2, L, ht⟩; exact (least2_len L L0) ▸ ht.1
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o1, o2, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  obtain ⟨y0, hy0⟩ := hne
  refine ⟨gs, o1, o2, L, by rw [least2_len L L0]; exact hl0, ?_, ?_⟩
  · intro h p gp hfree hgp hopp hph hnt hcov
    have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
        (g.op = GateOp.and ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
        T.card ≤ 2 := by
      intro T hTm
      obtain ⟨gs', o1', o2', hc', he', hlen⟩ :=
        exch2_gen (n + 1) F1 F2 gs o1 o2 h false T L.hcl L.hev hnc1 hnc2
          (fun x hx => hcov x (by simpa using hx))
          (fun t ht => by
            rcases hTm t ht with h1 | ⟨r, g, hg, hop, hrh, htr⟩
            · exact Or.inl h1
            · exact Or.inr ⟨r, g, hg, Or.inl ⟨rfl, hop⟩, hrh, htr⟩)
      have := L.hmin gs' o1' o2' hc' he'
      simp only [Bool.false_eq_true, ↓reduceIte] at hlen; omega
    intro r hrr
    by_contra hrp
    obtain ⟨gr, hgr, hhr⟩ := hrr
    have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
    have hpread : Reads gs p h := ⟨gp, hgp, hph⟩
    rcases L.hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop | hop, j, k, _, _, hjk⟩
    · have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
      rw [hj] at hjin
      have ho1r : o1 ≠ n + 1 + r := by
        intro e
        have hm := deepHyp'_supp H1 L.hev1 hy0
        rw [e, front_supp_gate gs L.hcl r gr hgr y0] at hm
        obtain ⟨a, ha, hia⟩ := hm
        rw [hjin, List.mem_singleton] at ha; subst ha
        exact hfree y0 hy0 hia
      have ho2r : o2 ≠ n + 1 + r := by
        intro e
        have hm := deepHyp'_supp H2 L.hev2 hy0
        rw [e, front_supp_gate gs L.hcl r gr hgr y0] at hm
        obtain ⟨a, ha, hia⟩ := hm
        rw [hjin, List.mem_singleton] at ha; subst ha
        exact hfree y0 hy0 hia
      obtain ⟨t, hrt, htr⟩ := L.live hnc1 hnc2 r hrlen ho1r ho2r
      have htp : t ≠ p := by
        intro e; subst e; exact L.no_tri hnc1 hnc2 r t h ⟨gr, hgr, hhr⟩ hpread htr
      have := hT {p, r, t} (by
        intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_eq_three.2 ⟨p, r, t, Ne.symm hrp, Ne.symm htp, by omega, rfl⟩] at this; omega
    · have ho1r : o1 ≠ n + 1 + r := by
        intro e
        have hF1eq : ∀ x, F1 x = vl gs x h := by
          intro x; cases hx : vl gs x h
          · rw [← L.hev1 x, e, vl_gate gs L.hcl x r gr hgr, hop, hjk]
            rw [hjk] at hhr; simp at hhr
            rcases hhr with rfl | rfl <;> simp [GateOp.eval, hx]
          · exact (hcov x hx).1
        obtain ⟨z, h0⟩ := deepHyp'_zero_ex H1
        obtain ⟨x', -, -, hF0, hF1⟩ := H1.win y0 hy0 z h0
        have := vl_update_of_not_supp gs h y0 (hfree y0 hy0) x' true
        rw [← hF1eq, ← hF1eq] at this; rw [hF0, hF1] at this; cases this
      have ho2r : o2 ≠ n + 1 + r := by
        intro e
        have hF2eq : ∀ x, F2 x = vl gs x h := by
          intro x; cases hx : vl gs x h
          · rw [← L.hev2 x, e, vl_gate gs L.hcl x r gr hgr, hop, hjk]
            rw [hjk] at hhr; simp at hhr
            rcases hhr with rfl | rfl <;> simp [GateOp.eval, hx]
          · exact (hcov x hx).2
        obtain ⟨z, h0⟩ := deepHyp'_zero_ex H2
        obtain ⟨x', -, -, hF0, hF1⟩ := H2.win y0 hy0 z h0
        have := vl_update_of_not_supp gs h y0 (hfree y0 hy0) x' true
        rw [← hF2eq, ← hF2eq] at this; rw [hF0, hF1] at this; cases this
      obtain ⟨t, hrt, htr⟩ := L.live hnc1 hnc2 r hrlen ho1r ho2r
      have htp : t ≠ p := by
        intro e; subst e; exact L.no_tri hnc1 hnc2 r t h ⟨gr, hgr, hhr⟩ hpread htr
      have := hT {p, r, t} (by
        intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_eq_three.2 ⟨p, r, t, Ne.symm hrp, Ne.symm htp, by omega, rfl⟩] at this; omega
    · obtain ⟨l, hinp⟩ : ∃ l, gp.inputs = [l, h] ∨ gp.inputs = [h, l] := by
        rcases L.hcl p gp hgp with ⟨h1, _⟩ | ⟨_, a, b, _, _, hab⟩
        · rw [hopp] at h1; cases h1
        · rw [hab] at hph; simp at hph
          rcases hph with rfl | rfl
          · exact ⟨b, Or.inr hab⟩
          · exact ⟨a, Or.inl hab⟩
      obtain ⟨q, hinr⟩ : ∃ q, gr.inputs = [q, h] ∨ gr.inputs = [h, q] := by
        rw [hjk] at hhr; simp at hhr
        rcases hhr with rfl | rfl
        · exact ⟨k, Or.inr hjk⟩
        · exact ⟨j, Or.inl hjk⟩
      obtain ⟨gs', o1', o2', L', ht'⟩ :=
        lift2_or (n + 1) F1 F2 gs o1 o2 p r l q h gp gr L hnc1 hnc2 (Ne.symm hrp)
          hgp hopp hinp hgr hop hinr hcov hnt
      have := hmax (M + 1) ⟨gs', o1', o2', L', ht' M ht⟩
      omega
  · intro h p gp hfree hgp hopp hph hcov
    have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
        (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
        T.card ≤ 3 := by
      intro T hTm
      obtain ⟨gs', o1', o2', hc', he', hlen⟩ :=
        exch2_gen (n + 1) F1 F2 gs o1 o2 h true T L.hcl L.hev hnc1 hnc2
          (fun x hx => hcov x (by simpa using hx))
          (fun t ht => by
            rcases hTm t ht with h1 | ⟨r, g, hg, hop, hrh, htr⟩
            · exact Or.inl h1
            · exact Or.inr ⟨r, g, hg, Or.inr ⟨rfl, hop⟩, hrh, htr⟩)
      have := L.hmin gs' o1' o2' hc' he'
      simp only [↓reduceIte] at hlen; omega
    have hpread : Reads gs p h := ⟨gp, hgp, hph⟩
    by_cases hsec : ∃ r, r ≠ p ∧ Reads gs r h
    · right
      obtain ⟨r, hrp, hrr⟩ := hsec
      have hr_and : ∀ r', r' ≠ p → Reads gs r' h → ∃ g', gs[r']? = some g' ∧ g'.op = GateOp.and := by
        intro r' hr'p ⟨gr', hgr', hhr'⟩
        have hr'len : r' < gs.length := (List.getElem?_eq_some_iff.1 hgr').1
        rcases L.hcl r' gr' hgr' with ⟨hnot, j, _, hjin⟩ | ⟨hop | hop, j, k, _, _, hjk⟩
        · exfalso
          have hj : j = h := by rw [hjin] at hhr'; simp at hhr'; exact hhr'.symm
          rw [hj] at hjin
          have ho1r : o1 ≠ n + 1 + r' := by
            intro e; have hm := deepHyp'_supp H1 L.hev1 hy0
            rw [e, front_supp_gate gs L.hcl r' gr' hgr' y0] at hm
            obtain ⟨a, ha, hia⟩ := hm; rw [hjin, List.mem_singleton] at ha; subst ha
            exact hfree y0 hy0 hia
          have ho2r : o2 ≠ n + 1 + r' := by
            intro e; have hm := deepHyp'_supp H2 L.hev2 hy0
            rw [e, front_supp_gate gs L.hcl r' gr' hgr' y0] at hm
            obtain ⟨a, ha, hia⟩ := hm; rw [hjin, List.mem_singleton] at ha; subst ha
            exact hfree y0 hy0 hia
          obtain ⟨t, hrt, htr⟩ := L.live hnc1 hnc2 r' hr'len ho1r ho2r
          have htp : t ≠ p := by
            intro e; subst e; exact L.no_tri hnc1 hnc2 r' t h ⟨gr', hgr', hhr'⟩ hpread htr
          obtain ⟨gs', o1', o2', L', ht'⟩ :=
            exch2_and_tail (n + 1) F1 F2 gs o1 o2 h p r' t gp gr' L hnc1 hnc2 hcov
              (Ne.symm hr'p) (Ne.symm htp) (by omega) hgp hopp hph hgr' (Or.inr hnot) hhr' htr
          have := hmax (M + 1) ⟨gs', o1', o2', L', ht' M ht⟩; omega
        · exact ⟨gr', hgr', hop⟩
        · exfalso
          have ho1r : o1 ≠ n + 1 + r' := by
            intro e; obtain ⟨x, x', hxx'⟩ := hnc1
            have key : ∀ z, F1 z = true := fun z => by
              cases hz : vl gs z h
              · exact (hcov z hz).1
              · rw [← L.hev1 z, e, vl_gate gs L.hcl z r' gr' hgr', hop, hjk]
                rw [hjk] at hhr'; simp at hhr'
                rcases hhr' with rfl | rfl <;> simp [GateOp.eval, hz]
            exact hxx' (by rw [key x, key x'])
          have ho2r : o2 ≠ n + 1 + r' := by
            intro e; obtain ⟨x, x', hxx'⟩ := hnc2
            have key : ∀ z, F2 z = true := fun z => by
              cases hz : vl gs z h
              · exact (hcov z hz).2
              · rw [← L.hev2 z, e, vl_gate gs L.hcl z r' gr' hgr', hop, hjk]
                rw [hjk] at hhr'; simp at hhr'
                rcases hhr' with rfl | rfl <;> simp [GateOp.eval, hz]
            exact hxx' (by rw [key x, key x'])
          obtain ⟨t, hrt, htr⟩ := L.live hnc1 hnc2 r' hr'len ho1r ho2r
          have htp : t ≠ p := by
            intro e; subst e; exact L.no_tri hnc1 hnc2 r' t h ⟨gr', hgr', hhr'⟩ hpread htr
          obtain ⟨gs', o1', o2', L', ht'⟩ :=
            exch2_and_tail (n + 1) F1 F2 gs o1 o2 h p r' t gp gr' L hnc1 hnc2 hcov
              (Ne.symm hr'p) (Ne.symm htp) (by omega) hgp hopp hph hgr' (Or.inl hop) hhr' htr
          have := hmax (M + 1) ⟨gs', o1', o2', L', ht' M ht⟩; omega
      obtain ⟨gr, hgr, hopr⟩ := hr_and r hrp hrr
      have hhr : h ∈ gr.inputs := by
        obtain ⟨gr', hgr', hhr'⟩ := hrr; rw [hgr] at hgr'; cases hgr'; exact hhr'
      obtain ⟨q, hinr⟩ : ∃ q, gr.inputs = [q, h] ∨ gr.inputs = [h, q] := by
        rcases L.hcl r gr hgr with ⟨h1, _⟩ | ⟨_, j, k, _, _, hjk⟩
        · rw [hopr] at h1; cases h1
        · rw [hjk] at hhr; simp at hhr
          rcases hhr with rfl | rfl
          · exact ⟨k, Or.inr hjk⟩
          · exact ⟨j, Or.inl hjk⟩
      refine ⟨r, gr, q, hrp, hgr, hopr, hinr, ?_⟩
      intro t htr
      by_contra hne; push Not at hne
      obtain ⟨htp, htr'⟩ := hne
      obtain ⟨gt, hgt, hopt⟩ := hr_and t htp htr
      have hht : h ∈ gt.inputs := by
        obtain ⟨gt', hgt', hht'⟩ := htr; rw [hgt] at hgt'; cases hgt'; exact hht'
      have get_in : ∀ (u : ℕ) (gu : Gate), gs[u]? = some gu → gu.op = GateOp.and → h ∈ gu.inputs →
          ∃ lu, gu.inputs = [lu, h] ∨ gu.inputs = [h, lu] := by
        intro u gu hgu hopu hhu
        rcases L.hcl u gu hgu with ⟨h1, _⟩ | ⟨_, j, k, _, _, hjk⟩
        · rw [hopu] at h1; cases h1
        · rw [hjk] at hhu; simp at hhu
          rcases hhu with rfl | rfl
          · exact ⟨k, Or.inr hjk⟩
          · exact ⟨j, Or.inl hjk⟩
      obtain ⟨lp, hinp⟩ := get_in p gp hgp hopp hph
      obtain ⟨lt', hint⟩ := get_in t gt hgt hopt hht
      have call3 : ∀ (a b c la lb lc : ℕ) (ga gb gc : Gate), a < b → b < c →
          gs[a]? = some ga → ga.op = GateOp.and → (ga.inputs = [la, h] ∨ ga.inputs = [h, la]) →
          gs[b]? = some gb → gb.op = GateOp.and → (gb.inputs = [lb, h] ∨ gb.inputs = [h, lb]) →
          gs[c]? = some gc → gc.op = GateOp.and → (gc.inputs = [lc, h] ∨ gc.inputs = [h, lc]) →
          False := by
        intro a b c la lb lc ga gb gc hab hbc hga hoa hia hgb hob hib hgc hoc hic
        obtain ⟨gs', o1', o2', L', ht'⟩ :=
          xmove3_and (n + 1) F1 F2 gs o1 o2 a b c la lb lc h ga gb gc L hnc1 hnc2 hab hbc
            hga hoa hia hgb hob hib hgc hoc hic hcov
        have := hmax (M + 3) ⟨gs', o1', o2', L', ht' M ht⟩; omega
      rcases lt_or_gt_of_ne hrp with h1 | h1 <;>
        rcases lt_or_gt_of_ne htp with h2 | h2 <;>
        rcases lt_or_gt_of_ne htr' with h3 | h3
      · exact call3 t r p lt' q lp gt gr gp h3 h1 hgt hopt hint hgr hopr hinr hgp hopp hinp
      · exact call3 r t p q lt' lp gr gt gp h3 h2 hgr hopr hinr hgt hopt hint hgp hopp hinp
      · omega
      · exact call3 r p t q lp lt' gr gp gt h1 h2 hgr hopr hinr hgp hopp hinp hgt hopt hint
      · exact call3 t p r lt' lp q gt gp gr h2 h1 hgt hopt hint hgp hopp hinp hgr hopr hinr
      · omega
      · exact call3 p t r lp lt' q gp gt gr h2 h3 hgp hopp hinp hgt hopt hint hgr hopr hinr
      · exact call3 p r t lp q lt' gp gr gt h1 h3 hgp hopp hinp hgr hopr hinr hgt hopt hint
    · left
      intro t htr
      by_contra htp
      exact hsec ⟨t, htp, htr⟩

def multiSwap (gs : List Gate) (Dead : Finset ℕ) (y : ℕ) : List Gate :=
  (List.range gs.length).map fun p =>
    if p ∈ Dead then ⟨GateOp.not, [y]⟩ else gs.getD p ⟨GateOp.not, [0]⟩

theorem multiSwap_length (gs : List Gate) (Dead : Finset ℕ) (y : ℕ) :
    (multiSwap gs Dead y).length = gs.length := by
  simp [multiSwap]

theorem multiSwap_get_mem (gs : List Gate) (Dead : Finset ℕ) (y p : ℕ)
    (hp : p < gs.length) (hmem : p ∈ Dead) :
    (multiSwap gs Dead y)[p]? = some ⟨GateOp.not, [y]⟩ := by
  simp [multiSwap, hp, hmem]

theorem multiSwap_get_notMem (gs : List Gate) (Dead : Finset ℕ) (y p : ℕ)
    (hmem : p ∉ Dead) : (multiSwap gs Dead y)[p]? = gs[p]? := by
  unfold multiSwap
  by_cases hp : p < gs.length
  · simp [hp, hmem]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem multiSwap_clean {N : ℕ} (gs : List Gate) (Dead : Finset ℕ) (y : ℕ)
    (hcl : CleanL N gs) (hy : y < N) : CleanL N (multiSwap gs Dead y) := by
  intro r g' hr'
  by_cases hrm : r ∈ Dead
  · have hrlen : r < gs.length := by
      have := (List.getElem?_eq_some_iff.1 hr').1
      rw [multiSwap_length] at this; exact this
    rw [multiSwap_get_mem gs Dead y r hrlen hrm] at hr'
    cases hr'; exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [multiSwap_get_notMem gs Dead y r hrm] at hr'
    exact hcl r g' hr'

theorem multiSwap_agree {N : ℕ} (gs : List Gate) (Dead : Finset ℕ) (y : ℕ)
    (hcl : CleanL N gs) (hy : y < N) (x : Fin N → Bool)
    (habs : ∀ r g, gs[r]? = some g → r ∉ Dead → (∃ ph ∈ Dead, N + ph ∈ g.inputs) →
      ∃ a ∈ g.inputs, (∀ ph ∈ Dead, a ≠ N + ph) ∧
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ vl gs x a = fixBit g) :
    ∀ w, (∀ ph ∈ Dead, w ≠ N + ph) → vl (multiSwap gs Dead y) x w = vl gs x w := by
  have hcl' := multiSwap_clean gs Dead y hcl hy
  have hlen := multiSwap_length gs Dead y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrm : r ∉ Dead := fun hm => hw r hm rfl
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g =>
        have hr' : (multiSwap gs Dead y)[r]? = some g := by
          rw [multiSwap_get_notMem gs Dead y r hrm]; exact hr
        by_cases hhit : ∃ ph ∈ Dead, N + ph ∈ g.inputs
        · obtain ⟨a, ha, hane, hop, hfix⟩ := habs r g hr hrm hhit
          have halt : a < N + r := (hcl r g hr).lt a ha
          have ha_eq : vl (multiSwap gs Dead y) x a = fixBit g := by
            rw [ih a halt hane, hfix]
          rw [vl_abs (multiSwap gs Dead y) hcl' x r g hr' hop a ha ha_eq,
            vl_abs gs hcl x r g hr hop a ha hfix]
        · rw [vl_gate _ hcl' x r g hr', vl_gate gs hcl x r g hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a ((hcl r g hr).lt a ha) (fun ph hph e => hhit ⟨ph, hph, e ▸ ha⟩)

theorem multiSwap_agree_dfree {N : ℕ} {D : Finset (Fin N)} (gs : List Gate) (Dead : Finset ℕ) (y : ℕ)
    (hcl : CleanL N gs) (hy : y < N)
    (hnd : ∀ ph ∈ Dead, ∀ r, Reads gs r (N + ph) → ¬ DFree D gs (N + r))
    (x : Fin N → Bool) :
    ∀ w, DFree D gs w → (∀ ph ∈ Dead, w ≠ N + ph) → vl (multiSwap gs Dead y) x w = vl gs x w := by
  have hcl' := multiSwap_clean gs Dead y hcl hy
  have hlen := multiSwap_length gs Dead y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hfree hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrm : r ∉ Dead := fun hm => hw r hm rfl
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g =>
        have hr' : (multiSwap gs Dead y)[r]? = some g := by
          rw [multiSwap_get_notMem gs Dead y r hrm]; exact hr
        rw [vl_gate _ hcl' x r g hr', vl_gate gs hcl x r g hr]
        congr 1
        apply List.map_congr_left
        intro a ha
        have hafree : DFree D gs a := fun u hu hm =>
          hfree u hu ((front_supp_gate gs hcl r g hr u).2 ⟨a, ha, hm⟩)
        exact ih a ((hcl r g hr).lt a ha) hafree (fun ph hph e => hnd ph hph r ⟨g, hr, e ▸ ha⟩ hfree)

def initOv (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) : List Stat × List Stat × List Gate :=
  ((List.range N).map fun i => if i = y then Sum.inl v else match ov i with
      | some b => Sum.inl b | none => Sum.inr i,
   (List.range N).map fun i => if i = y then Sum.inl v else Sum.inr i,
   [])

def elimOvStep (N : ℕ) (ov : ℕ → Option Bool) (acc : List Stat × List Stat × List Gate) (g : Gate) :
    List Stat × List Stat × List Gate :=
  let w := acc.1.length
  let r := simplify g.op (N + acc.2.2.length)
    (g.inputs.map fun a => acc.1.getD a (Sum.inl false))
  let eff := match ov w with | some b => Sum.inl b | none => r.2
  (acc.1 ++ [eff], acc.2.1 ++ [r.2], acc.2.2 ++ r.1.toList)

def elimOv (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate)
    (acc : List Stat × List Stat × List Gate) : List Stat × List Stat × List Gate :=
  gs.foldl (elimOvStep N ov) acc

theorem elimOv_cons (N : ℕ) (ov : ℕ → Option Bool) (g : Gate) (gs : List Gate)
    (acc : List Stat × List Stat × List Gate) :
    elimOv N ov (g :: gs) acc = elimOv N ov gs (elimOvStep N ov acc g) := rfl

theorem elimOv_append (N : ℕ) (ov : ℕ → Option Bool) (pre post : List Gate)
    (acc : List Stat × List Stat × List Gate) :
    elimOv N ov (pre ++ post) acc = elimOv N ov post (elimOv N ov pre acc) := by
  simp [elimOv, List.foldl_append]

theorem elimOv_fst_len (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Stat × List Gate,
    (elimOv N ov gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc; rw [elimOv_cons, ih]
    simp only [elimOvStep, List.length_append, List.length_cons, List.length_nil]; omega

theorem elimOv_getD (N : ℕ) (ov : ℕ → Option Bool) (k : ℕ) (d : Stat) (gs : List Gate) :
    ∀ acc : List Stat × List Stat × List Gate, k < acc.1.length →
    (elimOv N ov gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elimOv_cons, ih (elimOvStep N ov acc g) (by simp [elimOvStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem elimOv_split_getD (N : ℕ) (ov : ℕ → Option Bool) (pre : List Gate) (g : Gate)
    (post : List Gate) (acc : List Stat × List Stat × List Gate) (a : ℕ) (d : Stat)
    (h : a ≤ acc.1.length + pre.length) :
    (elimOv N ov (pre ++ g :: post) acc).1.getD a d =
      (elimOvStep N ov (elimOv N ov pre acc) g).1.getD a d := by
  rw [elimOv_append, elimOv_cons, elimOv_getD N ov a d post _ (by
    show a < ((elimOv N ov pre acc).1 ++ [_]).length
    rw [List.length_append, elimOv_fst_len, List.length_singleton]; omega)]

theorem elimOv_split_getD_lt (N : ℕ) (ov : ℕ → Option Bool) (pre : List Gate) (g : Gate)
    (post : List Gate) (acc : List Stat × List Stat × List Gate) (a : ℕ) (d : Stat)
    (h : a < acc.1.length + pre.length) :
    (elimOv N ov (pre ++ g :: post) acc).1.getD a d = (elimOv N ov pre acc).1.getD a d := by
  rw [elimOv_split_getD N ov pre g post acc a d (le_of_lt h)]
  show ((elimOv N ov pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elimOv_fst_len]; omega)

theorem elimOv_step_none (N : ℕ) (ov : ℕ → Option Bool) (acc : List Stat × List Stat × List Gate)
    (g : Gate) (hg : NOk g) (k : ℕ) (hk : k ∈ g.inputs) (c : Bool)
    (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimOvStep N ov acc g).2.2.length = acc.2.2.length := by
  have hnone : (simplify g.op (N + acc.2.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2.2 ++ (simplify g.op (N + acc.2.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

theorem elimOv_count (N : ℕ) (ov : ℕ → Option Bool) (acc : List Stat × List Stat × List Gate) :
    ∀ gs : List Gate, (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elimOv N ov gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elimOv N ov gs acc).2.2.length + S.card ≤ acc.2.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      obtain ⟨g, hg, _⟩ := hS p hp; simp at hg
    subst hE; simp [elimOv]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elimOv N ov (gs ++ [g]) acc = elimOvStep N ov (elimOv N ov gs acc) g := by
      rw [elimOv_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elimOv N ov (gs ++ [g]) acc).1.getD a d = (elimOv N ov gs acc).1.getD a d :=
      fun a d h => elimOv_split_getD_lt N ov gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1; omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by rw [List.getElem?_concat_length] at hg'; exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimOv_step_none N ov (elimOv N ov gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimOvStep N ov (elimOv N ov gs acc) g).2.2.length ≤
          (elimOv N ov gs acc).2.2.length + 1 := by
        simp only [elimOvStep, List.length_append]
        have := toList_length_le (simplify g.op (N + (elimOv N ov gs acc).2.2.length)
          (g.inputs.map fun i => (elimOv N ov gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'; omega

def GoodUpTo (ov : ℕ → Option Bool) (w : List Bool) (m : ℕ) : Prop :=
  ∀ j < m, ∀ b, ov j = some b → w.getD j false = b

def InvOv (N : ℕ) (ov : ℕ → Option Bool) (y : List Bool) (w : List Bool)
    (acc : List Stat × List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ acc.2.1.length = w.length ∧
  (∀ i, statValid (N + acc.2.2.length) (acc.1.getD i (Sum.inl false)) ∧
        statValid (N + acc.2.2.length) (acc.2.1.getD i (Sum.inl false))) ∧
  (∀ i, GoodUpTo ov w i →
    statVal (wiresFrom acc.2.2 y) (acc.2.1.getD i (Sum.inl false)) = w.getD i false) ∧
  (GoodUpTo ov w w.length →
    ∀ i, statVal (wiresFrom acc.2.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false)

theorem invOv_init (N : ℕ) (y : Fin N) (v : Bool) (ov : ℕ → Option Bool) (x : Fin N → Bool) :
    InvOv N ov (List.ofFn x) (List.ofFn (Function.update x y v)) (initOv N y.val v ov) := by
  refine ⟨by simp [initOv], by simp [initOv], ?_, ?_, ?_⟩
  · intro i
    unfold initOv; dsimp only
    by_cases hi : i < N
    · rw [List.getD_eq_getElem _ _ (by simp; exact hi),
        List.getD_eq_getElem _ _ (by simp; exact hi)]
      simp only [List.getElem_map, List.getElem_range]
      constructor
      · split_ifs
        · trivial
        · cases ov i <;> simp [statValid, hi]
      · split_ifs
        · trivial
        · simp [statValid, hi]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, trivial⟩
  · intro i _
    unfold initOv; dsimp only
    by_cases hi : i < N
    · rw [List.getD_eq_getElem _ _ (by simp; exact hi),
        List.getD_eq_getElem _ _ (by simp; exact hi)]
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      split_ifs with hiy
      · have e : (⟨i, hi⟩ : Fin N) = y := Fin.ext hiy
        rw [e, Function.update_self]; rfl
      · have hne : (⟨i, hi⟩ : Fin N) ≠ y := fun e => hiy (congrArg Fin.val e)
        rw [Function.update_of_ne hne]; simp [statVal, wiresFrom, hi]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      rfl
  · intro hgood i
    unfold initOv; dsimp only
    by_cases hi : i < N
    · rw [List.getD_eq_getElem _ _ (by simp; exact hi),
        List.getD_eq_getElem _ _ (by simp; exact hi)]
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      split_ifs with hiy
      · have e : (⟨i, hi⟩ : Fin N) = y := Fin.ext hiy
        rw [e, Function.update_self]; rfl
      · have hne : (⟨i, hi⟩ : Fin N) ≠ y := fun e => hiy (congrArg Fin.val e)
        cases hov : ov i with
        | none => rw [Function.update_of_ne hne]; simp [statVal, wiresFrom, hi]
        | some b =>
          have hb := hgood i (by simpa using hi) b hov
          rw [show (List.ofFn (Function.update x y v)).getD i false =
            Function.update x y v ⟨i, hi⟩ from getD_ofFn N _ false ⟨i, hi⟩] at hb
          exact hb.symm
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      rfl

theorem invOv_elim (N : ℕ) (ov : ℕ → Option Bool) (y : List Bool) (hy : y.length = N)
    (gs : List Gate) : ∀ (w : List Bool) (acc : List Stat × List Stat × List Gate),
    (∀ g ∈ gs, Ok g) → InvOv N ov y w acc →
    InvOv N ov y (wiresFrom gs w) (elimOv N ov gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimOvStep N ov acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl1, hl2, hval, hreal, heff⟩ := h
    set w' := wiresFrom acc.2.2 y with hw'
    have lw' : w'.length = N + acc.2.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2) (by
      intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs; rw [lw']; exact (hval a).1)
    rw [lw'] at hs
    set r := simplify g.op (N + acc.2.2.length) ins with hr
    have hnew : wiresFrom (acc.2.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    have hgood_pre : ∀ m ≤ w.length,
        GoodUpTo ov (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) m →
        GoodUpTo ov w m := by
      intro m hm hg j hj b hjb
      have := hg j hj b hjb
      rwa [getD_snoc_ne _ _ _ _ (by omega)] at this
    refine ⟨by simp [elimOvStep, hl1], by simp [elimOvStep, hl2], ?_, ?_, ?_⟩
    · intro i
      show statValid (N + (acc.2.2 ++ r.1.toList).length)
          ((acc.1 ++ [match ov acc.1.length with | some b => Sum.inl b | none => r.2]).getD i (Sum.inl false)) ∧
        statValid (N + (acc.2.2 ++ r.1.toList).length) ((acc.2.1 ++ [r.2]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hi : i = acc.1.length
      · rw [hi, getD_snoc_eq, show acc.1.length = acc.2.1.length by omega, getD_snoc_eq]
        refine ⟨?_, hs.1⟩
        cases ov acc.2.1.length <;> [exact hs.1; trivial]
      · rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ (by omega)]
        exact ⟨statValid_mono (by omega) _ (hval i).1, statValid_mono (by omega) _ (hval i).2⟩
    · intro i hgi
      show statVal (wiresFrom (acc.2.2 ++ r.1.toList) y)
          ((acc.2.1 ++ [r.2]).getD i (Sum.inl false)) = _
      rw [hnew]
      by_cases hi : i = w.length
      · subst hi
        rw [show w.length = acc.2.1.length by omega, getD_snoc_eq,
          show acc.2.1.length = w.length by omega, getD_snoc_eq]
        have hgw : GoodUpTo ov w w.length := hgood_pre w.length le_rfl hgi
        have hvals : ins.map (statVal w') = g.inputs.map fun a => w.getD a false := by
          rw [hins, List.map_map]
          exact List.map_congr_left fun a _ => heff hgw a
        rw [hs.2, hvals]
      · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ hi,
          ht, statVal_append _ _ _ (by rw [lw']; exact (hval i).2)]
        by_cases hlt : i < w.length
        · exact hreal i (hgood_pre i (le_of_lt hlt) hgi)
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]; rfl
    · intro hgall i
      have hgw : GoodUpTo ov w w.length := hgood_pre w.length le_rfl (fun j hj b hjb =>
        hgall j (by simp; omega) b hjb)
      show statVal (wiresFrom (acc.2.2 ++ r.1.toList) y)
          ((acc.1 ++ [match ov acc.1.length with | some b => Sum.inl b | none => r.2]).getD i (Sum.inl false)) = _
      rw [hnew]
      by_cases hi : i = w.length
      · subst hi
        rw [show w.length = acc.1.length by omega, getD_snoc_eq,
          show acc.1.length = w.length by omega, getD_snoc_eq]
        cases hov : ov w.length with
        | some b =>
          have hb := hgall w.length (by simp) b hov
          rw [getD_snoc_eq] at hb
          exact hb.symm
        | none =>
          have hvals : ins.map (statVal w') = g.inputs.map fun a => w.getD a false := by
            rw [hins, List.map_map]
            exact List.map_congr_left fun a _ => heff hgw a
          show statVal (wiresFrom r.1.toList w') r.2 = _
          rw [hs.2, hvals]
      · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ hi,
          ht, statVal_append _ _ _ (by rw [lw']; exact (hval i).1)]
        exact heff hgw i

theorem cleanOv_elim (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Stat × List Gate, (∀ g ∈ gs, Ok g) →
    (∀ i, statValid (N + acc.2.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL N acc.2.2 → CleanL N (elimOv N ov gs acc).2.2 := by
  induction gs with
  | nil => intro acc _ _ h; exact h
  | cons g gs ih =>
    intro acc hok hval hcl
    have hgok := hok g List.mem_cons_self
    set ins := g.inputs.map fun a => acc.1.getD a (Sum.inl false) with hins
    have hvins : ∀ s ∈ ins, statValid (N + acc.2.2.length) s := by
      intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs; exact hval a
    have hs := simplify_sound g.op hgok.1 (List.replicate (N + acc.2.2.length) false) ins
      (by simpa [hins] using hgok.2) (by simpa using hvins)
    simp only [List.length_replicate] at hs
    refine ih (elimOvStep N ov acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_ ?_
    · intro i
      show statValid (N + (acc.2.2 ++ (simplify g.op (N + acc.2.2.length) ins).1.toList).length)
        ((acc.1 ++ [match ov acc.1.length with
          | some b => Sum.inl b | none => (simplify g.op (N + acc.2.2.length) ins).2]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hi : i = acc.1.length
      · rw [hi, getD_snoc_eq]
        cases ov acc.1.length <;> [exact hs.1; trivial]
      · rw [getD_snoc_ne _ _ _ _ hi]; exact statValid_mono (by omega) _ (hval i)
    · intro p g' hp
      have hp' : (acc.2.2 ++ (simplify g.op (N + acc.2.2.length) ins).1.toList)[p]? = some g' := hp
      by_cases hlt : p < acc.2.2.length
      · rw [List.getElem?_append_left hlt] at hp'; exact hcl p g' hp'
      · rw [List.getElem?_append_right (by omega)] at hp'
        obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
        have hpl : p = acc.2.2.length := by omega
        rw [hpl]; exact simplify_clean _ _ _ hvins g' hmem

theorem elimOv_const_of_read (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate)
    (acc : List Stat × List Stat × List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs) (hlt : a < acc.1.length + p)
    (hno : ov (acc.1.length + p) = none)
    (hc : (elimOv N ov gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimOv N ov gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elimOv_split_getD_lt N ov pre g post acc a _ hlt] at hc
  rw [elimOv_split_getD N ov pre g post acc _ _ (le_refl _)]
  have hlen : (elimOv N ov pre acc).1.length = acc.1.length + pre.length := elimOv_fst_len N ov pre acc
  rw [show ((elimOvStep N ov (elimOv N ov pre acc) g).1).getD (acc.1.length + pre.length) (Sum.inl false) =
    match ov (elimOv N ov pre acc).1.length with
    | some b => Sum.inl b
    | none => (simplify g.op (N + (elimOv N ov pre acc).2.2.length)
        (g.inputs.map fun i => (elimOv N ov pre acc).1.getD i (Sum.inl false))).2
    from getD_snoc_len _ _ _ _ hlen, hlen, hno]
  exact simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g) (fun h => by simp [fixBit, h]) (fun h => by simp [fixBit, h])
    (List.mem_map.2 ⟨a, ha, hc⟩)

theorem elimOv_allconst (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate)
    (acc : List Stat × List Stat × List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hg : NOk g) (hlt : ∀ a ∈ g.inputs, a < acc.1.length + p)
    (hall : ∀ a ∈ g.inputs, ∃ c, (elimOv N ov gs acc).1.getD a (Sum.inl false) = Sum.inl c) :
    ∃ c, (elimOv N ov gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elimOv_split_getD N ov pre g post acc _ _ (le_refl _)]
  have hlen : (elimOv N ov pre acc).1.length = acc.1.length + pre.length := elimOv_fst_len N ov pre acc
  rw [show ((elimOvStep N ov (elimOv N ov pre acc) g).1).getD (acc.1.length + pre.length) (Sum.inl false) =
    match ov (elimOv N ov pre acc).1.length with
    | some b => Sum.inl b
    | none => (simplify g.op (N + (elimOv N ov pre acc).2.2.length)
        (g.inputs.map fun i => (elimOv N ov pre acc).1.getD i (Sum.inl false))).2
    from getD_snoc_len _ _ _ _ hlen]
  cases ov (elimOv N ov pre acc).1.length with
  | some b => exact ⟨b, rfl⟩
  | none =>
    apply simp_allconst g.op _ _ hg.1.1 (by simpa using hg.1.2)
    intro s hs; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
    obtain ⟨c, hc⟩ := hall a ha
    rw [elimOv_split_getD_lt N ov pre g post acc a _ (hlt a ha)] at hc
    exact ⟨c, hc⟩

theorem or_fold_stats {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) :
    ∀ (L : List Stat), (∀ s ∈ L, statValid (N + gs.length) s) →
    ∃ (gs' : List Gate) (st : Stat), CleanL N gs' ∧
      gs.length ≤ gs'.length ∧ gs'.length ≤ gs.length + (L.length - 1) ∧
      (L = [] → st = Sum.inl false) ∧
      statValid (N + gs'.length) st ∧
      (∀ x : Fin N → Bool, ∀ w < N + gs.length, vl gs' x w = vl gs x w) ∧
      (∀ x : Fin N → Bool, statVal (wiresFrom gs' (List.ofFn x)) st =
        (L.map (statVal (wiresFrom gs (List.ofFn x)))).any id) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨gs, Sum.inl false, hcl, le_rfl, by simp, fun _ => rfl, trivial, fun _ _ _ => rfl, fun _ => rfl⟩
  | cons s L ih =>
    intro hv
    obtain ⟨gs1, st1, hcl1, hge1, hlen1, hnil1, hv1, hag1, hev1⟩ :=
      ih (fun s' hs' => hv s' (List.mem_cons_of_mem _ hs'))
    have hvs : statValid (N + gs.length) s := hv s List.mem_cons_self
    cases s with
    | inl c =>
      cases c with
      | true =>
        refine ⟨gs, Sum.inl true, hcl, le_rfl, by omega, by simp, trivial, fun _ _ _ => rfl, fun x => ?_⟩
        simp [statVal]
      | false =>
        refine ⟨gs1, st1, hcl1, hge1, by cases L <;> simp at hlen1 ⊢ <;> omega, by simp, hv1, hag1, fun x => ?_⟩
        rw [hev1 x]; simp [statVal]
    | inr j =>
      have hj : j < N + gs.length := hvs
      cases st1 with
      | inl c =>
        cases c with
        | true =>
          refine ⟨gs, Sum.inl true, hcl, le_rfl, by omega, by simp, trivial, fun _ _ _ => rfl, fun x => ?_⟩
          have h1 := hev1 x; simp only [statVal] at h1 ⊢
          simp only [List.map_cons, List.any_cons, id, ← h1, Bool.or_true]
        | false =>
          refine ⟨gs, Sum.inr j, hcl, le_rfl, by omega, by simp, hj, fun _ _ _ => rfl, fun x => ?_⟩
          have h1 := hev1 x; simp only [statVal] at h1 ⊢
          simp only [List.map_cons, List.any_cons, id, ← h1, Bool.or_false]; rfl
      | inr j1 =>
        have hLpos : 1 ≤ L.length := by
          cases L with
          | nil => exact absurd (hnil1 rfl) (by simp)
          | cons _ _ => simp
        have hj1 : j1 < N + gs1.length := hv1
        have hj' : j < N + gs1.length := by omega
        refine ⟨gs1 ++ [⟨GateOp.or, [j, j1]⟩], Sum.inr (N + gs1.length),
          clean_append_or hcl1 hj' hj1, by simp; omega, by simp; omega, by simp,
          by simp [statValid],
          fun x w hw => by rw [vl_append_lt gs1 _ x w (by omega), hag1 x w hw], fun x => ?_⟩
        show vl (gs1 ++ [⟨GateOp.or, [j, j1]⟩]) x (N + gs1.length) = _
        rw [vl_append_or gs1 hcl1 j j1 hj' hj1 x, hag1 x j hj]
        have h1 := hev1 x
        simp only [List.map_cons, List.any_cons, id, statVal] at h1 ⊢
        rw [← h1]; rfl

theorem elimOv_finish_two {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} (gs : List Gate)
    (hcl : CleanL N gs) (y : Fin N) (v : Bool) (st1 st2 : Stat)
    (hv1 : statValid (N + gs.length) st1) (hv2 : statValid (N + gs.length) st2)
    (hnc1 : ∃ x x' : Fin N → Bool, F1 (Function.update x y v) ≠ F1 (Function.update x' y v))
    (hnc2 : ∃ x x' : Fin N → Bool, F2 (Function.update x y v) ≠ F2 (Function.update x' y v))
    (r : Stat) (hrv : statValid (N + gs.length) r)
    (hcov : ∀ x : Fin N → Bool, statVal (wiresFrom gs (List.ofFn x)) r = true →
      F1 (Function.update x y v) = true ∧ F2 (Function.update x y v) = true)
    (hgood : ∀ x : Fin N → Bool, statVal (wiresFrom gs (List.ofFn x)) r = false →
      statVal (wiresFrom gs (List.ofFn x)) st1 = F1 (Function.update x y v) ∧
      statVal (wiresFrom gs (List.ofFn x)) st2 = F2 (Function.update x y v)) :
    ∃ s' : ℕ, s' ≤ gs.length +
      (if r = Sum.inl false then 0 else
        (if st1 = Sum.inl false then 0 else 1) + (if st2 = Sum.inl false then 0 else 1)) ∧
      HasSize2 N (fun x => F1 (Function.update x y v)) (fun x => F2 (Function.update x y v)) s' := by
  cases r with
  | inl c =>
    cases c with
    | true =>
      exfalso; obtain ⟨x, x', hne⟩ := hnc1
      exact hne ((hcov x rfl).1.trans (hcov x' rfl).1.symm)
    | false =>
      have h1 : ∀ x : Fin N → Bool, statVal (wiresFrom gs (List.ofFn x)) st1 =
          F1 (Function.update x y v) := fun x => (hgood x rfl).1
      have h2 : ∀ x : Fin N → Bool, statVal (wiresFrom gs (List.ofFn x)) st2 =
          F2 (Function.update x y v) := fun x => (hgood x rfl).2
      cases st1 with
      | inl c =>
        exfalso; obtain ⟨x, x', hne⟩ := hnc1
        rw [← h1 x, ← h1 x'] at hne; exact hne rfl
      | inr j1 =>
        cases st2 with
        | inl c =>
          exfalso; obtain ⟨x, x', hne⟩ := hnc2
          rw [← h2 x, ← h2 x'] at hne; exact hne rfl
        | inr j2 =>
          refine ⟨gs.length, by simp, ⟨⟨gs, 0⟩, fun g hg => (clean_nok N gs hcl g hg).1,
            le_rfl, j1, j2, fun x => ⟨h1 x, h2 x⟩⟩⟩
  | inr jr =>
    have hjr : jr < N + gs.length := hrv
    have step1 : ∃ (gs1 : List Gate) (o1' : ℕ), CleanL N gs1 ∧ gs.length ≤ gs1.length ∧
        gs1.length ≤ gs.length + (if st1 = Sum.inl false then 0 else 1) ∧
        (∀ (x : Fin N → Bool) (w : ℕ), w < N + gs.length → vl gs1 x w = vl gs x w) ∧
        (∀ (x : Fin N → Bool), vl gs1 x o1' = F1 (Function.update x y v)) := by
      cases st1 with
      | inl c =>
        cases c with
        | true =>
          exfalso; obtain ⟨x, x', hne⟩ := hnc1
          have key : ∀ z, F1 (Function.update z y v) = true := fun z => by
            cases hz : vl gs z jr
            · exact (hgood z hz).1.symm
            · exact (hcov z hz).1
          exact hne (by rw [key x, key x'])
        | false =>
          refine ⟨gs, jr, hcl, le_rfl, by simp, fun _ _ _ => rfl, fun x => ?_⟩
          cases hx : vl gs x jr
          · exact (hgood x hx).1
          · exact (hcov x hx).1.symm
      | inr j1 =>
        have hj1 : j1 < N + gs.length := hv1
        refine ⟨gs ++ [⟨GateOp.or, [j1, jr]⟩], N + gs.length, clean_append_or hcl hj1 hjr,
          by simp, by simp, fun x w hw => vl_append_lt gs _ x w hw, fun x => ?_⟩
        rw [vl_append_or gs hcl j1 jr hj1 hjr x]
        cases hx : vl gs x jr
        · have h1 := (hgood x hx).1; change vl gs x j1 = _ at h1; rw [h1]; simp
        · rw [(hcov x hx).1]; simp
    obtain ⟨gs1, o1', hcl1, hge1, hle1, hag1, hev1⟩ := step1
    have ho1lt : o1' < N + gs1.length := out_lt_of_nc hev1 hnc1
    have step2 : ∃ (gs2 : List Gate) (o2' : ℕ), CleanL N gs2 ∧
        gs2.length ≤ gs1.length + (if st2 = Sum.inl false then 0 else 1) ∧
        (∀ (x : Fin N → Bool) (w : ℕ), w < N + gs1.length → vl gs2 x w = vl gs1 x w) ∧
        (∀ (x : Fin N → Bool), vl gs2 x o2' = F2 (Function.update x y v)) := by
      cases st2 with
      | inl c =>
        cases c with
        | true =>
          exfalso; obtain ⟨x, x', hne⟩ := hnc2
          have key : ∀ z, F2 (Function.update z y v) = true := fun z => by
            cases hz : vl gs z jr
            · exact (hgood z hz).2.symm
            · exact (hcov z hz).2
          exact hne (by rw [key x, key x'])
        | false =>
          refine ⟨gs1, jr, hcl1, by simp, fun _ _ _ => rfl, fun x => ?_⟩
          rw [hag1 x jr hjr]
          cases hx : vl gs x jr
          · exact (hgood x hx).2
          · exact (hcov x hx).2.symm
      | inr j2 =>
        have hj2 : j2 < N + gs.length := hv2
        refine ⟨gs1 ++ [⟨GateOp.or, [j2, jr]⟩], N + gs1.length,
          clean_append_or hcl1 (by omega) (by omega), by simp,
          fun x w hw => vl_append_lt gs1 _ x w hw, fun x => ?_⟩
        rw [vl_append_or gs1 hcl1 j2 jr (by omega) (by omega) x, hag1 x j2 hj2, hag1 x jr hjr]
        cases hx : vl gs x jr
        · have h2 := (hgood x hx).2; change vl gs x j2 = _ at h2; rw [h2]; simp
        · rw [(hcov x hx).2]; simp
    obtain ⟨gs2, o2', hcl2, hle2, hag2, hev2⟩ := step2
    refine ⟨gs2.length, ?_, ⟨⟨gs2, 0⟩, fun g hg => (clean_nok N gs2 hcl2 g hg).1, le_rfl,
      o1', o2', fun x => ⟨(hag2 x o1' ho1lt).trans (hev1 x), hev2 x⟩⟩⟩
    simp only [reduceCtorEq, ↓reduceIte]; omega

theorem restore_O (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs gs' : List Gate) (o1 o2 : ℕ)
    (y : Fin N) (v : Bool) (Oset : Finset ℕ) (hcl' : CleanL N gs')
    (hnc1 : ∃ x x' : Fin N → Bool, F1 (Function.update x y v) ≠ F1 (Function.update x' y v))
    (hnc2 : ∃ x x' : Fin N → Bool, F2 (Function.update x y v) ≠ F2 (Function.update x' y v))
    (hOlt : ∀ h ∈ Oset, h < N + gs'.length)
    (hOcov : ∀ h ∈ Oset, ∀ x : Fin N → Bool, vl gs' (Function.update x y v) h = true →
      F1 (Function.update x y v) = true ∧ F2 (Function.update x y v) = true)
    (hOeq : ∀ x : Fin N → Bool, (∀ h ∈ Oset, vl gs' (Function.update x y v) h = false) →
      vl gs' (Function.update x y v) o1 = F1 (Function.update x y v) ∧
      vl gs' (Function.update x y v) o2 = F2 (Function.update x y v))
    (E : Finset ℕ)
    (hE : ∀ p ∈ E, ∃ g, gs'[p]? = some g ∧ ∃ a ∈ g.inputs, a < N + p ∧
      ∃ c, (elimOv N (fun w => if w ∈ Oset then some false else none) gs'
        (initOv N y.val v (fun w => if w ∈ Oset then some false else none))).1.getD a
          (Sum.inl false) = Sum.inl c)
    (hlen : gs'.length = gs.length) :
    let ov := fun w => if w ∈ Oset then some false else none
    let acc := elimOv N ov gs' (initOv N y.val v ov)
    ∃ s' : ℕ, s' + E.card ≤ gs.length +
      (if Oset = ∅ then 0 else
        (Oset.card - 1) + (if acc.1.getD o1 (Sum.inl false) = Sum.inl false then 0 else 1) +
        (if acc.1.getD o2 (Sum.inl false) = Sum.inl false then 0 else 1)) ∧
      HasSize2 N (fun x => F1 (Function.update x y v)) (fun x => F2 (Function.update x y v)) s' := by
  classical
  set ov : ℕ → Option Bool := fun w => if w ∈ Oset then some false else none with hov
  set acc0 := initOv N y.val v ov with hacc0
  set acc := elimOv N ov gs' acc0 with hacc
  have hinv : ∀ x : Fin N → Bool,
      InvOv N ov (List.ofFn x) (wiresFrom gs' (List.ofFn (Function.update x y v))) acc :=
    fun x => invOv_elim N ov (List.ofFn x) (by simp) gs' _ acc0
      (fun g hg => (clean_nok N gs' hcl' g hg).1) (invOv_init N y v ov x)
  have hcl_acc : CleanL N acc.2.2 :=
    cleanOv_elim N ov gs' acc0 (fun g hg => (clean_nok N gs' hcl' g hg).1)
      (fun i => ((invOv_init N y v ov (fun _ => false)).2.2.1 i).1)
      (by intro p g hp; simp [hacc0, initOv] at hp)
  have hcnt := elimOv_count N ov acc0 gs' (clean_nok N gs' hcl') E (by
    intro p hp; obtain ⟨g, hg, a, ha, hlt, c, hc⟩ := hE p hp
    exact ⟨g, hg, a, ha, by simp [hacc0, initOv]; exact hlt, c, hc⟩)
  rw [← hacc] at hcnt
  simp only [hacc0, initOv, List.length_nil, zero_add] at hcnt
  have hvalid1 : statValid (N + acc.2.2.length) (acc.1.getD o1 (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2.1 o1).1
  have hvalid2 : statValid (N + acc.2.2.length) (acc.1.getD o2 (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2.1 o2).1
  set L : List Stat := Oset.toList.map fun h => acc.2.1.getD h (Sum.inl false) with hL
  have hLlen : L.length = Oset.card := by simp [hL]
  obtain ⟨gsR, r, hclR, hgeR, hleR, hnilR, hrv, hagR, hevR⟩ :=
    or_fold_stats acc.2.2 hcl_acc L (fun s hs => by
      obtain ⟨h, _, rfl⟩ := List.mem_map.1 hs
      exact ((hinv (fun _ => false)).2.2.1 h).2)
  have hgood_iff : ∀ x : Fin N → Bool,
      GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v)))
        (wiresFrom gs' (List.ofFn (Function.update x y v))).length ↔
      ∀ h ∈ Oset, vl gs' (Function.update x y v) h = false := by
    intro x
    have hwl : (wiresFrom gs' (List.ofFn (Function.update x y v))).length = N + gs'.length := by
      rw [length_wiresFrom]; simp
    constructor
    · intro hg h hh
      exact hg h (by rw [hwl]; exact hOlt h hh) false (by simp [hov, hh])
    · intro hall j hj b hjb
      simp only [hov] at hjb
      split_ifs at hjb with hjO
      cases hjb; exact hall j hjO
  have hr_cov : ∀ x : Fin N → Bool, statVal (wiresFrom gsR (List.ofFn x)) r = true →
      F1 (Function.update x y v) = true ∧ F2 (Function.update x y v) = true := by
    intro x hrx
    rw [hevR x, List.any_eq_true] at hrx
    by_cases hall : ∀ h ∈ Oset, vl gs' (Function.update x y v) h = false
    · exfalso
      obtain ⟨b, hb, hbt⟩ := hrx
      simp only [id_eq] at hbt; subst hbt
      obtain ⟨s, hs, hst⟩ := List.mem_map.1 hb
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hs
      have hhO : h ∈ Oset := Finset.mem_toList.1 hh
      have hgu : GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v))) h := fun j _ b' hb' => by
        simp only [hov] at hb'; split_ifs at hb' with hjO
        cases hb'; exact hall j hjO
      have hre := (hinv x).2.2.2.1 h hgu
      rw [hst] at hre
      have := hall h hhO; unfold vl at this; rw [this] at hre; cases hre
    · push Not at hall
      obtain ⟨h, hh, hv⟩ := hall
      exact hOcov h hh x (by simpa using hv)
  have hr_good : ∀ x : Fin N → Bool, statVal (wiresFrom gsR (List.ofFn x)) r = false →
      statVal (wiresFrom gsR (List.ofFn x)) (acc.1.getD o1 (Sum.inl false)) = F1 (Function.update x y v) ∧
      statVal (wiresFrom gsR (List.ofFn x)) (acc.1.getD o2 (Sum.inl false)) = F2 (Function.update x y v) := by
    intro x hrx
    have hall : ∀ h ∈ Oset, vl gs' (Function.update x y v) h = false := by
      by_contra hno; push Not at hno
      have hex : ∃ w, w ∈ Oset ∧ vl gs' (Function.update x y v) w = true := by
        obtain ⟨w, hw, hv⟩ := hno; exact ⟨w, hw, by simpa using hv⟩
      set wstar := Nat.find hex with hwstar
      obtain ⟨hwO, hwT⟩ := Nat.find_spec hex
      have hgu : GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v))) wstar := by
        intro j hj b hb
        simp only [hov] at hb; split_ifs at hb with hjO
        cases hb
        have hnm := Nat.find_min hex hj
        by_contra hne; exact hnm ⟨hjO, by unfold vl; simpa using hne⟩
      have hre := (hinv x).2.2.2.1 wstar hgu
      have hmem : statVal (wiresFrom acc.2.2 (List.ofFn x)) (acc.2.1.getD wstar (Sum.inl false)) ∈
          L.map (statVal (wiresFrom acc.2.2 (List.ofFn x))) :=
        List.mem_map.2 ⟨_, List.mem_map.2 ⟨wstar, Finset.mem_toList.2 hwO, rfl⟩, rfl⟩
      rw [hevR x] at hrx
      have hfalse := List.any_eq_false.1 hrx _ hmem
      simp only [id_eq, hre] at hfalse
      exact hfalse hwT
    have hga := (hgood_iff x).2 hall
    have he1 := (hinv x).2.2.2.2 hga o1
    have he2 := (hinv x).2.2.2.2 hga o2
    have hstR : ∀ s, statValid (N + acc.2.2.length) s →
        statVal (wiresFrom gsR (List.ofFn x)) s = statVal (wiresFrom acc.2.2 (List.ofFn x)) s := by
      intro s hs; cases s with
      | inl _ => rfl
      | inr j => exact hagR x j hs
    rw [hstR _ hvalid1, he1, hstR _ hvalid2, he2]
    exact hOeq x hall
  obtain ⟨s', hs', hsz2⟩ := elimOv_finish_two gsR hclR y v
    (acc.1.getD o1 (Sum.inl false)) (acc.1.getD o2 (Sum.inl false))
    (statValid_mono (by omega) _ hvalid1) (statValid_mono (by omega) _ hvalid2)
    hnc1 hnc2 r hrv hr_cov hr_good
  refine ⟨s', ?_, hsz2⟩
  rw [← hacc0, ← hacc]
  by_cases hOe : Oset = ∅
  · have hLnil : L = [] := by simp [hL, hOe]
    have hrnil : r = Sum.inl false := hnilR hLnil
    rw [ite_eq_left_iff.2 (fun hc => absurd hOe hc)]
    rw [ite_eq_left_iff.2 (fun hc => absurd hrnil hc)] at hs'
    simp only [hLnil, List.length_nil, Nat.zero_sub, add_zero] at hleR
    omega
  · rw [ite_eq_right_iff.2 (fun hc => absurd hc hOe)]
    split_ifs at hs' ⊢ <;> omega

theorem restore_A1 (N : ℕ) (F1 F2 : (Fin N → Bool) → Bool) (gs gs' : List Gate) (o1 o2 : ℕ)
    (y : Fin N) (v : Bool) (hA : ℕ) (hcl' : CleanL N gs')
    (hnc1 : ∃ x x' : Fin N → Bool, F1 (Function.update x y v) ≠ F1 (Function.update x' y v))
    (hnc2 : ∃ x x' : Fin N → Bool, F2 (Function.update x y v) ≠ F2 (Function.update x' y v))
    (hAlt : hA < N + gs'.length)
    (hAcov : ∀ x : Fin N → Bool, vl gs' (Function.update x y v) hA = false →
      F1 (Function.update x y v) = true ∧ F2 (Function.update x y v) = true)
    (hAeq : ∀ x : Fin N → Bool, vl gs' (Function.update x y v) hA = true →
      vl gs' (Function.update x y v) o1 = F1 (Function.update x y v) ∧
      vl gs' (Function.update x y v) o2 = F2 (Function.update x y v))
    (E : Finset ℕ)
    (hE : ∀ p ∈ E, ∃ g, gs'[p]? = some g ∧ ∃ a ∈ g.inputs, a < N + p ∧
      ∃ c, (elimOv N (fun w => if w = hA then some true else none) gs'
        (initOv N y.val v (fun w => if w = hA then some true else none))).1.getD a
          (Sum.inl false) = Sum.inl c)
    (hlen : gs'.length = gs.length) :
    let ov := fun w => if w = hA then some true else none
    let acc := elimOv N ov gs' (initOv N y.val v ov)
    ∃ s' : ℕ, s' + E.card ≤ gs.length + 1 +
      (if acc.1.getD o1 (Sum.inl false) = Sum.inl false then 0 else 1) +
      (if acc.1.getD o2 (Sum.inl false) = Sum.inl false then 0 else 1) ∧
      HasSize2 N (fun x => F1 (Function.update x y v)) (fun x => F2 (Function.update x y v)) s' := by
  set ov : ℕ → Option Bool := fun w => if w = hA then some true else none with hov
  set acc0 := initOv N y.val v ov with hacc0
  set acc := elimOv N ov gs' acc0 with hacc
  have hinv : ∀ x : Fin N → Bool,
      InvOv N ov (List.ofFn x) (wiresFrom gs' (List.ofFn (Function.update x y v))) acc :=
    fun x => invOv_elim N ov (List.ofFn x) (by simp) gs' _ acc0
      (fun g hg => (clean_nok N gs' hcl' g hg).1) (invOv_init N y v ov x)
  have hcl_acc : CleanL N acc.2.2 :=
    cleanOv_elim N ov gs' acc0 (fun g hg => (clean_nok N gs' hcl' g hg).1)
      (fun i => ((invOv_init N y v ov (fun _ => false)).2.2.1 i).1)
      (by intro p g hp; simp [hacc0, initOv] at hp)
  have hcnt := elimOv_count N ov acc0 gs' (clean_nok N gs' hcl') E (by
    intro p hp; obtain ⟨g, hg, a, ha, hlt, c, hc⟩ := hE p hp
    exact ⟨g, hg, a, ha, by simp [hacc0, initOv]; exact hlt, c, hc⟩)
  rw [← hacc] at hcnt
  simp only [hacc0, initOv, List.length_nil, zero_add] at hcnt
  have hvalid1 : statValid (N + acc.2.2.length) (acc.1.getD o1 (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2.1 o1).1
  have hvalid2 : statValid (N + acc.2.2.length) (acc.1.getD o2 (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2.1 o2).1
  have hvalidA : statValid (N + acc.2.2.length) (acc.2.1.getD hA (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2.1 hA).2
  have hrealA : ∀ x : Fin N → Bool,
      statVal (wiresFrom acc.2.2 (List.ofFn x)) (acc.2.1.getD hA (Sum.inl false)) =
        vl gs' (Function.update x y v) hA := by
    intro x
    refine (hinv x).2.2.2.1 hA ?_
    intro j hj b hb
    simp only [hov] at hb; split_ifs at hb with hjeq
    omega
  have hgoodA : ∀ x : Fin N → Bool, vl gs' (Function.update x y v) hA = true →
      statVal (wiresFrom acc.2.2 (List.ofFn x)) (acc.1.getD o1 (Sum.inl false)) = F1 (Function.update x y v) ∧
      statVal (wiresFrom acc.2.2 (List.ofFn x)) (acc.1.getD o2 (Sum.inl false)) = F2 (Function.update x y v) := by
    intro x hx
    have hgu : GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v)))
        (wiresFrom gs' (List.ofFn (Function.update x y v))).length := by
      intro j _ b hb; simp only [hov] at hb; split_ifs at hb with hjeq
      subst hjeq; cases hb; exact hx
    rw [(hinv x).2.2.2.2 hgu o1, (hinv x).2.2.2.2 hgu o2]
    exact hAeq x hx
  cases hstA : acc.2.1.getD hA (Sum.inl false) with
  | inl c =>
    cases c with
    | false =>
      exfalso; obtain ⟨x, x', hne⟩ := hnc1
      have key : ∀ z, F1 (Function.update z y v) = true := fun z =>
        (hAcov z (by have := hrealA z; rw [hstA] at this; exact this.symm)).1
      exact hne (by rw [key x, key x'])
    | true =>
      obtain ⟨s', hs', hsz2⟩ := elimOv_finish_two acc.2.2 hcl_acc y v
        (acc.1.getD o1 (Sum.inl false)) (acc.1.getD o2 (Sum.inl false))
        hvalid1 hvalid2 hnc1 hnc2 (Sum.inl false) trivial
        (fun _ h => by cases h)
        (fun x _ => hgoodA x (by have := hrealA x; rw [hstA] at this; exact this.symm))
      simp only [↓reduceIte, add_zero] at hs'
      refine ⟨s', ?_, hsz2⟩
      rw [← hacc0, ← hacc]; omega
  | inr jA =>
    rw [hstA] at hvalidA
    set gsN := acc.2.2 ++ [⟨GateOp.not, [jA]⟩] with hgsN
    have hclN : CleanL N gsN := clean_append_not hcl_acc hvalidA
    have hlenN : gsN.length = acc.2.2.length + 1 := by simp [hgsN]
    have hvalN : ∀ x : Fin N → Bool, vl gsN x (N + acc.2.2.length) = !vl gs' (Function.update x y v) hA := by
      intro x; rw [hgsN, vl_append_not acc.2.2 hcl_acc jA hvalidA x]
      have := hrealA x; rw [hstA] at this; rw [← this]; rfl
    have hstN : ∀ (x : Fin N → Bool) s, statValid (N + acc.2.2.length) s →
        statVal (wiresFrom gsN (List.ofFn x)) s = statVal (wiresFrom acc.2.2 (List.ofFn x)) s := by
      intro x s hs; cases s with
      | inl _ => rfl
      | inr j => exact vl_append_lt acc.2.2 _ x j hs
    obtain ⟨s', hs', hsz2⟩ := elimOv_finish_two gsN hclN y v
      (acc.1.getD o1 (Sum.inl false)) (acc.1.getD o2 (Sum.inl false))
      (statValid_mono (by omega) _ hvalid1) (statValid_mono (by omega) _ hvalid2)
      hnc1 hnc2 (Sum.inr (N + acc.2.2.length)) (by simp [statValid, hlenN])
      (fun x hx => hAcov x (by
        have := hvalN x; simp only [statVal] at hx; unfold vl at this ⊢; rw [this] at hx; simpa using hx))
      (fun x hx => by
        rw [hstN x _ hvalid1, hstN x _ hvalid2]
        exact hgoodA x (by
          have := hvalN x; simp only [statVal] at hx; unfold vl at this ⊢; rw [this] at hx; simpa using hx))
    simp only [reduceCtorEq, ↓reduceIte] at hs'
    refine ⟨s', ?_, hsz2⟩
    rw [← hacc0, ← hacc]; omega

theorem card_D_ge_two {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) (hne : D.Nonempty) : ∃ a b : Fin N, a ∈ D ∧ b ∈ D ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := hne
  by_contra hno; push Not at hno
  have hall : ∀ y ∈ D, y = a := fun y hy => (hno a y ha hy).symm
  have hz_eq : ∀ x : Fin N → Bool, zeroOn D x = Function.update x a false := by
    intro x; funext i; unfold zeroOn
    by_cases hi : i = a
    · subst hi; simp [ha]
    · have hiD : i ∉ D := fun h => hi (hall i h)
      simp [hiD, Function.update_of_ne hi]
  have htrue : ∀ x : Fin N → Bool, F (Function.update x a true) = true := by
    intro x
    cases h0 : F (zeroOn D x) with
    | true => exact H.mono (Function.update x a true) (by
        have e : zeroOn D (Function.update x a true) = zeroOn D x := by
          funext i; unfold zeroOn
          split_ifs with hi
          · rfl
          · exact Function.update_of_ne (fun e => hi (by rw [e]; exact ha)) _ _
        rw [e]; exact h0)
    | false =>
      obtain ⟨x', hx'out, hx'a, -, hF1⟩ := H.win a ha x h0
      have e : Function.update x' a true = Function.update x a true := by
        funext i
        by_cases hi : i = a
        · subst hi; simp
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]
          exact hx'out i (fun h => hi (hall i h))
      rw [← e]; exact hF1
  obtain ⟨x, x', hne'⟩ := H.nc a ha true
  exact hne' (by rw [htrue x, htrue x'])

def suppD {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (w : ℕ) : Finset (Fin N) :=
  (suppsFrom gs (inputSupps N)).getD w ∅ ∩ D

theorem dfree_iff_suppD_empty {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {w : ℕ} :
    DFree D gs w ↔ suppD D gs w = ∅ := by
  unfold DFree suppD
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h y hy; exact h y (Finset.mem_inter.1 hy).2 (Finset.mem_inter.1 hy).1
  · intro h y hy hm; exact h y (Finset.mem_inter.2 ⟨hm, hy⟩)

theorem suppD_input {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (w : ℕ) (hw : w < N) :
    suppD D gs w = if (⟨w, hw⟩ : Fin N) ∈ D then {⟨w, hw⟩} else ∅ := by
  unfold suppD
  rw [front_supp_input gs w hw]
  ext i
  split_ifs with h
  · simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun ⟨h1, _⟩ => h1, fun h1 => ⟨h1, h1 ▸ h⟩⟩
  · simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, hi⟩; exact h hi

theorem suppD_gate {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (hcl : CleanL N gs)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (i : Fin N) :
    i ∈ suppD D gs (N + p) ↔ ∃ a ∈ g.inputs, i ∈ suppD D gs a := by
  simp only [suppD, Finset.mem_inter, front_supp_gate gs hcl p g hp i]
  constructor
  · rintro ⟨⟨a, ha, hia⟩, hiD⟩; exact ⟨a, ha, hia, hiD⟩
  · rintro ⟨a, ha, hia, hiD⟩; exact ⟨⟨a, ha, hia⟩, hiD⟩

theorem first_multi_D {n : ℕ} {F1 F2 : (Fin (n + 1) → Bool) → Bool}
    {D : Finset (Fin (n + 1))} {gs : List Gate} {o1 o2 : ℕ}
    (H1 : DeepHyp' F1 D) (hne : D.Nonempty) (L : Least2 (n + 1) F1 F2 gs o1 o2) :
    ∃ (Q : ℕ) (gQ : Gate) (u v : ℕ) (a b : Fin (n + 1)),
      gs[Q]? = some gQ ∧ (gQ.op = GateOp.and ∨ gQ.op = GateOp.or) ∧
      gQ.inputs = [u, v] ∧ u < n + 1 + Q ∧ v < n + 1 + Q ∧
      a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
      suppD D gs u = {a} ∧ suppD D gs v = {b} ∧
      (∀ w < n + 1 + Q, (suppD D gs w).card ≤ 1) := by
  classical
  obtain ⟨a0, b0, ha0, hb0, hab0⟩ := card_D_ge_two H1 hne
  have hex : ∃ q, 2 ≤ (suppD D gs (n + 1 + q)).card := by
    have hmo1a : a0 ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 ha0, ha0⟩
    have hmo1b : b0 ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 hb0, hb0⟩
    have hcard : 2 ≤ (suppD D gs o1).card := by
      have hsub : ({a0, b0} : Finset (Fin (n + 1))) ⊆ suppD D gs o1 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hab0] at this
    by_cases ho1n : o1 < n + 1
    · rw [suppD_input D gs o1 ho1n] at hcard
      split_ifs at hcard <;> simp at hcard
    · exact ⟨o1 - (n + 1), by rwa [show n + 1 + (o1 - (n + 1)) = o1 by omega]⟩
  set Q := Nat.find hex with hQ
  have hQcard : 2 ≤ (suppD D gs (n + 1 + Q)).card := Nat.find_spec hex
  have hQmin : ∀ w < n + 1 + Q, (suppD D gs w).card ≤ 1 := by
    intro w hw
    by_cases hwn : w < n + 1
    · rw [suppD_input D gs w hwn]; split_ifs <;> simp
    · have hlt : w - (n + 1) < Q := by omega
      have hnm := Nat.find_min hex hlt
      rw [show n + 1 + (w - (n + 1)) = w by omega] at hnm
      omega
  cases hgQ : gs[Q]? with
  | none =>
    have hlen : gs.length ≤ Q := List.getElem?_eq_none_iff.1 hgQ
    have : suppD D gs (n + 1 + Q) = ∅ := by
      unfold suppD; rw [front_supp_beyond gs _ (by omega)]; simp
    rw [this] at hQcard; simp at hQcard
  | some gQ =>
    rcases L.hcl Q gQ hgQ with ⟨hop, j, hj, hin⟩ | ⟨hop, u, v, hu, hv, hin⟩
    · exfalso
      have hsub : suppD D gs (n + 1 + Q) ⊆ suppD D gs j := by
        intro i hi
        obtain ⟨a, ha, hia⟩ := (suppD_gate D gs L.hcl Q gQ hgQ i).1 hi
        rw [hin, List.mem_singleton] at ha; subst ha; exact hia
      have := Finset.card_le_card hsub
      have := hQmin j hj; omega
    · have hsub : suppD D gs (n + 1 + Q) ⊆ suppD D gs u ∪ suppD D gs v := by
        intro i hi
        obtain ⟨x, hx, hix⟩ := (suppD_gate D gs L.hcl Q gQ hgQ i).1 hi
        rw [hin] at hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_union_left _ hix
        · exact Finset.mem_union_right _ hix
      have hu1 := hQmin u hu
      have hv1 := hQmin v hv
      have hunion := Finset.card_union_le (suppD D gs u) (suppD D gs v)
      have hcle := Finset.card_le_card hsub
      have huc : (suppD D gs u).card = 1 := by omega
      have hvc : (suppD D gs v).card = 1 := by omega
      obtain ⟨a, haeq⟩ := Finset.card_eq_one.1 huc
      obtain ⟨b, hbeq⟩ := Finset.card_eq_one.1 hvc
      have haD : a ∈ D := (Finset.mem_inter.1 (haeq ▸ Finset.mem_singleton_self a)).2
      have hbD : b ∈ D := (Finset.mem_inter.1 (hbeq ▸ Finset.mem_singleton_self b)).2
      have hab : a ≠ b := by
        intro e; subst e
        rw [haeq, hbeq, Finset.union_idempotent] at hsub
        have := Finset.card_le_card hsub; simp at this; omega
      exact ⟨Q, gQ, u, v, a, b, hgQ, hop, hin, hu, hv, haD, hbD, hab, haeq, hbeq, hQmin⟩

def IsChain (N : ℕ) (D : Finset (Fin N)) (gs : List Gate) (a : Fin N) : List ℕ → ℕ → Prop
  | [], w => w = a.val
  | p :: ps, w => w = N + p ∧ ∃ u g, IsChain N D gs a ps u ∧
      gs[p]? = some g ∧
      (∀ r, Reads gs r u → r = p) ∧
      ((g.op = GateOp.not ∧ g.inputs = [u]) ∨
       ∃ h, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
         (g.inputs = [u, h] ∨ g.inputs = [h, u]) ∧ DFree D gs h)

def ChainWires (N : ℕ) (a : Fin N) (ps : List ℕ) (w : ℕ) : Prop :=
  w = a.val ∨ ∃ q ∈ ps, w = N + q

theorem chain_end_mem {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N} :
    ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w → ChainWires N a ps w
  | [], _, h => Or.inl h
  | p :: _, _, h => Or.inr ⟨p, List.mem_cons_self, h.1⟩

theorem chain_lt {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) : ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    ∀ w', ChainWires N a ps w' → w' ≤ w := by
  intro ps
  induction ps with
  | nil =>
    intro w h w' hw'
    change w = a.val at h
    rcases hw' with rfl | ⟨_, hm, _⟩
    · omega
    · simp at hm
  | cons p ps ih =>
    intro w h w' hw'
    obtain ⟨rfl, u, g, hch, hgp, _, hstep⟩ := h
    have hu_lt : u < N + p := by
      rcases hstep with ⟨_, hin⟩ | ⟨h, _, hin, _⟩
      · exact (hcl p g hgp).lt u (by rw [hin]; simp)
      · exact (hcl p g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
    rcases hw' with rfl | ⟨q, hq, rfl⟩
    · have := ih hch a.val (Or.inl rfl); omega
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact le_rfl
      · have := ih hch (N + q) (Or.inr ⟨q, hq', rfl⟩); omega

theorem chain_nodup {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) : ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w → ps.Nodup := by
  intro ps
  induction ps with
  | nil => intro _ _; exact List.nodup_nil
  | cons p ps ih =>
    intro w h
    obtain ⟨rfl, u, g, hch, hgp, _, hstep⟩ := h
    have hu_lt : u < N + p := by
      rcases hstep with ⟨_, hin⟩ | ⟨h, _, hin, _⟩
      · exact (hcl p g hgp).lt u (by rw [hin]; simp)
      · exact (hcl p g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
    refine List.nodup_cons.2 ⟨fun hm => ?_, ih hch⟩
    have := chain_lt hcl hch (N + p) (Or.inr ⟨p, hm, rfl⟩); omega

theorem chain_suppD {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) (haD : a ∈ D) : ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    suppD D gs w = {a} := by
  intro ps
  induction ps with
  | nil =>
    intro w h; change w = a.val at h; rw [h, suppD_input D gs a.val a.isLt]; simp [haD]
  | cons p ps ih =>
    intro w h
    obtain ⟨rfl, u, g, hch, hgp, _, hstep⟩ := h
    have ihu := ih hch
    ext i
    rw [suppD_gate D gs hcl p g hgp i]
    rcases hstep with ⟨_, hin⟩ | ⟨h, _, hin, hfree⟩
    · rw [hin]; simp [ihu]
    · have hf : suppD D gs h = ∅ := dfree_iff_suppD_empty.1 hfree
      rcases hin with hin | hin <;> rw [hin] <;> simp [ihu, hf]

theorem chain_only_read {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) : ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    ∀ w', ChainWires N a ps w' → w' ≠ w →
      ∀ r, Reads gs r w' → ∃ q ∈ ps, r = q ∧ N + q ≤ w := by
  intro ps
  induction ps with
  | nil =>
    intro w h w' hw' hne
    change w = a.val at h
    rcases hw' with rfl | ⟨_, hm, _⟩
    · exact absurd h.symm hne
    · simp at hm
  | cons p ps ih =>
    intro w h w' hw' hne r hr
    obtain ⟨rfl, u, g, hch, hgp, honly, hstep⟩ := h
    by_cases hwu : w' = u
    · subst hwu
      have := honly r hr
      exact ⟨p, List.mem_cons_self, this, le_rfl⟩
    · have hw'in : ChainWires N a ps w' := by
        rcases hw' with rfl | ⟨q, hq, rfl⟩
        · exact Or.inl rfl
        · rcases List.mem_cons.1 hq with rfl | hq'
          · exact absurd rfl hne
          · exact Or.inr ⟨q, hq', rfl⟩
      obtain ⟨q, hq, hrq, hle⟩ := ih hch w' hw'in hwu r hr
      have hu_lt : u < N + p := by
        rcases hstep with ⟨_, hin⟩ | ⟨h, _, hin, _⟩
        · exact (hcl p g hgp).lt u (by rw [hin]; simp)
        · exact (hcl p g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
      exact ⟨q, List.mem_cons_of_mem _ hq, hrq, by omega⟩

theorem chain_win_core {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o : ℕ} {a : Fin N} (H : DeepHyp' F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (haD : a ∈ D)
    {ps : List ℕ} {w : ℕ} (hch : IsChain N D gs a ps w)
    (p : ℕ) (g : Gate) (h : ℕ) (hp : gs[p]? = some g)
    (honly : ∀ r, Reads gs r w → r = p)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [w, h] ∨ g.inputs = [h, w]) (hfree : DFree D gs h) :
    ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
    exfalso
    have hz : F (zeroOn D x) = false := by
      cases e : F (zeroOn D x) with
      | false => rfl
      | true => rw [H.mono x e] at hFx; cases hFx
    obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win a haD x hz
    have hagr : ∀ i, i ∉ D → x i = Function.update x' a true i := by
      intro i hi; have hia : i ≠ a := fun e => hi (e ▸ haD)
      rw [Function.update_of_ne hia, hx'D i hi]
    have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
    have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
    have hc1 : vl gs x' (N + p) = fixBit g :=
      vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hfree x x' hagr']; exact hx)
    have hc2 : vl gs (Function.update x' a true) (N + p) = fixBit g :=
      vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hfree x _ hagr]; exact hx)
    have hBo : ¬ ChainWires N a ps o := by
      intro hmo
      obtain ⟨a1, b1, ha1, hb1, hab1⟩ := card_D_ge_two H ⟨a, haD⟩
      have hne_a : ∃ b ∈ D, b ≠ a := by
        by_cases h1 : a1 = a
        · exact ⟨b1, hb1, by rw [← h1]; exact Ne.symm hab1⟩
        · exact ⟨a1, ha1, h1⟩
      obtain ⟨b, hbD, hba⟩ := hne_a
      have hb_supp : b ∈ suppD D gs o := Finset.mem_inter.2 ⟨deepHyp'_supp H hev hbD, hbD⟩
      have ho_supp : suppD D gs o = {a} := by
        rcases hmo with rfl | ⟨q, hq, rfl⟩
        · rw [suppD_input D gs a.val a.isLt]; simp [haD]
        · have : ∀ {ps' : List ℕ} {w' : ℕ}, IsChain N D gs a ps' w' →
              ∀ q' ∈ ps', suppD D gs (N + q') = {a} := by
            intro ps'; induction ps' with
            | nil => intro _ _ _ hm; simp at hm
            | cons q0 ps0 ih =>
              intro w0 h0 q' hq'
              rcases List.mem_cons.1 hq' with rfl | hq''
              · rw [← h0.1]; exact chain_suppD hcl haD h0
              · obtain ⟨_, u0, _, hch0, _⟩ := h0
                exact ih hch0 q' hq''
          exact this hch q hq
      rw [ho_supp, Finset.mem_singleton] at hb_supp
      exact hba hb_supp
    have key := agree_B gs hcl x' (Function.update x' a true) (ChainWires N a ps) (o + 1)
      (by
        intro j hj hB
        rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
        have hne : (⟨j, hj⟩ : Fin N) ≠ a := fun e => hB (Or.inl (by rw [← e]))
        rw [Function.update_of_ne hne])
      (by
        intro q g' hq _ hBq hBa _
        obtain ⟨u0, hu0, hBu0⟩ := hBa
        have hR : Reads gs q u0 := ⟨g', hq, hu0⟩
        by_cases huw : u0 = w
        · subst huw
          have hqp : q = p := honly q hR
          rw [hqp, hc1, hc2]
        · exfalso
          obtain ⟨q', hq', hqq', _⟩ := chain_only_read hcl hch u0 hBu0 huw q hR
          exact hBq (Or.inr ⟨q', hq', by rw [hqq']⟩))
      o (by omega) hBo
    rw [hev, hev, hF0, hF1] at key
    cases key

theorem chain_eval {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) :
    ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    ∃ c : Bool, ∀ x : Fin N → Bool,
      (∀ p ∈ ps, ∀ g, gs[p]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ h ∈ g.inputs, DFree D gs h → vl gs x h ≠ fixBit g) →
      vl gs x w = xor (x a) c := by
  intro ps
  induction ps with
  | nil =>
    intro w h; change w = a.val at h
    exact ⟨false, fun x _ => by rw [h, vl_input gs x a.val a.isLt]; simp⟩
  | cons p ps ih =>
    intro w h
    obtain ⟨rfl, u, g, hch, hgp, _, hstep⟩ := h
    obtain ⟨c, hc⟩ := ih hch
    rcases hstep with ⟨hop, hin⟩ | ⟨h, hop, hin, hfree⟩
    · refine ⟨!c, fun x hx => ?_⟩
      have hxu := hc x (fun q hq => hx q (List.mem_cons_of_mem _ hq))
      rw [vl_not gs hcl x p g hgp u hop hin, hxu]
      cases x a <;> cases c <;> rfl
    · refine ⟨c, fun x hx => ?_⟩
      have hxu := hc x (fun q hq => hx q (List.mem_cons_of_mem _ hq))
      have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
      have hne := hx p List.mem_cons_self g hgp hop h hhmem hfree
      rcases hop with hop | hop
      · have hht : vl gs x h = true := by
          have : fixBit g = false := by simp [fixBit, hop]
          rw [this] at hne; simpa using hne
        rw [(vl_bin gs hcl x p u h g hgp hin).2 hop, hht, Bool.and_true, hxu]
      · have hhf : vl gs x h = false := by
          have : fixBit g = true := by simp [fixBit, hop]
          rw [this] at hne; simpa using hne
        rw [(vl_bin gs hcl x p u h g hgp hin).1 hop, hhf, Bool.or_false, hxu]

theorem chain_win_all {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o : ℕ} {a : Fin N} (H : DeepHyp' F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (haD : a ∈ D) :
    ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    ∀ p ∈ ps, ∀ g, gs[p]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ h ∈ g.inputs, DFree D gs h → ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  intro ps
  induction ps with
  | nil => intro _ _ p hp; simp at hp
  | cons p0 ps ih =>
    intro w hchain p hp g hg hop h hh hfree x hx
    obtain ⟨rfl, u0, g0, hch0, hgp0, honly0, hstep0⟩ := hchain
    rcases List.mem_cons.1 hp with rfl | hp'
    · rw [hgp0] at hg; cases hg
      rcases hstep0 with ⟨hnot, _⟩ | ⟨h0, _, hin0, _⟩
      · rcases hop with h1 | h1 <;> rw [h1] at hnot <;> cases hnot
      · have hheq : h = h0 := by
          rcases hin0 with e | e <;> rw [e] at hh <;> simp at hh
          · rcases hh with rfl | rfl
            · exfalso
              have hsu := chain_suppD hcl haD hch0
              have := dfree_iff_suppD_empty.1 hfree
              rw [hsu] at this; exact Finset.singleton_ne_empty a this
            · rfl
          · rcases hh with rfl | rfl
            · rfl
            · exfalso
              have hsu := chain_suppD hcl haD hch0
              have := dfree_iff_suppD_empty.1 hfree
              rw [hsu] at this; exact Finset.singleton_ne_empty a this
        subst hheq
        exact chain_win_core H hcl hev haD hch0 p g h hgp0 honly0 hop hin0 hfree x hx
    · exact ih hch0 p hp' g hg hop h hh hfree x hx

theorem chain_all_supp {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    (hcl : CleanL N gs) {ps : List ℕ} {u p : ℕ}
    (hch : IsChain N D gs a ps u) (honly : ∀ r, Reads gs r u → r = p) :
    ∀ w, w < N + p → a ∈ suppD D gs w → ChainWires N a ps w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwp haw
    by_cases hwn : w < N
    · rw [suppD_input D gs w hwn] at haw
      split_ifs at haw with hmem
      · left
        have ea : a = ⟨w, hwn⟩ := Finset.mem_singleton.1 haw
        rw [ea]
      · simp at haw
    · obtain ⟨q, rfl⟩ : ∃ q, w = N + q := ⟨w - N, by omega⟩
      cases hq : gs[q]? with
      | none =>
        have hlen : gs.length ≤ q := List.getElem?_eq_none_iff.1 hq
        have : suppD D gs (N + q) = ∅ := by
          unfold suppD; rw [front_supp_beyond gs _ (by omega)]; simp
        rw [this] at haw; simp at haw
      | some g =>
        obtain ⟨k, hk_in, hak⟩ := (suppD_gate D gs hcl q g hq a).1 haw
        have hk_lt : k < N + q := (hcl q g hq).lt k hk_in
        have hkB : ChainWires N a ps k := ih k hk_lt (by omega) hak
        have hR : Reads gs q k := ⟨g, hq, hk_in⟩
        by_cases hku : k = u
        · subst hku
          have hqp : q = p := honly q hR
          omega
        · obtain ⟨q', hq', hqq', _⟩ := chain_only_read hcl hch k hkB hku q hR
          exact Or.inr ⟨q', hq', by rw [hqq']⟩

theorem chain_build {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o1 o2 : ℕ} {a : Fin N} {Q : ℕ}
    (L : Least2 N F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y)
    (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y)
    (haD : a ∈ D)
    (hQmin : ∀ w < N + Q, (suppD D gs w).card ≤ 1) :
    ∀ w, w < N + Q → suppD D gs w = {a} →
    (∃ (ps : List ℕ) (w' : ℕ), IsChain N D gs a ps w' ∧ w' < w ∧
      ∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w' ∧ Reads gs T2 w') ∨
    (∃ ps : List ℕ, IsChain N D gs a ps w) := by
  have hcl := L.hcl
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hsw
    by_cases hwn : w < N
    · right
      rw [suppD_input D gs w hwn] at hsw
      split_ifs at hsw with hmem
      · have ea : (⟨w, hwn⟩ : Fin N) = a := Finset.singleton_injective hsw
        exact ⟨[], by rw [← ea]; rfl⟩
      · exact absurd hsw.symm (Finset.singleton_ne_empty a)
    · obtain ⟨p, rfl⟩ : ∃ p, w = N + p := ⟨w - N, by omega⟩
      cases hgp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hgp
        have : suppD D gs (N + p) = ∅ := by
          unfold suppD; rw [front_supp_beyond gs _ (by omega)]; simp
        rw [this] at hsw; exact absurd hsw.symm (Finset.singleton_ne_empty a)
      | some g =>
        have ha_mem : a ∈ suppD D gs (N + p) := by rw [hsw]; exact Finset.mem_singleton_self a
        obtain ⟨u, hu_in, hau⟩ := (suppD_gate D gs hcl p g hgp a).1 ha_mem
        have hu_lt : u < N + p := (hcl p g hgp).lt u hu_in
        have hsu : suppD D gs u = {a} := by
          have hc1 := hQmin u (by omega)
          have hpos : 1 ≤ (suppD D gs u).card := Finset.card_pos.2 ⟨a, hau⟩
          obtain ⟨a', ha'⟩ := Finset.card_eq_one.1 (le_antisymm hc1 hpos)
          rw [ha', Finset.mem_singleton] at hau; subst hau; exact ha'
        rcases ih u hu_lt (by omega) hsu with ⟨ps, w', hch, hw'u, T1, T2, h12, hT1, hT2⟩ | ⟨ps, hch⟩
        · exact Or.inl ⟨ps, w', hch, by omega, T1, T2, h12, hT1, hT2⟩
        · by_cases honly : ∀ r, Reads gs r u → r = p
          · right
            rcases hcl p g hgp with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, hin⟩
            · have e : u = j := by rw [hin] at hu_in; simpa using hu_in
              subst e
              exact ⟨p :: ps, rfl, u, g, hch, hgp, honly, Or.inl ⟨hop, hin⟩⟩
            · have hplen : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
              have hbad : ∀ h, h ∈ g.inputs → (g.inputs = [u, h] ∨ g.inputs = [h, u]) →
                  suppD D gs h = {a} → False := by
                intro h hh_in hpair hsh
                have hh_lt : h < N + p := (hcl p g hgp).lt h hh_in
                have hah : a ∈ suppD D gs h := by rw [hsh]; exact Finset.mem_singleton_self a
                have hhB : ChainWires N a ps h := chain_all_supp hcl hch honly h hh_lt hah
                by_cases hhu : h = u
                · rw [hhu] at hpair
                  refine L.no_alias hnc1 hnc2 p hplen u hu_lt (fun x => ?_)
                  rcases hop with hop | hop
                  · rw [(vl_bin gs hcl x p u u g hgp hpair).2 hop]; cases vl gs x u <;> rfl
                  · rw [(vl_bin gs hcl x p u u g hgp hpair).1 hop]; cases vl gs x u <;> rfl
                · obtain ⟨q', hq', hqp, _⟩ :=
                    chain_only_read hcl hch h hhB hhu p ⟨g, hgp, hh_in⟩
                  have hlt := chain_lt hcl hch (N + q') (Or.inr ⟨q', hq', rfl⟩)
                  omega
              have hoth : ∃ h, (g.inputs = [u, h] ∨ g.inputs = [h, u]) ∧ DFree D gs h := by
                have hdisj : ∀ x ∈ g.inputs, suppD D gs x ⊆ {a} := by
                  intro x hx i hi
                  rw [← hsw]
                  exact (suppD_gate D gs hcl p g hgp i).2 ⟨x, hx, hi⟩
                have hfree_or_a : ∀ x ∈ g.inputs, DFree D gs x ∨ suppD D gs x = {a} := by
                  intro x hx
                  by_cases he : suppD D gs x = ∅
                  · exact Or.inl (dfree_iff_suppD_empty.2 he)
                  · right
                    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 he
                    have hia : i = a := Finset.mem_singleton.1 (hdisj x hx hi)
                    subst hia
                    exact Finset.Subset.antisymm (hdisj x hx) (Finset.singleton_subset_iff.2 hi)
                rw [hin] at hu_in; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_in
                rcases hu_in with rfl | rfl
                · rcases hfree_or_a k (by rw [hin]; simp) with hf | hsk
                  · exact ⟨k, Or.inl hin, hf⟩
                  · exact False.elim (hbad k (by rw [hin]; simp) (Or.inl hin) hsk)
                · rcases hfree_or_a j (by rw [hin]; simp) with hf | hsj
                  · exact ⟨j, Or.inr hin, hf⟩
                  · exact False.elim (hbad j (by rw [hin]; simp) (Or.inr hin) hsj)
              obtain ⟨h, hin', hf⟩ := hoth
              exact ⟨p :: ps, rfl, u, g, hch, hgp, honly, Or.inr ⟨h, hop, hin', hf⟩⟩
          · push Not at honly
            obtain ⟨r, hr, hrp⟩ := honly
            exact Or.inl ⟨ps, u, hch, hu_lt, p, r, Ne.symm hrp, ⟨g, hgp, hu_in⟩, hr⟩

theorem chain_pair_funnel {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o Q u v : ℕ} {gQ : Gate} {a b : Fin N} {psu psv : List ℕ}
    (H : DeepHyp' F D) (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x)
    (haD : a ∈ D) (hbD : b ∈ D) (hab : a ≠ b)
    (hQ : gs[Q]? = some gQ) (hop : gQ.op = GateOp.and ∨ gQ.op = GateOp.or)
    (hin : gQ.inputs = [u, v])
    (hchu : IsChain N D gs a psu u) (hchv : IsChain N D gs b psv v)
    (honlyu : ∀ r, Reads gs r u → r = Q) (honlyv : ∀ r, Reads gs r v → r = Q) : False := by
  obtain ⟨cu, hcu⟩ := chain_eval hcl hchu
  obtain ⟨cv, hcv⟩ := chain_eval hcl hchv
  let ba : Bool := xor (fixBit gQ) cu
  let bb : Bool := xor (fixBit gQ) cv
  refine H.nf a haD b hbD hab ⟨!ba, !bb, fun x => ?_⟩
  simp only [Bool.not_not]
  let x1 := Function.update (Function.update x a ba) b (!bb)
  let x2 := Function.update (Function.update x a (!ba)) b bb
  let x3 := Function.update (Function.update x a ba) b bb
  have hfree_eq : ∀ (h : ℕ), DFree D gs h →
      vl gs x1 h = vl gs x h ∧ vl gs x2 h = vl gs x h ∧ vl gs x3 h = vl gs x h := by
    intro h hf
    have h1 := vl_update_of_not_supp gs h b (hf b hbD) (Function.update x a ba) (!bb)
    have h1' := vl_update_of_not_supp gs h a (hf a haD) x ba
    have h2 := vl_update_of_not_supp gs h b (hf b hbD) (Function.update x a (!ba)) bb
    have h2' := vl_update_of_not_supp gs h a (hf a haD) x (!ba)
    have h3 := vl_update_of_not_supp gs h b (hf b hbD) (Function.update x a ba) bb
    exact ⟨h1.trans h1', h2.trans h2', h3.trans h1'⟩
  by_cases hhit :
      (∃ p ∈ psu, ∃ g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ h ∈ g.inputs, DFree D gs h ∧ vl gs x h = fixBit g) ∨
      (∃ p ∈ psv, ∃ g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ h ∈ g.inputs, DFree D gs h ∧ vl gs x h = fixBit g)
  · rcases hhit with ⟨p, hp, g, hg, hopg, h, hh, hf, hx⟩ | ⟨p, hp, g, hg, hopg, h, hh, hf, hx⟩
    · obtain ⟨e1, e2, e3⟩ := hfree_eq h hf
      have f1 := chain_win_all H hcl hev haD hchu p hp g hg hopg h hh hf x1 (e1.trans hx)
      have f2 := chain_win_all H hcl hev haD hchu p hp g hg hopg h hh hf x2 (e2.trans hx)
      have f3 := chain_win_all H hcl hev haD hchu p hp g hg hopg h hh hf x3 (e3.trans hx)
      exact ⟨f1.trans f2.symm, f2.trans f3.symm⟩
    · obtain ⟨e1, e2, e3⟩ := hfree_eq h hf
      have f1 := chain_win_all H hcl hev hbD hchv p hp g hg hopg h hh hf x1 (e1.trans hx)
      have f2 := chain_win_all H hcl hev hbD hchv p hp g hg hopg h hh hf x2 (e2.trans hx)
      have f3 := chain_win_all H hcl hev hbD hchv p hp g hg hopg h hh hf x3 (e3.trans hx)
      exact ⟨f1.trans f2.symm, f2.trans f3.symm⟩
  · push Not at hhit
    obtain ⟨hnu, hnv⟩ := hhit
    have hu1 : vl gs x1 u = fixBit gQ := by
      have := hcu x1 (fun p hp g hg hopg h hh hf => by
        rw [(hfree_eq h hf).1]; exact hnu p hp g hg hopg h hh hf)
      have hx1a : x1 a = ba := by
        show Function.update (Function.update x a ba) b (!bb) a = ba
        rw [Function.update_of_ne hab, Function.update_self]
      rw [hx1a] at this; rw [this]
      change xor (xor (fixBit gQ) cu) cu = fixBit gQ
      cases fixBit gQ <;> cases cu <;> rfl
    have hv2 : vl gs x2 v = fixBit gQ := by
      have := hcv x2 (fun p hp g hg hopg h hh hf => by
        rw [(hfree_eq h hf).2.1]; exact hnv p hp g hg hopg h hh hf)
      have hx2b : x2 b = bb := by simp [x2]
      rw [hx2b] at this; rw [this]
      change xor (xor (fixBit gQ) cv) cv = fixBit gQ
      cases fixBit gQ <;> cases cv <;> rfl
    have hu3 : vl gs x3 u = fixBit gQ := by
      have := hcu x3 (fun p hp g hg hopg h hh hf => by
        rw [(hfree_eq h hf).2.2]; exact hnu p hp g hg hopg h hh hf)
      have hx3a : x3 a = ba := by
        show Function.update (Function.update x a ba) b bb a = ba
        rw [Function.update_of_ne hab, Function.update_self]
      rw [hx3a] at this; rw [this]
      change xor (xor (fixBit gQ) cu) cu = fixBit gQ
      cases fixBit gQ <;> cases cu <;> rfl
    have hQ1 : vl gs x1 (N + Q) = fixBit gQ :=
      vl_abs gs hcl x1 Q gQ hQ hop u (by rw [hin]; simp) hu1
    have hQ2 : vl gs x2 (N + Q) = fixBit gQ :=
      vl_abs gs hcl x2 Q gQ hQ hop v (by rw [hin]; simp) hv2
    have hQ3 : vl gs x3 (N + Q) = fixBit gQ :=
      vl_abs gs hcl x3 Q gQ hQ hop u (by rw [hin]; simp) hu3
    let B : ℕ → Prop := fun w => ChainWires N a psu w ∨ ChainWires N b psv w
    have hBo : ¬ B o := by
      intro hbo
      have has := deepHyp'_supp H hev haD
      have hbs := deepHyp'_supp H hev hbD
      have hsupp_in : ∀ (c : Fin N) (ps : List ℕ) (w0 : ℕ), c ∈ D → IsChain N D gs c ps w0 →
          ∀ w', ChainWires N c ps w' → suppD D gs w' = {c} := by
        intro c ps w0 hcD hch w' hw'
        rcases hw' with rfl | ⟨q, hq, rfl⟩
        · rw [suppD_input D gs c.val c.isLt]; simp [hcD]
        · have : ∀ {ps0 : List ℕ} {w1 : ℕ}, IsChain N D gs c ps0 w1 →
              ∀ q' ∈ ps0, suppD D gs (N + q') = {c} := by
            intro ps0; induction ps0 with
            | nil => intro _ _ _ hm; simp at hm
            | cons q0 ps1 ih =>
              intro w1 h1 q' hq'
              rcases List.mem_cons.1 hq' with rfl | hq''
              · rw [← h1.1]; exact chain_suppD hcl hcD h1
              · obtain ⟨_, u0, _, hch0, _⟩ := h1
                exact ih hch0 q' hq''
          exact this hch q hq
      rcases hbo with hbo | hbo
      · have hs := hsupp_in a psu u haD hchu o hbo
        have hm : b ∈ suppD D gs o := Finset.mem_inter.2 ⟨hbs, hbD⟩
        rw [hs, Finset.mem_singleton] at hm; exact hab hm.symm
      · have hs := hsupp_in b psv v hbD hchv o hbo
        have hm : a ∈ suppD D gs o := Finset.mem_inter.2 ⟨has, haD⟩
        rw [hs, Finset.mem_singleton] at hm; exact hab hm
    have hstep : ∀ (y1 y2 : Fin N → Bool),
        (∀ i : Fin N, i ≠ a → i ≠ b → y1 i = y2 i) →
        vl gs y1 (N + Q) = vl gs y2 (N + Q) →
        F y1 = F y2 := by
      intro y1 y2 hin_eq hQeq
      have key := agree_B gs hcl y1 y2 B (o + 1)
        (by
          intro j hj hBj
          rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
          exact hin_eq ⟨j, hj⟩ (fun e => hBj (Or.inl (Or.inl (by rw [← e]))))
            (fun e => hBj (Or.inr (Or.inl (by rw [← e])))))
        (by
          intro q g' hq _ hBq hBa _
          obtain ⟨u0, hu0, hBu0⟩ := hBa
          have hR : Reads gs q u0 := ⟨g', hq, hu0⟩
          rcases hBu0 with hBu0 | hBu0
          · by_cases huw : u0 = u
            · subst huw; rw [honlyu q hR]; exact hQeq
            · exfalso
              obtain ⟨q', hq', hqq', _⟩ := chain_only_read hcl hchu u0 hBu0 huw q hR
              exact hBq (Or.inl (Or.inr ⟨q', hq', by rw [hqq']⟩))
          · by_cases huw : u0 = v
            · subst huw; rw [honlyv q hR]; exact hQeq
            · exfalso
              obtain ⟨q', hq', hqq', _⟩ := chain_only_read hcl hchv u0 hBu0 huw q hR
              exact hBq (Or.inr (Or.inr ⟨q', hq', by rw [hqq']⟩)))
        o (by omega) hBo
      rw [hev, hev] at key; exact key
    have heq12 : F x1 = F x2 := hstep x1 x2 (fun i hia hib => by
      change Function.update (Function.update x a ba) b (!bb) i =
        Function.update (Function.update x a (!ba)) b bb i
      rw [Function.update_of_ne hib, Function.update_of_ne hia,
        Function.update_of_ne hib, Function.update_of_ne hia]) (hQ1.trans hQ2.symm)
    have heq23 : F x2 = F x3 := hstep x2 x3 (fun i hia hib => by
      change Function.update (Function.update x a (!ba)) b bb i =
        Function.update (Function.update x a ba) b bb i
      rw [Function.update_of_ne hib, Function.update_of_ne hia,
        Function.update_of_ne hib, Function.update_of_ne hia]) (hQ2.trans hQ3.symm)
    exact ⟨heq12, heq23⟩

def BinBase (N : ℕ) (gs : List Gate) (a : Fin N) (hasNot : Bool) (base : List ℕ) (w0 : ℕ) : Prop :=
  if hasNot then
    ∃ g0 gg0, base = [g0] ∧ w0 = N + g0 ∧ gs[g0]? = some gg0 ∧
      gg0.op = GateOp.not ∧ gg0.inputs = [a.val] ∧ ∀ r, Reads gs r a.val → r = g0
  else
    base = [] ∧ w0 = a.val

def BinChain (N : ℕ) (D : Finset (Fin N)) (gs : List Gate) (w0 : ℕ) : List ℕ → ℕ → Prop
  | [], w => w = w0
  | p :: ps, w => w = N + p ∧ ∃ u g h, BinChain N D gs w0 ps u ∧
      gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [u, h] ∨ g.inputs = [h, u]) ∧ DFree D gs h ∧
      (∀ r, Reads gs r u → r = p)

theorem binChain_end_mem {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {w0 : ℕ} :
    ∀ {bs : List ℕ} {w : ℕ}, BinChain N D gs w0 bs w → w = w0 ∨ ∃ q ∈ bs, w = N + q
  | [], _, h => Or.inl h
  | p :: _, _, h => Or.inr ⟨p, List.mem_cons_self, h.1⟩

theorem binChain_lt {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {w0 : ℕ} (hcl : CleanL N gs) :
    ∀ {bs : List ℕ} {w : ℕ}, BinChain N D gs w0 bs w →
    w0 ≤ w ∧ ∀ q ∈ bs, N + q ≤ w := by
  intro bs
  induction bs with
  | nil =>
    intro w h; change w = w0 at h; exact ⟨by omega, fun _ hm => by simp at hm⟩
  | cons p bs ih =>
    intro w h
    obtain ⟨rfl, u, g, h', hbc, hgp, _, hin, _, _⟩ := h
    have hu_lt : u < N + p := (hcl p g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
    obtain ⟨hw0, hle⟩ := ih hbc
    refine ⟨by omega, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact le_rfl
    · have := hle q hq'; omega

theorem binChain_nodup {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {w0 : ℕ} (hcl : CleanL N gs) :
    ∀ {bs : List ℕ} {w : ℕ}, BinChain N D gs w0 bs w → bs.Nodup := by
  intro bs
  induction bs with
  | nil => intro _ _; exact List.nodup_nil
  | cons p bs ih =>
    intro w h
    obtain ⟨rfl, u, g, h', hbc, hgp, _, hin, _, _⟩ := h
    have hu_lt : u < N + p := (hcl p g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
    refine List.nodup_cons.2 ⟨fun hm => ?_, ih hbc⟩
    have := (binChain_lt hcl hbc).2 p hm; omega

theorem binBase_suppD {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    {hasNot : Bool} {base : List ℕ} {w0 : ℕ}
    (hcl : CleanL N gs) (haD : a ∈ D) (hb : BinBase N gs a hasNot base w0) :
    suppD D gs w0 = {a} ∧ ∀ q ∈ base, suppD D gs (N + q) = {a} := by
  cases hasNot
  · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨by rw [suppD_input D gs a.val a.isLt]; simp [haD], fun _ hm => by simp at hm⟩
  · simp only [BinBase, ↓reduceIte] at hb
    obtain ⟨g0, gg0, rfl, rfl, hg0, _, hin, _⟩ := hb
    have hs : suppD D gs (N + g0) = {a} := by
      ext i; rw [suppD_gate D gs hcl g0 gg0 hg0 i, hin]
      simp [suppD_input D gs a.val a.isLt, haD]
    exact ⟨hs, fun q hq => by simp at hq; rw [hq]; exact hs⟩

theorem binChain_suppD {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N} {w0 : ℕ}
    (hcl : CleanL N gs) (hsw0 : suppD D gs w0 = {a}) :
    ∀ {bs : List ℕ} {w : ℕ}, BinChain N D gs w0 bs w →
    suppD D gs w = {a} ∧ ∀ q ∈ bs, suppD D gs (N + q) = {a} := by
  intro bs
  induction bs with
  | nil =>
    intro w h; change w = w0 at h; rw [h]; exact ⟨hsw0, fun _ hm => by simp at hm⟩
  | cons p bs ih =>
    intro w h
    obtain ⟨rfl, u, g, h', hbc, hgp, _, hin, hf, _⟩ := h
    obtain ⟨hsu, hsbs⟩ := ih hbc
    have hsp : suppD D gs (N + p) = {a} := by
      ext i; rw [suppD_gate D gs hcl p g hgp i]
      have hsf : suppD D gs h' = ∅ := dfree_iff_suppD_empty.1 hf
      rcases hin with e | e <;> rw [e] <;> simp [hsu, hsf]
    refine ⟨hsp, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact hsp
    · exact hsbs q hq'

theorem binChain_base_disj {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    {hasNot : Bool} {base bs : List ℕ} {w0 w : ℕ}
    (hcl : CleanL N gs) (hb : BinBase N gs a hasNot base w0) (hbc : BinChain N D gs w0 bs w) :
    ∀ q ∈ base, q ∉ bs := by
  cases hasNot
  · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hb
    obtain ⟨rfl, _⟩ := hb; intro _ hm; simp at hm
  · simp only [BinBase, ↓reduceIte] at hb
    obtain ⟨g0, gg0, rfl, rfl, _, _, _, _⟩ := hb
    intro q hq hmem
    simp at hq; rw [hq] at hmem
    have hlt : ∀ {bs0 : List ℕ} {w1 : ℕ}, BinChain N D gs (N + g0) bs0 w1 →
        ∀ p ∈ bs0, g0 < p := by
      intro bs0; induction bs0 with
      | nil => intro _ _ _ hm; simp at hm
      | cons p0 bs1 ih =>
        intro w1 h1 p hp
        obtain ⟨rfl, u, g, h', hbc1, hgp, _, hin, _, _⟩ := h1
        have hu_lt : u < N + p0 := (hcl p0 g hgp).lt u (by rcases hin with e | e <;> rw [e] <;> simp)
        have hw0 := (binChain_lt hcl hbc1).1
        rcases List.mem_cons.1 hp with rfl | hp'
        · omega
        · exact ih hbc1 p hp'
    have := hlt hbc g0 hmem; omega

theorem binChain_isChain {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    {hasNot : Bool} {base : List ℕ} {w0 : ℕ}
    (hb : BinBase N gs a hasNot base w0) :
    ∀ {bs : List ℕ} {w : ℕ}, BinChain N D gs w0 bs w → IsChain N D gs a (bs ++ base) w := by
  intro bs
  induction bs with
  | nil =>
    intro w h; change w = w0 at h; subst h
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hb
      obtain ⟨rfl, rfl⟩ := hb; exact rfl
    · simp only [BinBase, ↓reduceIte] at hb
      obtain ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0, honly0⟩ := hb
      exact ⟨rfl, a.val, gg0, rfl, hg0, honly0, Or.inl ⟨hop0, hin0⟩⟩
  | cons p bs ih =>
    intro w h
    obtain ⟨rfl, u, g, h', hbc, hgp, hop, hin, hf, honly⟩ := h
    exact ⟨rfl, u, g, ih hbc, hgp, honly, Or.inr ⟨h', hop, hin, hf⟩⟩

theorem chain_truncate_aux {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o1 o2 : ℕ} {a : Fin N}
    (L : Least2 N F1 F2 gs o1 o2)
    (hnc1 : ∃ x y : Fin N → Bool, F1 x ≠ F1 y)
    (hnc2 : ∃ x y : Fin N → Bool, F2 x ≠ F2 y) :
    ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w → (∃ T, Reads gs T w) →
    ps = [] ∨
    (∃ g0 gg0, ps = [g0] ∧ w = N + g0 ∧ gs[g0]? = some gg0 ∧
      gg0.op = GateOp.not ∧ gg0.inputs = [a.val]) ∨
    (∃ (hasNot : Bool) (base bs : List ℕ) (w0 w' : ℕ),
      BinBase N gs a hasNot base w0 ∧ BinChain N D gs w0 bs w' ∧ bs ≠ [] ∧
      (∀ p ∈ bs, p ∈ ps) ∧ (∀ q ∈ base, q ∈ ps) ∧
      (w' = w ∨
        ∃ gm ggm T, gs[gm]? = some ggm ∧ ggm.op = GateOp.not ∧ ggm.inputs = [w'] ∧
          Reads gs T (N + gm) ∧ ∀ r, Reads gs r w' → r = gm)) := by
  intro ps
  induction ps with
  | nil => intro _ _ _; exact Or.inl rfl
  | cons p ps ih =>
    intro w h hread
    obtain ⟨rfl, u, g, hch, hgp, honly, hstep⟩ := h
    have hu_in : u ∈ g.inputs := by
      rcases hstep with ⟨_, hin⟩ | ⟨_, _, hin, _⟩
      · rw [hin]; simp
      · rcases hin with e | e <;> rw [e] <;> simp
    have hread_u : ∃ T, Reads gs T u := ⟨p, g, hgp, hu_in⟩
    rcases ih hch hread_u with rfl | ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0⟩ |
      ⟨hasNot, base, bs, w0, w', hbase, hbc, hbsne, hsub_bs, hsub_base, hend⟩
    · change u = a.val at hch; subst hch
      rcases hstep with ⟨hop, hin⟩ | ⟨h', hop, hin, hf⟩
      · exact Or.inr (Or.inl ⟨p, g, rfl, rfl, hgp, hop, hin⟩)
      · refine Or.inr (Or.inr ⟨false, [], [p], a.val, N + p, ⟨rfl, rfl⟩,
          ⟨rfl, a.val, g, h', rfl, hgp, hop, hin, hf, honly⟩, List.cons_ne_nil _ _,
          fun q hq => by simp at hq; simp [hq], fun _ hm => by simp at hm, Or.inl rfl⟩)
    · rcases hstep with ⟨hop, hin⟩ | ⟨h', hop, hin, hf⟩
      · exfalso
        have hplen : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
        refine L.no_alias hnc1 hnc2 p hplen a.val (by have := a.isLt; omega) (fun x => ?_)
        rw [vl_not gs L.hcl x p g hgp (N + g0) hop hin,
          vl_not gs L.hcl x g0 gg0 hg0 a.val hop0 hin0]
        cases vl gs x a.val <;> rfl
      · have honly0 : ∀ r, Reads gs r a.val → r = g0 := by
          obtain ⟨_, u0, g0', hch0, hg0', honly0, _⟩ := hch
          change u0 = a.val at hch0; subst hch0; exact honly0
        refine Or.inr (Or.inr ⟨true, [g0], [p], N + g0, N + p,
          ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0, honly0⟩,
          ⟨rfl, N + g0, g, h', rfl, hgp, hop, hin, hf, honly⟩, List.cons_ne_nil _ _,
          fun q hq => by simp at hq; simp [hq], fun q hq => by simp at hq; simp [hq],
          Or.inl rfl⟩)
    · rcases hend with rfl | ⟨gm, ggm, T, hgm, hopm, hinm, hTm, honlym⟩
      · rcases hstep with ⟨hop, hin⟩ | ⟨h', hop, hin, hf⟩
        · obtain ⟨T, hT⟩ := hread
          refine Or.inr (Or.inr ⟨hasNot, base, bs, w0, w', hbase, hbc, hbsne,
            fun q hq => List.mem_cons_of_mem _ (hsub_bs q hq),
            fun q hq => List.mem_cons_of_mem _ (hsub_base q hq),
            Or.inr ⟨p, g, T, hgp, hop, hin, hT, honly⟩⟩)
        · refine Or.inr (Or.inr ⟨hasNot, base, p :: bs, w0, N + p, hbase,
            ⟨rfl, w', g, h', hbc, hgp, hop, hin, hf, honly⟩, List.cons_ne_nil _ _,
            fun q hq => by
              rcases List.mem_cons.1 hq with rfl | hq'
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hsub_bs q hq'),
            fun q hq => List.mem_cons_of_mem _ (hsub_base q hq),
            Or.inl rfl⟩)
      · refine Or.inr (Or.inr ⟨hasNot, base, bs, w0, w', hbase, hbc, hbsne,
          fun q hq => List.mem_cons_of_mem _ (hsub_bs q hq),
          fun q hq => List.mem_cons_of_mem _ (hsub_base q hq),
          Or.inr ⟨gm, ggm, T, hgm, hopm, hinm, hTm, honlym⟩⟩)

theorem chain_not_tailOK2 {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o1 o2 : ℕ} {a : Fin N}
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D) (hcl : CleanL N gs)
    (hev1 : ∀ x : Fin N → Bool, vl gs x o1 = F1 x)
    (hev2 : ∀ x : Fin N → Bool, vl gs x o2 = F2 x)
    (haD : a ∈ D) :
    ∀ {ps : List ℕ} {w : ℕ}, IsChain N D gs a ps w →
    ∀ p ∈ ps, ∀ g, gs[p]? = some g → g.op = GateOp.or → ¬ TailOK2 N F1 F2 gs p := by
  intro ps
  induction ps with
  | nil => intro _ _ p hp; simp at hp
  | cons p0 ps ih =>
    intro w hchain p hp g hg hop
    have hch_orig := hchain
    obtain ⟨rfl, u0, g0, hch0, hgp0, honly0, hstep0⟩ := hchain
    rcases List.mem_cons.1 hp with rfl | hp'
    · intro ⟨g', hg', htok⟩
      rw [hg] at hg'; cases hg'
      rcases htok with hnot | ⟨_, h1 | h2⟩
      · rw [hop] at hnot; cases hnot
      · obtain ⟨c, hc⟩ := chain_eval hcl hch_orig
        obtain ⟨x, x', hne⟩ := H1.nc a haD (!c)
        have hex0 : ∃ x0 : Fin N → Bool, x0 a = !c ∧ F1 x0 = false := by
          cases hf : F1 (Function.update x a (!c)) with
          | false => exact ⟨Function.update x a (!c), Function.update_self _ _ _, hf⟩
          | true =>
            cases hf' : F1 (Function.update x' a (!c)) with
            | false => exact ⟨Function.update x' a (!c), Function.update_self _ _ _, hf'⟩
            | true => exact absurd (hf.trans hf'.symm) hne
        obtain ⟨x0, hx0a, hx0f⟩ := hex0
        have hval : vl gs x0 (N + p) = true := by
          have := hc x0 (fun q hq gq hgq hopq hq' hhin hqfree hfix => by
            have := chain_win_all H1 hcl hev1 haD hch_orig q hq gq hgq hopq hq' hhin hqfree x0 hfix
            rw [hx0f] at this; cases this)
          rw [this, hx0a]; cases c <;> rfl
        have := h1 x0 hval; rw [hx0f] at this; cases this
      · obtain ⟨c, hc⟩ := chain_eval hcl hch_orig
        obtain ⟨x, x', hne⟩ := H2.nc a haD (!c)
        have hex0 : ∃ x0 : Fin N → Bool, x0 a = !c ∧ F2 x0 = false := by
          cases hf : F2 (Function.update x a (!c)) with
          | false => exact ⟨Function.update x a (!c), Function.update_self _ _ _, hf⟩
          | true =>
            cases hf' : F2 (Function.update x' a (!c)) with
            | false => exact ⟨Function.update x' a (!c), Function.update_self _ _ _, hf'⟩
            | true => exact absurd (hf.trans hf'.symm) hne
        obtain ⟨x0, hx0a, hx0f⟩ := hex0
        have hval : vl gs x0 (N + p) = true := by
          have := hc x0 (fun q hq gq hgq hopq hq' hhin hqfree hfix => by
            have := chain_win_all H2 hcl hev2 haD hch_orig q hq gq hgq hopq hq' hhin hqfree x0 hfix
            rw [hx0f] at this; cases this)
          rw [this, hx0a]; cases c <;> rfl
        have := h2 x0 hval; rw [hx0f] at this; cases this
    · exact ih hch0 p hp' g hg hop

theorem dfree_input_two_readers {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o : ℕ} {a : Fin N}
    (H : DeepHyp' F D) (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x)
    (haD : a ∈ D) {ps0 : List ℕ} {u p h : ℕ} {gp : Gate}
    (hch0 : IsChain N D gs a ps0 u) (hgp : gs[p]? = some gp)
    (hop : gp.op = GateOp.and ∨ gp.op = GateOp.or)
    (hin : gp.inputs = [u, h] ∨ gp.inputs = [h, u])
    (hfree : DFree D gs h)
    (honlyu : ∀ r, Reads gs r u → r = p)
    (honlyh : ∀ t, Reads gs t h → t = p) : N ≤ h := by
  by_contra hlt; push Not at hlt
  obtain ⟨c, hc⟩ := chain_eval hcl hch0
  let b : Bool := xor (fixBit gp) c
  obtain ⟨x, x', hne⟩ := H.nc a haD b
  have hex0 : ∃ x0 : Fin N → Bool, x0 a = b ∧ F x0 = false := by
    cases hf : F (Function.update x a b) with
    | false => exact ⟨Function.update x a b, Function.update_self _ _ _, hf⟩
    | true =>
      cases hf' : F (Function.update x' a b) with
      | false => exact ⟨Function.update x' a b, Function.update_self _ _ _, hf'⟩
      | true => exact absurd (hf.trans hf'.symm) hne
  obtain ⟨x0, hx0a, hx0f⟩ := hex0
  have hu0 : vl gs x0 u = fixBit gp := by
    have := hc x0 (fun q hq gq hgq hopq hq' hhin hqfree hfix => by
      have := chain_win_all H hcl hev haD hch0 q hq gq hgq hopq hq' hhin hqfree x0 hfix
      rw [hx0f] at this; cases this)
    rw [this, hx0a]; change xor (xor (fixBit gp) c) c = fixBit gp
    cases fixBit gp <;> cases c <;> rfl
  have hp0 : vl gs x0 (N + p) = fixBit gp :=
    vl_abs gs hcl x0 p gp hgp hop u (by rcases hin with e | e <;> rw [e] <;> simp) hu0
  let i : Fin N := ⟨h, hlt⟩
  let x1 : Fin N → Bool := Function.update x0 i (fixBit gp)
  have hh1 : vl gs x1 h = fixBit gp := by
    rw [vl_input gs x1 h hlt]; exact Function.update_self i (fixBit gp) x0
  have hp1 : vl gs x1 (N + p) = fixBit gp :=
    vl_abs gs hcl x1 p gp hgp hop h (by rcases hin with e | e <;> rw [e] <;> simp) hh1
  have hF1 : F x1 = true :=
    chain_win_core H hcl hev haD hch0 p gp h hgp honlyu hop hin hfree x1 hh1
  have hoh : o ≠ h := by
    intro e; subst e
    exact hfree a haD (deepHyp'_supp H hev haD)
  have key := agree_B gs hcl x0 x1 (fun w => w = h) (o + 1)
    (by
      intro j hj hne'
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hji : (⟨j, hj⟩ : Fin N) ≠ i := fun e => hne' (congrArg Fin.val e)
      exact (Function.update_of_ne hji (fixBit gp) x0).symm)
    (by
      intro q g' hq _ _ hBa _
      obtain ⟨w0, hw0, rfl⟩ := hBa
      have hqp : q = p := honlyh q ⟨g', hq, hw0⟩
      rw [hqp, hp0, hp1])
    o (by omega) hoh
  rw [hev, hev, hx0f, hF1] at key; cases key

theorem no_rA_eq_phO {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o1 o2 pO pA phO hA q : ℕ} {a b : Fin N} {gpO gpA gphO : Gate}
    (L : Least2 N F1 F2 gs o1 o2)
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D)
    (haD : a ∈ D) (hbD : b ∈ D) (hab : a ≠ b)
    (hgpO : gs[pO]? = some gpO) (hopO : gpO.op = GateOp.or)
    (hgpA : gs[pA]? = some gpA) (hopA : gpA.op = GateOp.and)
    (hphO : gs[phO]? = some gphO) (hopph : gphO.op = GateOp.and)
    (hinph : gphO.inputs = [q, hA] ∨ gphO.inputs = [hA, q])
    (hfree_ph : DFree D gs (N + phO)) (hfree_hA : DFree D gs hA)
    (honly_ph : ∀ r, Reads gs r (N + phO) → r = pO)
    (hord :
      ((gpO.inputs = [a.val, N + phO] ∨ gpO.inputs = [N + phO, a.val]) ∧
       (gpA.inputs = [N + pO, hA] ∨ gpA.inputs = [hA, N + pO]) ∧
       (∀ r, Reads gs r (N + pO) → r = pA)) ∨
      ((gpA.inputs = [a.val, hA] ∨ gpA.inputs = [hA, a.val]) ∧
       (gpO.inputs = [N + pA, N + phO] ∨ gpO.inputs = [N + phO, N + pA]) ∧
       (∀ r, Reads gs r (N + pA) → r = pO))) : False := by
  have hnc1 := deepHyp'_nc H1 ⟨a, haD⟩
  have hnc2 := deepHyp'_nc H2 ⟨a, haD⟩
  have hq_lt : q < N + phO := (L.hcl phO gphO hphO).lt q (by rcases hinph with e | e <;> rw [e] <;> simp)
  have hhA_lt : hA < N + phO := (L.hcl phO gphO hphO).lt hA (by rcases hinph with e | e <;> rw [e] <;> simp)
  have hphO_len : phO < gs.length := (List.getElem?_eq_some_iff.1 hphO).1
  have hpO_len : pO < gs.length := (List.getElem?_eq_some_iff.1 hgpO).1
  have hpA_len : pA < gs.length := (List.getElem?_eq_some_iff.1 hgpA).1
  have ho1_ph : o1 ≠ N + phO := fun e => hfree_ph a haD (e ▸ deepHyp'_supp H1 L.hev1 haD)
  have ho2_ph : o2 ≠ N + phO := fun e => hfree_ph a haD (e ▸ deepHyp'_supp H2 L.hev2 haD)
  rcases hord with ⟨hinO, hinA, honlyO⟩ | ⟨hinA, hinO, honlyA⟩
  · have hphO_lt_pO : N + phO < N + pO :=
      (L.hcl pO gpO hgpO).lt (N + phO) (by rcases hinO with e | e <;> rw [e] <;> simp)
    have hpO_lt_pA : N + pO < N + pA :=
      (L.hcl pA gpA hgpA).lt (N + pO) (by rcases hinA with e | e <;> rw [e] <;> simp)
    have hspO : suppD D gs (N + pO) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pO gpO hgpO i]
      have hf := dfree_iff_suppD_empty.1 hfree_ph
      rcases hinO with e | e <;> rw [e] <;> simp [suppD_input D gs a.val a.isLt, haD, hf]
    have ho1_pO : o1 ≠ N + pO := by
      intro e; have hm : b ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 hbD, hbD⟩
      rw [e, hspO, Finset.mem_singleton] at hm; exact hab hm.symm
    have ho2_pO : o2 ≠ N + pO := by
      intro e; have hm : b ∈ suppD D gs o2 := Finset.mem_inter.2 ⟨deepHyp'_supp H2 L.hev2 hbD, hbD⟩
      rw [e, hspO, Finset.mem_singleton] at hm; exact hab hm.symm
    let gnew : Gate := ⟨GateOp.or, [a.val, q]⟩
    let gs' := gs.set pO gnew
    have hlen' : gs'.length = gs.length := List.length_set
    have hget_pO : gs'[pO]? = some gnew := by simp [gs', hpO_len]
    have hget_ne : ∀ r, r ≠ pO → gs'[r]? = gs[r]? := fun r hr => by simp [gs', List.getElem?_set_ne hr.symm]
    have hcl' : CleanL N gs' := by
      intro r g' hr'
      by_cases hrp : r = pO
      · subst hrp; rw [hget_pO] at hr'; cases hr'
        exact Or.inr ⟨Or.inr rfl, a.val, q, by have := a.isLt; omega, by omega, rfl⟩
      · rw [hget_ne r hrp] at hr'; exact L.hcl r g' hr'
    have hagree : ∀ (x : Fin N → Bool) (w : ℕ), w ≠ N + pO → vl gs' x w = vl gs x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hwn : w < N
        · rw [vl_input gs' x w hwn, vl_input gs x w hwn]
        · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
          have hrp : r ≠ pO := fun e => hw (by rw [e])
          cases hr : gs[r]? with
          | none =>
            have hl := List.getElem?_eq_none_iff.1 hr
            rw [vl_beyond gs' x _ (by omega), vl_beyond gs x _ (by omega)]
          | some g' =>
            have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
            by_cases hrA : r = pA
            · subst r
              rw [hgpA] at hr; cases hr
              have hq' : vl gs' x q = vl gs x q := ih q (by omega) (by omega)
              have hhA' : vl gs' x hA = vl gs x hA := ih hA (by omega) (by omega)
              have hpO' : vl gs' x (N + pO) = (x a || vl gs x q) := by
                rw [(vl_bin gs' hcl' x pO a.val q gnew hget_pO (Or.inl rfl)).1 rfl,
                  vl_input gs' x a.val a.isLt, hq']
              have hpO_orig : vl gs x (N + pO) = (x a || (vl gs x q && vl gs x hA)) := by
                rw [(vl_bin gs L.hcl x pO a.val (N + phO) gpO hgpO hinO).1 hopO,
                  vl_input gs x a.val a.isLt,
                  (vl_bin gs L.hcl x phO q hA gphO hphO hinph).2 hopph]
              rw [(vl_bin gs' hcl' x pA (N + pO) hA gpA hr' hinA).2 hopA,
                (vl_bin gs L.hcl x pA (N + pO) hA gpA hgpA hinA).2 hopA,
                hpO', hpO_orig, hhA']
              cases x a <;> cases vl gs x q <;> cases vl gs x hA <;> rfl
            · rw [vl_gate gs' hcl' x r g' hr', vl_gate gs L.hcl x r g' hr]
              congr 1; apply List.map_congr_left; intro u hu
              have hlt := (L.hcl r g' hr).lt u hu
              exact ih u hlt (fun e => hrA (honlyO r ⟨g', hr, e ▸ hu⟩))
    have hno_ph : ∀ r, ¬ Reads gs' r (N + phO) := by
      intro r ⟨g', hr', hmem⟩
      by_cases hrp : r = pO
      · subst hrp; rw [hget_pO] at hr'; cases hr'
        simp [gnew] at hmem; rcases hmem with h1 | h2 <;> have := a.isLt <;> omega
      · rw [hget_ne r hrp] at hr'
        exact hrp (honly_ph r ⟨g', hr', hmem⟩)
    have hnc1' : ∃ y y' : Fin N → Bool, vl gs' y o1 ≠ vl gs' y' o1 := by
      obtain ⟨y, y', hne⟩ := hnc1
      exact ⟨y, y', by rw [hagree y o1 ho1_pO, hagree y' o1 ho1_pO, L.hev1, L.hev1]; exact hne⟩
    have hnc2' : ∃ y y' : Fin N → Bool, vl gs' y o2 ≠ vl gs' y' o2 := by
      obtain ⟨y, y', hne⟩ := hnc2
      exact ⟨y, y', by rw [hagree y o2 ho2_pO, hagree y' o2 ho2_pO, L.hev2, L.hev2]; exact hne⟩
    obtain ⟨gs'', o1'', o2'', hc'', hl'', he''⟩ :=
      drop_dead2 N gs' hcl' o1 o2 phO (by omega) ho1_ph ho2_ph hno_ph hnc1' hnc2'
    have := L.hmin gs'' o1'' o2'' hc'' (fun x =>
      ⟨by rw [(he'' x).1, hagree x o1 ho1_pO, L.hev1],
       by rw [(he'' x).2, hagree x o2 ho2_pO, L.hev2]⟩)
    omega
  · have hhA_lt_pA : hA < N + pA :=
      (L.hcl pA gpA hgpA).lt hA (by rcases hinA with e | e <;> rw [e] <;> simp)
    have hpA_lt_pO : N + pA < N + pO :=
      (L.hcl pO gpO hgpO).lt (N + pA) (by rcases hinO with e | e <;> rw [e] <;> simp)
    have hphO_lt_pO : N + phO < N + pO :=
      (L.hcl pO gpO hgpO).lt (N + phO) (by rcases hinO with e | e <;> rw [e] <;> simp)
    have hspA : suppD D gs (N + pA) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pA gpA hgpA i]
      have hf := dfree_iff_suppD_empty.1 hfree_hA
      rcases hinA with e | e <;> rw [e] <;> simp [suppD_input D gs a.val a.isLt, haD, hf]
    have ho1_pA : o1 ≠ N + pA := by
      intro e; have hm : b ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 hbD, hbD⟩
      rw [e, hspA, Finset.mem_singleton] at hm; exact hab hm.symm
    have ho2_pA : o2 ≠ N + pA := by
      intro e; have hm : b ∈ suppD D gs o2 := Finset.mem_inter.2 ⟨deepHyp'_supp H2 L.hev2 hbD, hbD⟩
      rw [e, hspA, Finset.mem_singleton] at hm; exact hab hm.symm
    have hphO_ne_pA : phO ≠ pA := by
      intro e; subst e
      have : a ∈ suppD D gs (N + phO) := by rw [hspA]; exact Finset.mem_singleton_self a
      exact hfree_ph a haD (Finset.mem_inter.1 this).1
    have hhA_ne_pA : hA ≠ N + pA := by omega
    let g1 : Gate := ⟨GateOp.or, [a.val, q]⟩
    let g2 : Gate := ⟨GateOp.and, [N + phO, hA]⟩
    let gs' := (gs.set phO g1).set pO g2
    have hlen' : gs'.length = gs.length := by simp [gs']
    have hget_pO : gs'[pO]? = some g2 := by simp [gs', hpO_len]
    have hget_phO : gs'[phO]? = some g1 := by
      have hne : pO ≠ phO := by omega
      show ((gs.set phO g1).set pO g2)[phO]? = some g1
      rw [List.getElem?_set_ne hne, List.getElem?_set_self (by omega)]
    have hget_ne : ∀ r, r ≠ pO → r ≠ phO → gs'[r]? = gs[r]? := fun r h1 h2 => by
      simp [gs', List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
    have hcl' : CleanL N gs' := by
      intro r g' hr'
      by_cases h1 : r = pO
      · subst h1; rw [hget_pO] at hr'; cases hr'
        exact Or.inr ⟨Or.inl rfl, N + phO, hA, by omega, by omega, rfl⟩
      · by_cases h2 : r = phO
        · subst h2; rw [hget_phO] at hr'; cases hr'
          exact Or.inr ⟨Or.inr rfl, a.val, q, by have := a.isLt; omega, by omega, rfl⟩
        · rw [hget_ne r h1 h2] at hr'; exact L.hcl r g' hr'
    have hagree : ∀ (x : Fin N → Bool) (w : ℕ), w ≠ N + phO → vl gs' x w = vl gs x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hwn : w < N
        · rw [vl_input gs' x w hwn, vl_input gs x w hwn]
        · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
          have hrph : r ≠ phO := fun e => hw (by rw [e])
          cases hr : gs[r]? with
          | none =>
            have hl := List.getElem?_eq_none_iff.1 hr
            rw [vl_beyond gs' x _ (by omega), vl_beyond gs x _ (by omega)]
          | some g' =>
            by_cases hrO : r = pO
            · subst r
              rw [hgpO] at hr; cases hr
              have hq' : vl gs' x q = vl gs x q := ih q (by omega) (by omega)
              have hhA' : vl gs' x hA = vl gs x hA := ih hA (by omega) (by omega)
              have hph' : vl gs' x (N + phO) = (x a || vl gs x q) := by
                rw [(vl_bin gs' hcl' x phO a.val q g1 hget_phO (Or.inl rfl)).1 rfl,
                  vl_input gs' x a.val a.isLt, hq']
              have hpO_orig : vl gs x (N + pO) =
                  ((x a && vl gs x hA) || (vl gs x q && vl gs x hA)) := by
                rw [(vl_bin gs L.hcl x pO (N + pA) (N + phO) gpO hgpO hinO).1 hopO,
                  (vl_bin gs L.hcl x pA a.val hA gpA hgpA hinA).2 hopA,
                  vl_input gs x a.val a.isLt,
                  (vl_bin gs L.hcl x phO q hA gphO hphO hinph).2 hopph]
              rw [(vl_bin gs' hcl' x pO (N + phO) hA g2 hget_pO (Or.inl rfl)).2 rfl,
                hph', hhA', hpO_orig]
              cases x a <;> cases vl gs x q <;> cases vl gs x hA <;> rfl
            · have hr' : gs'[r]? = some g' := by rw [hget_ne r hrO hrph]; exact hr
              rw [vl_gate gs' hcl' x r g' hr', vl_gate gs L.hcl x r g' hr]
              congr 1; apply List.map_congr_left; intro u hu
              have hlt := (L.hcl r g' hr).lt u hu
              exact ih u hlt (fun e => hrO (honly_ph r ⟨g', hr, e ▸ hu⟩))
    have hno_pA : ∀ r, ¬ Reads gs' r (N + pA) := by
      intro r ⟨g', hr', hmem⟩
      by_cases h1 : r = pO
      · subst h1; rw [hget_pO] at hr'; cases hr'
        simp [g2] at hmem; rcases hmem with h | h <;> omega
      · by_cases h2 : r = phO
        · subst r; rw [hget_phO] at hr'; cases hr'
          simp [g1] at hmem
          rcases hmem with h | h
          · have := a.isLt; omega
          · exact h1 (honlyA phO ⟨gphO, hphO, by
              rcases hinph with e | e <;> rw [e] <;> simp [h]⟩)
        · rw [hget_ne r h1 h2] at hr'
          exact h1 (honlyA r ⟨g', hr', hmem⟩)
    have hnc1' : ∃ y y' : Fin N → Bool, vl gs' y o1 ≠ vl gs' y' o1 := by
      obtain ⟨y, y', hne⟩ := hnc1
      exact ⟨y, y', by rw [hagree y o1 ho1_ph, hagree y' o1 ho1_ph, L.hev1, L.hev1]; exact hne⟩
    have hnc2' : ∃ y y' : Fin N → Bool, vl gs' y o2 ≠ vl gs' y' o2 := by
      obtain ⟨y, y', hne⟩ := hnc2
      exact ⟨y, y', by rw [hagree y o2 ho2_ph, hagree y' o2 ho2_ph, L.hev2, L.hev2]; exact hne⟩
    obtain ⟨gs'', o1'', o2'', hc'', hl'', he''⟩ :=
      drop_dead2 N gs' hcl' o1 o2 pA (by omega) ho1_pA ho2_pA hno_pA hnc1' hnc2'
    have := L.hmin gs'' o1'' o2'' hc'' (fun x =>
      ⟨by rw [(he'' x).1, hagree x o1 ho1_ph, L.hev1],
       by rw [(he'' x).2, hagree x o2 ho2_ph, L.hev2]⟩)
    omega

theorem no_rA_eq_T {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    {gs : List Gate} {o1 o2 pO pA phO hA gm T : ℕ} {a b : Fin N} {gpO gpA ggm gT : Gate}
    (L : Least2 N F1 F2 gs o1 o2)
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D)
    (haD : a ∈ D) (hbD : b ∈ D) (hab : a ≠ b)
    (hgpO : gs[pO]? = some gpO) (hopO : gpO.op = GateOp.or)
    (hgpA : gs[pA]? = some gpA) (hopA : gpA.op = GateOp.and)
    (hgm : gs[gm]? = some ggm) (hopm : ggm.op = GateOp.not)
    (hgT : gs[T]? = some gT) (hopT : gT.op = GateOp.and)
    (hinT : gT.inputs = [N + gm, hA] ∨ gT.inputs = [hA, N + gm])
    (hfree_ph : DFree D gs (N + phO)) (hfree_hA : DFree D gs hA)
    (honly_gm : ∀ r, Reads gs r (N + gm) → r = T)
    (hord :
      ((gpO.inputs = [a.val, N + phO] ∨ gpO.inputs = [N + phO, a.val]) ∧
       (gpA.inputs = [N + pO, hA] ∨ gpA.inputs = [hA, N + pO]) ∧
       ggm.inputs = [N + pA] ∧
       (∀ r, Reads gs r (N + pA) → r = gm)) ∨
      ((gpA.inputs = [a.val, hA] ∨ gpA.inputs = [hA, a.val]) ∧
       (gpO.inputs = [N + pA, N + phO] ∨ gpO.inputs = [N + phO, N + pA]) ∧
       ggm.inputs = [N + pO] ∧
       (∀ r, Reads gs r (N + pA) → r = pO) ∧
       (∀ r, Reads gs r (N + pO) → r = gm))) : False := by
  have hnc1 := deepHyp'_nc H1 ⟨a, haD⟩
  have hnc2 := deepHyp'_nc H2 ⟨a, haD⟩
  have hpO_len : pO < gs.length := (List.getElem?_eq_some_iff.1 hgpO).1
  have hpA_len : pA < gs.length := (List.getElem?_eq_some_iff.1 hgpA).1
  have hgm_len : gm < gs.length := (List.getElem?_eq_some_iff.1 hgm).1
  have hgm_lt_T : N + gm < N + T :=
    (L.hcl T gT hgT).lt (N + gm) (by rcases hinT with e | e <;> rw [e] <;> simp)
  have hhA_lt_T : hA < N + T :=
    (L.hcl T gT hgT).lt hA (by rcases hinT with e | e <;> rw [e] <;> simp)
  rcases hord with ⟨hinO, hinA, hinm, honlyA⟩ | ⟨hinA, hinO, hinm, honlyA, honlyO⟩
  · have hpO_lt_pA : N + pO < N + pA :=
      (L.hcl pA gpA hgpA).lt (N + pO) (by rcases hinA with e | e <;> rw [e] <;> simp)
    have hpA_lt_gm : N + pA < N + gm :=
      (L.hcl gm ggm hgm).lt (N + pA) (by rw [hinm]; simp)
    have hspO : suppD D gs (N + pO) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pO gpO hgpO i]
      have hf := dfree_iff_suppD_empty.1 hfree_ph
      rcases hinO with e | e <;> rw [e] <;> simp [suppD_input D gs a.val a.isLt, haD, hf]
    have hspA : suppD D gs (N + pA) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pA gpA hgpA i]
      have hf := dfree_iff_suppD_empty.1 hfree_hA
      rcases hinA with e | e <;> rw [e] <;> simp [hspO, hf]
    have hsgm : suppD D gs (N + gm) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl gm ggm hgm i, hinm]; simp [hspA]
    have hne_out : ∀ (w : ℕ), suppD D gs w = {a} → o1 ≠ w ∧ o2 ≠ w := by
      intro w hsw
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have hm : b ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 hbD, hbD⟩
        rw [e, hsw, Finset.mem_singleton] at hm; exact hab hm.symm
      · have hm : b ∈ suppD D gs o2 := Finset.mem_inter.2 ⟨deepHyp'_supp H2 L.hev2 hbD, hbD⟩
        rw [e, hsw, Finset.mem_singleton] at hm; exact hab hm.symm
    obtain ⟨ho1_pA, ho2_pA⟩ := hne_out (N + pA) hspA
    obtain ⟨ho1_gm, ho2_gm⟩ := hne_out (N + gm) hsgm
    let gnew : Gate := ⟨GateOp.not, [N + pO]⟩
    let gs' := gs.set gm gnew
    have hlen' : gs'.length = gs.length := List.length_set
    have hget_gm : gs'[gm]? = some gnew := by simp [gs', hgm_len]
    have hget_ne : ∀ r, r ≠ gm → gs'[r]? = gs[r]? := fun r hr => by simp [gs', List.getElem?_set_ne hr.symm]
    have hcl' : CleanL N gs' := by
      intro r g' hr'
      by_cases hrm : r = gm
      · subst hrm; rw [hget_gm] at hr'; cases hr'
        exact Or.inl ⟨rfl, N + pO, by omega, rfl⟩
      · rw [hget_ne r hrm] at hr'; exact L.hcl r g' hr'
    have hagree : ∀ (x : Fin N → Bool) (w : ℕ), w ≠ N + gm → vl gs' x w = vl gs x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hwn : w < N
        · rw [vl_input gs' x w hwn, vl_input gs x w hwn]
        · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
          have hrm : r ≠ gm := fun e => hw (by rw [e])
          cases hr : gs[r]? with
          | none =>
            have hl := List.getElem?_eq_none_iff.1 hr
            rw [vl_beyond gs' x _ (by omega), vl_beyond gs x _ (by omega)]
          | some g' =>
            have hr' : gs'[r]? = some g' := by rw [hget_ne r hrm]; exact hr
            by_cases hrT : r = T
            · subst r
              rw [hgT] at hr; cases hr
              have hpO' : vl gs' x (N + pO) = vl gs x (N + pO) := ih (N + pO) (by omega) (by omega)
              have hhA_ne : hA ≠ N + gm := fun e =>
                hfree_hA a haD (Finset.mem_inter.1 (e ▸ hsgm ▸ Finset.mem_singleton_self a)).1
              have hhA' : vl gs' x hA = vl gs x hA := ih hA hhA_lt_T hhA_ne
              have hgm' : vl gs' x (N + gm) = !vl gs x (N + pO) := by
                rw [vl_not gs' hcl' x gm gnew hget_gm (N + pO) rfl rfl, hpO']
              have hgm_orig : vl gs x (N + gm) = !(vl gs x (N + pO) && vl gs x hA) := by
                rw [vl_not gs L.hcl x gm ggm hgm (N + pA) hopm hinm,
                  (vl_bin gs L.hcl x pA (N + pO) hA gpA hgpA hinA).2 hopA]
              rw [(vl_bin gs' hcl' x T (N + gm) hA gT hr' hinT).2 hopT,
                (vl_bin gs L.hcl x T (N + gm) hA gT hgT hinT).2 hopT,
                hgm', hgm_orig, hhA']
              cases vl gs x (N + pO) <;> cases vl gs x hA <;> rfl
            · rw [vl_gate gs' hcl' x r g' hr', vl_gate gs L.hcl x r g' hr]
              congr 1; apply List.map_congr_left; intro u hu
              exact ih u ((L.hcl r g' hr).lt u hu) (fun e => hrT (honly_gm r ⟨g', hr, e ▸ hu⟩))
    have hno_pA : ∀ r, ¬ Reads gs' r (N + pA) := by
      intro r ⟨g', hr', hmem⟩
      by_cases hrm : r = gm
      · subst hrm; rw [hget_gm] at hr'; cases hr'; simp [gnew] at hmem; omega
      · rw [hget_ne r hrm] at hr'; exact hrm (honlyA r ⟨g', hr', hmem⟩)
    have hnc1' : ∃ y y' : Fin N → Bool, vl gs' y o1 ≠ vl gs' y' o1 := by
      obtain ⟨y, y', hne⟩ := hnc1
      exact ⟨y, y', by rw [hagree y o1 ho1_gm, hagree y' o1 ho1_gm, L.hev1, L.hev1]; exact hne⟩
    have hnc2' : ∃ y y' : Fin N → Bool, vl gs' y o2 ≠ vl gs' y' o2 := by
      obtain ⟨y, y', hne⟩ := hnc2
      exact ⟨y, y', by rw [hagree y o2 ho2_gm, hagree y' o2 ho2_gm, L.hev2, L.hev2]; exact hne⟩
    obtain ⟨gs'', o1'', o2'', hc'', hl'', he''⟩ :=
      drop_dead2 N gs' hcl' o1 o2 pA (by omega) ho1_pA ho2_pA hno_pA hnc1' hnc2'
    have := L.hmin gs'' o1'' o2'' hc'' (fun x =>
      ⟨by rw [(he'' x).1, hagree x o1 ho1_gm, L.hev1],
       by rw [(he'' x).2, hagree x o2 ho2_gm, L.hev2]⟩)
    omega
  · have hpA_lt_pO : N + pA < N + pO :=
      (L.hcl pO gpO hgpO).lt (N + pA) (by rcases hinO with e | e <;> rw [e] <;> simp)
    have hphO_lt_pO : N + phO < N + pO :=
      (L.hcl pO gpO hgpO).lt (N + phO) (by rcases hinO with e | e <;> rw [e] <;> simp)
    have hpO_lt_gm : N + pO < N + gm :=
      (L.hcl gm ggm hgm).lt (N + pO) (by rw [hinm]; simp)
    have hspA : suppD D gs (N + pA) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pA gpA hgpA i]
      have hf := dfree_iff_suppD_empty.1 hfree_hA
      rcases hinA with e | e <;> rw [e] <;> simp [suppD_input D gs a.val a.isLt, haD, hf]
    have hspO : suppD D gs (N + pO) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl pO gpO hgpO i]
      have hf := dfree_iff_suppD_empty.1 hfree_ph
      rcases hinO with e | e <;> rw [e] <;> simp [hspA, hf]
    have hsgm : suppD D gs (N + gm) = {a} := by
      ext i; rw [suppD_gate D gs L.hcl gm ggm hgm i, hinm]; simp [hspO]
    have hne_out : ∀ (w : ℕ), suppD D gs w = {a} → o1 ≠ w ∧ o2 ≠ w := by
      intro w hsw
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have hm : b ∈ suppD D gs o1 := Finset.mem_inter.2 ⟨deepHyp'_supp H1 L.hev1 hbD, hbD⟩
        rw [e, hsw, Finset.mem_singleton] at hm; exact hab hm.symm
      · have hm : b ∈ suppD D gs o2 := Finset.mem_inter.2 ⟨deepHyp'_supp H2 L.hev2 hbD, hbD⟩
        rw [e, hsw, Finset.mem_singleton] at hm; exact hab hm.symm
    obtain ⟨ho1_pA, ho2_pA⟩ := hne_out (N + pA) hspA
    obtain ⟨ho1_pO, ho2_pO⟩ := hne_out (N + pO) hspO
    obtain ⟨ho1_gm, ho2_gm⟩ := hne_out (N + gm) hsgm
    let gnew : Gate := ⟨GateOp.or, [a.val, N + phO]⟩
    let gs' := gs.set pO gnew
    have hlen' : gs'.length = gs.length := List.length_set
    have hget_pO : gs'[pO]? = some gnew := by simp [gs', hpO_len]
    have hget_ne : ∀ r, r ≠ pO → gs'[r]? = gs[r]? := fun r hr => by simp [gs', List.getElem?_set_ne hr.symm]
    have hcl' : CleanL N gs' := by
      intro r g' hr'
      by_cases hrp : r = pO
      · subst hrp; rw [hget_pO] at hr'; cases hr'
        exact Or.inr ⟨Or.inr rfl, a.val, N + phO, by have := a.isLt; omega, by omega, rfl⟩
      · rw [hget_ne r hrp] at hr'; exact L.hcl r g' hr'
    have hagree : ∀ (x : Fin N → Bool) (w : ℕ), w ≠ N + pO → w ≠ N + gm → vl gs' x w = vl gs x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw1 hw2
        by_cases hwn : w < N
        · rw [vl_input gs' x w hwn, vl_input gs x w hwn]
        · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
          have hr1 : r ≠ pO := fun e => hw1 (by rw [e])
          have hr2 : r ≠ gm := fun e => hw2 (by rw [e])
          cases hr : gs[r]? with
          | none =>
            have hl := List.getElem?_eq_none_iff.1 hr
            rw [vl_beyond gs' x _ (by omega), vl_beyond gs x _ (by omega)]
          | some g' =>
            have hr' : gs'[r]? = some g' := by rw [hget_ne r hr1]; exact hr
            by_cases hrT : r = T
            · subst r
              rw [hgT] at hr; cases hr
              have hph' : vl gs' x (N + phO) = vl gs x (N + phO) := ih (N + phO) (by omega) (by omega) (by omega)
              have hhA_ne1 : hA ≠ N + pO := fun e =>
                hfree_hA a haD (Finset.mem_inter.1 (e ▸ hspO ▸ Finset.mem_singleton_self a)).1
              have hhA_ne2 : hA ≠ N + gm := fun e =>
                hfree_hA a haD (Finset.mem_inter.1 (e ▸ hsgm ▸ Finset.mem_singleton_self a)).1
              have hhA' : vl gs' x hA = vl gs x hA := ih hA hhA_lt_T hhA_ne1 hhA_ne2
              have hpO' : vl gs' x (N + pO) = (x a || vl gs x (N + phO)) := by
                rw [(vl_bin gs' hcl' x pO a.val (N + phO) gnew hget_pO (Or.inl rfl)).1 rfl,
                  vl_input gs' x a.val a.isLt, hph']
              have hgm' : vl gs' x (N + gm) = !(x a || vl gs x (N + phO)) := by
                have hgm_ne : gm ≠ pO := by omega
                have hgm_get : gs'[gm]? = some ggm := by rw [hget_ne gm hgm_ne]; exact hgm
                rw [vl_not gs' hcl' x gm ggm hgm_get (N + pO) hopm hinm, hpO']
              have hgm_orig : vl gs x (N + gm) = !((x a && vl gs x hA) || vl gs x (N + phO)) := by
                rw [vl_not gs L.hcl x gm ggm hgm (N + pO) hopm hinm,
                  (vl_bin gs L.hcl x pO (N + pA) (N + phO) gpO hgpO hinO).1 hopO,
                  (vl_bin gs L.hcl x pA a.val hA gpA hgpA hinA).2 hopA,
                  vl_input gs x a.val a.isLt]
              rw [(vl_bin gs' hcl' x T (N + gm) hA gT hr' hinT).2 hopT,
                (vl_bin gs L.hcl x T (N + gm) hA gT hgT hinT).2 hopT,
                hgm', hgm_orig, hhA']
              cases x a <;> cases vl gs x (N + phO) <;> cases vl gs x hA <;> rfl
            · rw [vl_gate gs' hcl' x r g' hr', vl_gate gs L.hcl x r g' hr]
              congr 1; apply List.map_congr_left; intro u hu
              exact ih u ((L.hcl r g' hr).lt u hu)
                (fun e => hr2 (honlyO r ⟨g', hr, e ▸ hu⟩))
                (fun e => hrT (honly_gm r ⟨g', hr, e ▸ hu⟩))
    have hno_pA : ∀ r, ¬ Reads gs' r (N + pA) := by
      intro r ⟨g', hr', hmem⟩
      by_cases hrp : r = pO
      · subst hrp; rw [hget_pO] at hr'; cases hr'
        simp [gnew] at hmem
        rcases hmem with h | h
        · have := a.isLt; omega
        · exact hfree_ph a haD (Finset.mem_inter.1 (h.symm ▸ hspA ▸ Finset.mem_singleton_self a)).1
      · rw [hget_ne r hrp] at hr'; exact hrp (honlyA r ⟨g', hr', hmem⟩)
    have hnc1' : ∃ y y' : Fin N → Bool, vl gs' y o1 ≠ vl gs' y' o1 := by
      obtain ⟨y, y', hne⟩ := hnc1
      exact ⟨y, y', by rw [hagree y o1 ho1_pO ho1_gm, hagree y' o1 ho1_pO ho1_gm, L.hev1, L.hev1]; exact hne⟩
    have hnc2' : ∃ y y' : Fin N → Bool, vl gs' y o2 ≠ vl gs' y' o2 := by
      obtain ⟨y, y', hne⟩ := hnc2
      exact ⟨y, y', by rw [hagree y o2 ho2_pO ho2_gm, hagree y' o2 ho2_pO ho2_gm, L.hev2, L.hev2]; exact hne⟩
    obtain ⟨gs'', o1'', o2'', hc'', hl'', he''⟩ :=
      drop_dead2 N gs' hcl' o1 o2 pA (by omega) ho1_pA ho2_pA hno_pA hnc1' hnc2'
    have := L.hmin gs'' o1'' o2'' hc'' (fun x =>
      ⟨by rw [(he'' x).1, hagree x o1 ho1_pO ho1_gm, L.hev1],
       by rw [(he'' x).2, hagree x o2 ho2_pO ho2_gm, L.hev2]⟩)
    omega

theorem dfree_ne_a {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N} {h : ℕ}
    (hf : DFree D gs h) (haD : a ∈ D) : h ≠ a.val := by
  intro e; subst e
  have hmem : a ∈ (suppsFrom gs (inputSupps N)).getD a.val ∅ := by
    rw [front_supp_input gs a.val a.isLt]; exact Finset.mem_singleton_self a
  exact hf a haD hmem

theorem elimOv_fst_getD_append (N : ℕ) (ov : ℕ → Option Bool) (gs : List Gate)
    (acc : List Stat × List Stat × List Gate) (w : ℕ) (hw : w < acc.1.length) :
    (elimOv N ov gs acc).1.getD w (Sum.inl false) = acc.1.getD w (Sum.inl false) :=
  elimOv_getD N ov w (Sum.inl false) gs acc hw

theorem elimOv_ov_val (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs' : List Gate)
    (w : ℕ) (hw : w < N + gs'.length) (hwy : w ≠ y) (b : Bool) (hov : ov w = some b) :
    (elimOv N ov gs' (initOv N y v ov)).1.getD w (Sum.inl false) = Sum.inl b := by
  by_cases hwn : w < N
  · rw [elimOv_fst_getD_append N ov gs' _ w (by simp [initOv]; exact hwn)]
    simp only [initOv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hwn,
      Option.map_some, Option.getD_some, hwy, ↓reduceIte, hov]
  · obtain ⟨p, rfl⟩ : ∃ p, w = N + p := ⟨w - N, by omega⟩
    have hp : p < gs'.length := by omega
    obtain ⟨g, hgp⟩ : ∃ g, gs'[p]? = some g := ⟨gs'[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, hsplit, hlpre⟩ := split_at gs' p g hgp
    rw [hsplit, elimOv_append, elimOv_cons]
    set acc1 := elimOv N ov pre (initOv N y v ov) with hacc1
    have hlen1 : acc1.1.length = N + p := by
      rw [hacc1, elimOv_fst_len]; simp [initOv, hlpre]
    rw [elimOv_fst_getD_append N ov post _ (N + p) (by simp [elimOvStep, hlen1])]
    simp only [elimOvStep, hlen1, hov]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen1, Nat.sub_self]
    simp

theorem elimOv_input_y (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs' : List Gate) (hy : y < N) :
    (elimOv N ov gs' (initOv N y v ov)).1.getD y (Sum.inl false) = Sum.inl v := by
  rw [elimOv_fst_getD_append N ov gs' _ y (by simp [initOv]; exact hy)]
  simp only [initOv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hy,
    Option.map_some, Option.getD_some, ↓reduceIte]

theorem elimOv_gate_step (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hno : ov (N + p) = none) :
    let acc := elimOv N ov gs (initOv N y v ov)
    ∃ (w : ℕ), acc.1.getD (N + p) (Sum.inl false) =
      (simplify g.op w (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hacc0 : (initOv N y v ov).1.length = N := by simp [initOv]
  have hlen : (elimOv N ov pre (initOv N y v ov)).1.length = N + pre.length := by
    rw [elimOv_fst_len, hacc0]
  refine ⟨N + (elimOv N ov pre (initOv N y v ov)).2.2.length, ?_⟩
  have hsplit := elimOv_split_getD N ov pre g post (initOv N y v ov) (N + pre.length) (Sum.inl false)
    (by rw [hacc0])
  rw [hsplit]
  rw [show (elimOvStep N ov (elimOv N ov pre (initOv N y v ov)) g).1.getD (N + pre.length) (Sum.inl false) =
    match ov (elimOv N ov pre (initOv N y v ov)).1.length with
    | some b => Sum.inl b
    | none => (simplify g.op (N + (elimOv N ov pre (initOv N y v ov)).2.2.length)
        (g.inputs.map fun i => (elimOv N ov pre (initOv N y v ov)).1.getD i (Sum.inl false))).2
    from getD_snoc_len _ _ _ _ hlen, hlen, hno]
  dsimp only
  congr 2
  apply List.map_congr_left
  intro i hi
  have hilt : i < (initOv N y v ov).1.length + pre.length := by
    rw [hacc0]; exact (hcl pre.length g hp).lt i hi
  exact (elimOv_split_getD_lt N ov pre g post (initOv N y v ov) i (Sum.inl false) hilt).symm

theorem elimOv_not_const (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p u : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hin : g.inputs = [u]) (hno : ov (N + p) = none) (c : Bool)
    (hu : (elimOv N ov gs (initOv N y v ov)).1.getD u (Sum.inl false) = Sum.inl c) :
    (elimOv N ov gs (initOv N y v ov)).1.getD (N + p) (Sum.inl false) = Sum.inl (!c) := by
  obtain ⟨w, hw⟩ := elimOv_gate_step N y v ov gs hcl p g hp hno
  rw [hw, hop, hin, List.map_cons, List.map_nil, hu]; rfl

theorem elimOv_and_false (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p u : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.and) (hu_in : u ∈ g.inputs) (hno : ov (N + p) = none)
    (hu : (elimOv N ov gs (initOv N y v ov)).1.getD u (Sum.inl false) = Sum.inl false) :
    (elimOv N ov gs (initOv N y v ov)).1.getD (N + p) (Sum.inl false) = Sum.inl false := by
  obtain ⟨w, hw⟩ := elimOv_gate_step N y v ov gs hcl p g hp hno
  rcases hcl p g hp with ⟨h1, _⟩ | ⟨_, j, k, _, _, hjk⟩
  · rw [hop] at h1; cases h1
  · rw [hw, hop, hjk, List.map_cons, List.map_cons, List.map_nil]
    rw [hjk] at hu_in; simp at hu_in
    rcases hu_in with rfl | rfl
    · rw [hu]; cases (elimOv N ov gs (initOv N y v ov)).1.getD k (Sum.inl false) with
      | inl b => cases b <;> rfl
      | inr _ => rfl
    · rw [hu]; cases (elimOv N ov gs (initOv N y v ov)).1.getD j (Sum.inl false) with
      | inl b => cases b <;> rfl
      | inr _ => rfl

theorem elimOv_or_true (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p u : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.or) (hu_in : u ∈ g.inputs) (hno : ov (N + p) = none)
    (hu : (elimOv N ov gs (initOv N y v ov)).1.getD u (Sum.inl false) = Sum.inl true) :
    (elimOv N ov gs (initOv N y v ov)).1.getD (N + p) (Sum.inl false) = Sum.inl true := by
  obtain ⟨w, hw⟩ := elimOv_gate_step N y v ov gs hcl p g hp hno
  rcases hcl p g hp with ⟨h1, _⟩ | ⟨_, j, k, _, _, hjk⟩
  · rw [hop] at h1; cases h1
  · rw [hw, hop, hjk, List.map_cons, List.map_cons, List.map_nil]
    rw [hjk] at hu_in; simp at hu_in
    rcases hu_in with rfl | rfl
    · rw [hu]; cases (elimOv N ov gs (initOv N y v ov)).1.getD k (Sum.inl false) with
      | inl b => cases b <;> rfl
      | inr _ => rfl
    · rw [hu]; cases (elimOv N ov gs (initOv N y v ov)).1.getD j (Sum.inl false) with
      | inl b => cases b <;> rfl
      | inr _ => rfl

theorem elimOv_and_true (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p u u' : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.and) (hin : g.inputs = [u, u'] ∨ g.inputs = [u', u])
    (hno : ov (N + p) = none)
    (hu : (elimOv N ov gs (initOv N y v ov)).1.getD u (Sum.inl false) = Sum.inl true)
    (hu' : (elimOv N ov gs (initOv N y v ov)).1.getD u' (Sum.inl false) = Sum.inl true) :
    (elimOv N ov gs (initOv N y v ov)).1.getD (N + p) (Sum.inl false) = Sum.inl true := by
  obtain ⟨w, hw⟩ := elimOv_gate_step N y v ov gs hcl p g hp hno
  rw [hw, hop]; rcases hin with e | e <;> rw [e, List.map_cons, List.map_cons, List.map_nil, hu, hu'] <;> rfl

theorem elimOv_or_false (N y : ℕ) (v : Bool) (ov : ℕ → Option Bool) (gs : List Gate)
    (hcl : CleanL N gs) (p u u' : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.or) (hin : g.inputs = [u, u'] ∨ g.inputs = [u', u])
    (hno : ov (N + p) = none)
    (hu : (elimOv N ov gs (initOv N y v ov)).1.getD u (Sum.inl false) = Sum.inl false)
    (hu' : (elimOv N ov gs (initOv N y v ov)).1.getD u' (Sum.inl false) = Sum.inl false) :
    (elimOv N ov gs (initOv N y v ov)).1.getD (N + p) (Sum.inl false) = Sum.inl false := by
  obtain ⟨w, hw⟩ := elimOv_gate_step N y v ov gs hcl p g hp hno
  rw [hw, hop]; rcases hin with e | e <;> rw [e, List.map_cons, List.map_cons, List.map_nil, hu, hu'] <;> rfl

theorem elimOv_true_ne_out {N : ℕ} {F1 F2 : (Fin N → Bool) → Bool} {gs' : List Gate} {o1 o2 : ℕ}
    {y : Fin N} {v : Bool} {ov : ℕ → Option Bool}
    (hcl' : CleanL N gs')
    (hnc1 : ∃ x x' : Fin N → Bool, F1 (Function.update x y v) ≠ F1 (Function.update x' y v))
    (hnc2 : ∃ x x' : Fin N → Bool, F2 (Function.update x y v) ≠ F2 (Function.update x' y v))
    (hcov : ∀ x : Fin N → Bool,
      (¬ GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v)))
          (wiresFrom gs' (List.ofFn (Function.update x y v))).length) →
      F1 (Function.update x y v) = true ∧ F2 (Function.update x y v) = true)
    (heq : ∀ x : Fin N → Bool,
      GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update x y v)))
          (wiresFrom gs' (List.ofFn (Function.update x y v))).length →
      vl gs' (Function.update x y v) o1 = F1 (Function.update x y v) ∧
      vl gs' (Function.update x y v) o2 = F2 (Function.update x y v))
    (w : ℕ)
    (ht : (elimOv N ov gs' (initOv N y.val v ov)).1.getD w (Sum.inl false) = Sum.inl true) :
    o1 ≠ w ∧ o2 ≠ w := by
  have hinv := fun x => invOv_elim N ov (List.ofFn x) (by simp) gs' _ (initOv N y.val v ov)
    (fun g hg => (clean_nok N gs' hcl' g hg).1) (invOv_init N y v ov x)
  constructor
  · intro e; subst e
    obtain ⟨x, x', hne⟩ := hnc1
    have hall : ∀ z : Fin N → Bool, F1 (Function.update z y v) = true := by
      intro z
      by_cases hg : GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update z y v)))
          (wiresFrom gs' (List.ofFn (Function.update z y v))).length
      · rw [← (heq z hg).1]
        have := (hinv z).2.2.2.2 hg o1
        rw [ht] at this; exact this.symm
      · exact (hcov z hg).1
    exact hne (by rw [hall x, hall x'])
  · intro e; subst e
    obtain ⟨x, x', hne⟩ := hnc2
    have hall : ∀ z : Fin N → Bool, F2 (Function.update z y v) = true := by
      intro z
      by_cases hg : GoodUpTo ov (wiresFrom gs' (List.ofFn (Function.update z y v)))
          (wiresFrom gs' (List.ofFn (Function.update z y v))).length
      · rw [← (heq z hg).2]
        have := (hinv z).2.2.2.2 hg o2
        rw [ht] at this; exact this.symm
      · exact (hcov z hg).2
    exact hne (by rw [hall x, hall x'])

theorem binChain_elim_const {N : ℕ} {D : Finset (Fin N)} {gs gs' : List Gate} {a : Fin N}
    {hasNot : Bool} {base : List ℕ} {w0 : ℕ} {v : Bool} {ov : ℕ → Option Bool}
    (hcl : CleanL N gs) (hcl' : CleanL N gs') (hlen : gs'.length = gs.length)
    (haD : a ∈ D) (hb : BinBase N gs a hasNot base w0)
    (hbase_eq : ∀ q ∈ base, gs'[q]? = gs[q]?)
    (hbase_ov : ∀ q ∈ base, ov (N + q) = none) :
    ∀ {bs : List ℕ} {w' : ℕ}, BinChain N D gs w0 bs w' →
    (∀ p ∈ bs, gs'[p]? = gs[p]?) →
    (∀ p ∈ bs, ov (N + p) = none) →
    (∀ p ∈ bs, ∀ g h, gs[p]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      h ∈ g.inputs → DFree D gs h →
      (g.op = GateOp.or → xor v hasNot = false → ov h = some false) ∧
      (g.op = GateOp.and → xor v hasNot = true → ov h = some true)) →
    let acc := elimOv N ov gs' (initOv N a.val v ov)
    acc.1.getD w0 (Sum.inl false) = Sum.inl (xor v hasNot) ∧
    (∀ q ∈ base, ∃ g, gs'[q]? = some g ∧ ∃ u ∈ g.inputs, u < N + q ∧
      ∃ c, acc.1.getD u (Sum.inl false) = Sum.inl c) ∧
    acc.1.getD w' (Sum.inl false) = Sum.inl (xor v hasNot) ∧
    (∀ p ∈ bs, ∃ g, gs'[p]? = some g ∧ ∃ u ∈ g.inputs, u < N + p ∧
      ∃ c, acc.1.getD u (Sum.inl false) = Sum.inl c) := by
  have hw0_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD w0 (Sum.inl false) =
      Sum.inl (xor v hasNot) ∧
      ∀ q ∈ base, ∃ g, gs'[q]? = some g ∧ ∃ u ∈ g.inputs, u < N + q ∧
        ∃ c, (elimOv N ov gs' (initOv N a.val v ov)).1.getD u (Sum.inl false) = Sum.inl c := by
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨?_, fun _ hm => by simp at hm⟩
      simpa using elimOv_input_y N a.val v ov gs' a.isLt
    · simp only [BinBase, ↓reduceIte] at hb
      obtain ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0, _⟩ := hb
      have hg0' : gs'[g0]? = some gg0 := by rw [hbase_eq g0 List.mem_cons_self]; exact hg0
      have ha_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD a.val (Sum.inl false) = Sum.inl v :=
        elimOv_input_y N a.val v ov gs' a.isLt
      have hg0_st := elimOv_not_const N a.val v ov gs' hcl' g0 a.val gg0 hg0' hop0 hin0
        (hbase_ov g0 List.mem_cons_self) v ha_st
      refine ⟨by simpa using hg0_st, fun q hq => ?_⟩
      simp at hq; subst hq
      exact ⟨gg0, hg0', a.val, by rw [hin0]; simp, by have := a.isLt; omega, v, ha_st⟩
  intro bs
  induction bs with
  | nil =>
    intro w' hbc _ _ _
    change w' = w0 at hbc; subst hbc
    exact ⟨hw0_st.1, hw0_st.2, hw0_st.1, fun _ hm => by simp at hm⟩
  | cons p bs ih =>
    intro w' hbc hbs_eq hbs_ov hov_h
    obtain ⟨rfl, u, g, h', hbc0, hgp, hop, hin, hf, _⟩ := hbc
    obtain ⟨_, _, hu_st, hE0⟩ := ih hbc0
      (fun q hq => hbs_eq q (List.mem_cons_of_mem _ hq))
      (fun q hq => hbs_ov q (List.mem_cons_of_mem _ hq))
      (fun q hq => hov_h q (List.mem_cons_of_mem _ hq))
    have hgp' : gs'[p]? = some g := by rw [hbs_eq p List.mem_cons_self]; exact hgp
    have hu_in : u ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hh_in : h' ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hu_lt : u < N + p := (hcl p g hgp).lt u hu_in
    have hh_lt : h' < N + p := (hcl p g hgp).lt h' hh_in
    have hp_len : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
    have hha_ne : h' ≠ a.val := dfree_ne_a hf haD
    have hp_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD (N + p) (Sum.inl false) =
        Sum.inl (xor v hasNot) := by
      rcases hop with hop | hop
      · cases hc0 : xor v hasNot with
        | false =>
          rw [hc0] at hu_st
          exact elimOv_and_false N a.val v ov gs' hcl' p u g hgp' hop hu_in
            (hbs_ov p List.mem_cons_self) hu_st
        | true =>
          rw [hc0] at hu_st
          have hovh := (hov_h p List.mem_cons_self g h' hgp (Or.inl hop) hh_in hf).2 hop hc0
          have hh_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD h' (Sum.inl false) = Sum.inl true :=
            elimOv_ov_val N a.val v ov gs' h' (by omega) hha_ne true hovh
          exact elimOv_and_true N a.val v ov gs' hcl' p u h' g hgp' hop hin
            (hbs_ov p List.mem_cons_self) hu_st hh_st
      · cases hc0 : xor v hasNot with
        | true =>
          rw [hc0] at hu_st
          exact elimOv_or_true N a.val v ov gs' hcl' p u g hgp' hop hu_in
            (hbs_ov p List.mem_cons_self) hu_st
        | false =>
          rw [hc0] at hu_st
          have hovh := (hov_h p List.mem_cons_self g h' hgp (Or.inr hop) hh_in hf).1 hop hc0
          have hh_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD h' (Sum.inl false) = Sum.inl false :=
            elimOv_ov_val N a.val v ov gs' h' (by omega) hha_ne false hovh
          exact elimOv_or_false N a.val v ov gs' hcl' p u h' g hgp' hop hin
            (hbs_ov p List.mem_cons_self) hu_st hh_st
    refine ⟨hw0_st.1, hw0_st.2, hp_st, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨g, hgp', u, hu_in, hu_lt, xor v hasNot, hu_st⟩
    · exact hE0 q hq'

theorem binChain_vl_const {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {a : Fin N}
    {hasNot : Bool} {base : List ℕ} {w0 : ℕ} {v : Bool}
    (hcl : CleanL N gs) (haD : a ∈ D) (hb : BinBase N gs a hasNot base w0) (x : Fin N → Bool) (hxa : x a = v) :
    ∀ {bs : List ℕ} {w' : ℕ}, BinChain N D gs w0 bs w' →
    (∀ p ∈ bs, ∀ g h, gs[p]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      h ∈ g.inputs → DFree D gs h →
      (g.op = GateOp.or → xor v hasNot = false → vl gs x h = false) ∧
      (g.op = GateOp.and → xor v hasNot = true → vl gs x h = true)) →
    vl gs x w0 = xor v hasNot ∧ vl gs x w' = xor v hasNot ∧
    (∀ p ∈ bs, vl gs x (N + p) = xor v hasNot) ∧
    (∀ p ∈ bs, ∀ g, gs[p]? = some g → ∃ u ∈ g.inputs, suppD D gs u = {a} ∧ vl gs x u = xor v hasNot) := by
  have hw0_vl : vl gs x w0 = xor v hasNot := by
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hb
      obtain ⟨rfl, rfl⟩ := hb; rw [vl_input gs x a.val a.isLt, hxa]; simp
    · simp only [BinBase, ↓reduceIte] at hb
      obtain ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0, _⟩ := hb
      rw [vl_not gs hcl x g0 gg0 hg0 a.val hop0 hin0, vl_input gs x a.val a.isLt, hxa]; simp
  intro bs
  induction bs with
  | nil =>
    intro w' hbc _
    change w' = w0 at hbc; subst hbc
    exact ⟨hw0_vl, hw0_vl, fun _ hm => by simp at hm, fun _ hm => by simp at hm⟩
  | cons p bs ih =>
    intro w' hbc hcond
    obtain ⟨rfl, u, g, h', hbc0, hgp, hop, hin, hf, _⟩ := hbc
    obtain ⟨_, hu_vl, hbs_vl, hbs_u⟩ := ih hbc0 (fun q hq => hcond q (List.mem_cons_of_mem _ hq))
    have hu_in : u ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hh_in : h' ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hp_vl : vl gs x (N + p) = xor v hasNot := by
      rcases hop with hop | hop
      · cases hc0 : xor v hasNot with
        | false =>
          rw [hc0] at hu_vl
          rw [(vl_bin gs hcl x p u h' g hgp hin).2 hop, hu_vl, Bool.false_and]
        | true =>
          rw [hc0] at hu_vl
          have hh := (hcond p List.mem_cons_self g h' hgp (Or.inl hop) hh_in hf).2 hop hc0
          rw [(vl_bin gs hcl x p u h' g hgp hin).2 hop, hu_vl, hh]; rfl
      · cases hc0 : xor v hasNot with
        | true =>
          rw [hc0] at hu_vl
          rw [(vl_bin gs hcl x p u h' g hgp hin).1 hop, hu_vl, Bool.true_or]
        | false =>
          rw [hc0] at hu_vl
          have hh := (hcond p List.mem_cons_self g h' hgp (Or.inr hop) hh_in hf).1 hop hc0
          rw [(vl_bin gs hcl x p u h' g hgp hin).1 hop, hu_vl, hh]; rfl
    refine ⟨hw0_vl, hp_vl, fun q hq => ?_, fun q hq gq hgq => ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact hp_vl
      · exact hbs_vl q hq'
    · rcases List.mem_cons.1 hq with rfl | hq'
      · rw [hgp] at hgq; cases hgq
        have hsu := (binChain_suppD hcl (binBase_suppD hcl haD hb).1 hbc0).1
        exact ⟨u, hu_in, hsu, hu_vl⟩
      · exact hbs_u q hq' gq hgq

theorem binChain_split {n : ℕ} {F1 F2 : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o1 o2 : ℕ} {a : Fin (n + 1)} {hasNot : Bool} {base : List ℕ} {w0 : ℕ}
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D)
    (L : Least2 (n + 1) F1 F2 gs o1 o2) (hext : ExtProps2 n F1 F2 D gs)
    (haD : a ∈ D) (hb : BinBase (n + 1) gs a hasNot base w0) :
    ∀ {bs : List ℕ} {w' : ℕ}, BinChain (n + 1) D gs w0 bs w' →
    ∃ (Os As : List (ℕ × ℕ)),
      Os.length + As.length = bs.length ∧
      (Os.map Prod.fst).Nodup ∧ (As.map Prod.fst).Nodup ∧
      (∀ p, p ∈ bs ↔ (∃ h, (p, h) ∈ Os) ∨ (∃ h, (p, h) ∈ As)) ∧
      (∀ p h, (p, h) ∈ Os → ∃ u g ph, gs[p]? = some g ∧ g.op = GateOp.or ∧
        (g.inputs = [u, h] ∨ g.inputs = [h, u]) ∧ DFree D gs h ∧ suppD D gs u = {a} ∧
        (∀ x, vl gs x h = true → F1 x = true ∧ F2 x = true) ∧
        (∀ r, Reads gs r h → r = p) ∧ h = n + 1 + ph ∧ ph < gs.length) ∧
      (∀ p h, (p, h) ∈ As → ∃ u g, gs[p]? = some g ∧ g.op = GateOp.and ∧
        (g.inputs = [u, h] ∨ g.inputs = [h, u]) ∧ DFree D gs h ∧ suppD D gs u = {a} ∧
        (∀ x, vl gs x h = false → F1 x = true ∧ F2 x = true) ∧
        ((∀ r, Reads gs r h → r = p) → ∃ ph, h = n + 1 + ph ∧ ph < gs.length)) := by
  intro bs
  induction bs with
  | nil =>
    intro w' _
    refine ⟨[], [], rfl, List.nodup_nil, List.nodup_nil, by simp, ?_, ?_⟩
    · intro _ _ hm; simp at hm
    · intro _ _ hm; simp at hm
  | cons p bs ih =>
    intro w' hbc
    obtain ⟨rfl, u, g, h, hbc0, hgp, hop, hin, hf, honly⟩ := hbc
    obtain ⟨Os, As, hlen, hndO, hndA, hiff, hOs, hAs⟩ := ih hbc0
    have hch0 : IsChain (n + 1) D gs a (bs ++ base) u := binChain_isChain hb hbc0
    have hch1 : IsChain (n + 1) D gs a (p :: (bs ++ base)) (n + 1 + p) :=
      ⟨rfl, u, g, hch0, hgp, honly, Or.inr ⟨h, hop, hin, hf⟩⟩
    have hsu : suppD D gs u = {a} := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hb).1 hbc0).1
    have hp_not_bs : p ∉ bs := (List.nodup_cons.1 (binChain_nodup L.hcl
      (⟨rfl, u, g, h, hbc0, hgp, hop, hin, hf, honly⟩ :
        BinChain (n + 1) D gs w0 (p :: bs) (n + 1 + p)))).1
    have hcov1 : ∀ x, vl gs x h = fixBit g → F1 x = true :=
      chain_win_core H1 L.hcl L.hev1 haD hch0 p g h hgp honly hop hin hf
    have hcov2 : ∀ x, vl gs x h = fixBit g → F2 x = true :=
      chain_win_core H2 L.hcl L.hev2 haD hch0 p g h hgp honly hop hin hf
    have hh_in : h ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hh_lt : h < n + 1 + p := (L.hcl p g hgp).lt h hh_in
    have hp_len : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
    rcases hop with hop | hop
    · refine ⟨Os, (p, h) :: As, by simp; omega, hndO, List.nodup_cons.2 ⟨?_, hndA⟩, ?_, hOs, ?_⟩
      · intro hm
        obtain ⟨⟨p', h'⟩, hmem, heq⟩ := List.mem_map.1 hm
        simp only at heq; subst heq
        exact hp_not_bs ((hiff p').2 (Or.inr ⟨h', hmem⟩))
      · intro q
        simp only [List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (rfl | hq)
          · exact Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩
          · rcases (hiff q).1 hq with ⟨h', hh'⟩ | ⟨h', hh'⟩
            · exact Or.inl ⟨h', hh'⟩
            · exact Or.inr ⟨h', Or.inr hh'⟩
        · rintro (⟨h', hh'⟩ | ⟨h', ⟨rfl, _⟩ | hh'⟩)
          · exact Or.inr ((hiff q).2 (Or.inl ⟨h', hh'⟩))
          · exact Or.inl rfl
          · exact Or.inr ((hiff q).2 (Or.inr ⟨h', hh'⟩))
      · intro q h' hmem
        rcases List.mem_cons.1 hmem with e | hmem'
        · cases e
          refine ⟨u, g, hgp, hop, hin, hf, hsu, fun x hx => ?_, fun honlyh => ?_⟩
          · have hfbit : fixBit g = false := by simp [fixBit, hop]
            exact ⟨hcov1 x (by rw [hfbit]; exact hx), hcov2 x (by rw [hfbit]; exact hx)⟩
          · have hge := dfree_input_two_readers H1 L.hcl L.hev1 haD hch0 hgp (Or.inl hop)
              hin hf honly honlyh
            exact ⟨h - (n + 1), by omega, by omega⟩
        · exact hAs q h' hmem'
    · have hnt : ¬ TailOK2 (n + 1) F1 F2 gs p :=
        chain_not_tailOK2 H1 H2 L.hcl L.hev1 L.hev2 haD hch1 p List.mem_cons_self g hgp hop
      have hcov_or : ∀ x, vl gs x h = true → F1 x = true ∧ F2 x = true := fun x hx => by
        have hfbit : fixBit g = true := by simp [fixBit, hop]
        exact ⟨hcov1 x (by rw [hfbit]; exact hx), hcov2 x (by rw [hfbit]; exact hx)⟩
      have honlyh : ∀ r, Reads gs r h → r = p := hext.1 h p g hf hgp hop hh_in hnt hcov_or
      have hge := dfree_input_two_readers H1 L.hcl L.hev1 haD hch0 hgp (Or.inr hop)
        hin hf honly honlyh
      refine ⟨(p, h) :: Os, As, by simp; omega, List.nodup_cons.2 ⟨?_, hndO⟩, hndA, ?_, ?_, hAs⟩
      · intro hm
        obtain ⟨⟨p', h'⟩, hmem, heq⟩ := List.mem_map.1 hm
        simp only at heq; subst heq
        exact hp_not_bs ((hiff p').2 (Or.inl ⟨h', hmem⟩))
      · intro q
        simp only [List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (rfl | hq)
          · exact Or.inl ⟨h, Or.inl ⟨rfl, rfl⟩⟩
          · rcases (hiff q).1 hq with ⟨h', hh'⟩ | ⟨h', hh'⟩
            · exact Or.inl ⟨h', Or.inr hh'⟩
            · exact Or.inr ⟨h', hh'⟩
        · rintro (⟨h', ⟨rfl, _⟩ | hh'⟩ | ⟨h', hh'⟩)
          · exact Or.inl rfl
          · exact Or.inr ((hiff q).2 (Or.inl ⟨h', hh'⟩))
          · exact Or.inr ((hiff q).2 (Or.inr ⟨h', hh'⟩))
      · intro q h' hmem
        rcases List.mem_cons.1 hmem with e | hmem'
        · cases e
          exact ⟨u, g, h - (n + 1), hgp, hop, hin, hf, hsu, hcov_or, honlyh, by omega, by omega⟩
        · exact hOs q h' hmem'

theorem end_two_gates {N : ℕ} {D : Finset (Fin N)} {gs gs' : List Gate} {a : Fin N}
    {w' : ℕ} {v c0 : Bool} {ov : ℕ → Option Bool}
    (hcl : CleanL N gs) (hcl' : CleanL N gs') (hsw' : suppD D gs w' = {a})
    (hdead_free : ∀ q, gs'[q]? ≠ gs[q]? → DFree D gs (N + q))
    (hov_free : ∀ w, ov w ≠ none → DFree D gs w)
    (hw'_st : (elimOv N ov gs' (initOv N a.val v ov)).1.getD w' (Sum.inl false) = Sum.inl c0)
    (hend : (∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w' ∧ Reads gs T2 w') ∨
      (∃ gm ggm T, gs[gm]? = some ggm ∧ ggm.op = GateOp.not ∧ ggm.inputs = [w'] ∧
        Reads gs T (N + gm) ∧ ∀ r, Reads gs r w' → r = gm)) :
    ∃ e1 e2 : ℕ, e1 ≠ e2 ∧ w' < N + e1 ∧ w' < N + e2 ∧
      a ∈ suppD D gs (N + e1) ∧ a ∈ suppD D gs (N + e2) ∧
      (∃ g, gs'[e1]? = some g ∧ ∃ u ∈ g.inputs, u < N + e1 ∧
        ∃ c, (elimOv N ov gs' (initOv N a.val v ov)).1.getD u (Sum.inl false) = Sum.inl c) ∧
      (∃ g, gs'[e2]? = some g ∧ ∃ u ∈ g.inputs, u < N + e2 ∧
        ∃ c, (elimOv N ov gs' (initOv N a.val v ov)).1.getD u (Sum.inl false) = Sum.inl c) := by
  have ha_w' : a ∈ suppD D gs w' := by rw [hsw']; exact Finset.mem_singleton_self a
  rcases hend with ⟨T1, T2, h12, ⟨g1, hg1, hw1⟩, ⟨g2, hg2, hw2⟩⟩ |
    ⟨gm, ggm, T, hgm, hopm, hinm, ⟨gT, hgT, hmT⟩, _⟩
  · have ha1 : a ∈ suppD D gs (N + T1) := (suppD_gate D gs hcl T1 g1 hg1 a).2 ⟨w', hw1, ha_w'⟩
    have ha2 : a ∈ suppD D gs (N + T2) := (suppD_gate D gs hcl T2 g2 hg2 a).2 ⟨w', hw2, ha_w'⟩
    have hnf1 : ¬ DFree D gs (N + T1) := fun hf => hf a (Finset.mem_inter.1 ha1).2 (Finset.mem_inter.1 ha1).1
    have hnf2 : ¬ DFree D gs (N + T2) := fun hf => hf a (Finset.mem_inter.1 ha2).2 (Finset.mem_inter.1 ha2).1
    have hg1' : gs'[T1]? = some g1 := by
      by_contra hne; exact hnf1 (hdead_free T1 (by rw [hg1]; exact hne))
    have hg2' : gs'[T2]? = some g2 := by
      by_contra hne; exact hnf2 (hdead_free T2 (by rw [hg2]; exact hne))
    exact ⟨T1, T2, h12, (hcl T1 g1 hg1).lt w' hw1, (hcl T2 g2 hg2).lt w' hw2, ha1, ha2,
      ⟨g1, hg1', w', hw1, (hcl T1 g1 hg1).lt w' hw1, c0, hw'_st⟩,
      ⟨g2, hg2', w', hw2, (hcl T2 g2 hg2).lt w' hw2, c0, hw'_st⟩⟩
  · have hwm : w' ∈ ggm.inputs := by rw [hinm]; simp
    have ham : a ∈ suppD D gs (N + gm) := (suppD_gate D gs hcl gm ggm hgm a).2 ⟨w', hwm, ha_w'⟩
    have haT : a ∈ suppD D gs (N + T) := (suppD_gate D gs hcl T gT hgT a).2 ⟨N + gm, hmT, ham⟩
    have hnfm : ¬ DFree D gs (N + gm) := fun hf => hf a (Finset.mem_inter.1 ham).2 (Finset.mem_inter.1 ham).1
    have hnfT : ¬ DFree D gs (N + T) := fun hf => hf a (Finset.mem_inter.1 haT).2 (Finset.mem_inter.1 haT).1
    have hgm' : gs'[gm]? = some ggm := by
      by_contra hne; exact hnfm (hdead_free gm (by rw [hgm]; exact hne))
    have hgT' : gs'[T]? = some gT := by
      by_contra hne; exact hnfT (hdead_free T (by rw [hgT]; exact hne))
    have hovm : ov (N + gm) = none := by
      by_contra hne; exact hnfm (hov_free (N + gm) hne)
    have hgm_st := elimOv_not_const N a.val v ov gs' hcl' gm w' ggm hgm' hopm hinm hovm c0 hw'_st
    have hlt1 : w' < N + gm := (hcl gm ggm hgm).lt w' hwm
    have hlt2 : N + gm < N + T := (hcl T gT hgT).lt (N + gm) hmT
    exact ⟨gm, T, by omega, hlt1, by omega, ham, haT,
      ⟨ggm, hgm', w', hwm, hlt1, c0, hw'_st⟩,
      ⟨gT, hgT', N + gm, hmT, hlt2, !c0, hgm_st⟩⟩

theorem solve_case4c {n : ℕ} {F1 F2 : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o1 o2 pO pA phO hA rA qA w' : ℕ} {a b : Fin (n + 1)}
    {gpO gpA grA : Gate} {bs : List ℕ}
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D)
    (L : Least2 (n + 1) F1 F2 gs o1 o2)
    (haD : a ∈ D) (hbD : b ∈ D) (hab : a ≠ b)
    (hbc : BinChain (n + 1) D gs a.val bs w')
    (hbs : bs = [pA, pO] ∨ bs = [pO, pA])
    (hgpO : gs[pO]? = some gpO) (hopO : gpO.op = GateOp.or)
    (hgpA : gs[pA]? = some gpA) (hopA : gpA.op = GateOp.and)
    (hphO_lt : phO < gs.length)
    (hfree_ph : DFree D gs (n + 1 + phO)) (hfree_hA : DFree D gs hA)
    (hcovO : ∀ x, vl gs x (n + 1 + phO) = true → F1 x = true ∧ F2 x = true)
    (hcovA : ∀ x, vl gs x hA = false → F1 x = true ∧ F2 x = true)
    (honly_ph : ∀ r, Reads gs r (n + 1 + phO) → r = pO)
    (hrA_ne : rA ≠ pA) (hgrA : gs[rA]? = some grA) (hoprA : grA.op = GateOp.and)
    (hinrA : grA.inputs = [qA, hA] ∨ grA.inputs = [hA, qA])
    (hhA_lt_gs : hA < n + 1 + gs.length)
    (hord :
      ((gpO.inputs = [a.val, n + 1 + phO] ∨ gpO.inputs = [n + 1 + phO, a.val]) ∧
       (gpA.inputs = [n + 1 + pO, hA] ∨ gpA.inputs = [hA, n + 1 + pO]) ∧
       (∀ r, Reads gs r (n + 1 + pO) → r = pA) ∧ w' = n + 1 + pA) ∨
      ((gpA.inputs = [a.val, hA] ∨ gpA.inputs = [hA, a.val]) ∧
       (gpO.inputs = [n + 1 + pA, n + 1 + phO] ∨ gpO.inputs = [n + 1 + phO, n + 1 + pA]) ∧
       (∀ r, Reads gs r (n + 1 + pA) → r = pO) ∧ w' = n + 1 + pO))
    (hend : (∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w' ∧ Reads gs T2 w') ∨
      (∃ gm ggm T, gs[gm]? = some ggm ∧ ggm.op = GateOp.not ∧ ggm.inputs = [w'] ∧
        Reads gs T (n + 1 + gm) ∧ ∀ r, Reads gs r w' → r = gm)) :
    (∃ s' : ℕ, s' + 3 ≤ gs.length ∧
      HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
        (fun x => F2 (Function.update x a false)) s') ∨
    (∃ s' : ℕ, s' + 4 ≤ gs.length ∧
      HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
        (fun x => F2 (Function.update x a true)) s') := by
  classical
  have hnc1 := deepHyp'_nc H1 ⟨a, haD⟩
  have hnc2 := deepHyp'_nc H2 ⟨a, haD⟩
  have hpOA : pO ≠ pA := fun e => by subst e; rw [hgpO] at hgpA; cases hgpA; rw [hopO] at hopA; cases hopA
  have hbase : BinBase (n + 1) gs a false [] a.val := ⟨rfl, rfl⟩
  have hsw' : suppD D gs w' = {a} := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).1
  have ha_w' : a ∈ suppD D gs w' := by rw [hsw']; exact Finset.mem_singleton_self a
  have hpO_in_bs : pO ∈ bs := by rcases hbs with rfl | rfl <;> simp
  have hpA_in_bs : pA ∈ bs := by rcases hbs with rfl | rfl <;> simp
  have hle_pO : n + 1 + pO ≤ w' := (binChain_lt L.hcl hbc).2 pO hpO_in_bs
  have hle_pA : n + 1 + pA ≤ w' := (binChain_lt L.hcl hbc).2 pA hpA_in_bs
  have hphO_lt_pO : n + 1 + phO < n + 1 + pO := by
    rcases hord with ⟨hinO, _⟩ | ⟨_, hinO, _⟩
    · exact (L.hcl pO gpO hgpO).lt (n + 1 + phO) (by rcases hinO with e | e <;> rw [e] <;> simp)
    · exact (L.hcl pO gpO hgpO).lt (n + 1 + phO) (by rcases hinO with e | e <;> rw [e] <;> simp)
  have hphO_lt_gs : n + 1 + phO < n + 1 + gs.length := by omega
  have hrA_ne_phO : rA ≠ phO := by
    intro e; subst e
    exact no_rA_eq_phO L H1 H2 haD hbD hab hgpO hopO hgpA hopA hgrA hoprA hinrA
      hfree_ph hfree_hA honly_ph (by
        rcases hord with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h2, h3⟩)
  have hrA_ne_pO : rA ≠ pO := fun e => by subst e; rw [hgpO] at hgrA; cases hgrA; rw [hopO] at hoprA; cases hoprA
  have hphO_ne_a : n + 1 + phO ≠ a.val := by have := a.isLt; omega
  have hhA_ne_a : hA ≠ a.val := dfree_ne_a hfree_hA haD
  have hphO_ne_hA : n + 1 + phO ≠ hA := fun e =>
    hpOA (honly_ph pA ⟨gpA, hgpA, by
      rw [e]; rcases hord with ⟨_, hinA, _⟩ | ⟨hinA, _⟩ <;> rcases hinA with e' | e' <;> rw [e'] <;> simp⟩).symm
  have hrunF : ∀ (E : Finset ℕ),
      let ov := fun w => if w ∈ ({n + 1 + phO} : Finset ℕ) then some false else none
      let acc := elimOv (n + 1) ov gs (initOv (n + 1) a.val false ov)
      (∀ p ∈ E, ∃ g, gs[p]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + p ∧
        ∃ c, acc.1.getD u (Sum.inl false) = Sum.inl c) →
      (5 ≤ E.card ∨ (4 ≤ E.card ∧ (acc.1.getD o1 (Sum.inl false) = Sum.inl false ∨
        acc.1.getD o2 (Sum.inl false) = Sum.inl false))) →
      ∃ s' : ℕ, s' + 3 ≤ gs.length ∧
        HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
          (fun x => F2 (Function.update x a false)) s' := by
    dsimp only; intro E hE hcard
    have hres := restore_O (n + 1) F1 F2 gs gs o1 o2 a false {n + 1 + phO}
      L.hcl (H1.nc a haD false) (H2.nc a haD false)
      (fun h hh => by simp at hh; rw [hh]; exact hphO_lt_gs)
      (fun h hh x hx => by simp at hh; rw [hh] at hx; exact hcovO _ hx)
      (fun x _ => L.hev _) E hE rfl
    dsimp only at hres
    obtain ⟨s', hs', hsz⟩ := hres
    refine ⟨s', ?_, hsz⟩
    simp only [Finset.singleton_ne_empty, ↓reduceIte, Finset.card_singleton, Nat.sub_self, zero_add] at hs'
    rcases hcard with h5 | ⟨h4, ho1f | ho2f⟩
    · split_ifs at hs' <;> omega
    · rw [ho1f] at hs'; simp only [↓reduceIte, zero_add] at hs'; split_ifs at hs' <;> omega
    · rw [ho2f] at hs'; simp only [↓reduceIte, add_zero] at hs'; split_ifs at hs' <;> omega
  let gsT := multiSwap gs {phO} a.val
  have hclT : CleanL (n + 1) gsT := multiSwap_clean gs {phO} a.val L.hcl a.isLt
  have hlenT : gsT.length = gs.length := multiSwap_length gs {phO} a.val
  have hgetT_ne : ∀ r, r ≠ phO → gsT[r]? = gs[r]? := fun r hr =>
    multiSwap_get_notMem gs {phO} a.val r (by simp [hr])
  have hgetT_ph : gsT[phO]? = some ⟨GateOp.not, [a.val]⟩ :=
    multiSwap_get_mem gs {phO} a.val phO hphO_lt (Finset.mem_singleton_self phO)
  have hphO_not_bs : phO ∉ bs := by
    intro hm
    have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 phO hm
    exact hfree_ph a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
  have hagreeT_dfree : ∀ x : Fin (n + 1) → Bool, vl gsT x hA = vl gs x hA := fun x =>
    multiSwap_agree_dfree gs {phO} a.val L.hcl a.isLt
      (fun ph hph r hr => by
        simp at hph; subst hph
        have rO : r = pO := honly_ph r hr; subst r
        intro hf
        have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pO hpO_in_bs
        exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1)
      x hA hfree_hA (fun ph hph => by simp at hph; subst hph; exact Ne.symm hphO_ne_hA)
  have hagreeT_out : ∀ x : Fin (n + 1) → Bool, vl gs (Function.update x a true) hA = true →
      vl gsT (Function.update x a true) o1 = F1 (Function.update x a true) ∧
      vl gsT (Function.update x a true) o2 = F2 (Function.update x a true) := by
    intro x hhA
    have hvl := binChain_vl_const L.hcl haD hbase (Function.update x a true)
      (Function.update_self _ _ _) hbc (fun p hp g h' hgp hop' hh' hf => by
        refine ⟨fun _ h => by simp at h, fun hopA' _ => ?_⟩
        have hpA' : p = pA := by
          rcases hbs with rfl | rfl <;> simp at hp <;> rcases hp with rfl | rfl
          · rfl
          · rw [hgpO] at hgp; cases hgp; rw [hopO] at hopA'; cases hopA'
          · rw [hgpO] at hgp; cases hgp; rw [hopO] at hopA'; cases hopA'
          · rfl
        subst hpA'; rw [hgpA] at hgp; cases hgp
        have hh'eq : h' = hA := by
          rcases hord with ⟨_, hinA, _⟩ | ⟨hinA, _⟩
          · rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
            · rcases hh' with rfl | rfl
              · exfalso
                have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pO hpO_in_bs
                exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
              · rfl
            · rcases hh' with rfl | rfl
              · rfl
              · exfalso
                have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pO hpO_in_bs
                exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
          · rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
            · rcases hh' with rfl | rfl
              · exact absurd rfl (dfree_ne_a hf haD)
              · rfl
            · rcases hh' with rfl | rfl
              · rfl
              · exact absurd rfl (dfree_ne_a hf haD)
        rw [hh'eq]; exact hhA)
    have hag := multiSwap_agree gs {phO} a.val L.hcl a.isLt (Function.update x a true)
      (fun r g hr _ ⟨ph, hph, hmem⟩ => by
        simp at hph; subst hph
        have rO : r = pO := honly_ph r ⟨g, hr, hmem⟩; subst r
        rw [hgpO] at hr; cases hr
        obtain ⟨u, hu, hsu, huvl⟩ := hvl.2.2.2 pO hpO_in_bs gpO hgpO
        refine ⟨u, hu, fun ph' hph' e => ?_, Or.inr hopO, by simpa [fixBit, hopO] using huvl⟩
        simp at hph'; subst hph'
        exact hfree_ph a haD (Finset.mem_inter.1 (e ▸ hsu ▸ Finset.mem_singleton_self a)).1)
    have ho1_ne : ∀ ph ∈ ({phO} : Finset ℕ), o1 ≠ n + 1 + ph := fun ph hph e => by
      simp at hph; subst hph; exact hfree_ph a haD (e ▸ deepHyp'_supp H1 L.hev1 haD)
    have ho2_ne : ∀ ph ∈ ({phO} : Finset ℕ), o2 ≠ n + 1 + ph := fun ph hph e => by
      simp at hph; subst hph; exact hfree_ph a haD (e ▸ deepHyp'_supp H2 L.hev2 haD)
    exact ⟨by rw [hag o1 ho1_ne, L.hev1], by rw [hag o2 ho2_ne, L.hev2]⟩
  have hrunT : ∀ (E : Finset ℕ),
      let ov := fun w => if w = hA then some true else none
      let acc := elimOv (n + 1) ov gsT (initOv (n + 1) a.val true ov)
      (∀ p ∈ E, ∃ g, gsT[p]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + p ∧
        ∃ c, acc.1.getD u (Sum.inl false) = Sum.inl c) →
      (7 ≤ E.card ∨ (6 ≤ E.card ∧ (acc.1.getD o1 (Sum.inl false) = Sum.inl false ∨
        acc.1.getD o2 (Sum.inl false) = Sum.inl false))) →
      ∃ s' : ℕ, s' + 4 ≤ gs.length ∧
        HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
          (fun x => F2 (Function.update x a true)) s' := by
    dsimp only; intro E hE hcard
    have hres := restore_A1 (n + 1) F1 F2 gs gsT o1 o2 a true hA hclT
      (H1.nc a haD true) (H2.nc a haD true) (by omega)
      (fun x hx => hcovA _ (by rw [← hagreeT_dfree]; exact hx))
      (fun x hx => hagreeT_out x (by rw [← hagreeT_dfree]; exact hx))
      E hE hlenT
    dsimp only at hres
    obtain ⟨s', hs', hsz⟩ := hres
    refine ⟨s', ?_, hsz⟩
    rcases hcard with h7 | ⟨h6, ho1f | ho2f⟩
    · split_ifs at hs' <;> omega
    · rw [ho1f] at hs'; simp only [↓reduceIte, add_zero] at hs'; split_ifs at hs' <;> omega
    · rw [ho2f] at hs'; simp only [↓reduceIte, add_zero] at hs'; split_ifs at hs' <;> omega
  let ovF : ℕ → Option Bool := fun w => if w ∈ ({n + 1 + phO} : Finset ℕ) then some false else none
  let accF := elimOv (n + 1) ovF gs (initOv (n + 1) a.val false ovF)
  have hchainF := binChain_elim_const (gs' := gs) (v := false) (ov := ovF) L.hcl L.hcl rfl haD hbase
    (fun _ hm => by simp at hm) (fun _ hm => by simp at hm) hbc
    (fun _ _ => rfl)
    (fun p hp => by
      simp only [ovF, Finset.mem_singleton]
      split_ifs with heq
      · exfalso
        have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 p hp
        exact hfree_ph a haD (Finset.mem_inter.1 (heq ▸ hs ▸ Finset.mem_singleton_self a)).1
      · rfl)
    (fun p hp g h' hgp _ hh' hf => by
      refine ⟨fun hopO' _ => ?_, fun _ h => by simp at h⟩
      have hpO' : p = pO := by
        rcases hbs with rfl | rfl <;> simp at hp <;> rcases hp with rfl | rfl
        · rw [hgpA] at hgp; cases hgp; rw [hopA] at hopO'; cases hopO'
        · rfl
        · rfl
        · rw [hgpA] at hgp; cases hgp; rw [hopA] at hopO'; cases hopO'
      subst hpO'; rw [hgpO] at hgp; cases hgp
      have hh'eq : h' = n + 1 + phO := by
        rcases hord with ⟨hinO, _⟩ | ⟨_, hinO, _⟩
        · rcases hinO with e | e <;> rw [e] at hh' <;> simp at hh'
          · rcases hh' with rfl | rfl
            · exact absurd rfl (dfree_ne_a hf haD)
            · rfl
          · rcases hh' with rfl | rfl
            · rfl
            · exact absurd rfl (dfree_ne_a hf haD)
        · rcases hinO with e | e <;> rw [e] at hh' <;> simp at hh'
          · rcases hh' with rfl | rfl
            · exfalso
              have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pA hpA_in_bs
              exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
            · rfl
          · rcases hh' with rfl | rfl
            · rfl
            · exfalso
              have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pA hpA_in_bs
              exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
      simp [ovF, hh'eq])
  let ovT : ℕ → Option Bool := fun w => if w = hA then some true else none
  let accT := elimOv (n + 1) ovT gsT (initOv (n + 1) a.val true ovT)
  have hchainT := binChain_elim_const (gs' := gsT) (v := true) (ov := ovT) L.hcl hclT hlenT haD hbase
    (fun _ hm => by simp at hm) (fun _ hm => by simp at hm) hbc
    (fun p hp => hgetT_ne p (fun e => hphO_not_bs (e ▸ hp)))
    (fun p hp => by
      simp only [ovT]; split_ifs with heq
      · exfalso
        have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 p hp
        exact hfree_hA a haD (Finset.mem_inter.1 (heq ▸ hs ▸ Finset.mem_singleton_self a)).1
      · rfl)
    (fun p hp g h' hgp _ hh' hf => by
      refine ⟨fun _ h => by simp at h, fun hopA' _ => ?_⟩
      have hpA' : p = pA := by
        rcases hbs with rfl | rfl <;> simp at hp <;> rcases hp with rfl | rfl
        · rfl
        · rw [hgpO] at hgp; cases hgp; rw [hopO] at hopA'; cases hopA'
        · rw [hgpO] at hgp; cases hgp; rw [hopO] at hopA'; cases hopA'
        · rfl
      subst hpA'; rw [hgpA] at hgp; cases hgp
      have hh'eq : h' = hA := by
        rcases hord with ⟨_, hinA, _⟩ | ⟨hinA, _⟩
        · rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
          · rcases hh' with rfl | rfl
            · exfalso
              have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pO hpO_in_bs
              exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
            · rfl
          · rcases hh' with rfl | rfl
            · rfl
            · exfalso
              have hs := (binChain_suppD L.hcl (binBase_suppD L.hcl haD hbase).1 hbc).2 pO hpO_in_bs
              exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
        · rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
          · rcases hh' with rfl | rfl
            · exact absurd rfl (dfree_ne_a hf haD)
            · rfl
          · rcases hh' with rfl | rfl
            · rfl
            · exact absurd rfl (dfree_ne_a hf haD)
      simp [ovT, hh'eq])
  have hw'F : accF.1.getD w' (Sum.inl false) = Sum.inl false := by simpa [accF] using hchainF.2.2.1
  have hw'T : accT.1.getD w' (Sum.inl false) = Sum.inl true := by simpa [accT] using hchainT.2.2.1
  have hE_phO_T : ∃ g, gsT[phO]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + phO ∧
      ∃ c, accT.1.getD u (Sum.inl false) = Sum.inl c :=
    ⟨⟨GateOp.not, [a.val]⟩, hgetT_ph, a.val, by simp, by have := a.isLt; omega, true,
      elimOv_input_y (n + 1) a.val true ovT gsT a.isLt⟩
  have hhA_stT : accT.1.getD hA (Sum.inl false) = Sum.inl true :=
    elimOv_ov_val (n + 1) a.val true ovT gsT hA (by omega) hhA_ne_a true (by simp [ovT])
  have hE_rA_T : ∃ g, gsT[rA]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + rA ∧
      ∃ c, accT.1.getD u (Sum.inl false) = Sum.inl c :=
    ⟨grA, by rw [hgetT_ne rA hrA_ne_phO]; exact hgrA, hA, by rcases hinrA with e | e <;> rw [e] <;> simp,
      (L.hcl rA grA hgrA).lt hA (by rcases hinrA with e | e <;> rw [e] <;> simp), true, hhA_stT⟩
  have htrueF_ne : ∀ w, accF.1.getD w (Sum.inl false) = Sum.inl true → o1 ≠ w ∧ o2 ≠ w := fun w hw =>
    elimOv_true_ne_out L.hcl (H1.nc a haD false) (H2.nc a haD false)
      (fun x hng => by
        by_contra hno
        have hfalse : vl gs (Function.update x a false) (n + 1 + phO) = false := by
          by_contra hnt; exact hno (hcovO _ (by simpa using hnt))
        exact hng (fun j _ b' hb' => by
          simp only [ovF, Finset.mem_singleton] at hb'
          split_ifs at hb' with hjeq; subst hjeq; cases hb'; exact hfalse))
      (fun x _ => L.hev _) w hw
  have htrueT_ne : ∀ w, accT.1.getD w (Sum.inl false) = Sum.inl true → o1 ≠ w ∧ o2 ≠ w := fun w hw =>
    elimOv_true_ne_out hclT (H1.nc a haD true) (H2.nc a haD true)
      (fun x hng => by
        by_contra hno
        have htrue : vl gsT (Function.update x a true) hA = true := by
          by_contra hnf
          exact hno (hcovA _ (by rw [← hagreeT_dfree]; simpa using hnf))
        exact hng (fun j _ b' hb' => by
          simp only [ovT] at hb'
          split_ifs at hb' with hjeq; subst hjeq; cases hb'; exact htrue))
      (fun x hg => by
        have hwl : (wiresFrom gsT (List.ofFn (Function.update x a true))).length = n + 1 + gsT.length := by
          rw [length_wiresFrom]; simp
        have hht : vl gsT (Function.update x a true) hA = true :=
          hg hA (by rw [hwl]; omega) true (by simp [ovT])
        exact hagreeT_out x (by rw [← hagreeT_dfree]; exact hht))
      w hw
  rcases hend with ⟨T1, T2, h12, ⟨g1, hg1, hw1⟩, ⟨g2, hg2, hw2⟩⟩ |
    ⟨gm, ggm, T, hgm, hopm, hinm, ⟨gT, hgT, hmT⟩, honly_w'⟩
  · have hT1_gt : w' < n + 1 + T1 := (L.hcl T1 g1 hg1).lt w' hw1
    have hT2_gt : w' < n + 1 + T2 := (L.hcl T2 g2 hg2).lt w' hw2
    have haT1 : a ∈ suppD D gs (n + 1 + T1) := (suppD_gate D gs L.hcl T1 g1 hg1 a).2 ⟨w', hw1, ha_w'⟩
    have haT2 : a ∈ suppD D gs (n + 1 + T2) := (suppD_gate D gs L.hcl T2 g2 hg2 a).2 ⟨w', hw2, ha_w'⟩
    have hT1_ne_ph : T1 ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haT1)).1
    have hT2_ne_ph : T2 ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haT2)).1
    have hnot_or : ∀ (Ta Tb : ℕ) (ga gb : Gate), Ta ≠ Tb →
        gs[Ta]? = some ga → w' ∈ ga.inputs → gs[Tb]? = some gb → w' ∈ gb.inputs →
        (ga.op = GateOp.and ∨ ga.op = GateOp.not) →
        ∃ s' : ℕ, s' + 3 ≤ gs.length ∧
          HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
            (fun x => F2 (Function.update x a false)) s' := by
      intro Ta Tb ga gb hab' hga hwa hgb hwb hopa
      have hTa_gt : w' < n + 1 + Ta := (L.hcl Ta ga hga).lt w' hwa
      have hTb_gt : w' < n + 1 + Tb := (L.hcl Tb gb hgb).lt w' hwb
      have haTa : a ∈ suppD D gs (n + 1 + Ta) := (suppD_gate D gs L.hcl Ta ga hga a).2 ⟨w', hwa, ha_w'⟩
      have hova : ovF (n + 1 + Ta) = none := by
        simp only [ovF, Finset.mem_singleton]; split_ifs with e
        · exfalso; exact hfree_ph a haD (Finset.mem_inter.1 (e ▸ haTa)).1
        · rfl
      have hTa_st : ∃ c, accF.1.getD (n + 1 + Ta) (Sum.inl false) = Sum.inl c := by
        rcases hopa with ha' | hn'
        · exact ⟨false, elimOv_and_false (n + 1) a.val false ovF gs L.hcl Ta w' ga hga ha' hwa hova hw'F⟩
        · have hwa_in : ga.inputs = [w'] := by
            rcases L.hcl Ta ga hga with ⟨_, j, _, hin⟩ | ⟨h1, _⟩
            · rw [hin] at hwa; simp at hwa; subst hwa; exact hin
            · rcases h1 with h1 | h1 <;> rw [hn'] at h1 <;> cases h1
          exact ⟨true, elimOv_not_const (n + 1) a.val false ovF gs L.hcl Ta w' ga hga hn' hwa_in hova false hw'F⟩
      obtain ⟨ca, hca⟩ := hTa_st
      have hE4 : ∀ p ∈ ({pO, pA, Ta, Tb} : Finset ℕ), ∃ g, gs[p]? = some g ∧ ∃ u ∈ g.inputs,
          u < n + 1 + p ∧ ∃ c, accF.1.getD u (Sum.inl false) = Sum.inl c := by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hchainF.2.2.2 p hpO_in_bs
        · exact hchainF.2.2.2 p hpA_in_bs
        · exact ⟨ga, hga, w', hwa, hTa_gt, false, hw'F⟩
        · exact ⟨gb, hgb, w', hwb, hTb_gt, false, hw'F⟩
      have hcard4 : ({pO, pA, Ta, Tb} : Finset ℕ).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp; refine ⟨hpOA, by omega, by omega⟩),
          Finset.card_insert_of_notMem (by simp; refine ⟨by omega, by omega⟩),
          Finset.card_pair hab']
      by_cases hout : accF.1.getD o1 (Sum.inl false) = Sum.inl false ∨
          accF.1.getD o2 (Sum.inl false) = Sum.inl false
      · exact hrunF {pO, pA, Ta, Tb} hE4 (Or.inr ⟨by omega, hout⟩)
      · push Not at hout
        have ho1a : o1 ≠ n + 1 + Ta := by
          intro e; cases ca
          · exact hout.1 (by rw [e]; exact hca)
          · exact (htrueF_ne (n + 1 + Ta) hca).1 e
        have ho2a : o2 ≠ n + 1 + Ta := by
          intro e; cases ca
          · exact hout.2 (by rw [e]; exact hca)
          · exact (htrueF_ne (n + 1 + Ta) hca).2 e
        obtain ⟨U, hUTa, ⟨gU, hgU, hTaU⟩⟩ := L.live hnc1 hnc2 Ta
          (List.getElem?_eq_some_iff.1 hga).1 ho1a ho2a
        have hUTb : U ≠ Tb := by
          intro e; subst e
          exact L.no_tri hnc1 hnc2 Ta U w' ⟨ga, hga, hwa⟩ ⟨gb, hgb, hwb⟩ ⟨gU, hgU, hTaU⟩
        refine hrunF (insert U {pO, pA, Ta, Tb}) (fun p hp => ?_) (Or.inl ?_)
        · rcases Finset.mem_insert.1 hp with rfl | hp'
          · exact ⟨gU, hgU, n + 1 + Ta, hTaU, (L.hcl p gU hgU).lt _ hTaU, ca, hca⟩
          · exact hE4 p hp'
        · rw [Finset.card_insert_of_notMem (by simp; refine ⟨by omega, by omega, by omega, hUTb⟩), hcard4]
    have h1cases : g1.op = GateOp.and ∨ g1.op = GateOp.not ∨ g1.op = GateOp.or := by
      rcases L.hcl T1 g1 hg1 with ⟨h, _⟩ | ⟨h | h, _⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have h2cases : g2.op = GateOp.and ∨ g2.op = GateOp.not ∨ g2.op = GateOp.or := by
      rcases L.hcl T2 g2 hg2 with ⟨h, _⟩ | ⟨h | h, _⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    rcases h1cases with h1op | h1op | h1op
    · exact Or.inl (hnot_or T1 T2 g1 g2 h12 hg1 hw1 hg2 hw2 (Or.inl h1op))
    · exact Or.inl (hnot_or T1 T2 g1 g2 h12 hg1 hw1 hg2 hw2 (Or.inr h1op))
    · rcases h2cases with h2op | h2op | h2op
      · exact Or.inl (hnot_or T2 T1 g2 g1 h12.symm hg2 hw2 hg1 hw1 (Or.inl h2op))
      · exact Or.inl (hnot_or T2 T1 g2 g1 h12.symm hg2 hw2 hg1 hw1 (Or.inr h2op))
      · right
        have hrA_ne_T1 : rA ≠ T1 := fun e => by subst e; rw [hg1] at hgrA; cases hgrA; rw [h1op] at hoprA; cases hoprA
        have hrA_ne_T2 : rA ≠ T2 := fun e => by subst e; rw [hg2] at hgrA; cases hgrA; rw [h2op] at hoprA; cases hoprA
        have hT1_stT : accT.1.getD (n + 1 + T1) (Sum.inl false) = Sum.inl true := by
          have hov1 : ovT (n + 1 + T1) = none := by
            simp only [ovT]; split_ifs with e
            · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ haT1)).1
            · rfl
          exact elimOv_or_true (n + 1) a.val true ovT gsT hclT T1 w' g1
            (by rw [hgetT_ne T1 hT1_ne_ph]; exact hg1) h1op hw1 hov1 hw'T
        have hT2_stT : accT.1.getD (n + 1 + T2) (Sum.inl false) = Sum.inl true := by
          have hov2 : ovT (n + 1 + T2) = none := by
            simp only [ovT]; split_ifs with e
            · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ haT2)).1
            · rfl
          exact elimOv_or_true (n + 1) a.val true ovT gsT hclT T2 w' g2
            (by rw [hgetT_ne T2 hT2_ne_ph]; exact hg2) h2op hw2 hov2 hw'T
        let E6 : Finset ℕ := {phO, pO, pA, rA, T1, T2}
        have hE6_ok : ∀ p ∈ E6, ∃ g, gsT[p]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + p ∧
            ∃ c, accT.1.getD u (Sum.inl false) = Sum.inl c := by
          intro p hp; simp only [E6, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hE_phO_T
          · exact hchainT.2.2.2 p hpO_in_bs
          · exact hchainT.2.2.2 p hpA_in_bs
          · exact hE_rA_T
          · exact ⟨g1, by rw [hgetT_ne p hT1_ne_ph]; exact hg1, w', hw1, hT1_gt, true, hw'T⟩
          · exact ⟨g2, by rw [hgetT_ne p hT2_ne_ph]; exact hg2, w', hw2, hT2_gt, true, hw'T⟩
        have hcard6 : E6.card = 6 := by
          have hph_pO : phO ≠ pO := fun e => hphO_not_bs (e ▸ hpO_in_bs)
          have hph_pA : phO ≠ pA := fun e => hphO_not_bs (e ▸ hpA_in_bs)
          simp only [E6]
          rw [Finset.card_insert_of_notMem (by simp; exact ⟨hph_pO, hph_pA, hrA_ne_phO.symm, hT1_ne_ph.symm, hT2_ne_ph.symm⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hpOA, hrA_ne_pO.symm, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hrA_ne.symm, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hrA_ne_T1, hrA_ne_T2⟩),
            Finset.card_pair h12]
        obtain ⟨ho1T1, ho2T1⟩ := htrueT_ne (n + 1 + T1) hT1_stT
        obtain ⟨U, hUT1, ⟨gU, hgU, hT1U⟩⟩ := L.live hnc1 hnc2 T1
          (List.getElem?_eq_some_iff.1 hg1).1 ho1T1 ho2T1
        have haU : a ∈ suppD D gs (n + 1 + U) := (suppD_gate D gs L.hcl U gU hgU a).2 ⟨n + 1 + T1, hT1U, haT1⟩
        have hU_ne_ph : U ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haU)).1
        have hU_ne_T2 : U ≠ T2 := fun e =>
          L.no_tri hnc1 hnc2 T1 T2 w' ⟨g1, hg1, hw1⟩ ⟨g2, hg2, hw2⟩ (e ▸ ⟨gU, hgU, hT1U⟩)
        by_cases hUrA : U = rA
        · subst U
          rw [hgrA] at hgU; cases hgU
          have hqA_eq : qA = n + 1 + T1 := by
            rcases hinrA with e | e <;> rw [e] at hT1U <;> simp at hT1U
            · rcases hT1U with rfl | h'
              · rfl
              · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (h' ▸ haT1)).1
            · rcases hT1U with h' | rfl
              · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (h' ▸ haT1)).1
              · rfl
          have hovrA : ovT (n + 1 + rA) = none := by
            simp only [ovT]; split_ifs with e
            · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ haU)).1
            · rfl
          have hrA_stT : accT.1.getD (n + 1 + rA) (Sum.inl false) = Sum.inl true :=
            elimOv_and_true (n + 1) a.val true ovT gsT hclT rA (n + 1 + T1) hA grA
              (by rw [hgetT_ne rA hU_ne_ph]; exact hgrA) hoprA (by rw [← hqA_eq]; exact hinrA)
              hovrA hT1_stT hhA_stT
          obtain ⟨ho1r, ho2r⟩ := htrueT_ne (n + 1 + rA) hrA_stT
          obtain ⟨W, hWU, ⟨gW, hgW, hUW⟩⟩ := L.live hnc1 hnc2 rA
            (List.getElem?_eq_some_iff.1 hgrA).1 ho1r ho2r
          have haW : a ∈ suppD D gs (n + 1 + W) := (suppD_gate D gs L.hcl W gW hgW a).2 ⟨n + 1 + rA, hUW, haU⟩
          have hW_ne_ph : W ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haW)).1
          by_cases hWT2 : W = T2
          · subst W
            obtain ⟨ho1T2, ho2T2⟩ := htrueT_ne (n + 1 + T2) hT2_stT
            obtain ⟨W', hW'W, ⟨gW', hgW', hWW'⟩⟩ := L.live hnc1 hnc2 T2
              (List.getElem?_eq_some_iff.1 hg2).1 ho1T2 ho2T2
            have haW' : a ∈ suppD D gs (n + 1 + W') :=
              (suppD_gate D gs L.hcl W' gW' hgW' a).2 ⟨n + 1 + T2, hWW', haW⟩
            have hW'_ne_ph : W' ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haW')).1
            refine hrunT (insert W' E6) (fun p hp => ?_) (Or.inl ?_)
            · rcases Finset.mem_insert.1 hp with rfl | hp'
              · exact ⟨gW', by rw [hgetT_ne p hW'_ne_ph]; exact hgW', n + 1 + T2, hWW',
                  (L.hcl p gW' hgW').lt _ hWW', true, hT2_stT⟩
              · exact hE6_ok p hp'
            · rw [Finset.card_insert_of_notMem (by
                simp [E6]; exact ⟨hW'_ne_ph, by omega, by omega, by omega, by omega, by omega⟩), hcard6]
          · refine hrunT (insert W E6) (fun p hp => ?_) (Or.inl ?_)
            · rcases Finset.mem_insert.1 hp with rfl | hp'
              · exact ⟨gW, by rw [hgetT_ne p hW_ne_ph]; exact hgW, n + 1 + rA, hUW,
                  (L.hcl p gW hgW).lt _ hUW, true, hrA_stT⟩
              · exact hE6_ok p hp'
            · rw [Finset.card_insert_of_notMem (by
                simp [E6]; exact ⟨hW_ne_ph, by omega, by omega, by omega, by omega, hWT2⟩), hcard6]
        · refine hrunT (insert U E6) (fun p hp => ?_) (Or.inl ?_)
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨gU, by rw [hgetT_ne p hU_ne_ph]; exact hgU, n + 1 + T1, hT1U,
                (L.hcl p gU hgU).lt _ hT1U, true, hT1_stT⟩
            · exact hE6_ok p hp'
          · rw [Finset.card_insert_of_notMem (by
              simp [E6]; exact ⟨hU_ne_ph, by omega, by omega, hUrA, by omega, hU_ne_T2⟩), hcard6]
  · have hwm : w' ∈ ggm.inputs := by rw [hinm]; simp
    have hgm_gt : w' < n + 1 + gm := (L.hcl gm ggm hgm).lt w' hwm
    have hT_gt : n + 1 + gm < n + 1 + T := (L.hcl T gT hgT).lt (n + 1 + gm) hmT
    have ham : a ∈ suppD D gs (n + 1 + gm) := (suppD_gate D gs L.hcl gm ggm hgm a).2 ⟨w', hwm, ha_w'⟩
    have haT : a ∈ suppD D gs (n + 1 + T) := (suppD_gate D gs L.hcl T gT hgT a).2 ⟨n + 1 + gm, hmT, ham⟩
    have hgm_ne_ph : gm ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ ham)).1
    have hT_ne_ph : T ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haT)).1
    have hTcases : gT.op = GateOp.not ∨ gT.op = GateOp.or ∨ gT.op = GateOp.and := by
      rcases L.hcl T gT hgT with ⟨h, _⟩ | ⟨h | h, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    rcases hTcases with hTop | hTop | hTop
    · exfalso
      have hTin : gT.inputs = [n + 1 + gm] := by
        rcases L.hcl T gT hgT with ⟨_, j, _, hin⟩ | ⟨h1, _⟩
        · rw [hin] at hmT; simp at hmT; subst hmT; exact hin
        · rcases h1 with h1 | h1 <;> rw [hTop] at h1 <;> cases h1
      refine L.no_alias hnc1 hnc2 T (List.getElem?_eq_some_iff.1 hgT).1 w' (by omega) (fun x => ?_)
      rw [vl_not gs L.hcl x T gT hgT (n + 1 + gm) hTop hTin,
        vl_not gs L.hcl x gm ggm hgm w' hopm hinm]
      cases vl gs x w' <;> rfl
    · left
      have hovmF : ovF (n + 1 + gm) = none := by
        simp only [ovF, Finset.mem_singleton]; split_ifs with e
        · exfalso; exact hfree_ph a haD (Finset.mem_inter.1 (e ▸ ham)).1
        · rfl
      have hgm_stF : accF.1.getD (n + 1 + gm) (Sum.inl false) = Sum.inl true :=
        elimOv_not_const (n + 1) a.val false ovF gs L.hcl gm w' ggm hgm hopm hinm hovmF false hw'F
      have hovTF : ovF (n + 1 + T) = none := by
        simp only [ovF, Finset.mem_singleton]; split_ifs with e
        · exfalso; exact hfree_ph a haD (Finset.mem_inter.1 (e ▸ haT)).1
        · rfl
      have hT_stF : accF.1.getD (n + 1 + T) (Sum.inl false) = Sum.inl true :=
        elimOv_or_true (n + 1) a.val false ovF gs L.hcl T (n + 1 + gm) gT hgT hTop hmT hovTF hgm_stF
      obtain ⟨ho1T, ho2T⟩ := htrueF_ne (n + 1 + T) hT_stF
      obtain ⟨U, hUT, ⟨gU, hgU, hTU⟩⟩ := L.live hnc1 hnc2 T
        (List.getElem?_eq_some_iff.1 hgT).1 ho1T ho2T
      refine hrunF {pO, pA, gm, T, U} (fun p hp => ?_) (Or.inl ?_)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact hchainF.2.2.2 p hpO_in_bs
        · exact hchainF.2.2.2 p hpA_in_bs
        · exact ⟨ggm, hgm, w', hwm, hgm_gt, false, hw'F⟩
        · exact ⟨gT, hgT, n + 1 + gm, hmT, hT_gt, true, hgm_stF⟩
        · exact ⟨gU, hgU, n + 1 + T, hTU, (L.hcl p gU hgU).lt _ hTU, true, hT_stF⟩
      · rw [Finset.card_insert_of_notMem (by simp; refine ⟨hpOA, by omega, by omega, by omega⟩),
          Finset.card_insert_of_notMem (by simp; refine ⟨by omega, by omega, by omega⟩),
          Finset.card_insert_of_notMem (by simp; refine ⟨by omega, by omega⟩),
          Finset.card_pair (by omega)]
    · right
      have hovmT : ovT (n + 1 + gm) = none := by
        simp only [ovT]; split_ifs with e
        · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ ham)).1
        · rfl
      have hgm_stT : accT.1.getD (n + 1 + gm) (Sum.inl false) = Sum.inl false :=
        elimOv_not_const (n + 1) a.val true ovT gsT hclT gm w' ggm
          (by rw [hgetT_ne gm hgm_ne_ph]; exact hgm) hopm hinm hovmT true hw'T
      have hovTT : ovT (n + 1 + T) = none := by
        simp only [ovT]; split_ifs with e
        · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ haT)).1
        · rfl
      have hT_stT : accT.1.getD (n + 1 + T) (Sum.inl false) = Sum.inl false :=
        elimOv_and_false (n + 1) a.val true ovT gsT hclT T (n + 1 + gm) gT
          (by rw [hgetT_ne T hT_ne_ph]; exact hgT) hTop hmT hovTT hgm_stT
      have hph_pO : phO ≠ pO := fun e => hphO_not_bs (e ▸ hpO_in_bs)
      have hph_pA : phO ≠ pA := fun e => hphO_not_bs (e ▸ hpA_in_bs)
      by_cases hsec : ∃ T', T' ≠ T ∧ Reads gs T' (n + 1 + gm)
      · obtain ⟨T', hT'T, ⟨gT', hgT', hmT'⟩⟩ := hsec
        have hT'_gt : n + 1 + gm < n + 1 + T' := (L.hcl T' gT' hgT').lt (n + 1 + gm) hmT'
        have haT' : a ∈ suppD D gs (n + 1 + T') := (suppD_gate D gs L.hcl T' gT' hgT' a).2 ⟨n + 1 + gm, hmT', ham⟩
        have hT'_ne_ph : T' ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haT')).1
        let E6 : Finset ℕ := {phO, pO, pA, gm, T, T'}
        have hE6_ok : ∀ p ∈ E6, ∃ g, gsT[p]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + p ∧
            ∃ c, accT.1.getD u (Sum.inl false) = Sum.inl c := by
          intro p hp; simp only [E6, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hE_phO_T
          · exact hchainT.2.2.2 p hpO_in_bs
          · exact hchainT.2.2.2 p hpA_in_bs
          · exact ⟨ggm, by rw [hgetT_ne p hgm_ne_ph]; exact hgm, w', hwm, hgm_gt, true, hw'T⟩
          · exact ⟨gT, by rw [hgetT_ne p hT_ne_ph]; exact hgT, n + 1 + gm, hmT, hT_gt, false, hgm_stT⟩
          · exact ⟨gT', by rw [hgetT_ne p hT'_ne_ph]; exact hgT', n + 1 + gm, hmT', hT'_gt, false, hgm_stT⟩
        have hcard6 : E6.card = 6 := by
          simp only [E6]
          rw [Finset.card_insert_of_notMem (by simp; exact ⟨hph_pO, hph_pA, hgm_ne_ph.symm, hT_ne_ph.symm, hT'_ne_ph.symm⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hpOA, by omega, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨by omega, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨by omega, by omega⟩),
            Finset.card_pair hT'T.symm]
        by_cases hout : accT.1.getD o1 (Sum.inl false) = Sum.inl false ∨
            accT.1.getD o2 (Sum.inl false) = Sum.inl false
        · exact hrunT E6 hE6_ok (Or.inr ⟨by omega, hout⟩)
        · push Not at hout
          have ho1T : o1 ≠ n + 1 + T := fun e => hout.1 (by rw [e]; exact hT_stT)
          have ho2T : o2 ≠ n + 1 + T := fun e => hout.2 (by rw [e]; exact hT_stT)
          obtain ⟨U, hUT, ⟨gU, hgU, hTU⟩⟩ := L.live hnc1 hnc2 T
            (List.getElem?_eq_some_iff.1 hgT).1 ho1T ho2T
          have haU : a ∈ suppD D gs (n + 1 + U) := (suppD_gate D gs L.hcl U gU hgU a).2 ⟨n + 1 + T, hTU, haT⟩
          have hU_ne_ph : U ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haU)).1
          have hU_ne_T' : U ≠ T' := fun e =>
            L.no_tri hnc1 hnc2 T T' (n + 1 + gm) ⟨gT, hgT, hmT⟩ ⟨gT', hgT', hmT'⟩ (e ▸ ⟨gU, hgU, hTU⟩)
          refine hrunT (insert U E6) (fun p hp => ?_) (Or.inl ?_)
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨gU, by rw [hgetT_ne p hU_ne_ph]; exact hgU, n + 1 + T, hTU,
                (L.hcl p gU hgU).lt _ hTU, false, hT_stT⟩
            · exact hE6_ok p hp'
          · rw [Finset.card_insert_of_notMem (by
              simp [E6]; exact ⟨hU_ne_ph, by omega, by omega, by omega, by omega, hU_ne_T'⟩), hcard6]
      · push Not at hsec
        have honly_gm : ∀ r, Reads gs r (n + 1 + gm) → r = T := fun r hr => by
          by_contra hne; exact hsec r hne hr
        have hrA_ne_gm : rA ≠ gm := fun e => by subst e; rw [hgm] at hgrA; cases hgrA; rw [hopm] at hoprA; cases hoprA
        have hrA_ne_T : rA ≠ T := by
          intro e; subst e
          rw [hgT] at hgrA; cases hgrA
          have hqA_eq : qA = n + 1 + gm := by
            rcases hinrA with e' | e' <;> rw [e'] at hmT <;> simp at hmT
            · rcases hmT with rfl | h'
              · rfl
              · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (h' ▸ ham)).1
            · rcases hmT with h' | rfl
              · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (h' ▸ ham)).1
              · rfl
          rw [hqA_eq] at hinrA
          exact no_rA_eq_T L H1 H2 haD hbD hab hgpO hopO hgpA hopA hgm hopm hgT hTop hinrA
            hfree_ph hfree_hA honly_gm (by
              rcases hord with ⟨h1, h2, _, rfl⟩ | ⟨h1, h2, h3, rfl⟩
              · exact Or.inl ⟨h1, h2, hinm, honly_w'⟩
              · exact Or.inr ⟨h1, h2, hinm, h3, honly_w'⟩)
        let E6 : Finset ℕ := {phO, pO, pA, rA, gm, T}
        have hE6_ok : ∀ p ∈ E6, ∃ g, gsT[p]? = some g ∧ ∃ u ∈ g.inputs, u < n + 1 + p ∧
            ∃ c, accT.1.getD u (Sum.inl false) = Sum.inl c := by
          intro p hp; simp only [E6, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hE_phO_T
          · exact hchainT.2.2.2 p hpO_in_bs
          · exact hchainT.2.2.2 p hpA_in_bs
          · exact hE_rA_T
          · exact ⟨ggm, by rw [hgetT_ne p hgm_ne_ph]; exact hgm, w', hwm, hgm_gt, true, hw'T⟩
          · exact ⟨gT, by rw [hgetT_ne p hT_ne_ph]; exact hgT, n + 1 + gm, hmT, hT_gt, false, hgm_stT⟩
        have hcard6 : E6.card = 6 := by
          simp only [E6]
          rw [Finset.card_insert_of_notMem (by simp; exact ⟨hph_pO, hph_pA, hrA_ne_phO.symm, hgm_ne_ph.symm, hT_ne_ph.symm⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hpOA, hrA_ne_pO.symm, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hrA_ne.symm, by omega, by omega⟩),
            Finset.card_insert_of_notMem (by simp; exact ⟨hrA_ne_gm, hrA_ne_T⟩),
            Finset.card_pair (by omega)]
        by_cases hout : accT.1.getD o1 (Sum.inl false) = Sum.inl false ∨
            accT.1.getD o2 (Sum.inl false) = Sum.inl false
        · exact hrunT E6 hE6_ok (Or.inr ⟨by omega, hout⟩)
        · push Not at hout
          have ho1T : o1 ≠ n + 1 + T := fun e => hout.1 (by rw [e]; exact hT_stT)
          have ho2T : o2 ≠ n + 1 + T := fun e => hout.2 (by rw [e]; exact hT_stT)
          obtain ⟨U, hUT, ⟨gU, hgU, hTU⟩⟩ := L.live hnc1 hnc2 T
            (List.getElem?_eq_some_iff.1 hgT).1 ho1T ho2T
          have haU : a ∈ suppD D gs (n + 1 + U) := (suppD_gate D gs L.hcl U gU hgU a).2 ⟨n + 1 + T, hTU, haT⟩
          have hU_ne_ph : U ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haU)).1
          by_cases hUrA : U = rA
          · subst U
            rw [hgrA] at hgU; cases hgU
            have hovrA : ovT (n + 1 + rA) = none := by
              simp only [ovT]; split_ifs with e
              · exfalso; exact hfree_hA a haD (Finset.mem_inter.1 (e ▸ haU)).1
              · rfl
            have hrA_stT : accT.1.getD (n + 1 + rA) (Sum.inl false) = Sum.inl false :=
              elimOv_and_false (n + 1) a.val true ovT gsT hclT rA (n + 1 + T) grA
                (by rw [hgetT_ne rA hU_ne_ph]; exact hgrA) hoprA hTU hovrA hT_stT
            have ho1r : o1 ≠ n + 1 + rA := fun e => hout.1 (by rw [e]; exact hrA_stT)
            have ho2r : o2 ≠ n + 1 + rA := fun e => hout.2 (by rw [e]; exact hrA_stT)
            obtain ⟨W, hWU, ⟨gW, hgW, hUW⟩⟩ := L.live hnc1 hnc2 rA
              (List.getElem?_eq_some_iff.1 hgrA).1 ho1r ho2r
            have haW : a ∈ suppD D gs (n + 1 + W) := (suppD_gate D gs L.hcl W gW hgW a).2 ⟨n + 1 + rA, hUW, haU⟩
            have hW_ne_ph : W ≠ phO := fun e => hfree_ph a haD (Finset.mem_inter.1 (e ▸ haW)).1
            refine hrunT (insert W E6) (fun p hp => ?_) (Or.inl ?_)
            · rcases Finset.mem_insert.1 hp with rfl | hp'
              · exact ⟨gW, by rw [hgetT_ne p hW_ne_ph]; exact hgW, n + 1 + rA, hUW,
                  (L.hcl p gW hgW).lt _ hUW, false, hrA_stT⟩
              · exact hE6_ok p hp'
            · rw [Finset.card_insert_of_notMem (by
                simp [E6]; exact ⟨hW_ne_ph, by omega, by omega, by omega, by omega, by omega⟩), hcard6]
          · refine hrunT (insert U E6) (fun p hp => ?_) (Or.inl ?_)
            · rcases Finset.mem_insert.1 hp with rfl | hp'
              · exact ⟨gU, by rw [hgetT_ne p hU_ne_ph]; exact hgU, n + 1 + T, hTU,
                  (L.hcl p gU hgU).lt _ hTU, false, hT_stT⟩
              · exact hE6_ok p hp'
            · rw [Finset.card_insert_of_notMem (by
                simp [E6]; exact ⟨hU_ne_ph, by omega, by omega, hUrA, by omega, by omega⟩), hcard6]

theorem solve_chain {n : ℕ} {F1 F2 : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o1 o2 w0 w' : ℕ} {a b : Fin (n + 1)} {hasNot : Bool} {base bs : List ℕ}
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D)
    (L : Least2 (n + 1) F1 F2 gs o1 o2) (hext : ExtProps2 n F1 F2 D gs)
    (haD : a ∈ D) (hbD : b ∈ D) (hab : a ≠ b)
    (hbase : BinBase (n + 1) gs a hasNot base w0)
    (hbc : BinChain (n + 1) D gs w0 bs w') (hbsne : bs ≠ [])
    (hend : (∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w' ∧ Reads gs T2 w') ∨
      (∃ gm ggm T, gs[gm]? = some ggm ∧ ggm.op = GateOp.not ∧ ggm.inputs = [w'] ∧
        Reads gs T (n + 1 + gm) ∧ ∀ r, Reads gs r w' → r = gm)) :
    (∃ s' : ℕ, s' + 3 ≤ gs.length ∧
      HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
        (fun x => F2 (Function.update x a false)) s') ∨
    (∃ s' : ℕ, s' + 4 ≤ gs.length ∧
      HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
        (fun x => F2 (Function.update x a true)) s') := by
  classical
  obtain ⟨Os, As, hlenOA, hndO, hndA, hiffOA, hOs, hAs⟩ :=
    binChain_split H1 H2 L hext haD hbase hbc
  have hbase_nd : base.Nodup := by
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hbase
      rw [hbase.1]; exact List.nodup_nil
    · simp only [BinBase, ↓reduceIte] at hbase
      obtain ⟨g0, _, rfl, _⟩ := hbase; exact List.nodup_singleton g0
  have hbase_len : base.length = if hasNot then 1 else 0 := by
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hbase; simp [hbase.1]
    · simp only [BinBase, ↓reduceIte] at hbase
      obtain ⟨g0, _, rfl, _⟩ := hbase; simp
  have hbs_nd : bs.Nodup := binChain_nodup L.hcl hbc
  have hdisj_base_bs : ∀ q ∈ base, q ∉ bs := binChain_base_disj L.hcl hbase hbc
  have hsupp_base := binBase_suppD L.hcl haD hbase
  have hsupp_bs := binChain_suppD L.hcl hsupp_base.1 hbc
  have hle_bs := binChain_lt L.hcl hbc
  have hle_base : ∀ q ∈ base, n + 1 + q ≤ w' := by
    intro q hq
    cases hasNot
    · simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hbase
      rw [hbase.1] at hq; simp at hq
    · simp only [BinBase, ↓reduceIte] at hbase
      obtain ⟨g0, _, rfl, rfl, _⟩ := hbase
      simp at hq; subst hq; exact hle_bs.1
  let Oset : Finset ℕ := (Os.map Prod.snd).toFinset
  let ODead : Finset ℕ := (Os.map fun x => x.2 - (n + 1)).toFinset
  have hOs_snd_nd : (Os.map Prod.snd).Nodup := by
    have hinj : ∀ x ∈ Os, ∀ y ∈ Os, x.2 = y.2 → x = y := by
      intro ⟨p1, h1⟩ hx ⟨p2, h2⟩ hy heq
      simp only at heq; subst heq
      obtain ⟨_, g1, _, hg1, _, hin1, _, _, _, honly1, _⟩ := hOs p1 h1 hx
      obtain ⟨_, g2, _, hg2, _, hin2, _, _, _, _, _⟩ := hOs p2 h1 hy
      have hp12 : p2 = p1 := honly1 p2 ⟨g2, hg2, by rcases hin2 with e | e <;> rw [e] <;> simp⟩
      subst hp12; rfl
    have hOs_nd : Os.Nodup := List.Nodup.of_map Prod.fst hndO
    exact List.Nodup.map_on hinj hOs_nd
  have hOset_card : Oset.card = Os.length := by
    rw [List.toFinset_card_of_nodup hOs_snd_nd, List.length_map]
  have hODead_nd : (Os.map fun x => x.2 - (n + 1)).Nodup := by
    have hinj : ∀ x ∈ Os, ∀ y ∈ Os, x.2 - (n + 1) = y.2 - (n + 1) → x = y := by
      intro ⟨p1, h1⟩ hx ⟨p2, h2⟩ hy heq
      obtain ⟨_, _, ph1, _, _, _, _, _, _, honly1, e1, _⟩ := hOs p1 h1 hx
      obtain ⟨_, g2, ph2, hg2, _, hin2, _, _, _, _, e2, _⟩ := hOs p2 h2 hy
      have hh : h1 = h2 := by omega
      subst hh
      have hp12 : p2 = p1 := honly1 p2 ⟨g2, hg2, by rcases hin2 with e | e <;> rw [e] <;> simp⟩
      subst hp12; rfl
    exact List.Nodup.map_on hinj (List.Nodup.of_map Prod.fst hndO)
  have hODead_card : ODead.card = Os.length := by
    rw [List.toFinset_card_of_nodup hODead_nd, List.length_map]
  have hOset_mem : ∀ h ∈ Oset, ∃ p ph, (p, h) ∈ Os ∧ h = n + 1 + ph ∧ ph < gs.length ∧
      DFree D gs h ∧ (∀ x, vl gs x h = true → F1 x = true ∧ F2 x = true) ∧
      (∀ r, Reads gs r h → r = p) := by
    intro h hh
    obtain ⟨⟨p, h'⟩, hmem, heq⟩ := List.mem_map.1 (List.mem_toFinset.1 hh)
    simp only at heq; subst heq
    obtain ⟨_, _, ph, _, _, _, hf, _, hcov, honly, eph, hphlt⟩ := hOs p h' hmem
    exact ⟨p, ph, hmem, eph, hphlt, hf, hcov, honly⟩
  have hODead_mem : ∀ ph ∈ ODead, ∃ p, (p, n + 1 + ph) ∈ Os ∧ ph < gs.length ∧
      DFree D gs (n + 1 + ph) ∧ (∀ r, Reads gs r (n + 1 + ph) → r = p) := by
    intro ph hph
    obtain ⟨⟨p, h'⟩, hmem, heq⟩ := List.mem_map.1 (List.mem_toFinset.1 hph)
    simp only at heq
    obtain ⟨_, _, ph', _, _, _, hf, _, _, honly, eph, hphlt⟩ := hOs p h' hmem
    have e1 : ph' = ph := by omega
    subst e1; rw [eph] at hmem hf honly
    exact ⟨p, hmem, hphlt, hf, honly⟩
  have hOset_free : ∀ h ∈ Oset, DFree D gs h := fun h hh => by
    obtain ⟨_, _, _, _, _, hf, _⟩ := hOset_mem h hh; exact hf
  have hOset_cov : ∀ h ∈ Oset, ∀ x, vl gs x h = true → F1 x = true ∧ F2 x = true := fun h hh => by
    obtain ⟨_, _, _, _, _, _, hc, _⟩ := hOset_mem h hh; exact hc
  have hODead_lt : ∀ ph ∈ ODead, ph < gs.length := fun ph hph => by
    obtain ⟨_, _, hlt, _⟩ := hODead_mem ph hph; exact hlt
  have hODead_free : ∀ ph ∈ ODead, DFree D gs (n + 1 + ph) := fun ph hph => by
    obtain ⟨_, _, _, hf, _⟩ := hODead_mem ph hph; exact hf
  have hbuild_E : ∀ (Dead : Finset ℕ) (e1 e2 : ℕ),
      (∀ ph ∈ Dead, DFree D gs (n + 1 + ph)) →
      e1 ≠ e2 → w' < n + 1 + e1 → w' < n + 1 + e2 →
      a ∈ suppD D gs (n + 1 + e1) → a ∈ suppD D gs (n + 1 + e2) →
      (Dead ∪ base.toFinset ∪ bs.toFinset ∪ {e1, e2}).card =
        Dead.card + base.length + bs.length + 2 := by
    intro Dead e1 e2 hDf h12 he1 he2 ha1 ha2
    have hd1 : Disjoint Dead base.toFinset := Finset.disjoint_left.2 fun ph hph hq => by
      have hs := hsupp_base.2 ph (List.mem_toFinset.1 hq)
      exact hDf ph hph a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
    have hd2 : Disjoint (Dead ∪ base.toFinset) bs.toFinset := Finset.disjoint_left.2 fun q hq hbsm => by
      have hbsm' := List.mem_toFinset.1 hbsm
      rcases Finset.mem_union.1 hq with hph | hbm
      · have hs := hsupp_bs.2 q hbsm'
        exact hDf q hph a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1
      · exact hdisj_base_bs q (List.mem_toFinset.1 hbm) hbsm'
    have hd3 : Disjoint (Dead ∪ base.toFinset ∪ bs.toFinset) {e1, e2} :=
      Finset.disjoint_left.2 fun q hq he => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases Finset.mem_union.1 hq with hdb | hbsm
        · rcases Finset.mem_union.1 hdb with hph | hbm
          · rcases he with rfl | rfl
            · exact hDf q hph a haD (Finset.mem_inter.1 ha1).1
            · exact hDf q hph a haD (Finset.mem_inter.1 ha2).1
          · have hlt := hle_base q (List.mem_toFinset.1 hbm)
            rcases he with rfl | rfl <;> omega
        · have hlt := hle_bs.2 q (List.mem_toFinset.1 hbsm)
          rcases he with rfl | rfl <;> omega
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1, List.toFinset_card_of_nodup hbase_nd,
      List.toFinset_card_of_nodup hbs_nd, Finset.card_pair h12]
  have hgoal_vF : ∀ s', s' + (if hasNot then 4 else 3) ≤ gs.length →
      HasSize2 (n + 1) (fun x => F1 (Function.update x a hasNot))
        (fun x => F2 (Function.update x a hasNot)) s' →
      (∃ s', s' + 3 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
        (fun x => F2 (Function.update x a false)) s') ∨
      (∃ s', s' + 4 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
        (fun x => F2 (Function.update x a true)) s') := by
    intro s' hs' hsz; cases hasNot
    · exact Or.inl ⟨s', by simpa using hs', hsz⟩
    · exact Or.inr ⟨s', by simpa using hs', hsz⟩
  have hgoal_vT : ∀ s', s' + (if hasNot then 3 else 4) ≤ gs.length →
      HasSize2 (n + 1) (fun x => F1 (Function.update x a (!hasNot)))
        (fun x => F2 (Function.update x a (!hasNot))) s' →
      (∃ s', s' + 3 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
        (fun x => F2 (Function.update x a false)) s') ∨
      (∃ s', s' + 4 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
        (fun x => F2 (Function.update x a true)) s') := by
    intro s' hs' hsz; cases hasNot
    · exact Or.inr ⟨s', by simpa using hs', hsz⟩
    · exact Or.inl ⟨s', by simpa using hs', hsz⟩
  have hrun_vF : ∀ (Dead : Finset ℕ),
      (∀ ph ∈ Dead, ph < gs.length ∧ DFree D gs (n + 1 + ph) ∧
        ∀ r, Reads gs r (n + 1 + ph) → ∃ h, (r, h) ∈ As) →
      (∀ h ∈ Oset, ∀ ph ∈ Dead, h ≠ n + 1 + ph) →
      (if Oset = ∅ then 0 else Oset.card + 1) + (if hasNot then 4 else 3) ≤
        Dead.card + base.length + bs.length + 2 →
      (∃ s', s' + 3 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a false))
        (fun x => F2 (Function.update x a false)) s') ∨
      (∃ s', s' + 4 ≤ gs.length ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x a true))
        (fun x => F2 (Function.update x a true)) s') := by
    intro Dead hDead hO_ne_Dead harith
    let gs' := multiSwap gs Dead a.val
    have hcl' : CleanL (n + 1) gs' := multiSwap_clean gs Dead a.val L.hcl a.isLt
    have hlen' : gs'.length = gs.length := multiSwap_length gs Dead a.val
    let ov : ℕ → Option Bool := fun w => if w ∈ Oset then some false else none
    have hdead_free : ∀ q, gs'[q]? ≠ gs[q]? → DFree D gs (n + 1 + q) := by
      intro q hne
      by_cases hqm : q ∈ Dead
      · exact (hDead q hqm).2.1
      · exact absurd (multiSwap_get_notMem gs Dead a.val q hqm) hne
    have hov_free : ∀ w, ov w ≠ none → DFree D gs w := by
      intro w hw; simp only [ov] at hw; split_ifs at hw with hm
      · exact hOset_free w hm
      · exact absurd rfl hw
    have hbase_eq : ∀ q ∈ base, gs'[q]? = gs[q]? := fun q hq => by
      by_contra hne
      exact hdead_free q hne a haD (Finset.mem_inter.1 (hsupp_base.2 q hq ▸ Finset.mem_singleton_self a)).1
    have hbs_eq : ∀ p ∈ bs, gs'[p]? = gs[p]? := fun p hp => by
      by_contra hne
      exact hdead_free p hne a haD (Finset.mem_inter.1 (hsupp_bs.2 p hp ▸ Finset.mem_singleton_self a)).1
    have hbase_ov : ∀ q ∈ base, ov (n + 1 + q) = none := fun q hq => by
      by_contra hne
      exact hov_free (n + 1 + q) hne a haD (Finset.mem_inter.1 (hsupp_base.2 q hq ▸ Finset.mem_singleton_self a)).1
    have hbs_ov : ∀ p ∈ bs, ov (n + 1 + p) = none := fun p hp => by
      by_contra hne
      exact hov_free (n + 1 + p) hne a haD (Finset.mem_inter.1 (hsupp_bs.2 p hp ▸ Finset.mem_singleton_self a)).1
    have hchain := binChain_elim_const (gs' := gs') (v := hasNot) (ov := ov)
      L.hcl hcl' hlen' haD hbase hbase_eq hbase_ov hbc hbs_eq hbs_ov
      (fun p hp g h' hgp _ hh' hf => by
        refine ⟨fun hopO _ => ?_, fun _ hx => by simp at hx⟩
        have hmemO : ∃ h0, (p, h0) ∈ Os := by
          rcases (hiffOA p).1 hp with h1 | ⟨h0, h0m⟩
          · exact h1
          · obtain ⟨_, g0, hg0, hopA, _⟩ := hAs p h0 h0m
            rw [hgp] at hg0; cases hg0; rw [hopO] at hopA; cases hopA
        obtain ⟨h0, h0m⟩ := hmemO
        obtain ⟨u0, g0, _, hg0, _, hin0, _, hsu0, _⟩ := hOs p h0 h0m
        rw [hgp] at hg0; cases hg0
        have heq : h' = h0 := by
          rcases hin0 with e | e <;> rw [e] at hh' <;> simp at hh'
          · rcases hh' with rfl | rfl
            · exfalso; exact hf a haD (Finset.mem_inter.1 (hsu0 ▸ Finset.mem_singleton_self a)).1
            · rfl
          · rcases hh' with rfl | rfl
            · rfl
            · exfalso; exact hf a haD (Finset.mem_inter.1 (hsu0 ▸ Finset.mem_singleton_self a)).1
        subst heq
        have hmem : h' ∈ Oset := List.mem_toFinset.2 (List.mem_map.2 ⟨(p, h'), h0m, rfl⟩)
        simp [ov, hmem])
    have hw'_st : (elimOv (n + 1) ov gs' (initOv (n + 1) a.val hasNot ov)).1.getD w' (Sum.inl false) =
        Sum.inl false := by simpa using hchain.2.2.1
    obtain ⟨e1, e2, h12, he1, he2, ha1, ha2, hEe1, hEe2⟩ :=
      end_two_gates L.hcl hcl' hsupp_bs.1 hdead_free hov_free hw'_st hend
    let E := Dead ∪ base.toFinset ∪ bs.toFinset ∪ {e1, e2}
    have hEcard := hbuild_E Dead e1 e2 (fun ph hph => (hDead ph hph).2.1) h12 he1 he2 ha1 ha2
    have hagree_df : ∀ (x : Fin (n + 1) → Bool) (h : ℕ), h ∈ Oset → vl gs' x h = vl gs x h := by
      intro x h hh
      exact multiSwap_agree_dfree gs Dead a.val L.hcl a.isLt
        (fun ph hph r hr hf => by
          obtain ⟨h0, h0m⟩ := (hDead ph hph).2.2 r hr
          have hs := hsupp_bs.2 r ((hiffOA r).2 (Or.inr ⟨h0, h0m⟩))
          exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1)
        x h (hOset_free h hh) (hO_ne_Dead h hh)
    have hres := restore_O (n + 1) F1 F2 gs gs' o1 o2 a hasNot Oset hcl'
      (H1.nc a haD hasNot) (H2.nc a haD hasNot)
      (fun h hh => by obtain ⟨_, ph, _, rfl, hlt, _⟩ := hOset_mem h hh; omega)
      (fun h hh x hx => hOset_cov h hh _ (by rw [← hagree_df _ h hh]; exact hx))
      (fun x hall => by
        have hvl := binChain_vl_const L.hcl haD hbase (Function.update x a hasNot)
          (Function.update_self _ _ _) hbc (fun p hp g h' hgp _ hh' hf => by
            refine ⟨fun hopO _ => ?_, fun _ hx => by simp at hx⟩
            have hmemO : ∃ h0, (p, h0) ∈ Os := by
              rcases (hiffOA p).1 hp with h1 | ⟨h0, h0m⟩
              · exact h1
              · obtain ⟨_, g0, hg0, hopA, _⟩ := hAs p h0 h0m
                rw [hgp] at hg0; cases hg0; rw [hopO] at hopA; cases hopA
            obtain ⟨h0, h0m⟩ := hmemO
            obtain ⟨u0, g0, _, hg0, _, hin0, _, hsu0, _⟩ := hOs p h0 h0m
            rw [hgp] at hg0; cases hg0
            have heq : h' = h0 := by
              rcases hin0 with e | e <;> rw [e] at hh' <;> simp at hh'
              · rcases hh' with rfl | rfl
                · exfalso; exact hf a haD (Finset.mem_inter.1 (hsu0 ▸ Finset.mem_singleton_self a)).1
                · rfl
              · rcases hh' with rfl | rfl
                · rfl
                · exfalso; exact hf a haD (Finset.mem_inter.1 (hsu0 ▸ Finset.mem_singleton_self a)).1
            subst heq
            have hmem : h' ∈ Oset := List.mem_toFinset.2 (List.mem_map.2 ⟨(p, h'), h0m, rfl⟩)
            rw [← hagree_df _ h' hmem]; exact hall h' hmem)
        have hag := multiSwap_agree gs Dead a.val L.hcl a.isLt (Function.update x a hasNot)
          (fun r g hr _ ⟨ph, hph, hmem⟩ => by
            obtain ⟨h0, h0m⟩ := (hDead ph hph).2.2 r ⟨g, hr, hmem⟩
            obtain ⟨_, g0, hg0, hopA, _⟩ := hAs r h0 h0m
            rw [hr] at hg0; cases hg0
            obtain ⟨u, hu, hsu, huvl⟩ := hvl.2.2.2 r ((hiffOA r).2 (Or.inr ⟨h0, h0m⟩)) g hr
            refine ⟨u, hu, fun ph' hph' e => ?_, Or.inl hopA, by simpa [fixBit, hopA] using huvl⟩
            exact (hDead ph' hph').2.1 a haD (Finset.mem_inter.1 (e ▸ hsu ▸ Finset.mem_singleton_self a)).1)
        have ho1_ne : ∀ ph ∈ Dead, o1 ≠ n + 1 + ph := fun ph hph e =>
          (hDead ph hph).2.1 a haD (e ▸ deepHyp'_supp H1 L.hev1 haD)
        have ho2_ne : ∀ ph ∈ Dead, o2 ≠ n + 1 + ph := fun ph hph e =>
          (hDead ph hph).2.1 a haD (e ▸ deepHyp'_supp H2 L.hev2 haD)
        exact ⟨by rw [hag o1 ho1_ne, L.hev1], by rw [hag o2 ho2_ne, L.hev2]⟩)
      E (fun p hp => by
        rcases Finset.mem_union.1 hp with h1 | h2
        · rcases Finset.mem_union.1 h1 with h11 | hbsm
          · rcases Finset.mem_union.1 h11 with hdm | hbm
            · exact ⟨⟨GateOp.not, [a.val]⟩,
                multiSwap_get_mem gs Dead a.val p (hDead p hdm).1 hdm,
                a.val, by simp, by have := a.isLt; omega, hasNot,
                elimOv_input_y (n + 1) a.val hasNot ov gs' a.isLt⟩
            · exact hchain.2.1 p (List.mem_toFinset.1 hbm)
          · exact hchain.2.2.2 p (List.mem_toFinset.1 hbsm)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
          rcases h2 with rfl | rfl
          · exact hEe1
          · exact hEe2) hlen'
    dsimp only at hres
    obtain ⟨s', hs', hsz⟩ := hres
    refine hgoal_vF s' ?_ hsz
    rw [hEcard] at hs'
    have hOpos : Oset ≠ ∅ → 1 ≤ Oset.card := fun h => Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h)
    by_cases hOe : Oset = ∅
    · simp only [hOe, ↓reduceIte, add_zero, zero_add] at hs' harith
      split_ifs at hs' harith ⊢ <;> omega
    · have h1 := hOpos hOe
      simp only [hOe, ↓reduceIte] at hs' harith
      split_ifs at hs' harith ⊢ <;> omega
  cases hOs_eq : Os with
  | nil =>
    have hOempty : Oset = ∅ := by simp [Oset, hOs_eq]
    have hbs_pos : 1 ≤ bs.length := by
      cases bs with
      | nil => exact absurd rfl hbsne
      | cons _ _ => simp
    exact hrun_vF ∅ (fun _ hm => by simp at hm) (fun _ _ _ hm => by simp at hm)
      (by simp [hOempty, hbase_len]; split_ifs <;> omega)
  | cons o0 Os' =>
    have hO_ne_empty : Oset ≠ ∅ := by
      intro he; have := hOset_card; rw [he, hOs_eq] at this; simp at this
    cases hAs_eq : As with
    | nil =>
      let gs' := multiSwap gs ODead a.val
      have hcl' : CleanL (n + 1) gs' := multiSwap_clean gs ODead a.val L.hcl a.isLt
      have hlen' : gs'.length = gs.length := multiSwap_length gs ODead a.val
      let ov : ℕ → Option Bool := fun _ => none
      have hdead_free : ∀ q, gs'[q]? ≠ gs[q]? → DFree D gs (n + 1 + q) := fun q hne => by
        by_cases hqm : q ∈ ODead
        · exact hODead_free q hqm
        · exact absurd (multiSwap_get_notMem gs ODead a.val q hqm) hne
      have hbase_eq : ∀ q ∈ base, gs'[q]? = gs[q]? := fun q hq => by
        by_contra hne
        exact hdead_free q hne a haD (Finset.mem_inter.1 (hsupp_base.2 q hq ▸ Finset.mem_singleton_self a)).1
      have hbs_eq : ∀ p ∈ bs, gs'[p]? = gs[p]? := fun p hp => by
        by_contra hne
        exact hdead_free p hne a haD (Finset.mem_inter.1 (hsupp_bs.2 p hp ▸ Finset.mem_singleton_self a)).1
      have hchain := binChain_elim_const (gs' := gs') (v := !hasNot) (ov := ov)
        L.hcl hcl' hlen' haD hbase hbase_eq (fun _ _ => rfl) hbc hbs_eq (fun _ _ => rfl)
        (fun p hp g _ hgp _ _ _ => by
          refine ⟨fun _ hx => by cases hasNot <;> simp at hx, fun hopA _ => ?_⟩
          exfalso
          rcases (hiffOA p).1 hp with ⟨h0, h0m⟩ | ⟨h0, h0m⟩
          · obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs p h0 h0m
            rw [hgp] at hg0; cases hg0; rw [hopO] at hopA; cases hopA
          · rw [hAs_eq] at h0m; simp at h0m)
      have hw'_st : (elimOv (n + 1) ov gs' (initOv (n + 1) a.val (!hasNot) ov)).1.getD w' (Sum.inl false) =
          Sum.inl true := by
        have := hchain.2.2.1; cases hasNot <;> simpa using this
      obtain ⟨e1, e2, h12, he1, he2, ha1, ha2, hEe1, hEe2⟩ :=
        end_two_gates L.hcl hcl' hsupp_bs.1 hdead_free (fun _ h => absurd rfl h) hw'_st hend
      let E := ODead ∪ base.toFinset ∪ bs.toFinset ∪ {e1, e2}
      have hEcard := hbuild_E ODead e1 e2 hODead_free h12 he1 he2 ha1 ha2
      have hres := restore_O (n + 1) F1 F2 gs gs' o1 o2 a (!hasNot) ∅ hcl'
        (H1.nc a haD (!hasNot)) (H2.nc a haD (!hasNot))
        (fun _ hm => by simp at hm) (fun _ hm => by simp at hm)
        (fun x _ => by
          have hvl := binChain_vl_const L.hcl haD hbase (Function.update x a (!hasNot))
            (Function.update_self _ _ _) hbc (fun p hp g _ hgp _ _ _ => by
              refine ⟨fun _ hx => by cases hasNot <;> simp at hx, fun hopA _ => ?_⟩
              exfalso
              rcases (hiffOA p).1 hp with ⟨h0, h0m⟩ | ⟨h0, h0m⟩
              · obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs p h0 h0m
                rw [hgp] at hg0; cases hg0; rw [hopO] at hopA; cases hopA
              · rw [hAs_eq] at h0m; simp at h0m)
          have hag := multiSwap_agree gs ODead a.val L.hcl a.isLt (Function.update x a (!hasNot))
            (fun r g hr _ ⟨ph, hph, hmem⟩ => by
              obtain ⟨p, hpm, _, _, honly⟩ := hODead_mem ph hph
              have hrp : r = p := honly r ⟨g, hr, hmem⟩; subst p
              obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs r (n + 1 + ph) hpm
              rw [hr] at hg0; cases hg0
              obtain ⟨u, hu, hsu, huvl⟩ := hvl.2.2.2 r ((hiffOA r).2 (Or.inl ⟨n + 1 + ph, hpm⟩)) g hr
              refine ⟨u, hu, fun ph' hph' e => ?_, Or.inr hopO, by cases hasNot <;> simpa [fixBit, hopO] using huvl⟩
              exact hODead_free ph' hph' a haD (Finset.mem_inter.1 (e ▸ hsu ▸ Finset.mem_singleton_self a)).1)
          have ho1_ne : ∀ ph ∈ ODead, o1 ≠ n + 1 + ph := fun ph hph e =>
            hODead_free ph hph a haD (e ▸ deepHyp'_supp H1 L.hev1 haD)
          have ho2_ne : ∀ ph ∈ ODead, o2 ≠ n + 1 + ph := fun ph hph e =>
            hODead_free ph hph a haD (e ▸ deepHyp'_supp H2 L.hev2 haD)
          exact ⟨by rw [hag o1 ho1_ne, L.hev1], by rw [hag o2 ho2_ne, L.hev2]⟩)
        E (fun p hp => by
          rcases Finset.mem_union.1 hp with h1 | h2
          · rcases Finset.mem_union.1 h1 with h11 | hbsm
            · rcases Finset.mem_union.1 h11 with hdm | hbm
              · exact ⟨⟨GateOp.not, [a.val]⟩,
                  multiSwap_get_mem gs ODead a.val p (hODead_lt p hdm) hdm,
                  a.val, by simp, by have := a.isLt; omega, !hasNot,
                  elimOv_input_y (n + 1) a.val (!hasNot) ov gs' a.isLt⟩
              · exact hchain.2.1 p (List.mem_toFinset.1 hbm)
            · exact hchain.2.2.2 p (List.mem_toFinset.1 hbsm)
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
            rcases h2 with rfl | rfl
            · exact hEe1
            · exact hEe2) hlen'
      dsimp only at hres
      obtain ⟨s', hs', hsz⟩ := hres
      refine hgoal_vT s' ?_ hsz
      simp only [↓reduceIte, add_zero] at hs'
      rw [hEcard, hODead_card, hbase_len] at hs'
      rw [hOs_eq, hAs_eq] at hlenOA; simp only [List.length_cons, List.length_nil, add_zero] at hlenOA
      rw [hOs_eq] at hs'; simp only [List.length_cons] at hs'
      split_ifs at hs' ⊢ <;> omega
    | cons a0 As' =>
      cases hAs'_eq : As' with
      | cons a1 As'' =>
        refine hrun_vF ∅ (fun _ hm => by simp at hm) (fun _ _ _ hm => by simp at hm) ?_
        rw [ite_eq_right_iff.2 (fun h => absurd h hO_ne_empty), hOset_card, hbase_len]
        rw [hAs_eq, hAs'_eq] at hlenOA; simp only [List.length_cons] at hlenOA
        split_ifs <;> omega
      | nil =>
        rcases a0 with ⟨pA, hA⟩
        have hAmem : (pA, hA) ∈ As := by rw [hAs_eq]; exact List.mem_cons_self
        obtain ⟨uA, gpA, hgpA, hopA, hinA, hfreeA, hsuA, hcovA, hgateA⟩ := hAs pA hA hAmem
        have hhA_in : hA ∈ gpA.inputs := by rcases hinA with e | e <;> rw [e] <;> simp
        have hhA_lt_gs : hA < n + 1 + gs.length := by
          have := (L.hcl pA gpA hgpA).lt hA hhA_in
          have := (List.getElem?_eq_some_iff.1 hgpA).1; omega
        rcases hext.2 hA pA gpA hfreeA hgpA hopA hhA_in hcovA with honlyA |
          ⟨rA, grA, qA, hrA_ne, hgrA, hoprA, hinrA, _⟩
        · obtain ⟨phA, hhA_eq, hphA_lt⟩ := hgateA honlyA
          refine hrun_vF {phA} (fun ph hph => ?_) (fun h hh ph hph => ?_) ?_
          · simp at hph; subst hph
            refine ⟨hphA_lt, by rw [← hhA_eq]; exact hfreeA, fun r hr => ?_⟩
            have hrA : r = pA := honlyA r (by rw [hhA_eq]; exact hr); subst r
            exact ⟨hA, hAmem⟩
          · simp at hph; subst hph; intro e; rw [← hhA_eq] at e; subst e
            obtain ⟨pO, _, hOm, _, _, _, _, honlyO⟩ := hOset_mem h hh
            have hpOA : pA = pO := honlyO pA ⟨gpA, hgpA, hhA_in⟩
            subst pO
            obtain ⟨_, gpO, _, hgpO, hopO, _⟩ := hOs pA h hOm
            rw [hgpA] at hgpO; cases hgpO; rw [hopA] at hopO; cases hopO
          · rw [ite_eq_right_iff.2 (fun h => absurd h hO_ne_empty), hOset_card, Finset.card_singleton, hbase_len]
            rw [hAs_eq, hAs'_eq] at hlenOA; simp only [List.length_cons, List.length_nil] at hlenOA
            split_ifs <;> omega
        · by_cases h4b : hasNot = true ∨ 2 ≤ Os.length
          · let gs' := multiSwap gs ODead a.val
            have hcl' : CleanL (n + 1) gs' := multiSwap_clean gs ODead a.val L.hcl a.isLt
            have hlen' : gs'.length = gs.length := multiSwap_length gs ODead a.val
            let ov : ℕ → Option Bool := fun w => if w = hA then some true else none
            have hdead_free : ∀ q, gs'[q]? ≠ gs[q]? → DFree D gs (n + 1 + q) := fun q hne => by
              by_cases hqm : q ∈ ODead
              · exact hODead_free q hqm
              · exact absurd (multiSwap_get_notMem gs ODead a.val q hqm) hne
            have hov_free : ∀ w, ov w ≠ none → DFree D gs w := fun w hw => by
              simp only [ov] at hw; split_ifs at hw with e
              · subst e; exact hfreeA
              · exact absurd rfl hw
            have hbase_eq : ∀ q ∈ base, gs'[q]? = gs[q]? := fun q hq => by
              by_contra hne
              exact hdead_free q hne a haD (Finset.mem_inter.1 (hsupp_base.2 q hq ▸ Finset.mem_singleton_self a)).1
            have hbs_eq : ∀ p ∈ bs, gs'[p]? = gs[p]? := fun p hp => by
              by_contra hne
              exact hdead_free p hne a haD (Finset.mem_inter.1 (hsupp_bs.2 p hp ▸ Finset.mem_singleton_self a)).1
            have hbase_ov : ∀ q ∈ base, ov (n + 1 + q) = none := fun q hq => by
              by_contra hne
              exact hov_free (n + 1 + q) hne a haD (Finset.mem_inter.1 (hsupp_base.2 q hq ▸ Finset.mem_singleton_self a)).1
            have hbs_ov : ∀ p ∈ bs, ov (n + 1 + p) = none := fun p hp => by
              by_contra hne
              exact hov_free (n + 1 + p) hne a haD (Finset.mem_inter.1 (hsupp_bs.2 p hp ▸ Finset.mem_singleton_self a)).1
            have hhA_ne_ODead : ∀ ph ∈ ODead, hA ≠ n + 1 + ph := fun ph hph e => by
              obtain ⟨pO, hOm, _, _, honlyO⟩ := hODead_mem ph hph
              have hpOA : pA = pO := honlyO pA ⟨gpA, hgpA, e ▸ hhA_in⟩
              subst pO
              obtain ⟨_, gpO, _, hgpO, hopO, _⟩ := hOs pA (n + 1 + ph) hOm
              rw [hgpA] at hgpO; cases hgpO; rw [hopA] at hopO; cases hopO
            have hchain := binChain_elim_const (gs' := gs') (v := !hasNot) (ov := ov)
              L.hcl hcl' hlen' haD hbase hbase_eq hbase_ov hbc hbs_eq hbs_ov
              (fun p hp g h' hgp _ hh' hf => by
                refine ⟨fun _ hx => by cases hasNot <;> simp at hx, fun hopA' _ => ?_⟩
                have hpA' : p = pA := by
                  rcases (hiffOA p).1 hp with ⟨h0, h0m⟩ | ⟨h0, h0m⟩
                  · obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs p h0 h0m
                    rw [hgp] at hg0; cases hg0; rw [hopO] at hopA'; cases hopA'
                  · rw [hAs_eq, hAs'_eq] at h0m; simp at h0m; exact h0m.1
                subst p; rw [hgpA] at hgp; cases hgp
                have heq : h' = hA := by
                  rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
                  · rcases hh' with rfl | rfl
                    · exfalso; exact hf a haD (Finset.mem_inter.1 (hsuA ▸ Finset.mem_singleton_self a)).1
                    · rfl
                  · rcases hh' with rfl | rfl
                    · rfl
                    · exfalso; exact hf a haD (Finset.mem_inter.1 (hsuA ▸ Finset.mem_singleton_self a)).1
                simp [ov, heq])
            have hw'_st : (elimOv (n + 1) ov gs' (initOv (n + 1) a.val (!hasNot) ov)).1.getD w' (Sum.inl false) =
                Sum.inl true := by
              have := hchain.2.2.1; cases hasNot <;> simpa using this
            obtain ⟨e1, e2, h12, he1, he2, ha1, ha2, hEe1, hEe2⟩ :=
              end_two_gates L.hcl hcl' hsupp_bs.1 hdead_free hov_free hw'_st hend
            let E := ODead ∪ base.toFinset ∪ bs.toFinset ∪ {e1, e2}
            have hEcard := hbuild_E ODead e1 e2 hODead_free h12 he1 he2 ha1 ha2
            have hagree_df : ∀ x : Fin (n + 1) → Bool, vl gs' x hA = vl gs x hA := fun x =>
              multiSwap_agree_dfree gs ODead a.val L.hcl a.isLt
                (fun ph hph r hr hf => by
                  obtain ⟨pO, hOm, _, _, honlyO⟩ := hODead_mem ph hph
                  have hrO : r = pO := honlyO r hr; subst pO
                  have hs := hsupp_bs.2 r ((hiffOA r).2 (Or.inl ⟨n + 1 + ph, hOm⟩))
                  exact hf a haD (Finset.mem_inter.1 (hs ▸ Finset.mem_singleton_self a)).1)
                x hA hfreeA hhA_ne_ODead
            have hres := restore_A1 (n + 1) F1 F2 gs gs' o1 o2 a (!hasNot) hA hcl'
              (H1.nc a haD (!hasNot)) (H2.nc a haD (!hasNot)) (by omega)
              (fun x hx => hcovA _ (by rw [← hagree_df]; exact hx))
              (fun x hx => by
                have hhAt : vl gs (Function.update x a (!hasNot)) hA = true := by
                  rw [← hagree_df]; exact hx
                have hvl := binChain_vl_const L.hcl haD hbase (Function.update x a (!hasNot))
                  (Function.update_self _ _ _) hbc (fun p hp g h' hgp _ hh' hf => by
                    refine ⟨fun _ hxx => by cases hasNot <;> simp at hxx, fun hopA' _ => ?_⟩
                    have hpA' : p = pA := by
                      rcases (hiffOA p).1 hp with ⟨h0, h0m⟩ | ⟨h0, h0m⟩
                      · obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs p h0 h0m
                        rw [hgp] at hg0; cases hg0; rw [hopO] at hopA'; cases hopA'
                      · rw [hAs_eq, hAs'_eq] at h0m; simp at h0m; exact h0m.1
                    subst p; rw [hgpA] at hgp; cases hgp
                    have heq : h' = hA := by
                      rcases hinA with e | e <;> rw [e] at hh' <;> simp at hh'
                      · rcases hh' with rfl | rfl
                        · exfalso; exact hf a haD (Finset.mem_inter.1 (hsuA ▸ Finset.mem_singleton_self a)).1
                        · rfl
                      · rcases hh' with rfl | rfl
                        · rfl
                        · exfalso; exact hf a haD (Finset.mem_inter.1 (hsuA ▸ Finset.mem_singleton_self a)).1
                    rw [heq]; exact hhAt)
                have hag := multiSwap_agree gs ODead a.val L.hcl a.isLt (Function.update x a (!hasNot))
                  (fun r g hr _ ⟨ph, hph, hmem⟩ => by
                    obtain ⟨p, hpm, _, _, honly⟩ := hODead_mem ph hph
                    have hrp : r = p := honly r ⟨g, hr, hmem⟩; subst p
                    obtain ⟨_, g0, _, hg0, hopO, _⟩ := hOs r (n + 1 + ph) hpm
                    rw [hr] at hg0; cases hg0
                    obtain ⟨u, hu, hsu, huvl⟩ := hvl.2.2.2 r ((hiffOA r).2 (Or.inl ⟨n + 1 + ph, hpm⟩)) g hr
                    refine ⟨u, hu, fun ph' hph' e => ?_, Or.inr hopO, by cases hasNot <;> simpa [fixBit, hopO] using huvl⟩
                    exact hODead_free ph' hph' a haD (Finset.mem_inter.1 (e ▸ hsu ▸ Finset.mem_singleton_self a)).1)
                have ho1_ne : ∀ ph ∈ ODead, o1 ≠ n + 1 + ph := fun ph hph e =>
                  hODead_free ph hph a haD (e ▸ deepHyp'_supp H1 L.hev1 haD)
                have ho2_ne : ∀ ph ∈ ODead, o2 ≠ n + 1 + ph := fun ph hph e =>
                  hODead_free ph hph a haD (e ▸ deepHyp'_supp H2 L.hev2 haD)
                exact ⟨by rw [hag o1 ho1_ne, L.hev1], by rw [hag o2 ho2_ne, L.hev2]⟩)
              E (fun p hp => by
                rcases Finset.mem_union.1 hp with h1 | h2
                · rcases Finset.mem_union.1 h1 with h11 | hbsm
                  · rcases Finset.mem_union.1 h11 with hdm | hbm
                    · exact ⟨⟨GateOp.not, [a.val]⟩,
                        multiSwap_get_mem gs ODead a.val p (hODead_lt p hdm) hdm,
                        a.val, by simp, by have := a.isLt; omega, !hasNot,
                        elimOv_input_y (n + 1) a.val (!hasNot) ov gs' a.isLt⟩
                    · exact hchain.2.1 p (List.mem_toFinset.1 hbm)
                  · exact hchain.2.2.2 p (List.mem_toFinset.1 hbsm)
                · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
                  rcases h2 with rfl | rfl
                  · exact hEe1
                  · exact hEe2) hlen'
            dsimp only at hres
            obtain ⟨s', hs', hsz⟩ := hres
            refine hgoal_vT s' ?_ hsz
            rw [hEcard, hODead_card, hbase_len] at hs'
            rw [hAs_eq, hAs'_eq] at hlenOA; simp only [List.length_cons, List.length_nil] at hlenOA
            rw [hOs_eq] at h4b hs' hlenOA; simp only [List.length_cons] at h4b hs' hlenOA
            rcases h4b with rfl | hge2
            · simp only [↓reduceIte] at hs' ⊢; split_ifs at hs' <;> omega
            · cases hasNot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs' ⊢ <;> split_ifs at hs' <;> omega
          · push Not at h4b
            have hhasNotF : hasNot = false := by cases hasNot <;> simp at h4b ⊢
            subst hhasNotF
            have hOs'_nil : Os' = [] := by
              cases Os' with
              | nil => rfl
              | cons _ _ => rw [hOs_eq] at h4b; simp at h4b
            subst hOs'_nil
            rcases o0 with ⟨pO, hO⟩
            have hOmem : (pO, hO) ∈ Os := by rw [hOs_eq]; exact List.mem_cons_self
            obtain ⟨uO, gpO, phO, hgpO, hopO, hinO, hfreeO, hsuO, hcovO, honlyO, hhO_eq, hphO_lt⟩ :=
              hOs pO hO hOmem
            subst hhO_eq
            simp only [BinBase, Bool.false_eq_true, ↓reduceIte] at hbase
            obtain ⟨rfl, rfl⟩ := hbase
            have hpOA : pO ≠ pA := fun e => by subst e; rw [hgpO] at hgpA; cases hgpA; rw [hopO] at hopA; cases hopA
            have hbs_len2 : bs.length = 2 := by rw [← hlenOA, hOs_eq, hAs_eq, hAs'_eq]; rfl
            have hpO_in : pO ∈ bs := (hiffOA pO).2 (Or.inl ⟨n + 1 + phO, hOmem⟩)
            have hpA_in : pA ∈ bs := (hiffOA pA).2 (Or.inr ⟨hA, hAmem⟩)
            obtain ⟨q1, q2, hbs2⟩ : ∃ q1 q2, bs = [q1, q2] := by
              cases bs with
              | nil => simp at hbs_len2
              | cons q1 bs1 =>
                cases bs1 with
                | nil => simp at hbs_len2
                | cons q2 bs2 =>
                  cases bs2 with
                  | nil => exact ⟨q1, q2, rfl⟩
                  | cons _ _ => simp at hbs_len2
            subst hbs2
            have hord_cases : (q1 = pA ∧ q2 = pO) ∨ (q1 = pO ∧ q2 = pA) := by
              simp at hpO_in hpA_in
              rcases hpO_in with rfl | rfl <;> rcases hpA_in with h1 | h1
              · exact absurd h1.symm hpOA
              · exact Or.inr ⟨rfl, h1.symm⟩
              · exact Or.inl ⟨h1.symm, rfl⟩
              · exact absurd h1.symm hpOA
            rcases hord_cases with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
            · subst q1; subst q2
              have hbc_orig := hbc
              obtain ⟨hw', u1, g1, h1', hbc1, hg1, _, hin1, hf1, honly1⟩ := hbc
              obtain ⟨hu1, u2, g2, h2', hbc2, hg2, _, hin2, hf2, _⟩ := hbc1
              change u2 = a.val at hbc2; subst hbc2; subst hu1
              rw [hgpA] at hg1; cases hg1
              rw [hgpO] at hg2; cases hg2
              have eh1 : h1' = hA := by
                rcases hin1 with e | e
                · rw [e] at hinA; rcases hinA with e' | e'
                  · simp at e'; exact e'.2
                  · simp at e'; exfalso
                    exact hf1 a haD (Finset.mem_inter.1 (e'.2 ▸ hsuA ▸ Finset.mem_singleton_self a)).1
                · rw [e] at hinA; rcases hinA with e' | e'
                  · simp at e'; exfalso
                    exact hf1 a haD (Finset.mem_inter.1 (e'.1 ▸ hsuA ▸ Finset.mem_singleton_self a)).1
                  · simp at e'; exact e'.1
              have eh2 : h2' = n + 1 + phO := by
                rcases hin2 with e | e
                · rw [e] at hinO; rcases hinO with e' | e'
                  · simp at e'; exact e'.2
                  · simp at e'; exfalso
                    exact hf2 a haD (Finset.mem_inter.1 (e'.2 ▸ hsuO ▸ Finset.mem_singleton_self a)).1
                · rw [e] at hinO; rcases hinO with e' | e'
                  · simp at e'; exfalso
                    exact hf2 a haD (Finset.mem_inter.1 (e'.1 ▸ hsuO ▸ Finset.mem_singleton_self a)).1
                  · simp at e'; exact e'.1
              subst eh1; subst eh2
              exact solve_case4c H1 H2 L haD hbD hab hbc_orig (Or.inl rfl) hgpO hopO hgpA hopA
                hphO_lt hfreeO hfreeA hcovO hcovA honlyO hrA_ne hgrA hoprA hinrA hhA_lt_gs
                (Or.inl ⟨hin2, hin1, honly1, hw'⟩) hend
            · subst q1; subst q2
              have hbc_orig := hbc
              obtain ⟨hw', u1, g1, h1', hbc1, hg1, _, hin1, hf1, honly1⟩ := hbc
              obtain ⟨hu1, u2, g2, h2', hbc2, hg2, _, hin2, hf2, _⟩ := hbc1
              change u2 = a.val at hbc2; subst hbc2; subst hu1
              rw [hgpO] at hg1; cases hg1
              rw [hgpA] at hg2; cases hg2
              have eh1 : h1' = n + 1 + phO := by
                rcases hin1 with e | e
                · rw [e] at hinO; rcases hinO with e' | e'
                  · simp at e'; exact e'.2
                  · simp at e'; exfalso
                    exact hf1 a haD (Finset.mem_inter.1 (e'.2 ▸ hsuO ▸ Finset.mem_singleton_self a)).1
                · rw [e] at hinO; rcases hinO with e' | e'
                  · simp at e'; exfalso
                    exact hf1 a haD (Finset.mem_inter.1 (e'.1 ▸ hsuO ▸ Finset.mem_singleton_self a)).1
                  · simp at e'; exact e'.1
              have eh2 : h2' = hA := by
                rcases hin2 with e | e
                · rw [e] at hinA; rcases hinA with e' | e'
                  · simp at e'; exact e'.2
                  · simp at e'; exfalso
                    exact hf2 a haD (Finset.mem_inter.1 (e'.2 ▸ hsuA ▸ Finset.mem_singleton_self a)).1
                · rw [e] at hinA; rcases hinA with e' | e'
                  · simp at e'; exfalso
                    exact hf2 a haD (Finset.mem_inter.1 (e'.1 ▸ hsuA ▸ Finset.mem_singleton_self a)).1
                  · simp at e'; exact e'.1
              subst eh1; subst eh2
              exact solve_case4c H1 H2 L haD hbD hab hbc_orig (Or.inr rfl) hgpO hopO hgpA hopA
                hphO_lt hfreeO hfreeA hcovO hcovA honlyO hrA_ne hgrA hoprA hinrA hhA_lt_gs
                (Or.inr ⟨hin2, hin1, honly1, hw'⟩) hend

theorem stmtML2 (n s : ℕ) (F1 F2 : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1)))
    (H1 : DeepHyp' F1 D) (H2 : DeepHyp' F2 D) (hne : D.Nonempty)
    (hs : HasSize2 (n + 1) F1 F2 s) :
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y false))
        (fun x => F2 (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y true))
        (fun x => F2 (Function.update x y true)) s') := by
  obtain ⟨gs, o1, o2, L, hlen, hext⟩ := stmtExt2 n s F1 F2 D H1 H2 hne hs
  have hnc1 := deepHyp'_nc H1 hne
  have hnc2 := deepHyp'_nc H2 hne
  have hfrom_pays : ∀ y ∈ D, Pays2 F1 F2 y gs.length →
      ∃ y' ∈ D,
        (∃ s' : ℕ, s' + 3 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y' false))
          (fun x => F2 (Function.update x y' false)) s') ∨
        (∃ s' : ℕ, s' + 4 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y' true))
          (fun x => F2 (Function.update x y' true)) s') := by
    intro y hy hpays
    refine ⟨y, hy, ?_⟩
    rcases hpays with ⟨⟨s', hs', hsz⟩, _⟩ | ⟨⟨s', hs', hsz⟩, _⟩ | ⟨_, ⟨s', hs', hsz⟩⟩
    · exact Or.inl ⟨s', by omega, hsz⟩
    · exact Or.inl ⟨s', by omega, hsz⟩
    · exact Or.inr ⟨s', by omega, hsz⟩
  have hfrom_branch : ∀ (a b : Fin (n + 1)) (ps : List ℕ) (w : ℕ),
      a ∈ D → b ∈ D → a ≠ b → IsChain (n + 1) D gs a ps w →
      (∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w ∧ Reads gs T2 w) →
      ∃ y ∈ D,
        (∃ s' : ℕ, s' + 3 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y false))
          (fun x => F2 (Function.update x y false)) s') ∨
        (∃ s' : ℕ, s' + 4 ≤ s ∧ HasSize2 (n + 1) (fun x => F1 (Function.update x y true))
          (fun x => F2 (Function.update x y true)) s') := by
    intro a b ps w haD hbD hab hch ⟨T1, T2, h12, hT1, hT2⟩
    rcases chain_truncate_aux L hnc1 hnc2 hch ⟨T1, hT1⟩ with rfl |
      ⟨g0, gg0, rfl, rfl, hg0, hop0, hin0⟩ |
      ⟨hasNot, base, bs, w0, w', hbase, hbc, hbsne, _, _, hend⟩
    · change w = a.val at hch; subst hch
      exact hfrom_pays a haD (L.two_readers a (H1.nc a haD) (H2.nc a haD) T1 T2 h12 hT1 hT2)
    · have ⟨⟨s', hs', hsz⟩, _⟩ :=
        L.not_two_readers a (H1.nc a haD) (H2.nc a haD) g0 gg0 hg0 hop0 (by rw [hin0]; simp)
          T1 T2 h12 hT1 hT2
      exact ⟨a, haD, Or.inl ⟨s', by omega, hsz⟩⟩
    · have hend' : (∃ T1 T2, T1 ≠ T2 ∧ Reads gs T1 w' ∧ Reads gs T2 w') ∨
          (∃ gm ggm T, gs[gm]? = some ggm ∧ ggm.op = GateOp.not ∧ ggm.inputs = [w'] ∧
            Reads gs T (n + 1 + gm) ∧ ∀ r, Reads gs r w' → r = gm) := by
        rcases hend with rfl | h2
        · exact Or.inl ⟨T1, T2, h12, hT1, hT2⟩
        · exact Or.inr h2
      rcases solve_chain H1 H2 L hext haD hbD hab hbase hbc hbsne hend' with
        ⟨s', hs', hsz⟩ | ⟨s', hs', hsz⟩
      · exact ⟨a, haD, Or.inl ⟨s', by omega, hsz⟩⟩
      · exact ⟨a, haD, Or.inr ⟨s', by omega, hsz⟩⟩
  obtain ⟨Q, gQ, u, v, a, b, hgQ, hopQ, hinQ, hu_lt, hv_lt, haD, hbD, hab, hsu, hsv, hQmin⟩ :=
    first_multi_D H1 hne L
  rcases chain_build L hnc1 hnc2 haD hQmin u hu_lt hsu with
    ⟨ps, w', hch, _, hbr⟩ | ⟨psu, hchu⟩
  · exact hfrom_branch a b ps w' haD hbD hab hch hbr
  · rcases chain_build L hnc1 hnc2 hbD hQmin v hv_lt hsv with
      ⟨ps, w', hch, _, hbr⟩ | ⟨psv, hchv⟩
    · exact hfrom_branch b a ps w' hbD haD hab.symm hch hbr
    · by_cases honlyu : ∀ r, Reads gs r u → r = Q
      · by_cases honlyv : ∀ r, Reads gs r v → r = Q
        · exact False.elim (chain_pair_funnel H1 L.hcl L.hev1 haD hbD hab hgQ hopQ hinQ
            hchu hchv honlyu honlyv)
        · push Not at honlyv
          obtain ⟨r, hr, hrQ⟩ := honlyv
          exact hfrom_branch b a psv v hbD haD hab.symm hchv
            ⟨Q, r, Ne.symm hrQ, ⟨gQ, hgQ, by rw [hinQ]; simp⟩, hr⟩
      · push Not at honlyu
        obtain ⟨r, hr, hrQ⟩ := honlyu
        exact hfrom_branch a b psu u haD hbD hab hchu
          ⟨Q, r, Ne.symm hrQ, ⟨gQ, hgQ, by rw [hinQ]; simp⟩, hr⟩

end PEqualNP.Outside.L_meta_605_aux

theorem PEqualNP.Outside.L_meta_605 :
    ∀ (n s : ℕ) (F1 F2 : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))),
    (∀ F ∈ [F1, F2],
      (∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
        F (Function.update x y b) ≠ F (Function.update x' y b)) ∧
      (∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ ∃ a b : Bool, ∀ x : Fin (n + 1) → Bool,
        F (Function.update (Function.update x y (!a)) y' b) =
        F (Function.update (Function.update x y a) y' (!b)) ∧
        F (Function.update (Function.update x y a) y' (!b)) =
        F (Function.update (Function.update x y (!a)) y' (!b))) ∧
      (∀ y ∈ D, ∀ x : Fin (n + 1) → Bool,
        F (fun i => if i ∈ D then false else x i) = false →
        ∃ x' : Fin (n + 1) → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧
          F x' = false ∧ F (Function.update x' y true) = true) ∧
      (∀ x : Fin (n + 1) → Bool, F (fun i => if i ∈ D then false else x i) = true → F x = true) ∧
      (∃ z : Fin (n + 1) → Bool, (∀ y ∈ D, z y = false) ∧ F z = false)) →
    D.Nonempty →
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
      ∃ o1 o2 : ℕ, ∀ x : Fin (n + 1) → Bool,
        (C.wires (List.ofFn x)).getD o1 false = F1 x ∧
        (C.wires (List.ofFn x)).getD o2 false = F2 x) →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s' ∧
        ∃ o1 o2 : ℕ, ∀ x : Fin (n + 1) → Bool,
          (C.wires (List.ofFn x)).getD o1 false = F1 (Function.update x y false) ∧
          (C.wires (List.ofFn x)).getD o2 false = F2 (Function.update x y false)) ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s' ∧
        ∃ o1 o2 : ℕ, ∀ x : Fin (n + 1) → Bool,
          (C.wires (List.ofFn x)).getD o1 false = F1 (Function.update x y true) ∧
          (C.wires (List.ofFn x)).getD o2 false = F2 (Function.update x y true)) := by
  intro n s F1 F2 D hF hne hs
  have H1 : PEqualNP.Outside.L_meta_605_aux.DeepHyp' F1 D := hF F1 (by simp)
  have H2 : PEqualNP.Outside.L_meta_605_aux.DeepHyp' F2 D := hF F2 (by simp)
  exact PEqualNP.Outside.L_meta_605_aux.stmtML2 n s F1 F2 D H1 H2 hne hs
